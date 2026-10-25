-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# A distinguisher from two exchangeable keys

Finite key and observation types `K`, `C`; a key law `μ : PMF K`; for each key a law
`P k : PMF C` of the observation; a score `s : K → C → ℝ` and a scale `B`. The distinguisher
draws the key `k` and an independent copy `k'` from `μ` and, on an observation `c`, outputs `1`
with probability `(1 + (s k c - s k' c) / B) / 2` (`exchangeableOutput`; it lies in `[0, 1]` when
`0 ≤ s ≤ B`, `exchangeableOutput_mem_Icc`).

* `exchangeableAcceptProb_const`: if the observation has a law `Q` that does not depend on the
  keys, the distinguisher outputs `1` with probability exactly `1/2`, for every `Q`.
* `exchangeableAcceptProb_real`: if the observation follows `P k` of the drawn key, it outputs `1`
  with probability `1/2 + scoreGap μ P s / (2B)`, with
  `scoreGap = E_{k,k'} E_{c ← P k} (s k c - s k' c)`.
* `scoreGap_density_eq`: for the normalized score `s k c = |C| · P k c` (the density of `P k`
  against the uniform law `U`), `scoreGap` is half the expected squared `L²(U)` distance
  `E_{k,k'} ‖P k / U - P k' / U‖²`, i.e. half the expected `χ²`-type distance between the
  observation laws of two independent keys; `scoreGap_density_nonneg`, and
  `scoreGap_density_pos_iff`: it is positive exactly when two keys of positive mass have
  different observation laws.

All probabilities are real numbers: `(μ k).toReal`, `(P k c).toReal`. The statements concern one
observation; nothing here is claimed for several observations under the same key.
-/

namespace PMF

open Finset

variable {K C : Type*} [Fintype K] [Fintype C]

/-- The masses of a law on a finite type sum to `1` as real numbers. -/
theorem sum_toReal_eq_one (μ : PMF K) : ∑ k, (μ k).toReal = 1 := by
  have h := μ.tsum_coe
  rw [tsum_fintype] at h
  rw [← ENNReal.toReal_sum fun k _ => μ.apply_ne_top k, h, ENNReal.toReal_one]

/-- The probability that the exchangeable distinguisher outputs `1` on observation `c` under
keys `(k, k')`: `(1 + (s k c - s k' c) / B) / 2`. -/
noncomputable def exchangeableOutput (s : K → C → ℝ) (B : ℝ) (k k' : K) (c : C) : ℝ :=
  (1 + (s k c - s k' c) / B) / 2

omit [Fintype K] [Fintype C] in
/-- With scores in `[0, B]`, the output probability is in `[0, 1]`. -/
theorem exchangeableOutput_mem_Icc {s : K → C → ℝ} {B : ℝ} (hB : 0 < B)
    (hs : ∀ k c, 0 ≤ s k c ∧ s k c ≤ B) (k k' : K) (c : C) :
    exchangeableOutput s B k k' c ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨h1, h2⟩ := hs k c
  obtain ⟨h3, h4⟩ := hs k' c
  have hlo : -1 ≤ (s k c - s k' c) / B := by
    rw [le_div_iff₀ hB]; linarith
  have hhi : (s k c - s k' c) / B ≤ 1 := by
    rw [div_le_iff₀ hB]; linarith
  unfold exchangeableOutput
  constructor <;> linarith

/-- The probability that the exchangeable distinguisher outputs `1` when, given the keys
`(k, k')`, the observation has law `obs k k'`: `E_{k,k'} E_{c ← obs k k'} exchangeableOutput`. -/
noncomputable def exchangeableAcceptProb (μ : PMF K) (obs : K → K → PMF C) (s : K → C → ℝ)
    (B : ℝ) : ℝ :=
  ∑ k, ∑ k', (μ k).toReal * (μ k').toReal *
    ∑ c, (obs k k' c).toReal * exchangeableOutput s B k k' c

/-- **The score gap** `E_{k,k'} E_{c ← P k} (s k c - s k' c)`, with `k, k'` independent draws
from `μ`. -/
noncomputable def scoreGap (μ : PMF K) (P : K → PMF C) (s : K → C → ℝ) : ℝ :=
  ∑ k, ∑ k', (μ k).toReal * (μ k').toReal * ∑ c, (P k c).toReal * (s k c - s k' c)

/-- The swap-antisymmetric part averages to zero over two independent draws. -/
theorem sum_sum_mul_sub_eq_zero (μ : PMF K) (f : K → ℝ) :
    ∑ k, ∑ k', (μ k).toReal * (μ k').toReal * (f k - f k') = 0 := by
  have h : ∑ k, ∑ k', (μ k).toReal * (μ k').toReal * f k' =
      ∑ k, ∑ k', (μ k).toReal * (μ k').toReal * f k := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => by ring
  simp only [mul_sub, Finset.sum_sub_distrib, h, sub_self]

/-- **Simulated side**: if the observation has a law `Q` that does not depend on the keys, the
distinguisher outputs `1` with probability exactly `1/2`, whatever `Q`, `s` and `B` are. -/
theorem exchangeableAcceptProb_const (μ : PMF K) (Q : PMF C) (s : K → C → ℝ) (B : ℝ) :
    exchangeableAcceptProb μ (fun _ _ => Q) s B = 1 / 2 := by
  have hsplit : ∀ k k' : K, ∑ c, (Q c).toReal * exchangeableOutput s B k k' c =
      1 / 2 + ((fun k => ∑ c, (Q c).toReal * s k c / (2 * B)) k -
        (fun k => ∑ c, (Q c).toReal * s k c / (2 * B)) k') := by
    intro k k'
    have hQ := sum_toReal_eq_one Q
    simp only [exchangeableOutput]
    rw [← Finset.sum_sub_distrib]
    calc ∑ c, (Q c).toReal * ((1 + (s k c - s k' c) / B) / 2)
        = (∑ c, (Q c).toReal) / 2 + ∑ c, ((Q c).toReal * s k c / (2 * B) -
            (Q c).toReal * s k' c / (2 * B)) := by
          rw [Finset.sum_div, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun c _ => by ring
      _ = _ := by rw [hQ]
  simp only [exchangeableAcceptProb, hsplit, mul_add, Finset.sum_add_distrib,
    sum_sum_mul_sub_eq_zero, add_zero]
  simp only [← Finset.sum_mul, ← Finset.mul_sum, sum_toReal_eq_one, mul_one, one_mul]

/-- **Real side**: if the observation follows `P k` of the drawn key, the distinguisher outputs
`1` with probability `1/2 + scoreGap μ P s / (2B)`. -/
theorem exchangeableAcceptProb_real (μ : PMF K) (P : K → PMF C) (s : K → C → ℝ) (B : ℝ) :
    exchangeableAcceptProb μ (fun k _ => P k) s B = 1 / 2 + scoreGap μ P s / (2 * B) := by
  have hsplit : ∀ k k' : K, ∑ c, (P k c).toReal * exchangeableOutput s B k k' c =
      1 / 2 + (∑ c, (P k c).toReal * (s k c - s k' c)) / (2 * B) := by
    intro k k'
    have hP := sum_toReal_eq_one (P k)
    simp only [exchangeableOutput]
    calc ∑ c, (P k c).toReal * ((1 + (s k c - s k' c) / B) / 2)
        = (∑ c, (P k c).toReal) / 2 +
            ∑ c, (P k c).toReal * (s k c - s k' c) / (2 * B) := by
          rw [Finset.sum_div, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun c _ => by ring
      _ = _ := by rw [hP, Finset.sum_div]
  simp only [exchangeableAcceptProb, hsplit, mul_add, Finset.sum_add_distrib, scoreGap]
  rw [Finset.sum_div]
  congr 1
  · simp only [← Finset.sum_mul, ← Finset.mul_sum, sum_toReal_eq_one]
    ring
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun k' _ => by ring

/-- **The advantage** of the exchangeable distinguisher between the real observation (law
`P k`) and any key-independent simulated observation (law `Q`) is `scoreGap μ P s / (2B)`. -/
theorem exchangeableAcceptProb_real_sub_const (μ : PMF K) (P : K → PMF C) (Q : PMF C)
    (s : K → C → ℝ) (B : ℝ) :
    exchangeableAcceptProb μ (fun k _ => P k) s B - exchangeableAcceptProb μ (fun _ _ => Q) s B =
      scoreGap μ P s / (2 * B) := by
  rw [exchangeableAcceptProb_real, exchangeableAcceptProb_const]
  ring

/-- The density of `P k` against the uniform law on `C`: `|C| · P k c`. -/
noncomputable def uniformDensity (P : K → PMF C) (k : K) (c : C) : ℝ :=
  (Fintype.card C : ℝ) * (P k c).toReal

/-- **The normalized gap is half an expected `χ²`-type distance**: with the score
`s = uniformDensity P`,
`scoreGap = ½ · E_{k,k'} ‖P k / U - P k' / U‖²_{L²(U)}`, where
`‖g‖²_{L²(U)} = |C|⁻¹ · ∑_c g(c)²`. -/
theorem scoreGap_density_eq [Nonempty C] (μ : PMF K) (P : K → PMF C) :
    scoreGap μ P (uniformDensity P) =
      (1 / 2) * ∑ k, ∑ k', (μ k).toReal * (μ k').toReal *
        ((Fintype.card C : ℝ)⁻¹ *
          ∑ c, (uniformDensity P k c - uniformDensity P k' c) ^ 2) := by
  have hN : (Fintype.card C : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  set F : K → ℝ := fun k => ∑ c, (Fintype.card C : ℝ) * (P k c).toReal ^ 2 with hF
  have key : ∀ k k' : K,
      (1 / 2) * ((Fintype.card C : ℝ)⁻¹ *
          ∑ c, (uniformDensity P k c - uniformDensity P k' c) ^ 2) =
        ∑ c, (P k c).toReal * (uniformDensity P k c - uniformDensity P k' c) -
          (1 / 2) * (F k - F k') := by
    intro k k'
    simp only [hF, uniformDensity, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    field_simp
    ring
  have hanti := sum_sum_mul_sub_eq_zero μ F
  symm
  calc (1 / 2) * ∑ k, ∑ k', (μ k).toReal * (μ k').toReal *
        ((Fintype.card C : ℝ)⁻¹ * ∑ c, (uniformDensity P k c - uniformDensity P k' c) ^ 2)
      = ∑ k, ∑ k', ((μ k).toReal * (μ k').toReal *
            ∑ c, (P k c).toReal * (uniformDensity P k c - uniformDensity P k' c) -
          (1 / 2) * ((μ k).toReal * (μ k').toReal * (F k - F k'))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k' _ => ?_
        linear_combination (μ k).toReal * (μ k').toReal * key k k'
    _ = scoreGap μ P (uniformDensity P) := by
        simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hanti, mul_zero, sub_zero, scoreGap]

/-- The normalized gap is nonnegative. -/
theorem scoreGap_density_nonneg [Nonempty C] (μ : PMF K) (P : K → PMF C) :
    0 ≤ scoreGap μ P (uniformDensity P) := by
  rw [scoreGap_density_eq]
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun k' _ => ?_)
  exact mul_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    (mul_nonneg (by positivity) (Finset.sum_nonneg fun c _ => sq_nonneg _))

/-- **When the normalized gap is positive**: exactly when two keys of positive `μ`-mass have
different observation laws. -/
theorem scoreGap_density_pos_iff [Nonempty C] (μ : PMF K) (P : K → PMF C) :
    0 < scoreGap μ P (uniformDensity P) ↔
      ∃ k k', μ k ≠ 0 ∧ μ k' ≠ 0 ∧ P k ≠ P k' := by
  have hN : (0 : ℝ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hterm : ∀ k k', 0 ≤ (μ k).toReal * (μ k').toReal *
      ((Fintype.card C : ℝ)⁻¹ * ∑ c, (uniformDensity P k c - uniformDensity P k' c) ^ 2) :=
    fun k k' => mul_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      (mul_nonneg (by positivity) (Finset.sum_nonneg fun c _ => sq_nonneg _))
  rw [scoreGap_density_eq, mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 1 / 2),
    Finset.sum_pos_iff_of_nonneg fun k _ => Finset.sum_nonneg fun k' _ => hterm k k']
  constructor
  · rintro ⟨k, -, hk⟩
    rw [Finset.sum_pos_iff_of_nonneg fun k' _ => hterm k k'] at hk
    obtain ⟨k', -, hk'⟩ := hk
    refine ⟨k, k', fun h => ?_, fun h => ?_, fun h => ?_⟩
    · simp [h] at hk'
    · simp [h] at hk'
    · simp [uniformDensity, h] at hk'
  · rintro ⟨k, k', hk, hk', hne⟩
    refine ⟨k, Finset.mem_univ _,
      Finset.sum_pos_iff_of_nonneg (fun k' _ => hterm k k') |>.2 ⟨k', Finset.mem_univ _, ?_⟩⟩
    have hmk : 0 < (μ k).toReal :=
      ENNReal.toReal_pos hk (μ.apply_ne_top k)
    have hmk' : 0 < (μ k').toReal :=
      ENNReal.toReal_pos hk' (μ.apply_ne_top k')
    obtain ⟨c, hc⟩ : ∃ c, P k c ≠ P k' c := by
      by_contra h
      push Not at h
      exact hne (PMF.ext h)
    have hcR : (P k c).toReal ≠ (P k' c).toReal := fun h =>
      hc ((ENNReal.toReal_eq_toReal_iff' ((P k).apply_ne_top c) ((P k').apply_ne_top c)).1 h)
    have hsum : 0 < ∑ c, (uniformDensity P k c - uniformDensity P k' c) ^ 2 := by
      refine Finset.sum_pos_iff_of_nonneg (fun c _ => sq_nonneg _) |>.2 ⟨c, Finset.mem_univ _, ?_⟩
      have hne0 : uniformDensity P k c - uniformDensity P k' c ≠ 0 := by
        simp only [uniformDensity, ← mul_sub]
        exact mul_ne_zero hN.ne' (sub_ne_zero.2 hcR)
      exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne0))
    positivity

end PMF
