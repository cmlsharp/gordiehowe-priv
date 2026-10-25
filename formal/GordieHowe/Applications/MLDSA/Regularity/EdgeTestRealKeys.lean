-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Regularity.StandinError44

@[expose] public section

/-!
# The edge test against real keys and the real signer

This file composes the three ingredients of result 3 (`analysis/nowhereman/README.md`,
"Result 3") into one bound at ML-DSA-44, ML-DSA-65 and ML-DSA-87.

**The game.** `SampleInBall` is a random oracle `G : CommitHashBytes → B_τ` (`ChallengeOracle`,
`oraclePrims G`), and `ExpandA` is a random oracle, so `Â` is uniform and independent of the
secret. The secret `(s₁, s₂)` has a law `S`; at ML-DSA-65 and ML-DSA-87 it is the ExpandS law of a
uniform key-generation seed (`deviceSecretLaw`, FIPS 204 Algorithm 6), and at ML-DSA-44 the law of
a uniform box secret, with `ExpandS` a random oracle as well (`oracleSecretLaw`). The key is `t = Â s₁ + s₂`, and
the adversary sees `t₁`. A real presentation `(w₁, c̃)` follows the law of the idealized FIPS 204
signer (`realPresentationLaw`, the accepted pair of `acceptedCommitLawOf`; at the concrete
primitives this is `acceptedCommitLaw`, `acceptedCommitLaw_eq_acceptedCommitLawOf`). A simulated
presentation follows a law `Q G` that may depend on the oracle `G` but not on the key.
`realKeyEdgeAcceptProb` is the probability that the edge test outputs `1`, averaged over
`(s₁, s₂) ← S`, `Â` and `G`.

**The laws.**
* `toReal_acceptedCommitLawOf`, `isRealCommitLaw_realPresentationLaw`: the real law is the
  normalized real accepted mass `realMass` whenever that mass is positive. Where it is zero the
  signer never accepts; `IsRealCommitLaw` and the distance bound of `StandinError.lean` need
  nothing there, so no positivity hypothesis on the key remains.
* `standinCommitLaw`: the normalized stand-in weight `t0Weight` (density proportional to the
  stand-in score against the uniform law, as in `edge_test.cc`).
  `isStandinCommitLaw_standinCommitLaw`: it is a stand-in commitment law. When `τ · 2^12 < γ₂`
  (true at ML-DSA-65 and ML-DSA-87) its total weight is positive for every `t₀` with
  `‖t₀‖∞ ≤ 2^12` (`sum_t0Weight_pos`); at ML-DSA-44 it can vanish.

**The composition.**
* `PMF.abs_sum_toReal_mul_sub_le_tvDist`: a `[0, 1]`-valued test accepts with probabilities that
  differ by at most the total variation distance of the two laws.
* `oracleEdgeHybridAdv_sub_le_realKeyEdgeAdvantage`: for every key-independent `Q`,
  `Pr_real[g = 1] - Pr_Q[g = 1] ≥ oracleEdgeHybridAdv - Pr[E]/(2·8193²) - Adv^MLWE_S(B_g) - ε - δ`,
  with `ε` bounding `Adv^MLWE_S(B_x)` for every oracle and observation, and `δ` bounding the
  averaged distance between the real and the stand-in laws.
* `edgeTest_real_sub_simulator_ge_mldsa65`, `_mldsa87`: the same with `δ` the stand-in error
  of `sum_expect_tvDist_standin_le_mldsa65` / `_mldsa87`.
* `edgeTest_real_sub_simulator_ge_mldsa44`: the same with `S = oracleSecretLaw` and `δ = 2^-95`,
  the stand-in error of `sum_expect_tvDist_standin_le_mldsa44`, which has no MLWE term.

**What is assumed and not formalized.** `oracleEdgeHybridAdv` is measured outside Lean
(`edge_test.cc`, with the SHAKE-based `SampleInBall` standing in for the oracle); this file
proves nothing about its size. The MLWE advantages of `B_g` (`oracleStandinTest`), `B_x`
(`observationTest`) and `B_typ` (`atypicalTest`) enter as terms or hypotheses: MLWE is an
assumption. The efficiency of these tests is not formalized. `Pr[E]` (`edgeEventProb`) is not
evaluated here.
-/

open Finset Real
open scoped BigOperators ENNReal

namespace GordieHowe.MLDSA.Regularity

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA
open LatticeCrypto TransformOps
open PMF (tvDist tvDist_le_one)

/-! ### Bounded tests and total variation -/

/-- **A bounded test separates two laws by at most their distance**: for `f` with values in
`[0, 1]`, `|𝔼_P f - 𝔼_Q f| ≤ tvDist P Q`. -/
theorem PMF.abs_sum_toReal_mul_sub_le_tvDist {X : Type*} [Fintype X] (P Q : PMF X) (f : X → ℝ)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    |∑ x, (P x).toReal * f x - ∑ x, (Q x).toReal * f x| ≤ tvDist P Q := by
  have heq : ∑ x, (P x).toReal * f x - ∑ x, (Q x).toReal * f x =
      ∑ x, ((P x).toReal - (Q x).toReal) * (f x - 1 / 2) := by
    have hP := PMF.sum_toReal_eq_one P
    have hQ := PMF.sum_toReal_eq_one Q
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hP, hQ]
    ring
  rw [heq, PMF.tvDist_eq_sum, Finset.sum_div]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [abs_mul]
  have h : |f x - 1 / 2| ≤ 1 / 2 := abs_le.2 ⟨by linarith [(hf x).1], by linarith [(hf x).2]⟩
  calc |(P x).toReal - (Q x).toReal| * |f x - 1 / 2|
      ≤ |(P x).toReal - (Q x).toReal| * (1 / 2) := mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = |(P x).toReal - (Q x).toReal| / 2 := by ring

attribute [local instance] concreteNTTRingOps

/-! ### The real presentation law -/

section RealLaw

variable {p : Params} [NeZero (bucketCount p)] [Nonempty (MaskBox p)]
  (prims : Primitives p) (sk : SecretKey p) (aHat : TqMatrix p.k p.l)

/-- **The accepted commitment law** of the idealized FIPS 204 signer with primitives `prims`, key
`sk` and matrix `Â`: the pair `(w1, c̃) = (HighBits(Â·y), c̃)` of the first accepted attempt
(`y` uniform on the mask box, `c̃` a fresh uniform hash). If the attempt never accepts the signer
outputs nothing, and this definition falls back to the uniform law. `acceptedCommitLaw` is its
instance at the device key (`acceptedCommitLaw_eq_acceptedCommitLawOf`). -/
noncomputable def acceptedCommitLawOf : PMF (BucketVec p × CommitHashBytes p) :=
  if h : PMF.acceptProb (maskUniform p) (attemptAccept prims sk aHat) = 0 then
    PMF.uniformOfFintype _
  else
    (PMF.condSome (PMF.rejectionAttempt (maskUniform p) (attemptAccept prims sk aHat))
      (PMF.rejectionAttempt_apply_none_ne_one h)).map fun yc => (realBuckets aHat yc.1, yc.2)

/-- The accepted commitment law of the device key is `acceptedCommitLawOf` at the concrete
primitives, the device key and its matrix. -/
theorem acceptedCommitLaw_eq_acceptedCommitLawOf (seed : Bytes 32) :
    acceptedCommitLaw p seed =
      acceptedCommitLawOf (Spec.concretePrimitivesKeyGen p) (deviceKey p seed)
        (deviceMatrix p seed) :=
  rfl

/-- **The real accepted mass sums to `|C|` times the acceptance probability.** -/
theorem sum_realMass_eq :
    ∑ vc : BucketVec p × CommitHashBytes p, realMass prims sk aHat vc.1 vc.2 =
      (Fintype.card (CommitHashBytes p) : ℝ≥0∞) *
        PMF.acceptProb (maskUniform p) (attemptAccept prims sk aHat) := by
  classical
  have hC0 : (Fintype.card (CommitHashBytes p) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hCt : (Fintype.card (CommitHashBytes p) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [PMF.acceptProb, Finset.mul_sum]
  have hterm : ∀ c, (Fintype.card (CommitHashBytes p) : ℝ≥0∞) *
      (PMF.acceptProbAt (maskUniform p) (attemptAccept prims sk aHat) c *
        (Fintype.card (CommitHashBytes p) : ℝ≥0∞)⁻¹) =
      PMF.acceptProbAt (maskUniform p) (attemptAccept prims sk aHat) c := fun c => by
    rw [mul_comm, mul_assoc, ENNReal.inv_mul_cancel hC0 hCt, mul_one]
  simp_rw [hterm]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [realMass, PMF.signerMass, PMF.acceptProbAt]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp_rw [ite_and]
  rw [Finset.sum_ite_eq]
  simp

/-- **The accepted commitment law has density proportional to the real accepted mass**:
`realMass v c̃ · |C|⁻¹ / ᾱ` when the acceptance probability `ᾱ` is positive. -/
theorem acceptedCommitLawOf_apply
    (h : PMF.acceptProb (maskUniform p) (attemptAccept prims sk aHat) ≠ 0)
    (vc : BucketVec p × CommitHashBytes p) :
    acceptedCommitLawOf prims sk aHat vc =
      realMass prims sk aHat vc.1 vc.2 * (Fintype.card (CommitHashBytes p) : ℝ≥0∞)⁻¹ /
        PMF.acceptProb (maskUniform p) (attemptAccept prims sk aHat) := by
  classical
  obtain ⟨v, c⟩ := vc
  rw [acceptedCommitLawOf, dite_eq_right_of_eq_false (eq_false h), PMF.map_apply, tsum_fintype,
    Fintype.sum_prod_type]
  simp_rw [PMF.condSome_rejectionAttempt_apply h, Prod.mk.injEq]
  simp only [realMass, PMF.signerMass, div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_eq_single c (fun c' _ hc' => by simp [Ne.symm hc']) (by simp)]
  by_cases hv : v = realBuckets aHat y
  · subst hv
    by_cases ha : attemptAccept prims sk aHat y c = true <;> simp [ha]
  · simp [hv, Ne.symm hv]

/-- **The real law is the normalized real accepted mass**, whenever that mass is positive. -/
theorem toReal_acceptedCommitLawOf
    (hpos : 0 < ∑ vc' : BucketVec p × CommitHashBytes p,
      (realMass prims sk aHat vc'.1 vc'.2).toReal)
    (vc : BucketVec p × CommitHashBytes p) :
    (acceptedCommitLawOf prims sk aHat vc).toReal =
      (realMass prims sk aHat vc.1 vc.2).toReal /
        ∑ vc' : BucketVec p × CommitHashBytes p, (realMass prims sk aHat vc'.1 vc'.2).toReal := by
  have hfin : ∀ vc' : BucketVec p × CommitHashBytes p,
      realMass prims sk aHat vc'.1 vc'.2 ≠ ⊤ := fun vc' =>
    ENNReal.sum_ne_top.2 fun y _ => by split_ifs <;> simp [PMF.apply_ne_top]
  have hsum : ∑ vc' : BucketVec p × CommitHashBytes p,
      (realMass prims sk aHat vc'.1 vc'.2).toReal =
      (Fintype.card (CommitHashBytes p) : ℝ) *
        (PMF.acceptProb (maskUniform p) (attemptAccept prims sk aHat)).toReal := by
    rw [← ENNReal.toReal_sum fun vc' _ => hfin vc', sum_realMass_eq, ENNReal.toReal_mul,
      ENNReal.toReal_natCast]
  have h : PMF.acceptProb (maskUniform p) (attemptAccept prims sk aHat) ≠ 0 := fun h0 => by
    rw [hsum, h0, ENNReal.toReal_zero, mul_zero] at hpos
    exact lt_irrefl _ hpos
  have hC : (0 : ℝ) < Fintype.card (CommitHashBytes p) := by exact_mod_cast Fintype.card_pos
  have hA : 0 < (PMF.acceptProb (maskUniform p) (attemptAccept prims sk aHat)).toReal := by
    rw [hsum] at hpos
    exact pos_of_mul_pos_right hpos hC.le
  rw [acceptedCommitLawOf_apply prims sk aHat h, hsum, ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]
  field_simp

/-- **The device key with secret `(s₁, s₂)`.** The idealized signer reads only `s₁`, `s₂` and
`t₀` (`signAccept`), and the regularity key `matrixKey` recomputes `t₀` from `Â s₁ + s₂`; the
seeds `ρ`, `K` and `tr` are placeholders. -/
def secretKeyOfPair (s : RqVec p.l × RqVec p.k) : SecretKey p :=
  ⟨default, default, default, s.1, s.2, 0⟩

/-- **The real presentation law** in the random-oracle game: the accepted `(w₁, c̃)` of the
idealized signer with `SampleInBall = G`, under the key with secret `s` and `t₀` from
`t = Â s₁ + s₂`. -/
noncomputable def realPresentationLaw (s : RqVec p.l × RqVec p.k)
    (G : CommitHashBytes p → ChallengeBall p.tau) (aHat : TqMatrix p.k p.l) :
    PMF (BucketVec p × CommitHashBytes p) :=
  acceptedCommitLawOf (oraclePrims G) (matrixKey (secretKeyOfPair s) aHat) aHat

/-- The real presentation law is a real commitment law in the sense of `IsRealCommitLaw`. -/
theorem isRealCommitLaw_realPresentationLaw (s : RqVec p.l × RqVec p.k) :
    IsRealCommitLaw (secretKeyOfPair s) (realPresentationLaw s) :=
  fun _ _ hpos vc => toReal_acceptedCommitLawOf _ _ _ hpos vc

end RealLaw

/-! ### The stand-in law -/

section StandinLaw

variable {p : Params} [NeZero (bucketCount p)]

/-- **The random oracle `SampleInBall`**: a function from commitment hashes onto the challenge
set `B_τ`. -/
abbrev ChallengeOracle (p : Params) : Type := CommitHashBytes p → ChallengeBall p.tau

/-- **The stand-in commitment law** of `t₀` with `SampleInBall = G`: density proportional to the
stand-in weight `t0Weight` (the acceptance weight of the ct₀ and hint checks, `standinScore`)
against the uniform law on `(w₁, c̃)`. If the total weight is zero this definition falls back to
the uniform law. -/
noncomputable def standinCommitLaw (G : ChallengeOracle p) (t0 : RqVec p.k) :
    PMF (BucketVec p × CommitHashBytes p) :=
  if h : ∑ vc, t0Weight (oraclePrims G) t0 vc = 0 then PMF.uniformOfFintype _ else
    PMF.ofFintype
      (fun vc => t0Weight (oraclePrims G) t0 vc / ∑ vc', t0Weight (oraclePrims G) t0 vc')
      (by
        simp only [div_eq_mul_inv, ← Finset.sum_mul]
        exact ENNReal.mul_inv_cancel h (ENNReal.sum_ne_top.2 fun _ _ => ENNReal.ofReal_ne_top))

/-- **The stand-in weight has positive total** when the ct₀ check always passes:
for `τ · 2^12 < γ₂` and `‖t₀‖∞ ≤ 2^12`, every challenge `c ∈ B_τ` gives `‖c t₀‖∞ < γ₂`, so every
acceptance weight is positive (`acceptWeight_pos`). -/
theorem sum_t0Weight_pos (hp : p.isApproved) (hγ : p.tau * 4096 < p.gamma2)
    (G : ChallengeOracle p) (t0 : RqVec p.k) (ht0 : polyVecNorm t0 ≤ 4096) :
    0 < ∑ vc, (t0Weight (oraclePrims G) t0 vc).toReal := by
  have hsp := SigningParams.of_isApproved hp
  have := concreteNTTRingLaws
  obtain ⟨c0⟩ : Nonempty (CommitHashBytes p) := inferInstance
  obtain ⟨v0⟩ : Nonempty (BucketVec p) := inferInstance
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun vc _ => ENNReal.toReal_nonneg)
    (Finset.mem_univ (v0, c0)))
  rw [t0Weight, ENNReal.toReal_ofReal (acceptWeight_nonneg hsp.beta_lt_gamma2 _ _ _)]
  refine acceptWeight_pos hsp.beta_lt_gamma2 _ (fun x => ?_) _
  have hn := norm_challenge_coeffScalarVecMul_le concreteNTTRingOps (G c0).1 t0 (G c0).2.1
    (G c0).2.2.le ht0
  have h := GordieHowe.MLDSA44.natAbs_centeredRepr_le_polyVecNorm ((G c0).1 • t0) x.1 x.2
  have h' : (centeredCoeffs ((G c0).1 • t0) x).natAbs < p.gamma2 := (h.trans hn).trans_lt hγ
  rw [Int.abs_eq_natAbs]
  exact_mod_cast h'

/-- **The stand-in law is a stand-in commitment law.** -/
theorem isStandinCommitLaw_standinCommitLaw : IsStandinCommitLaw (standinCommitLaw (p := p)) := by
  intro G t0 _ hpos vc
  have hfin : ∀ vc' : BucketVec p × CommitHashBytes p, t0Weight (oraclePrims G) t0 vc' ≠ ⊤ :=
    fun _ => ENNReal.ofReal_ne_top
  rw [← ENNReal.toReal_sum fun vc' _ => hfin vc'] at hpos
  have h : ∑ vc', t0Weight (oraclePrims G) t0 vc' ≠ 0 := fun h0 => by
    rw [h0, ENNReal.toReal_zero] at hpos
    exact lt_irrefl _ hpos
  rw [standinCommitLaw, dite_eq_right_of_eq_false (eq_false h), PMF.ofFintype_apply,
    ENNReal.toReal_div,
    ENNReal.toReal_sum fun vc' _ => hfin vc']

end StandinLaw

/-! ### Averages over the game -/

section Averages

variable {p : Params}

/-- **The average over the game** of a quantity `F s Â G`: `(s₁, s₂) ← S`, `Â` uniform (`ExpandA`
a random oracle) and `G` uniform (`SampleInBall` a random oracle). -/
noncomputable def realKeyMean (S : PMF (RqVec p.l × RqVec p.k))
    (F : RqVec p.l × RqVec p.k → TqMatrix p.k p.l → ChallengeOracle p → ℝ) : ℝ :=
  ∑ s, (S s).toReal * 𝔼 aHat : TqMatrix p.k p.l, 𝔼 G : ChallengeOracle p, F s aHat G

/-- **The acceptance probability of the edge test with real keys**: `Pr[g(t₁, x) = 1]` for
`(s₁, s₂) ← S`, `Â` and `G` uniform, `t = Â s₁ + s₂` and the presentation `x` drawn from
`obs s G Â`, with `c = G(c̃)` in the test. -/
noncomputable def realKeyEdgeAcceptProb (S : PMF (RqVec p.l × RqVec p.k))
    (obs : RqVec p.l × RqVec p.k → ChallengeOracle p → TqMatrix p.k p.l →
      PMF (BucketVec p × CommitHashBytes p)) : ℝ :=
  realKeyMean S fun s aHat G =>
    ∑ x, (obs s G aHat x).toReal * edgeTestOutput p (oraclePrims G) (t1Of p (aHat * s.1 + s.2)) x

/-- A uniform average is the sum against the uniform law. -/
theorem expect_eq_sum_uniformOfFintype {α : Type*} [Fintype α] [Nonempty α] (g : α → ℝ) :
    𝔼 a, g a = ∑ a, (PMF.uniformOfFintype α a).toReal * g a := by
  rw [Fintype.expect_eq_sum_div_card, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [PMF.toReal_uniformOfFintype_apply]
  ring

/-- The game average is linear. -/
theorem realKeyMean_sub (S : PMF (RqVec p.l × RqVec p.k))
    (F H : RqVec p.l × RqVec p.k → TqMatrix p.k p.l → ChallengeOracle p → ℝ) :
    realKeyMean S (fun s aHat G => F s aHat G - H s aHat G) =
      realKeyMean S F - realKeyMean S H := by
  simp only [realKeyMean, Finset.expect_sub_distrib, mul_sub, Finset.sum_sub_distrib]

/-- The game average is monotone. -/
theorem realKeyMean_mono (S : PMF (RqVec p.l × RqVec p.k))
    {F H : RqVec p.l × RqVec p.k → TqMatrix p.k p.l → ChallengeOracle p → ℝ}
    (h : ∀ s aHat G, F s aHat G ≤ H s aHat G) : realKeyMean S F ≤ realKeyMean S H :=
  Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
    (Finset.expect_le_expect fun aHat _ => Finset.expect_le_expect fun G _ => h s aHat G)
    ENNReal.toReal_nonneg

/-- **A test that reads `(Â, t)`, averaged over the game**, is the oracle average of its real
MLWE means. -/
theorem realKeyMean_eq_expect_mlweRealMean (S : PMF (RqVec p.l × RqVec p.k))
    (f : ChallengeOracle p → TqMatrix p.k p.l → RqVec p.k → ℝ) :
    realKeyMean S (fun s aHat G => f G aHat (aHat * s.1 + s.2)) =
      𝔼 G : ChallengeOracle p, mlweRealMean S (f G) := by
  simp only [realKeyMean, mlweRealMean, expect_eq_sum_uniformOfFintype (α := TqMatrix p.k p.l),
    Finset.expect_sum_comm, ← Finset.mul_expect, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun aHat _ => Finset.sum_congr rfl fun s _ => ?_
  ring

/-- The real MLWE mean commutes with an average over the oracle. -/
theorem mlweRealMean_expect (S : PMF (RqVec p.l × RqVec p.k))
    (f : ChallengeOracle p → TqMatrix p.k p.l → RqVec p.k → ℝ) :
    mlweRealMean S (fun aHat t => 𝔼 G : ChallengeOracle p, f G aHat t) =
      𝔼 G : ChallengeOracle p, mlweRealMean S (f G) := by
  simp only [mlweRealMean, Finset.mul_expect, Finset.expect_sum_comm]

/-- The uniform MLWE mean commutes with an average over the oracle. -/
theorem mlweUniformMean_expect (f : ChallengeOracle p → TqMatrix p.k p.l → RqVec p.k → ℝ) :
    mlweUniformMean (fun aHat t => 𝔼 G : ChallengeOracle p, f G aHat t) =
      𝔼 G : ChallengeOracle p, mlweUniformMean (f G) := by
  simp only [mlweUniformMean, Finset.mul_expect, Finset.expect_sum_comm]

end Averages

/-! ### The composition -/

section Compose

variable (p : Params) [NeZero (bucketCount p)] [Nonempty (MaskBox p)]

/-- **The hybrid advantage of the edge test in the random-oracle game**: `edgeHybridAdv` with
`SampleInBall = G` and presentations from the stand-in law, averaged over `G`. This is the
quantity `edge_test.cc` measures (with the SHAKE-based `SampleInBall` in place of the oracle);
its size is not proved here. -/
noncomputable def oracleEdgeHybridAdv : ℝ :=
  𝔼 G : ChallengeOracle p, edgeHybridAdv p (oraclePrims G) (standinCommitLaw G)

/-- **`B_g` in the random-oracle game**: on an MLWE instance `(Â, t)`, draw the oracle `G`,
sample a presentation from the stand-in law of `t₀` and run the edge test on `t₁`. -/
noncomputable def oracleStandinTest : TqMatrix p.k p.l → RqVec p.k → ℝ :=
  fun aHat t => 𝔼 G : ChallengeOracle p, standinTest p (oraclePrims G) (standinCommitLaw G) aHat t

/-- **The edge test against every simulator, with real keys and the real signer.** In the
random-oracle game, let `ε` bound the MLWE advantage of every fixed-observation test `B_x`
(`observationTest`, for every oracle `G`), and let `δ` bound the averaged distance between the
real presentation law and the stand-in law. Then for every law `Q G` of the simulated
presentation that does not depend on the key,
`Pr_real[g = 1] - Pr_Q[g = 1] ≥
  oracleEdgeHybridAdv - Pr[E]/(2·8193²) - Adv^MLWE_S(B_g) - ε - δ`. -/
theorem oracleEdgeHybridAdv_sub_le_realKeyEdgeAdvantage (hp : p.isApproved)
    (S : PMF (RqVec p.l × RqVec p.k)) {ε δ : ℝ}
    (hε : ∀ (G : ChallengeOracle p) x, mlweAdvantage S (observationTest p (oraclePrims G) x) ≤ ε)
    (hδ : realKeyMean S (fun s aHat G => tvDist (realPresentationLaw s G aHat)
      (standinCommitLaw G (matrixKey (secretKeyOfPair s) aHat).t0)) ≤ δ)
    (Q : ChallengeOracle p → PMF (BucketVec p × CommitHashBytes p)) :
    oracleEdgeHybridAdv p - edgeEventProb p / (2 * 8193 ^ 2) -
        mlweAdvantage S (oracleStandinTest p) - ε - δ ≤
      realKeyEdgeAcceptProb S realPresentationLaw - realKeyEdgeAcceptProb S (fun _ G _ => Q G) := by
  have := challengeBall_nonempty (tau_le_ringDegree hp)
  set Sd : ChallengeOracle p → TqMatrix p.k p.l → RqVec p.k → ℝ := fun G =>
    standinTest p (oraclePrims G) (standinCommitLaw G)
  set Sm : ChallengeOracle p → TqMatrix p.k p.l → RqVec p.k → ℝ := fun G =>
    simulatorTest p (oraclePrims G) (Q G)
  -- The real law against the stand-in law, pointwise.
  have hpt : ∀ s aHat (G : ChallengeOracle p),
      Sd G aHat (aHat * s.1 + s.2) - Sm G aHat (aHat * s.1 + s.2) -
          tvDist (realPresentationLaw s G aHat)
            (standinCommitLaw G (matrixKey (secretKeyOfPair s) aHat).t0) ≤
        ∑ x, (realPresentationLaw s G aHat x).toReal *
            edgeTestOutput p (oraclePrims G) (t1Of p (aHat * s.1 + s.2)) x -
          Sm G aHat (aHat * s.1 + s.2) := fun s aHat G => by
    have h := PMF.abs_sum_toReal_mul_sub_le_tvDist (realPresentationLaw s G aHat)
      (standinCommitLaw G (matrixKey (secretKeyOfPair s) aHat).t0)
      (edgeTestOutput p (oraclePrims G) (t1Of p (aHat * s.1 + s.2)))
      (edgeTestOutput_mem_Icc p (oraclePrims G) _)
    have hSd : Sd G aHat (aHat * s.1 + s.2) =
        ∑ x, (standinCommitLaw G (matrixKey (secretKeyOfPair s) aHat).t0 x).toReal *
          edgeTestOutput p (oraclePrims G) (t1Of p (aHat * s.1 + s.2)) x := by
      simp only [Sd, standinTest, matrixKey_t0]
      rfl
    rw [hSd]
    linarith [neg_abs_le (∑ x, (realPresentationLaw s G aHat x).toReal *
        edgeTestOutput p (oraclePrims G) (t1Of p (aHat * s.1 + s.2)) x -
      ∑ x, (standinCommitLaw G (matrixKey (secretKeyOfPair s) aHat).t0 x).toReal *
        edgeTestOutput p (oraclePrims G) (t1Of p (aHat * s.1 + s.2)) x)]
  have hmono : realKeyMean S (fun s aHat G =>
        Sd G aHat (aHat * s.1 + s.2) - Sm G aHat (aHat * s.1 + s.2)) -
      realKeyMean S (fun s aHat G => tvDist (realPresentationLaw s G aHat)
        (standinCommitLaw G (matrixKey (secretKeyOfPair s) aHat).t0)) ≤
      realKeyMean S (fun s aHat G => ∑ x, (realPresentationLaw s G aHat x).toReal *
          edgeTestOutput p (oraclePrims G) (t1Of p (aHat * s.1 + s.2)) x) -
        realKeyMean S (fun s aHat G => Sm G aHat (aHat * s.1 + s.2)) := by
    rw [← realKeyMean_sub, ← realKeyMean_sub]
    exact realKeyMean_mono S hpt
  have hkey := realKeyMean_eq_expect_mlweRealMean S (fun G aHat t => Sd G aHat t - Sm G aHat t)
  beta_reduce at hkey
  rw [hkey] at hmono
  have hreal : realKeyEdgeAcceptProb S realPresentationLaw -
      realKeyEdgeAcceptProb S (fun _ G _ => Q G) =
      realKeyMean S (fun s aHat G => ∑ x, (realPresentationLaw s G aHat x).toReal *
          edgeTestOutput p (oraclePrims G) (t1Of p (aHat * s.1 + s.2)) x) -
        realKeyMean S (fun s aHat G => Sm G aHat (aHat * s.1 + s.2)) := rfl
  rw [hreal]
  -- The stand-in side: the MLWE hop on the oracle-averaged `B_g`.
  have hdiff : 𝔼 G : ChallengeOracle p, mlweRealMean S (fun aHat t => Sd G aHat t - Sm G aHat t) =
      mlweRealMean S (oracleStandinTest p) - 𝔼 G : ChallengeOracle p, mlweRealMean S (Sm G) := by
    unfold oracleStandinTest
    rw [mlweRealMean_expect, ← Finset.expect_sub_distrib]
    refine Finset.expect_congr rfl fun G _ => ?_
    simp only [mlweRealMean, mul_sub, Finset.sum_sub_distrib]
    rfl
  have hunif : mlweUniformMean (oracleStandinTest p) = 1 / 2 + oracleEdgeHybridAdv p := by
    unfold oracleStandinTest
    rw [mlweUniformMean_expect, oracleEdgeHybridAdv]
    simp_rw [mlweUniformMean_standinTest]
    rw [Finset.expect_add_distrib, Finset.expect_const Finset.univ_nonempty]
  have hBg := abs_mlweRealMean_sub_mlweUniformMean_le S (oracleStandinTest p)
  rw [hunif] at hBg
  -- The simulator side: every key-independent `Q G` gets a fair coin.
  have hsim : 𝔼 G : ChallengeOracle p, mlweRealMean S (Sm G) ≤
      1 / 2 + edgeEventProb p / (2 * 8193 ^ 2) + ε := by
    refine (Finset.expect_le_expect fun G _ => ?_).trans_eq
      (Finset.expect_const Finset.univ_nonempty _)
    have h := abs_mlweRealMean_simulatorTest_sub_half_le_of_forall p (oraclePrims G) S (hε G) (Q G)
    linarith [le_abs_self (mlweRealMean S (simulatorTest p (oraclePrims G) (Q G)) - 1 / 2)]
  rw [hdiff] at hmono
  linarith [neg_abs_le (mlweRealMean S (oracleStandinTest p) - (1 / 2 + oracleEdgeHybridAdv p))]

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] in
/-- The device secret `(s₁, s₂)` lies in the `η`-box. -/
theorem deviceSecretLaw_bounded (hp : p.isApproved) (s : RqVec p.l × RqVec p.k)
    (hs : deviceSecretLaw p s ≠ 0) :
    polyVecBounded s.1 p.eta ∧ polyVecBounded s.2 p.eta := by
  obtain ⟨seed, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 ((PMF.mem_support_iff _ _).2 hs)
  exact ⟨Spec.keyGenFromSeed_s1_bounded hp seed, Spec.keyGenFromSeed_s2_bounded hp seed⟩

end Compose

/-! ### ML-DSA-65 and ML-DSA-87 -/

section Instances

/-- **Result 3 at ML-DSA-65: the edge test separates every key-independent simulator from the
real signer, with real keys.** In the game where `SampleInBall` and `ExpandA` are random oracles
and the device secret comes from ExpandS on a uniform seed (`deviceSecretLaw`), suppose every
fixed-observation test `B_x` has MLWE advantage at most `ε`. Then for every law `Q G` of the
simulated `(w₁, c̃)` that may depend on the oracle `G` but not on the device key,
`Pr_real[g = 1] - Pr_Q[g = 1] ≥ oracleEdgeHybridAdv - Pr[E]/(2·8193²) - Adv^MLWE(B_g) - ε -
(2^-60 + Adv^MLWE(B_typ) + 2^-56)`, where `B_typ` tests `‖t₀‖₂² > (9/20) · 1536 · 2^24`.

What is assumed: `oracleEdgeHybridAdv` is measured outside Lean (`edge_test.cc`), and nothing
about its size is proved here; the MLWE advantages of `B_g`, `B_x` and `B_typ` are assumptions
(`ε` is a hypothesis, the others are terms of the bound); the efficiency of the tests is not
formalized. -/
theorem edgeTest_real_sub_simulator_ge_mldsa65 {ε : ℝ}
    (hε : ∀ (G : ChallengeOracle mldsa65) x,
      mlweAdvantage (deviceSecretLaw mldsa65) (observationTest mldsa65 (oraclePrims G) x) ≤ ε)
    (Q : ChallengeOracle mldsa65 → PMF (BucketVec mldsa65 × CommitHashBytes mldsa65)) :
    oracleEdgeHybridAdv mldsa65 - edgeEventProb mldsa65 / (2 * 8193 ^ 2) -
        mlweAdvantage (deviceSecretLaw mldsa65) (oracleStandinTest mldsa65) - ε -
        (1 / 2 ^ 60 + mlweAdvantage (deviceSecretLaw mldsa65)
          (atypicalTest mldsa65 (Atypical (9 / 20 * (1536 * 4096 ^ 2)))) + 1 / 2 ^ 56) ≤
      realKeyEdgeAcceptProb (deviceSecretLaw mldsa65) realPresentationLaw -
        realKeyEdgeAcceptProb (deviceSecretLaw mldsa65) (fun _ G _ => Q G) := by
  have hp : mldsa65.isApproved := Or.inr (Or.inl rfl)
  refine oracleEdgeHybridAdv_sub_le_realKeyEdgeAdvantage mldsa65 hp _ hε ?_ Q
  exact sum_expect_tvDist_standin_le_mldsa65 (deviceSecretLaw mldsa65)
    (deviceSecretLaw_bounded mldsa65 hp) secretKeyOfPair (fun _ => rfl) (fun _ => rfl)
    realPresentationLaw isRealCommitLaw_realPresentationLaw standinCommitLaw
    isStandinCommitLaw_standinCommitLaw

/-- **Result 3 at ML-DSA-87**: as `edgeTest_real_sub_simulator_ge_mldsa65`, with stand-in error
`2^-100 + Adv^MLWE(B_typ) + 2^-100`, where `B_typ` tests `‖t₀‖₂² > (1/2) · 2048 · 2^24`.

What is assumed: `oracleEdgeHybridAdv` is measured outside Lean (`edge_test.cc`), and nothing
about its size is proved here; the MLWE advantages of `B_g`, `B_x` and `B_typ` are assumptions
(`ε` is a hypothesis, the others are terms of the bound); the efficiency of the tests is not
formalized. -/
theorem edgeTest_real_sub_simulator_ge_mldsa87 {ε : ℝ}
    (hε : ∀ (G : ChallengeOracle mldsa87) x,
      mlweAdvantage (deviceSecretLaw mldsa87) (observationTest mldsa87 (oraclePrims G) x) ≤ ε)
    (Q : ChallengeOracle mldsa87 → PMF (BucketVec mldsa87 × CommitHashBytes mldsa87)) :
    oracleEdgeHybridAdv mldsa87 - edgeEventProb mldsa87 / (2 * 8193 ^ 2) -
        mlweAdvantage (deviceSecretLaw mldsa87) (oracleStandinTest mldsa87) - ε -
        (1 / 2 ^ 100 + mlweAdvantage (deviceSecretLaw mldsa87)
          (atypicalTest mldsa87 (Atypical (1 / 2 * (2048 * 4096 ^ 2)))) + 1 / 2 ^ 100) ≤
      realKeyEdgeAcceptProb (deviceSecretLaw mldsa87) realPresentationLaw -
        realKeyEdgeAcceptProb (deviceSecretLaw mldsa87) (fun _ G _ => Q G) := by
  have hp : mldsa87.isApproved := Or.inr (Or.inr rfl)
  refine oracleEdgeHybridAdv_sub_le_realKeyEdgeAdvantage mldsa87 hp _ hε ?_ Q
  exact sum_expect_tvDist_standin_le_mldsa87 (deviceSecretLaw mldsa87)
    (deviceSecretLaw_bounded mldsa87 hp) secretKeyOfPair (fun _ => rfl) (fun _ => rfl)
    realPresentationLaw isRealCommitLaw_realPresentationLaw standinCommitLaw
    isStandinCommitLaw_standinCommitLaw

/-- **Result 3 at ML-DSA-44**: as `edgeTest_real_sub_simulator_ge_mldsa65`, in the game where
`ExpandS` is a random oracle as well, so that the device secret is a uniform box secret
(`oracleSecretLaw`), with stand-in error `2^-95` (`sum_expect_tvDist_standin_le_mldsa44`) and no
typicality test.

What is assumed: `oracleEdgeHybridAdv` is measured outside Lean (`edge_test.cc`), and nothing
about its size is proved here; the MLWE advantages of `B_g` and `B_x` are assumptions (`ε` is a
hypothesis, the other is a term of the bound); the efficiency of the tests is not formalized. -/
theorem edgeTest_real_sub_simulator_ge_mldsa44 {ε : ℝ}
    (hε : ∀ (G : ChallengeOracle _root_.MLDSA.mldsa44) x,
      mlweAdvantage (oracleSecretLaw _root_.MLDSA.mldsa44)
        (observationTest _root_.MLDSA.mldsa44 (oraclePrims G) x) ≤ ε)
    (Q : ChallengeOracle _root_.MLDSA.mldsa44 →
      PMF (BucketVec _root_.MLDSA.mldsa44 × CommitHashBytes _root_.MLDSA.mldsa44)) :
    oracleEdgeHybridAdv _root_.MLDSA.mldsa44 - edgeEventProb _root_.MLDSA.mldsa44 / (2 * 8193 ^ 2) -
        mlweAdvantage (oracleSecretLaw _root_.MLDSA.mldsa44)
          (oracleStandinTest _root_.MLDSA.mldsa44) - ε - 1 / 2 ^ 95 ≤
      realKeyEdgeAcceptProb (oracleSecretLaw _root_.MLDSA.mldsa44) realPresentationLaw -
        realKeyEdgeAcceptProb (oracleSecretLaw _root_.MLDSA.mldsa44) (fun _ G _ => Q G) := by
  refine oracleEdgeHybridAdv_sub_le_realKeyEdgeAdvantage _root_.MLDSA.mldsa44 isApproved_mldsa44 _
    hε ?_ Q
  exact sum_expect_tvDist_standin_le_mldsa44 secretKeyOfPair (fun _ => rfl) (fun _ => rfl)
    realPresentationLaw isRealCommitLaw_realPresentationLaw standinCommitLaw
    isStandinCommitLaw_standinCommitLaw

end Instances

end GordieHowe.MLDSA.Regularity
