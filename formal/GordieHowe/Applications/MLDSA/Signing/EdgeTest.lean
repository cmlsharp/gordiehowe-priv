-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Signing.ChallengeDistinguisher
public import GordieHowe.Applications.MLDSA.Signing.MLWE
public import GordieHowe.Foundations.ToMathlib.SignSymmetry
import all LatticeCrypto.MLDSA.Concrete.Rounding

@[expose] public section

/-!
# The edge test: its advantage is the same against every key-independent simulator

**Setting** (`analysis/nowhereman/README.md`, "Result 3"; `analysis/nowhereman/edge_test.cc`).
In the hybrid key law, `t` is uniform on `R_q^k` (`hybridKeyLaw`), and
`(t₁, t₀) = Power2Round(t)` (FIPS 204 Algorithm 35; `t1Of`, `t0Of`). Since
`q = 1023 · 2^13 + 1`, a coefficient with `t₁ = 0` has `t₀ ∈ [0, 4096]`, and one with
`t₁ = 1023` has `t₀ ∈ [-4095, 0]`. Such a coefficient is an *edge* (`IsEdgeHigh`). Its sign
(`edgeSign`) is `+` for `t₁ = 0` and `-` for `t₁ = 1023`, and it is visible in `t₁`.

**The test** (`edgeTestValue`, `edgeTestOutput`). It reads `t₁` and the challenge hash `c̃` of
the observation `(w1, c̃)`. Let `E` be the event that some component of `t₁` has exactly two edges
(`EdgeEvent`). On `E`, take the two edges `(kp, j1)`, `(kp, j2)` of the lowest such component
(`edgePair`). Let `ρ` be their sign product, and let
`A(c) = ⟨c·X^j1, c·X^j2⟩` be the centered negacyclic correlation (`shiftCorrelation`,
`shiftCorrelation_pair`) for `c = SampleInBall(c̃)`, with `SampleInBall` taken from the
primitives `prims`: the concrete FIPS 204 Algorithm 29, or a random oracle onto the challenge set
(`Regularity/StandinError.lean`, `Regularity/EdgeTestRealKeys.lean`). Then `g = -ρ · sign A(c)`.
Off `E`, `g = 0`. The test outputs `1` with probability `(1 + g)/2`.

**The sign symmetry.** Given the edge positions, the signs are independent with mean `1/8193`.
Among the `8193` edge values of a coefficient, `4097` have `t₁ = 0` and `4096` have `t₁ = 1023`
(`card_filter_isEdgeHigh`, `sum_filter_isEdgeHigh_edgeSign`).

* `sum_hybrid_edgeTestValue`: for every observation `x`,
  `𝔼_t g(t₁, x) = 8193⁻² · 𝔼_t f_x(D)`, where `D` is the edge set and `f_x` is the sign-free
  factor `edgeTestFactor`, with `|f_x| ≤ 1_E`.
* `abs_sum_hybrid_edgeTestValue_le`: `|𝔼_t g(t₁, x)| ≤ Pr[E] / 8193²`, where `Pr[E]` is
  `edgeEventProb`.
* `abs_sum_hybrid_edgeTestOutput_sub_half_le`: `|Pr_t[g = 1 | x] - 1/2| ≤ Pr[E] / (2·8193²)`.
* `abs_edgeAcceptProb_const_sub_half_le`: for every key-independent law `Q` of the observation,
  `|Pr_Q[g = 1] - 1/2| ≤ Pr[E] / (2·8193²)`.
* `abs_edgeAcceptProb_sub_const_sub_edgeHybridAdv_le`: the test's advantage between presentations
  from a `t₀`-dependent law `P` and any key-independent `Q` is `edgeHybridAdv p prims P` up to
  `Pr[E] / (2·8193²)`. `edgeHybridAdv` is the measured quantity, `Pr_hybrid[g = 1] - 1/2` with
  presentations from `P (t₀)`. `edge_test.cc` measures it with `P` the stand-in law.

**The MLWE hop.** Four tests on an MLWE instance `(Â, t)`, all `[0, 1]`-valued:
* `standinTest P` (`B_g`): it samples a presentation from `P (t₀)` and runs the edge test;
* `observationTest x` (`B_x`): it runs the edge test at the fixed observation `x`;
* `simulatorTest Q`: it samples a presentation from the key-independent law `Q` and runs the
  edge test; its real mean is the `Q`-average of the real means of `B_x`
  (`mlweRealMean_simulatorTest`);
* `atypicalTest atyp` (`B_typ`): the indicator of an event `atyp` of `t₀`.

The lemmas `abs_mlweRealMean_standinTest_sub_le`, `abs_mlweRealMean_simulatorTest_sub_half_le`,
`abs_mlweRealMean_simulatorTest_sub_half_le_sum` and `mlweRealMean_atypicalTest_le` bound each
real-key mean by its hybrid value plus an MLWE advantage. A simulator need not be efficient, so
`B_Q` need not be; `abs_mlweRealMean_simulatorTest_sub_half_le_of_forall` uses only the
advantages of the tests `B_x`, each of which reads only `t₁` and the fixed `x`.
`edgeHybridAdv_sub_le_mlweRealMean_standinTest_sub_simulatorTest` combines the hops:
with real keys, the edge test separates `P (t₀)` from every key-independent `Q` by at least
`edgeHybridAdv p prims P - Pr[E] / (2·8193²) - Adv^MLWE(B_g) - max_x Adv^MLWE(B_x)`.
`deviceSecretLaw` is the law of the device key's `(s₁, s₂)` (ExpandS on the key-generation
seed, FIPS 204 Algorithm 33).

**What is not formalized.** The stand-in law and the atypicality event enter as parameters `P`
and `atyp`. The value of `Pr[E]` and the size of `edgeHybridAdv` are not proved here. The
efficiency of the tests is not formalized.
-/

namespace GordieHowe.MLDSA

open _root_.MLDSA _root_.MLDSA.Concrete LatticeCrypto TransformOps Finset

/-! ### Power2Round edges of one coefficient -/

/-- `2^d = 8192`. -/
theorem power2Scale_eq : power2Scale = 8192 := by
  norm_num [power2Scale, droppedBits]

/-- The `Power2Round` high part of a coefficient is at most `1023`. -/
theorem power2RoundCoeff_fst_le (r : Coeff) : (power2RoundCoeff r).1 ≤ 1023 := by
  have hr : r.val < 8380417 := ZMod.val_lt r
  unfold power2RoundCoeff
  rw [power2Scale_eq]
  dsimp only
  split <;> simp only <;> omega

/-- The high part is `0` exactly on `[0, 4096]`. -/
theorem power2RoundCoeff_fst_eq_zero_iff (r : Coeff) :
    (power2RoundCoeff r).1 = 0 ↔ r.val ≤ 4096 := by
  have hr : r.val < 8380417 := ZMod.val_lt r
  unfold power2RoundCoeff
  rw [power2Scale_eq]
  dsimp only
  split <;> simp only <;> omega

/-- The high part is `1023` exactly on `[q - 4096, q - 1]`. -/
theorem power2RoundCoeff_fst_eq_top_iff (r : Coeff) :
    (power2RoundCoeff r).1 = 1023 ↔ 8380417 - 4096 ≤ r.val := by
  have hr : r.val < 8380417 := ZMod.val_lt r
  unfold power2RoundCoeff
  rw [power2Scale_eq]
  dsimp only
  split <;> simp only <;> omega

/-- The `Power2Round` high part of a coefficient, as a coefficient. -/
def power2RoundHighCoeff (r : Coeff) : Coeff :=
  ((power2RoundCoeff r).1 : Coeff)

/-- The value of the high coefficient is the high part. -/
theorem val_power2RoundHighCoeff (r : Coeff) :
    (power2RoundHighCoeff r).val = (power2RoundCoeff r).1 := by
  rw [power2RoundHighCoeff, ZMod.val_natCast]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (power2RoundCoeff_fst_le r) (by norm_num [modulus]))

/-- **An edge** value of `t₁`: `0` or `1023`, the two extreme high parts. -/
def IsEdgeHigh (h : Coeff) : Prop :=
  h.val = 0 ∨ h.val = 1023

instance : DecidablePred IsEdgeHigh :=
  fun h => inferInstanceAs (Decidable (h.val = 0 ∨ h.val = 1023))

/-- **The sign of an edge**: `+1` for `t₁ = 0` (`t₀ ≥ 0`), `-1` otherwise (`t₁ = 1023`,
`t₀ ≤ 0`). -/
def edgeSign (h : Coeff) : ℝ :=
  if h.val = 0 then 1 else -1

/-- A coefficient of `t` gives an edge of `t₁` exactly when it lies in `[0, 4096]` or in
`[q - 4096, q - 1]`. -/
theorem isEdgeHigh_power2RoundHighCoeff_iff (r : Coeff) :
    IsEdgeHigh (power2RoundHighCoeff r) ↔ r.val ≤ 4096 ∨ 8380417 - 4096 ≤ r.val := by
  rw [IsEdgeHigh, val_power2RoundHighCoeff, power2RoundCoeff_fst_eq_zero_iff,
    power2RoundCoeff_fst_eq_top_iff]

/-- Coefficients counted through their values. -/
theorem card_filter_val (P : ℕ → Prop) [DecidablePred P] :
    (univ.filter fun a : Coeff => P a.val).card = ((range modulus).filter P).card := by
  refine Finset.card_bij (fun a _ => a.val) ?_ ?_ ?_
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha
    simp only [mem_filter, mem_range]
    exact ⟨ZMod.val_lt a, ha⟩
  · intro a _ b _ h
    exact ZMod.val_injective _ h
  · intro n hn
    simp only [mem_filter, mem_range] at hn
    refine ⟨(n : Coeff), ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and]
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hn.1]
      exact hn.2
    · rw [ZMod.val_natCast, Nat.mod_eq_of_lt hn.1]

/-- `4097` coefficients have high part `0`. -/
theorem card_filter_val_le : (univ.filter fun a : Coeff => a.val ≤ 4096).card = 4097 := by
  rw [card_filter_val (· ≤ 4096)]
  have : (range modulus).filter (· ≤ 4096) = range 4097 := by
    ext n
    simp only [mem_filter, mem_range, modulus]
    omega
  rw [this, card_range]

/-- `4096` coefficients have high part `1023`. -/
theorem card_filter_le_val : (univ.filter fun a : Coeff => 8380417 - 4096 ≤ a.val).card = 4096 := by
  rw [card_filter_val (8380417 - 4096 ≤ ·)]
  have : (range modulus).filter (8380417 - 4096 ≤ ·) = Ico (8380417 - 4096) 8380417 := by
    ext n
    simp only [mem_filter, mem_range, mem_Ico, modulus]
    omega
  rw [this, Nat.card_Ico]

/-- The edge coefficients split into those with high part `0` and those with high part `1023`. -/
theorem filter_isEdgeHigh_eq :
    univ.filter (fun r : Coeff => IsEdgeHigh (power2RoundHighCoeff r)) =
      univ.filter (fun a : Coeff => a.val ≤ 4096) ∪
        univ.filter (fun a : Coeff => 8380417 - 4096 ≤ a.val) := by
  ext r
  simp only [mem_filter, mem_univ, true_and, mem_union, isEdgeHigh_power2RoundHighCoeff_iff]

/-- The two kinds of edges are disjoint. -/
theorem disjoint_filter_val_le :
    Disjoint (univ.filter (fun a : Coeff => a.val ≤ 4096))
      (univ.filter (fun a : Coeff => 8380417 - 4096 ≤ a.val)) := by
  rw [Finset.disjoint_filter]
  intro a _ h
  omega

/-- **`8193` edge values**: `8193` coefficients of `t` give an edge of `t₁`. -/
theorem card_filter_isEdgeHigh :
    (univ.filter fun r : Coeff => IsEdgeHigh (power2RoundHighCoeff r)).card = 8193 := by
  rw [filter_isEdgeHigh_eq, card_union_of_disjoint disjoint_filter_val_le, card_filter_val_le,
    card_filter_le_val]

/-- **The signed count of edges is `1`**: `4097 - 4096`. -/
theorem sum_filter_isEdgeHigh_edgeSign :
    ∑ r with IsEdgeHigh (power2RoundHighCoeff r), edgeSign (power2RoundHighCoeff r) = 1 := by
  rw [filter_isEdgeHigh_eq, sum_union disjoint_filter_val_le]
  have hplus : ∀ r ∈ univ.filter (fun a : Coeff => a.val ≤ 4096),
      edgeSign (power2RoundHighCoeff r) = 1 := by
    intro r hr
    simp only [mem_filter, mem_univ, true_and] at hr
    rw [edgeSign, val_power2RoundHighCoeff, ite_eq_left_iff.2 fun h => absurd ((power2RoundCoeff_fst_eq_zero_iff r).2 hr) h]
  have hminus : ∀ r ∈ univ.filter (fun a : Coeff => 8380417 - 4096 ≤ a.val),
      edgeSign (power2RoundHighCoeff r) = -1 := by
    intro r hr
    simp only [mem_filter, mem_univ, true_and] at hr
    have h0 : ¬ (power2RoundCoeff r).1 = 0 := by
      rw [power2RoundCoeff_fst_eq_zero_iff]
      omega
    rw [edgeSign, val_power2RoundHighCoeff, ite_eq_right_iff.2 fun h => absurd h h0]
  rw [sum_congr rfl hplus, sum_congr rfl hminus, sum_const, sum_const, card_filter_val_le,
    card_filter_le_val]
  norm_num

/-- **The mean sign of an edge is `1/8193`** under the uniform coefficient law. -/
theorem sum_filter_isEdgeHigh_uniform_edgeSign :
    ∑ r with IsEdgeHigh (power2RoundHighCoeff r),
        (1 / (modulus : ℝ)) * edgeSign (power2RoundHighCoeff r) =
      1 / 8193 * ∑ r with IsEdgeHigh (power2RoundHighCoeff r), (1 / (modulus : ℝ)) := by
  rw [← mul_sum, sum_filter_isEdgeHigh_edgeSign, sum_const, card_filter_isEdgeHigh]
  ring

/-! ### The hybrid key and its edges -/

section Hybrid

variable (p : Params)

/-- **The hybrid key law**: `t` uniform on `R_q^k`, in place of `t = Â·s₁ + s₂` (the MLWE
hop). -/
noncomputable def hybridKeyLaw : PMF (RqVec p.k) :=
  PMF.uniformOfFintype (RqVec p.k)

/-- `t₁` of `t`: the high part of `(t₁, t₀) = Power2Round(t)` (FIPS 204 Algorithm 35,
coefficientwise), as in `keyGenFromSeed`. -/
def t1Of (t : RqVec p.k) : RqVec p.k :=
  ((Spec.concretePrimitivesKeyGen p).power2RoundVec t).1

/-- `t₀` of `t`: the low part of `(t₁, t₀) = Power2Round(t)`, as in `keyGenFromSeed`. -/
def t0Of (t : RqVec p.k) : RqVec p.k :=
  ((Spec.concretePrimitivesKeyGen p).power2RoundVec t).2

/-- The coefficients of `t₁` are the high parts of the coefficients of `t`. -/
theorem rqVecCoeffs_t1Of (t : RqVec p.k) (x : CoeffIndex p) :
    rqVecCoeffs (t1Of p t) x = power2RoundHighCoeff (rqVecCoeffs t x) := by
  simp [t1Of, power2RoundHighCoeff, rqVecCoeffs_apply, Primitives.power2RoundVec,
    Spec.concretePrimitivesKeyGen, concretePrimitives, power2Round, power2RoundHigh,
    Vector.get_map, Vector.get_ofFn]

/-- **The edge positions** of `t₁`. -/
def edgePositions (t1 : RqVec p.k) : Finset (CoeffIndex p) :=
  SignSymmetry.edgeSet IsEdgeHigh (rqVecCoeffs t1)

/-- The edge positions of `t₁` are the positions of `t` holding an edge value. -/
theorem edgePositions_t1Of (t : RqVec p.k) :
    edgePositions p (t1Of p t) =
      SignSymmetry.edgeSet (fun r => IsEdgeHigh (power2RoundHighCoeff r)) (rqVecCoeffs t) := by
  ext x
  simp only [edgePositions, SignSymmetry.mem_edgeSet, rqVecCoeffs_t1Of]

variable {p}

/-- The components holding exactly two edges. -/
def pairComponents (D : Finset (CoeffIndex p)) : Finset (Fin p.k) :=
  univ.filter fun j => (D.filter fun x => x.1 = j).card = 2

/-- **The event `E`**: some component has exactly two edges. -/
def EdgeEvent (D : Finset (CoeffIndex p)) : Prop :=
  (pairComponents D).Nonempty

instance : DecidablePred (EdgeEvent (p := p)) :=
  fun D => inferInstanceAs (Decidable (pairComponents D).Nonempty)

/-- **The edge pair**: on `E`, the two edges of the lowest component with exactly two edges;
empty off `E`. -/
def edgePair (D : Finset (CoeffIndex p)) : Finset (CoeffIndex p) :=
  if h : (pairComponents D).Nonempty then D.filter fun x => x.1 = (pairComponents D).min' h
  else ∅

/-- The edge pair consists of edges. -/
theorem edgePair_subset (D : Finset (CoeffIndex p)) : edgePair D ⊆ D := by
  unfold edgePair
  split
  · exact filter_subset _ _
  · exact empty_subset _

/-- On `E`, the edge pair has two elements. -/
theorem card_edgePair {D : Finset (CoeffIndex p)} (hE : EdgeEvent D) : (edgePair D).card = 2 := by
  unfold EdgeEvent at hE
  have hmem := (pairComponents D).min'_mem hE
  simp only [pairComponents, mem_filter, mem_univ, true_and] at hmem
  rw [edgePair, dite_eq_left_of_eq_true (eq_true hE)]
  exact hmem

/-- The monomial `X^j` of `R_q`. -/
def xPow (j : Fin ringDegree) : Rq :=
  Vector.ofFn fun i => if i = j then 1 else 0

/-- **The negacyclic correlation of `c` at a set of shifts `P`**:
`∑_i ∏_{j ∈ P} (c·X^j)_i` over centered coefficients. For `P = {j1, j2}` this is
`A(c) = ⟨c·X^j1, c·X^j2⟩` (`shiftCorrelation_pair`). -/
def shiftCorrelation (c : Rq) (P : Finset (Fin ringDegree)) : ℤ :=
  ∑ i : Fin ringDegree, ∏ j ∈ P, centeredRepr ((c * xPow j).get i)

/-- For two shifts, the correlation is the inner product `⟨c·X^j1, c·X^j2⟩`. -/
theorem shiftCorrelation_pair (c : Rq) {j1 j2 : Fin ringDegree} (h : j1 ≠ j2) :
    shiftCorrelation c {j1, j2} =
      ∑ i : Fin ringDegree, centeredRepr ((c * xPow j1).get i) *
        centeredRepr ((c * xPow j2).get i) := by
  simp only [shiftCorrelation, prod_pair h]

/-- **The sign-free factor** of the edge test on challenge `c`: `-sign A(c)` for the edge pair on
`E`, `0` off `E`. -/
def edgeTestFactor (c : Rq) (D : Finset (CoeffIndex p)) : ℝ :=
  if EdgeEvent D then -((shiftCorrelation c ((edgePair D).image Prod.snd)).sign : ℝ) else 0

/-- The factor has absolute value at most `1` on `E` and vanishes off `E`. -/
theorem abs_edgeTestFactor_le (c : Rq) (D : Finset (CoeffIndex p)) :
    |edgeTestFactor c D| ≤ if EdgeEvent D then 1 else 0 := by
  unfold edgeTestFactor
  split
  · rw [abs_neg]
    rcases Int.sign_trichotomy (shiftCorrelation c ((edgePair D).image Prod.snd)) with
      h | h | h <;> simp [h]
  · simp

variable (p) (prims : Primitives p)

/-- **The edge test value** `g(t₁, x) = -ρ · sign A(c)` on `E` and `0` off `E`, with `ρ` the sign
product of the edge pair and `c = prims.sampleInBall(c̃)` for the observation `x = (w1, c̃)`. -/
def edgeTestValue (t1 : RqVec p.k) (x : BucketVec p × CommitHashBytes p) : ℝ :=
  edgeTestFactor (prims.sampleInBall x.2) (edgePositions p t1) *
    ∏ y ∈ edgePair (edgePositions p t1), edgeSign (rqVecCoeffs t1 y)

/-- **The edge test**: its probability of outputting `1`, `(1 + g)/2`. -/
noncomputable def edgeTestOutput (t1 : RqVec p.k) (x : BucketVec p × CommitHashBytes p) : ℝ :=
  (1 + edgeTestValue p prims t1 x) / 2

/-- The edge test value is in `[-1, 1]`. -/
theorem abs_edgeTestValue_le (t1 : RqVec p.k) (x : BucketVec p × CommitHashBytes p) :
    |edgeTestValue p prims t1 x| ≤ 1 := by
  rw [edgeTestValue, abs_mul, abs_prod]
  have hsign : ∀ y ∈ edgePair (edgePositions p t1), |edgeSign (rqVecCoeffs t1 y)| = 1 := by
    intro y _
    unfold edgeSign
    split <;> simp
  rw [prod_congr rfl hsign, prod_const_one, mul_one]
  refine (abs_edgeTestFactor_le _ _).trans ?_
  split <;> norm_num

/-- The edge test outputs a probability. -/
theorem edgeTestOutput_mem_Icc (t1 : RqVec p.k) (x : BucketVec p × CommitHashBytes p) :
    edgeTestOutput p prims t1 x ∈ Set.Icc (0 : ℝ) 1 := by
  have h := abs_le.1 (abs_edgeTestValue_le p prims t1 x)
  unfold edgeTestOutput
  constructor <;> linarith [h.1, h.2]

/-- **`Pr[E]`** under the hybrid key law. -/
noncomputable def edgeEventProb : ℝ :=
  ∑ t, (hybridKeyLaw p t).toReal * if EdgeEvent (edgePositions p (t1Of p t)) then 1 else 0

/-- The hybrid key law is the product of uniform coefficient laws. -/
theorem hybridKeyLaw_toReal (t : RqVec p.k) :
    (hybridKeyLaw p t).toReal = ∏ _x : CoeffIndex p, (1 / (modulus : ℝ)) := by
  rw [hybridKeyLaw, PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    Fintype.card_congr (rqVecCoeffEquiv p.k), Fintype.card_fun, ZMod.card, prod_const,
    card_univ, Nat.cast_pow, one_div, inv_pow]

/-- An average over the hybrid key law that reads `t` through its coefficients is an average
over independent uniform coefficients. -/
theorem sum_hybridKeyLaw_eq (G : (CoeffIndex p → Coeff) → ℝ) :
    ∑ t, (hybridKeyLaw p t).toReal * G (rqVecCoeffs t) =
      ∑ f : CoeffIndex p → Coeff, (∏ x, (fun _ : Coeff => 1 / (modulus : ℝ)) (f x)) * G f := by
  refine Fintype.sum_equiv (rqVecCoeffEquiv p.k) _ _ fun t => ?_
  rw [hybridKeyLaw_toReal]
  rfl

/-- The edge test value, written through the coefficients of `t`. -/
theorem edgeTestValue_t1Of (t : RqVec p.k) (x : BucketVec p × CommitHashBytes p) :
    edgeTestValue p prims (t1Of p t) x =
      edgeTestFactor (prims.sampleInBall x.2)
          (SignSymmetry.edgeSet (fun r => IsEdgeHigh (power2RoundHighCoeff r)) (rqVecCoeffs t)) *
        ∏ y ∈ edgePair (SignSymmetry.edgeSet (fun r => IsEdgeHigh (power2RoundHighCoeff r))
          (rqVecCoeffs t)), edgeSign (power2RoundHighCoeff (rqVecCoeffs t y)) := by
  simp only [edgeTestValue, edgePositions_t1Of, rqVecCoeffs_t1Of]

/-- **The sign symmetry, exact form**: for every observation `x`, the hybrid mean of the edge
test value is `8193⁻²` times the hybrid mean of its sign-free factor. -/
theorem sum_hybrid_edgeTestValue (x : BucketVec p × CommitHashBytes p) :
    ∑ t, (hybridKeyLaw p t).toReal * edgeTestValue p prims (t1Of p t) x =
      (1 / 8193) ^ 2 * ∑ t, (hybridKeyLaw p t).toReal *
        edgeTestFactor (prims.sampleInBall x.2)
          (edgePositions p (t1Of p t)) := by
  set c := prims.sampleInBall x.2
  simp only [edgeTestValue_t1Of, edgePositions_t1Of]
  rw [sum_hybridKeyLaw_eq p (fun f => edgeTestFactor c
      (SignSymmetry.edgeSet (fun r => IsEdgeHigh (power2RoundHighCoeff r)) f) *
        ∏ y ∈ edgePair (SignSymmetry.edgeSet (fun r => IsEdgeHigh (power2RoundHighCoeff r)) f),
          edgeSign (power2RoundHighCoeff (f y))),
    sum_hybridKeyLaw_eq p (fun f => edgeTestFactor c
      (SignSymmetry.edgeSet (fun r => IsEdgeHigh (power2RoundHighCoeff r)) f)),
    SignSymmetry.sum_prod_mul_prod_sign_eq (fun _ => 1 / (modulus : ℝ))
      (fun r => edgeSign (power2RoundHighCoeff r)) (fun r => IsEdgeHigh (power2RoundHighCoeff r))
      (1 / 8193) sum_filter_isEdgeHigh_uniform_edgeSign _ edgePair edgePair_subset, mul_sum]
  refine sum_congr rfl fun f _ => ?_
  set D := SignSymmetry.edgeSet (fun r => IsEdgeHigh (power2RoundHighCoeff r)) f
  by_cases hE : EdgeEvent D
  · rw [card_edgePair hE]
    ring
  · have h0 : edgeTestFactor c D = 0 := by simp [edgeTestFactor, hE]
    simp [h0]

/-- **The sign symmetry**: for every observation `x`, `|𝔼_t g(t₁, x)| ≤ Pr[E] / 8193²`. -/
theorem abs_sum_hybrid_edgeTestValue_le (x : BucketVec p × CommitHashBytes p) :
    |∑ t, (hybridKeyLaw p t).toReal * edgeTestValue p prims (t1Of p t) x| ≤
      edgeEventProb p / 8193 ^ 2 := by
  set c := prims.sampleInBall x.2
  simp only [edgeTestValue_t1Of]
  rw [sum_hybridKeyLaw_eq p (fun f => edgeTestFactor c
      (SignSymmetry.edgeSet (fun r => IsEdgeHigh (power2RoundHighCoeff r)) f) *
        ∏ y ∈ edgePair (SignSymmetry.edgeSet (fun r => IsEdgeHigh (power2RoundHighCoeff r)) f),
          edgeSign (power2RoundHighCoeff (f y)))]
  refine (SignSymmetry.abs_sum_prod_mul_prod_sign_le (fun _ => 1 / (modulus : ℝ))
    (fun r => edgeSign (power2RoundHighCoeff r)) (fun r => IsEdgeHigh (power2RoundHighCoeff r))
    (1 / 8193) sum_filter_isEdgeHigh_uniform_edgeSign (fun _ => by positivity) EdgeEvent
    (edgeTestFactor c) (abs_edgeTestFactor_le c) edgePair edgePair_subset
    (fun _ hE => card_edgePair hE)).trans (le_of_eq ?_)
  rw [edgeEventProb]
  simp only [edgePositions_t1Of]
  rw [sum_hybridKeyLaw_eq p (fun f =>
    if EdgeEvent (SignSymmetry.edgeSet (fun r => IsEdgeHigh (power2RoundHighCoeff r)) f)
    then 1 else 0)]
  ring

/-- **The test is a fair coin up to `Pr[E] / (2·8193²)`**, for every fixed observation. -/
theorem abs_sum_hybrid_edgeTestOutput_sub_half_le (x : BucketVec p × CommitHashBytes p) :
    |∑ t, (hybridKeyLaw p t).toReal * edgeTestOutput p prims (t1Of p t) x - 1 / 2| ≤
      edgeEventProb p / (2 * 8193 ^ 2) := by
  have hsum : ∑ t, (hybridKeyLaw p t).toReal * edgeTestOutput p prims (t1Of p t) x - 1 / 2 =
      (∑ t, (hybridKeyLaw p t).toReal * edgeTestValue p prims (t1Of p t) x) / 2 := by
    simp only [edgeTestOutput, mul_div_assoc', mul_add, mul_one]
    rw [← sum_div, sum_add_distrib, PMF.sum_toReal_eq_one]
    ring
  rw [hsum, abs_div, abs_two]
  have := abs_sum_hybrid_edgeTestValue_le p prims x
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  calc _ ≤ edgeEventProb p / 8193 ^ 2 := this
    _ = edgeEventProb p / (2 * 8193 ^ 2) * 2 := by ring

/-- **The acceptance probability of the edge test** under the hybrid key law, when the
observation has law `obs t` given the key `t`: `𝔼_t 𝔼_{x ← obs t} (1 + g(t₁, x))/2`. -/
noncomputable def edgeAcceptProb (obs : RqVec p.k → PMF (BucketVec p × CommitHashBytes p)) : ℝ :=
  ∑ t, (hybridKeyLaw p t).toReal * ∑ x, (obs t x).toReal * edgeTestOutput p prims (t1Of p t) x

/-- **Every key-independent simulator gets a fair coin up to `Pr[E] / (2·8193²)`**: for every
law `Q` of the simulated observation, `|Pr_Q[g = 1] - 1/2| ≤ Pr[E] / (2·8193²)`. -/
theorem abs_edgeAcceptProb_const_sub_half_le (Q : PMF (BucketVec p × CommitHashBytes p)) :
    |edgeAcceptProb p prims (fun _ => Q) - 1 / 2| ≤ edgeEventProb p / (2 * 8193 ^ 2) := by
  have heq : edgeAcceptProb p prims (fun _ => Q) - 1 / 2 =
      ∑ x, (Q x).toReal *
        (∑ t, (hybridKeyLaw p t).toReal * edgeTestOutput p prims (t1Of p t) x - 1 / 2) := by
    simp only [edgeAcceptProb, mul_sub, sum_sub_distrib, mul_sum]
    rw [sum_comm, ← sum_mul, PMF.sum_toReal_eq_one]
    congr 1
    · exact sum_congr rfl fun x _ => sum_congr rfl fun t _ => by ring
    · ring
  rw [heq]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ x, |(Q x).toReal *
        (∑ t, (hybridKeyLaw p t).toReal * edgeTestOutput p prims (t1Of p t) x - 1 / 2)|
      ≤ ∑ x, (Q x).toReal * (edgeEventProb p / (2 * 8193 ^ 2)) := by
        refine sum_le_sum fun x _ => ?_
        rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
        exact mul_le_mul_of_nonneg_left (abs_sum_hybrid_edgeTestOutput_sub_half_le p prims x)
          ENNReal.toReal_nonneg
    _ = edgeEventProb p / (2 * 8193 ^ 2) := by
        rw [← sum_mul, PMF.sum_toReal_eq_one, one_mul]

/-- **The hybrid advantage of the edge test** against presentations whose law `P (t₀)` depends
on the key through `t₀`: `Pr_hybrid[g = 1] - 1/2`. Its size is measured outside Lean
(`edge_test.cc`, with `P` the stand-in law), and not proved here. -/
noncomputable def edgeHybridAdv (P : RqVec p.k → PMF (BucketVec p × CommitHashBytes p)) : ℝ :=
  edgeAcceptProb p prims (fun t => P (t0Of p t)) - 1 / 2

/-- **The edge test's advantage is the same against every simulator**: for every key-independent
law `Q`, the advantage between presentations from `P (t₀)` and from `Q` is `edgeHybridAdv p prims P`
up to `Pr[E] / (2·8193²)`. -/
theorem abs_edgeAcceptProb_sub_const_sub_edgeHybridAdv_le
    (P : RqVec p.k → PMF (BucketVec p × CommitHashBytes p))
    (Q : PMF (BucketVec p × CommitHashBytes p)) :
    |edgeAcceptProb p prims (fun t => P (t0Of p t)) - edgeAcceptProb p prims (fun _ => Q) -
        edgeHybridAdv p prims P| ≤ edgeEventProb p / (2 * 8193 ^ 2) := by
  have h := abs_edgeAcceptProb_const_sub_half_le p prims Q
  rw [edgeHybridAdv, show edgeAcceptProb p prims (fun t => P (t0Of p t)) -
      edgeAcceptProb p prims (fun _ => Q) -
        (edgeAcceptProb p prims (fun t => P (t0Of p t)) - 1 / 2) =
      -(edgeAcceptProb p prims (fun _ => Q) - 1 / 2) by ring, abs_neg]
  exact h

end Hybrid

/-! ### The MLWE hop for the edge test -/

section Hop

variable (p : Params) (prims : Primitives p) [nttOps : NTTRingOps]

/-- **The device secret law**: the law of `(s₁, s₂) = ExpandS(ρ')` of the device key from a
uniform seed (`deviceKey`, FIPS 204 Algorithm 6). -/
noncomputable def deviceSecretLaw : PMF (RqVec p.l × RqVec p.k) :=
  seedLaw.map fun seed => ((deviceKey p seed).s1, (deviceKey p seed).s2)

omit nttOps in
/-- An average of a `[0, 1]`-valued function under a law is in `[0, 1]`. -/
theorem sum_toReal_mul_mem_Icc {X : Type*} [Fintype X] (μ : PMF X) (h : X → ℝ)
    (hh : ∀ x, h x ∈ Set.Icc (0 : ℝ) 1) : ∑ x, (μ x).toReal * h x ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact sum_nonneg fun x _ => mul_nonneg ENNReal.toReal_nonneg (hh x).1
  · calc ∑ x, (μ x).toReal * h x ≤ ∑ x, (μ x).toReal :=
          sum_le_sum fun x _ => mul_le_of_le_one_right ENNReal.toReal_nonneg (hh x).2
      _ = 1 := PMF.sum_toReal_eq_one μ

/-- **`B_g`**: on an MLWE instance `(Â, t)`, sample a presentation from `P (t₀)` and run the edge
test on `t₁`. -/
noncomputable def standinTest (P : RqVec p.k → PMF (BucketVec p × CommitHashBytes p)) :
    TqMatrix p.k p.l → RqVec p.k → ℝ :=
  fun _ t => ∑ x, (P (t0Of p t) x).toReal * edgeTestOutput p prims (t1Of p t) x

/-- On an MLWE instance `(Â, t)`, sample a presentation from the key-independent law `Q` and run
the edge test on `t₁`. -/
noncomputable def simulatorTest (Q : PMF (BucketVec p × CommitHashBytes p)) :
    TqMatrix p.k p.l → RqVec p.k → ℝ :=
  fun _ t => ∑ x, (Q x).toReal * edgeTestOutput p prims (t1Of p t) x

/-- **`B_typ`**: on an MLWE instance `(Â, t)`, the indicator of an event `atyp` of `t₀`. -/
def atypicalTest (atyp : RqVec p.k → Prop) [DecidablePred atyp] :
    TqMatrix p.k p.l → RqVec p.k → ℝ :=
  fun _ t => if atyp (t0Of p t) then 1 else 0

omit nttOps in
/-- `B_g` outputs a probability. -/
theorem standinTest_mem_Icc (P : RqVec p.k → PMF (BucketVec p × CommitHashBytes p))
    (A : TqMatrix p.k p.l) (t : RqVec p.k) : standinTest p prims P A t ∈ Set.Icc (0 : ℝ) 1 :=
  sum_toReal_mul_mem_Icc _ _ fun x => edgeTestOutput_mem_Icc p prims _ x

omit nttOps in
/-- The simulator test outputs a probability. -/
theorem simulatorTest_mem_Icc (Q : PMF (BucketVec p × CommitHashBytes p))
    (A : TqMatrix p.k p.l) (t : RqVec p.k) : simulatorTest p prims Q A t ∈ Set.Icc (0 : ℝ) 1 :=
  sum_toReal_mul_mem_Icc _ _ fun x => edgeTestOutput_mem_Icc p prims _ x

omit nttOps in
/-- `B_typ` outputs a probability. -/
theorem atypicalTest_mem_Icc (atyp : RqVec p.k → Prop) [DecidablePred atyp]
    (A : TqMatrix p.k p.l) (t : RqVec p.k) : atypicalTest p atyp A t ∈ Set.Icc (0 : ℝ) 1 := by
  unfold atypicalTest
  split <;> norm_num

omit nttOps in
/-- The uniform mean of `B_g` is the hybrid acceptance probability
`1/2 + edgeHybridAdv p prims P`. -/
theorem mlweUniformMean_standinTest (P : RqVec p.k → PMF (BucketVec p × CommitHashBytes p)) :
    mlweUniformMean (standinTest p prims P) = 1 / 2 + edgeHybridAdv p prims P := by
  unfold standinTest
  rw [mlweUniformMean_of_vector, edgeHybridAdv, edgeAcceptProb]
  simp only [hybridKeyLaw]
  ring

omit nttOps in
/-- The uniform mean of the simulator test is the hybrid acceptance probability under `Q`. -/
theorem mlweUniformMean_simulatorTest (Q : PMF (BucketVec p × CommitHashBytes p)) :
    mlweUniformMean (simulatorTest p prims Q) = edgeAcceptProb p prims (fun _ => Q) := by
  unfold simulatorTest
  rw [mlweUniformMean_of_vector, edgeAcceptProb]
  rfl

/-- **The probability of `atyp` in the hybrid**: `Pr_{t uniform}[atyp(t₀)]`. -/
noncomputable def hybridEventProb (atyp : RqVec p.k → Prop) [DecidablePred atyp] : ℝ :=
  ∑ t, (hybridKeyLaw p t).toReal * if atyp (t0Of p t) then 1 else 0

omit nttOps in
/-- The uniform mean of `B_typ` is the hybrid probability of `atyp`. -/
theorem mlweUniformMean_atypicalTest (atyp : RqVec p.k → Prop) [DecidablePred atyp] :
    mlweUniformMean (atypicalTest p atyp) = hybridEventProb p atyp := by
  unfold atypicalTest
  rw [mlweUniformMean_of_vector, hybridEventProb]
  rfl

/-- **The MLWE hop on `B_g`**: with real keys `t = Â·s₁ + s₂`, `(s₁, s₂) ← S`, the edge test on
presentations from `P (t₀)` accepts with probability within `Adv^MLWE_S(B_g)` of
`1/2 + edgeHybridAdv p prims P`. -/
theorem abs_mlweRealMean_standinTest_sub_le (S : PMF (RqVec p.l × RqVec p.k))
    (P : RqVec p.k → PMF (BucketVec p × CommitHashBytes p)) :
    |mlweRealMean S (standinTest p prims P) - (1 / 2 + edgeHybridAdv p prims P)| ≤
      mlweAdvantage S (standinTest p prims P) := by
  rw [← mlweUniformMean_standinTest]
  exact abs_mlweRealMean_sub_mlweUniformMean_le S _

/-- **The MLWE hop on the simulator test**: with real keys, every key-independent simulator `Q`
gets acceptance probability within `Pr[E] / (2·8193²) + Adv^MLWE_S(B_Q)` of `1/2`. -/
theorem abs_mlweRealMean_simulatorTest_sub_half_le (S : PMF (RqVec p.l × RqVec p.k))
    (Q : PMF (BucketVec p × CommitHashBytes p)) :
    |mlweRealMean S (simulatorTest p prims Q) - 1 / 2| ≤
      edgeEventProb p / (2 * 8193 ^ 2) + mlweAdvantage S (simulatorTest p prims Q) := by
  have h1 := abs_mlweRealMean_sub_mlweUniformMean_le S (simulatorTest p prims Q)
  have h2 := abs_edgeAcceptProb_const_sub_half_le p prims Q
  rw [mlweUniformMean_simulatorTest] at h1
  calc |mlweRealMean S (simulatorTest p prims Q) - 1 / 2|
      = |(mlweRealMean S (simulatorTest p prims Q) - edgeAcceptProb p prims (fun _ => Q)) +
          (edgeAcceptProb p prims (fun _ => Q) - 1 / 2)| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (by linarith)

/-- **`B_x`**: on an MLWE instance `(Â, t)`, run the edge test on `t₁` at the fixed observation
`x`. -/
noncomputable def observationTest (x : BucketVec p × CommitHashBytes p) :
    TqMatrix p.k p.l → RqVec p.k → ℝ :=
  fun _ t => edgeTestOutput p prims (t1Of p t) x

omit nttOps in
/-- `B_x` outputs a probability. -/
theorem observationTest_mem_Icc (x : BucketVec p × CommitHashBytes p)
    (A : TqMatrix p.k p.l) (t : RqVec p.k) : observationTest p prims x A t ∈ Set.Icc (0 : ℝ) 1 :=
  edgeTestOutput_mem_Icc p prims _ x

omit nttOps in
/-- The uniform mean of `B_x` is the hybrid acceptance probability at `x`. -/
theorem mlweUniformMean_observationTest (x : BucketVec p × CommitHashBytes p) :
    mlweUniformMean (observationTest p prims x) =
      ∑ t, (hybridKeyLaw p t).toReal * edgeTestOutput p prims (t1Of p t) x := by
  unfold observationTest
  rw [mlweUniformMean_of_vector]
  rfl

/-- The real mean of the simulator test is the `Q`-average of the real means of the tests `B_x`. -/
theorem mlweRealMean_simulatorTest (S : PMF (RqVec p.l × RqVec p.k))
    (Q : PMF (BucketVec p × CommitHashBytes p)) :
    mlweRealMean S (simulatorTest p prims Q) =
      ∑ x, (Q x).toReal * mlweRealMean S (observationTest p prims x) := by
  simp only [mlweRealMean, simulatorTest, observationTest, mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine sum_congr rfl fun A _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  exact sum_congr rfl fun s _ => sum_congr rfl fun x _ => by ring

/-- **The MLWE hop for every simulator**: with real keys, every key-independent law `Q` of the
observation gets acceptance probability within `Pr[E] / (2·8193²)` plus the `Q`-average of
`Adv^MLWE_S(B_x)` of `1/2`. -/
theorem abs_mlweRealMean_simulatorTest_sub_half_le_sum (S : PMF (RqVec p.l × RqVec p.k))
    (Q : PMF (BucketVec p × CommitHashBytes p)) :
    |mlweRealMean S (simulatorTest p prims Q) - 1 / 2| ≤
      edgeEventProb p / (2 * 8193 ^ 2) +
        ∑ x, (Q x).toReal * mlweAdvantage S (observationTest p prims x) := by
  have heq : mlweRealMean S (simulatorTest p prims Q) - 1 / 2 =
      ∑ x, (Q x).toReal * (mlweRealMean S (observationTest p prims x) - 1 / 2) := by
    rw [mlweRealMean_simulatorTest]
    simp only [mul_sub, sum_sub_distrib]
    rw [← sum_mul, PMF.sum_toReal_eq_one, one_mul]
  rw [heq]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hx : ∀ x, |(Q x).toReal * (mlweRealMean S (observationTest p prims x) - 1 / 2)| ≤
      (Q x).toReal *
        (edgeEventProb p / (2 * 8193 ^ 2) + mlweAdvantage S (observationTest p prims x)) := by
    intro x
    rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
    have h1 := abs_mlweRealMean_sub_mlweUniformMean_le S (observationTest p prims x)
    have h2 := abs_sum_hybrid_edgeTestOutput_sub_half_le p prims x
    rw [mlweUniformMean_observationTest] at h1
    calc |mlweRealMean S (observationTest p prims x) - 1 / 2|
        = |(mlweRealMean S (observationTest p prims x) -
              ∑ t, (hybridKeyLaw p t).toReal * edgeTestOutput p prims (t1Of p t) x) +
            (∑ t, (hybridKeyLaw p t).toReal * edgeTestOutput p prims (t1Of p t) x - 1 / 2)| := by
          ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (by linarith)
  refine (sum_le_sum fun x _ => hx x).trans (le_of_eq ?_)
  rw [sum_congr rfl fun x _ => mul_add _ _ _, sum_add_distrib, ← sum_mul,
    PMF.sum_toReal_eq_one, one_mul]

/-- **The MLWE hop for every simulator, uniform form**: if every test `B_x` has MLWE advantage at
most `ε`, then with real keys every key-independent law `Q` gets acceptance probability within
`Pr[E] / (2·8193²) + ε` of `1/2`. -/
theorem abs_mlweRealMean_simulatorTest_sub_half_le_of_forall (S : PMF (RqVec p.l × RqVec p.k))
    {ε : ℝ} (hε : ∀ x, mlweAdvantage S (observationTest p prims x) ≤ ε)
    (Q : PMF (BucketVec p × CommitHashBytes p)) :
    |mlweRealMean S (simulatorTest p prims Q) - 1 / 2| ≤ edgeEventProb p / (2 * 8193 ^ 2) + ε := by
  refine (abs_mlweRealMean_simulatorTest_sub_half_le_sum p prims S Q).trans ?_
  have hle : ∑ x, (Q x).toReal * mlweAdvantage S (observationTest p prims x) ≤
      ∑ x, (Q x).toReal * ε :=
    sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hε x) ENNReal.toReal_nonneg
  rw [← sum_mul, PMF.sum_toReal_eq_one, one_mul] at hle
  linarith

/-- **The edge test against every simulator, with real keys**: if every test `B_x` has MLWE
advantage at most `ε`, the edge test distinguishes presentations from `P (t₀)` from those of any
key-independent law `Q` with advantage at least
`edgeHybridAdv p prims P - Pr[E] / (2·8193²) - Adv^MLWE_S(B_g) - ε`. -/
theorem edgeHybridAdv_sub_le_mlweRealMean_standinTest_sub_simulatorTest
    (S : PMF (RqVec p.l × RqVec p.k)) (P : RqVec p.k → PMF (BucketVec p × CommitHashBytes p))
    {ε : ℝ} (hε : ∀ x, mlweAdvantage S (observationTest p prims x) ≤ ε)
    (Q : PMF (BucketVec p × CommitHashBytes p)) :
    edgeHybridAdv p prims P - edgeEventProb p / (2 * 8193 ^ 2) -
        mlweAdvantage S (standinTest p prims P) - ε ≤
      mlweRealMean S (standinTest p prims P) - mlweRealMean S (simulatorTest p prims Q) := by
  have h1 := abs_mlweRealMean_standinTest_sub_le p prims S P
  have h2 := abs_mlweRealMean_simulatorTest_sub_half_le_of_forall p prims S hε Q
  have h1' :=
    neg_abs_le (mlweRealMean S (standinTest p prims P) - (1 / 2 + edgeHybridAdv p prims P))
  have h2' := le_abs_self (mlweRealMean S (simulatorTest p prims Q) - 1 / 2)
  linarith

/-- **The MLWE hop on `B_typ`**: with real keys, the probability of `atyp(t₀)` is at most its
hybrid probability plus `Adv^MLWE_S(B_typ)`. -/
theorem mlweRealMean_atypicalTest_le (S : PMF (RqVec p.l × RqVec p.k))
    (atyp : RqVec p.k → Prop) [DecidablePred atyp] :
    mlweRealMean S (atypicalTest p atyp) ≤
      hybridEventProb p atyp + mlweAdvantage S (atypicalTest p atyp) := by
  have h := abs_mlweRealMean_sub_mlweUniformMean_le S (atypicalTest p atyp)
  rw [mlweUniformMean_atypicalTest] at h
  linarith [le_abs_self (mlweRealMean S (atypicalTest p atyp) - hybridEventProb p atyp)]

end Hop

end GordieHowe.MLDSA
