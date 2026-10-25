-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.PublicW1.MLDSAPublicW1ExpandS
public import GordieHowe.Applications.MLDSA.Regularity.WeightTail
public import GordieHowe.Applications.MLDSA.Regularity.WeightTail44
public import GordieHowe.Applications.MLDSA.Regularity.InstancesSeven
public import GordieHowe.Applications.Ring.PublicW1.MLDSAPublicW1Concentration

@[expose] public section

/-!
# Anonymity of the ML-DSA ring signature with the regularity term evaluated

The game in which `ExpandA`, `ExpandS` and `SampleInBall` are random oracles: `oraclePrimitives
G_B G_S` are the concrete primitives with `SampleInBall = G_B` onto the challenge set `B_τ`
(FIPS 204 §2.3, Algorithm 29) and `ExpandS = G_S` onto the `η`-box (Algorithm 33, `withExpandS`),
and `ExpandA` (Algorithm 32) is a random oracle `G_A` (`withExpandA`).

* `concreteWithSampleInBallExpandS`, `advantage_le_ideal_concrete`: `advantage_le_ideal` at the
  concrete primitives with any `SampleInBall` of challenge shape and any `ExpandS` onto secrets
  with `‖s₂‖∞ ≤ η`, the signing and verification laws, the encoding and `‖s₂‖∞ ≤ η` discharged.
  At the FIPS 204 `SampleInBall` and `ExpandS` the primitives are `concretePrimitivesKeyGen`
  (`concreteWithSampleInBallExpandS_concrete`).
* `expect_regGapAvg_le_of`: `𝔼_{G_B, G_S} regGapAvg ≤ R / β_min · √B` from a per-key bound
  `𝔼_Â ringRegGap ≤ R / β_min · √(𝔼_Â w⁻²)` for every positive lower bound `w` on the mean member
  weights (`expect_ringRegGap_le_sqrt`), a bound `F(‖t₀‖₂²)` on the oracle average of the inverse
  square acceptance floor (`oracleAcceptFloor`, which bounds the mean member weights for
  `β_min ≤ 1`: `oracleAcceptFloor_le_expect_memberWeight`), and a bound `B` on
  `𝔼_{s, Â} F(‖t₀‖₂²)`. `ExpandS` as a random oracle gives a uniform box secret
  (`expect_regGapAvg_withExpandS`); the key of key generation is the key of the regularity
  argument (`ringRegGap_idealSecretKey_eq`); Jensen's inequality for `√` over `G_B` and over the
  secret (`Real.expect_sqrt_le_sqrt_expect`) leaves `√(𝔼_{s, G_B, Â} w⁻²)`.
* `expect_regGapAvg_le_mldsa65`, `_mldsa87`: for `β_min ≤ 1`,
  `𝔼_{G_B, G_S} regGapAvg ≤ R · C / β_min` with the seven-slot regularity bound `R = 11 · 2^-199`
  at ML-DSA-65 and `R = 12 · 2^-294` at ML-DSA-87 (`expect_ringRegGap_le_sqrt_mldsa65_seven`,
  `_mldsa87_seven`), and the weight factor `C = 9/2` at ML-DSA-65 and `C = 33/5` at ML-DSA-87
  (`expect_expect_floorInvSqBound_le_mldsa65`, `_mldsa87`): `log₂ C = 2.17` and `2.72` bits, so
  `log₂ (R · C) = -193.37` at ML-DSA-65 and `-287.69` at ML-DSA-87.
* `advantage_le_bkm06`: BKM06 Definition 4 (Bender, Katz and Morselli, "Ring Signatures:
  Stronger Definitions, and Constructions without Random Oracles", ePrint 2005/304, p. 5: one
  challenge signature, `Q = 1`) in the game with the three random oracles and the check oracle,
  the advantage averaged over `G_B`, `G_S` and `G_A`, with any bound `Rg` on
  `𝔼_{G_B, G_S} regGapAvg` in the regularity term. The McDiarmid terms, the
  witness-indistinguishability error and the check term `C · checkError reps tol s x` are those of
  `advantage_le_ideal_concrete`, averaged over the oracles.
* `advantage_le_bkm06_mldsa65`, `_mldsa87`: the regularity term
  `2 / ((1 - s) θ) · n · R · C / β_min` and the McDiarmid terms at most
  `√(N n log (C + 1)) / (2^2000 · θ (1 - θ) (1 - s) β_min)` (`expect_mcDiarmidTerms_le_of`: the
  collision probability of the commitment under a uniform matrix is at most `2^-4352`,
  `commitCollisionBound_le_mldsa65`, `_mldsa87`; `K |V| ≥ 1/16`,
  `one_div_sixteen_le_standinScale_mul_card_mldsa65`, `_mldsa87`), for `β_min ≤ 1`, at every
  defect budget `s < 1`, threshold fraction `θ ∈ (0, 1)` and number `reps` of check samples per
  member.
* `checkError_checkParams_le`, `advantage_le_bkm06_mldsa65_checkParams`, `_mldsa87_checkParams`:
  at `reps = 355`, `tol = 2` and `s = 1/2` the mass ratio factor is `2`, the McDiarmid terms at
  most `√(N n log (C + 1)) / (2^1999 · θ (1 - θ) β_min)` and the check term at `x = 89` at most
  `C · 2^-240`.

At ML-DSA-44 `τ · 2^12 > γ₂`, so the ct₀ check can fail and the acceptance floor (`FloorParams`)
does not apply. In its place:

* `expect_regGapAvg_le_of_weight`: `expect_regGapAvg_le_of` for any weight `W G t₀ ≥ 0` that
  bounds the mean member weights and is `0` only where they all are, with the Cauchy–Schwarz bound
  for a weight that may vanish (`expect_ringRegGap_le_sqrt_of_nonneg`) and a bound `B` on
  `𝔼_{s, Â, G} (W G t₀)⁻²`.
* `expect_regGapAvg_le_mldsa44`: for `β_min ≤ 1`, `𝔼_{G_B, G_S} regGapAvg ≤ R · C / β_min` with
  `R = 11 · 2^-101` (`expect_ringRegGap_le_sqrt_mldsa44_box_seven_of_nonneg`) and `C = 24/5`
  (`mldsa44OracleWeight`, `expect_expect_expect_inv_sq_mldsa44OracleWeight_le`): `log₂ C = 2.26`
  bits, so `log₂ (R · C) = -95.27`.
* `advantage_le_bkm06_mldsa44`, `advantage_le_bkm06_mldsa44_checkParams`: as at ML-DSA-65 and
  ML-DSA-87, with the same McDiarmid inputs (`commitCollisionBound_le_mldsa44`,
  `one_div_sixteen_le_standinScale_mul_card_mldsa44`, `two_pow_le_card_bucketVec_mldsa44`); at
  `reps = 355`, `tol = 2` and `s = 1/2` the check term is at most `C · 2^-240`
  (`checkError_checkParams_le`). At `β_min = θ = 1/2` and `n = 1024` the regularity term is
  `2 · 2 · 2/θ · n · R · C / β_min = 2^-80.27`.
-/

open Finset
open scoped BigOperators ENNReal

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA GordieHowe.MLDSA.Spec
  GordieHowe.MLDSA.Regularity PMF IOP GordieHowe.SPBCS GordieHowe.QROM
open LatticeCrypto TransformOps

attribute [local instance] concreteNTTRingOps

/-! ### The primitives of the game -/

section Primitives

variable (p : Params)

/-- **The concrete primitives with `SampleInBall = G` and `ExpandS = X`**: the vendored FIPS 204
primitives with the FIPS 204 `ExpandS` (`concretePrimitivesKeyGen`) with `SampleInBall`
(Algorithm 29) replaced by `G` and `ExpandS` (Algorithm 33) by `X`. -/
abbrev concreteWithSampleInBallExpandS (G : CommitHashBytes p → ChallengePoly)
    (X : _root_.MLDSA.Bytes 64 → RqVec p.l × RqVec p.k) : Primitives p :=
  { concretePrimitivesKeyGen p with sampleInBall := G, expandS := X }

/-- At the FIPS 204 `SampleInBall` and `ExpandS` these are the primitives
`concretePrimitivesKeyGen`. -/
theorem concreteWithSampleInBallExpandS_concrete :
    concreteWithSampleInBallExpandS p (concretePrimitives p).sampleInBall (Spec.expandS p) =
      concretePrimitivesKeyGen p :=
  rfl

variable {p}

/-- **The primitives with `SampleInBall` and `ExpandS` random oracles**: `SampleInBall = G_B`
onto the challenge set `B_τ` and `ExpandS = G_S` onto the coefficient arrays of `η`-bounded
secrets (`secretOfCoeffs`). -/
noncomputable abbrev oraclePrimitives (GB : CommitHashBytes p → ChallengeBall p.tau)
    (GS : _root_.MLDSA.Bytes 64 → SecretCoeffs p) : Primitives p :=
  concreteWithSampleInBallExpandS p (fun c => (GB c).1) fun rhoPrime => secretOfCoeffs (GS rhoPrime)

/-- The oracle primitives are `withExpandS` of `withSampleInBall` of `concretePrimitivesKeyGen`. -/
theorem oraclePrimitives_eq (GB : CommitHashBytes p → ChallengeBall p.tau)
    (GS : _root_.MLDSA.Bytes 64 → SecretCoeffs p) :
    oraclePrimitives GB GS =
      withExpandS (withSampleInBall (concretePrimitivesKeyGen p) fun c => (GB c).1) GS :=
  rfl

/-- ML-DSA-65 is an approved parameter set. -/
theorem isApproved_mldsa65 : mldsa65.isApproved := Or.inr (Or.inl rfl)

/-- ML-DSA-87 is an approved parameter set. -/
theorem isApproved_mldsa87 : mldsa87.isApproved := Or.inr (Or.inr rfl)

end Primitives

/-! ### Anonymity at the concrete primitives with `ExpandA` a random oracle -/

section Ideal

variable {p : Params} [NeZero (bucketCount p)] [Nonempty (MaskBox p)] {Msg : Type} [Fintype Msg]
  [DecidableEq Msg] {N : ℕ} {βmin : ℝ≥0∞} {reps tol : ℕ}
  {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {n Q : ℕ}

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] in
/-- **The signing laws at `concreteWithSampleInBallExpandS`** for `SampleInBall` of challenge
shape (`signingLaws_concreteWithSampleInBall`; the laws do not read `ExpandS`). -/
theorem signingLaws_concreteWithSampleInBallExpandS (hp : p.isApproved)
    {G : CommitHashBytes p → ChallengePoly} (hG : SampleInBallShape (concreteWithSampleInBall p G))
    (X : _root_.MLDSA.Bytes 64 → RqVec p.l × RqVec p.k) :
    SigningLaws (concreteWithSampleInBallExpandS p G X) :=
  let h := signingLaws_concreteWithSampleInBall p hp hG
  ⟨h.transform, h.hide_low, h.sampleInBall_smul_bound⟩

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] in
/-- **The verification laws at `concreteWithSampleInBallExpandS`** (`verifyLaws_concrete`; the
laws do not read `SampleInBall` or `ExpandS`). -/
theorem verifyLaws_concreteWithSampleInBallExpandS (hp : p.isApproved)
    (G : CommitHashBytes p → ChallengePoly) (X : _root_.MLDSA.Bytes 64 → RqVec p.l × RqVec p.k) :
    VerifyLaws (concreteWithSampleInBallExpandS p G X) (nttOps := concreteNTTRingOps) :=
  let h := verifyLaws_concrete hp
  ⟨h.transform, h.power2Round_decomp, h.useHint_makeHint⟩

open Classical in
/-- **Anonymity at the concrete primitives with `ExpandA` a random oracle**: `advantage_le_ideal`
at the vendored FIPS 204 primitives with any `SampleInBall = G` of challenge shape and any
`ExpandS = X` onto secrets with `‖s₂‖∞ ≤ η` (`concreteWithSampleInBallExpandS`), at every approved
parameter set, with the signing and verification laws
(`signingLaws_concreteWithSampleInBallExpandS`, `verifyLaws_concreteWithSampleInBallExpandS`), the
encoding (`concreteEnc_highBitsVec`) and `‖s₂‖∞ ≤ η` discharged. At the FIPS 204 `SampleInBall`
(`sampleInBallShape_concrete`) and `ExpandS` (`expandS_bounded`) the primitives are
`concretePrimitivesKeyGen` (`concreteWithSampleInBallExpandS_concrete`). -/
theorem advantage_le_ideal_concrete (hp : p.isApproved) {G : CommitHashBytes p → ChallengePoly}
    (hG : SampleInBallShape (concreteWithSampleInBall p G))
    {X : _root_.MLDSA.Bytes 64 → RqVec p.l × RqVec p.k}
    (hX : ∀ rhoPrime, polyVecBounded (X rhoPrime).2 p.eta) (hβ0 : βmin ≠ 0) (hβt : βmin ≠ ⊤)
    {s θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs1 : s < 1) {x : ℝ} (hx : 1 ≤ x) [NeZero n]
    {M : ∀ GA : _root_.MLDSA.Bytes 32 → TqMatrix p.k p.l, SPBCS Mg P (pubSigner
      (withExpandA (concreteWithSampleInBallExpandS p G X) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc p)).Stmt k kN kS L e}
    (A : ∀ GA : _root_.MLDSA.Bytes 32 → TqMatrix p.k p.l, PubAnonAdversary (pubSigner
      (withExpandA (concreteWithSampleInBallExpandS p G X) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc p)) (M GA) n Q)
    {E : ∀ GA, (j : ι) → ((M GA).comp j).Encoder}
    {V : ∀ GA, GameOrc (concretePrimitivesKeyGen p) Msg N reps →
      (pubSigner (withExpandA (concreteWithSampleInBallExpandS p G X) GA)
        (Msg := Msg) N βmin reps tol (concreteEnc p)).Stmt → FullTr P τ → Bool}
    {Qs : ∀ GA H x, (M GA).IOPQueries (V GA H) x} {R : Type} [Fintype R] [Nonempty R]
    {honest : ∀ GA, GameOrc (concretePrimitivesKeyGen p) Msg N reps →
      (pubSigner (withExpandA (concreteWithSampleInBallExpandS p G X) GA)
        (Msg := Msg) N βmin reps tol (concreteEnc p)).Wit → R → CausalProver P τ (pubSigner
        (withExpandA (concreteWithSampleInBallExpandS p G X) GA) (Msg := Msg) N βmin reps tol
          (concreteEnc p)).Stmt}
    (Rv : ∀ GA H, (M GA).Reveal (E GA) (Qs GA H)) {PubZ : Type}
    {pubZ : ∀ GA, (pubSigner (withExpandA (concreteWithSampleInBallExpandS p G X) GA) (Msg := Msg)
      N βmin reps tol (concreteEnc p)).Stmt → PubZ}
    {sim : ∀ GA H, CausalJointSimulator (Rv GA H).MV PubZ} {δ : NNReal}
    (hz : ∀ GA H, CausalHVZK (Rv GA H).MV ((pubSigner
      (withExpandA (concreteWithSampleInBallExpandS p G X) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc p)).rel H) (honest GA H) (pubZ GA) (sim GA H) δ)
    {C : ℕ} (hC : ∀ GA, (A GA).choices.card ≤ C)
    (D : ∀ GA, (Fin n → _root_.MLDSA.Bytes 32) → GameOrc (concretePrimitivesKeyGen p) Msg N reps →
      (Query k kN kS L → Out k e) →
      PubHist (BucketVec p) (M GA).NIProof Q → Prop) :
    𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix p.k p.l,
        (A GA).advantage (E GA) (Qs GA) (honest GA) (D GA) ≤
      (Q + 1) * idealAnonError (concreteWithSampleInBallExpandS p G X) A
          (SigningParams.of_isApproved hp) hβ0 hβt s θ C +
        Q * 𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix p.k p.l, (M GA).wiError δ (Q * C) +
          C * checkError reps tol s x :=
  advantage_le_ideal (concreteWithSampleInBallExpandS p G X) A (SigningParams.of_isApproved hp)
    hβ0 hβt (signingLaws_concreteWithSampleInBallExpandS hp hG X)
    (verifyLaws_concreteWithSampleInBallExpandS hp G X) (fun w => concreteEnc_highBitsVec hp w)
    (fun _ => hX _) hθ0 hθ1 hs1 hx Rv hz hC D

end Ideal


/-! ### The averaged regularity gap -/

section RegGap

variable {p : Params} [NeZero (bucketCount p)] [Nonempty (MaskBox p)]

/-- **The averaged regularity gap from the Cauchy–Schwarz bound and the weight tail.** For
`β_min ≤ 1` and the acceptance floor parameters of `p` (`FloorParams`), if
* for every key `sk₀` with `s₁, s₂` in the `η`-box, every `SampleInBall` oracle `G` onto `B_τ` and
  every positive lower bound `w Â` on the mean member weights,
  `𝔼_Â ringRegGap ≤ R / β_min · √(𝔼_Â (w Â)⁻²)` (`expect_ringRegGap_le_sqrt_mldsa65`),
* `𝔼_G (oracleAcceptFloor p κ G t₀)⁻² ≤ F(‖t₀‖₂²)` for `‖t₀‖∞ ≤ 2^12`, and
* `𝔼_{e, Â} F(‖t₀‖₂²) ≤ B` over uniform box secrets `e` and a uniform matrix, for every key,

then `𝔼_{G_B, G_S} regGapAvg (oraclePrimitives G_B G_S) ≤ R / β_min · √B`. -/
theorem expect_regGapAvg_le_of {x₀ κ : ℝ} (hf : FloorParams p x₀ κ) {βmin : ℝ≥0∞}
    (hβ1 : βmin ≤ 1) {R : ℝ} (hR : 0 ≤ R)
    (hgap : ∀ sk₀ : SecretKey p, polyVecBounded sk₀.s1 p.eta → polyVecBounded sk₀.s2 p.eta →
      ∀ (G : CommitHashBytes p → ChallengeBall p.tau) (w : TqMatrix p.k p.l → ℝ),
        (∀ aHat, 0 < w aHat) →
        (∀ aHat v, w aHat ≤ 𝔼 c, (memberWeight (oraclePrims G) βmin
          (matrixKey sk₀ aHat).t0 (v, c)).toReal) →
        𝔼 aHat, ringRegGap (oraclePrims G) (matrixKey sk₀ aHat) aHat βmin ≤
          R / βmin.toReal * √(𝔼 aHat, (w aHat ^ 2)⁻¹))
    {F : ℝ → ℝ} (hF : ∀ t0 : RqVec p.k, polyVecNorm t0 ≤ 4096 →
      𝔼 G : CommitHashBytes p → ChallengeBall p.tau, (oracleAcceptFloor p κ G t0)⁻¹ ^ 2 ≤
        F (t0SqNorm t0))
    {B : ℝ} (hB : ∀ sk : SecretKey p, 𝔼 e : SecretCoeffs p, 𝔼 aHat : TqMatrix p.k p.l,
      F (t0SqNorm (keyOf (keyOfCoeffs sk e)
        (keyMap (fun b => (keyOfCoeffs sk e).s1.get b) (matOfHat aHat))).t0) ≤ B) :
    𝔼 GB : CommitHashBytes p → ChallengeBall p.tau, 𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs p,
        regGapAvg (oraclePrimitives GB GS) βmin ≤ R / βmin.toReal * √B := by
  have := concreteNTTRingLaws
  have := challengeBall_nonempty hf.tau_le
  set c := R / βmin.toReal
  have hc : 0 ≤ c := div_nonneg hR ENNReal.toReal_nonneg
  set sk : _root_.MLDSA.Bytes 32 → SecretKey p := fun seed =>
    (keyGenFromSeed p (concretePrimitivesKeyGen p) seed).2
  set w : (CommitHashBytes p → ChallengeBall p.tau) → _root_.MLDSA.Bytes 32 → SecretCoeffs p →
      TqMatrix p.k p.l → ℝ := fun GB seed e aHat =>
    oracleAcceptFloor p κ GB (matrixKey (keyOfCoeffs (sk seed) e) aHat).t0
  set Y : (CommitHashBytes p → ChallengeBall p.tau) → _root_.MLDSA.Bytes 32 → SecretCoeffs p →
      ℝ := fun GB seed e => 𝔼 aHat, (w GB seed e aHat ^ 2)⁻¹
  have ht0 : ∀ (sk₀ : SecretKey p) aHat, polyVecNorm (matrixKey sk₀ aHat).t0 ≤ 4096 :=
    fun sk₀ aHat => by
      rw [matrixKey_t0]
      exact polyVecNorm_edgeT0Of_le _
  -- The gap at the key of key generation is the gap of the regularity argument.
  have hkey : ∀ GB, 𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs p,
      regGapAvg (oraclePrimitives GB GS) βmin =
        𝔼 seed : _root_.MLDSA.Bytes 32, 𝔼 e : SecretCoeffs p, 𝔼 aHat : TqMatrix p.k p.l,
          ringRegGap (oraclePrims GB) (matrixKey (keyOfCoeffs (sk seed) e) aHat) aHat βmin :=
    fun GB => by
      refine (expect_regGapAvg_withExpandS
        (withSampleInBall (concretePrimitivesKeyGen p) fun c => (GB c).1) βmin).trans ?_
      refine Finset.expect_congr rfl fun seed _ => Finset.expect_congr rfl fun e _ =>
        Finset.expect_congr rfl fun aHat _ => ?_
      exact ringRegGap_idealSecretKey_eq (fun c => (GB c).1) _ _ aHat _
        (keyOfCoeffs (sk seed) e) rfl rfl βmin
  -- The Cauchy–Schwarz bound for each key and oracle.
  have hstep : ∀ GB seed e, 𝔼 aHat : TqMatrix p.k p.l,
      ringRegGap (oraclePrims GB) (matrixKey (keyOfCoeffs (sk seed) e) aHat) aHat βmin ≤
        c * √(Y GB seed e) := fun GB seed e =>
    hgap (keyOfCoeffs (sk seed) e) (secretOfCoeffs_bounded e).1 (secretOfCoeffs_bounded e).2 GB
      (w GB seed e) (fun aHat => acceptFloor_pos _ _ _ _) fun aHat v =>
        oracleAcceptFloor_le_expect_memberWeight hf (oraclePrims GB) GB (fun _ => rfl) hβ1 _
          (ht0 _ aHat) v
  have hY0 : ∀ GB seed e, 0 ≤ Y GB seed e := fun GB seed e =>
    Finset.expect_nonneg fun aHat _ => inv_nonneg.2 (sq_nonneg _)
  -- The tail of the weight, averaged over the oracle, the secret and the matrix.
  have hYB : ∀ seed, 𝔼 e : SecretCoeffs p, 𝔼 GB : CommitHashBytes p → ChallengeBall p.tau,
      Y GB seed e ≤ B := fun seed => by
    refine le_trans (le_of_eq ?_) ((Finset.expect_le_expect fun e _ =>
      Finset.expect_le_expect fun aHat _ => hF _ (ht0 _ aHat)).trans (hB (sk seed)))
    refine Finset.expect_congr rfl fun e _ => ?_
    simp only [Y, w, inv_pow]
    exact Finset.expect_comm _ _ _
  calc 𝔼 GB : CommitHashBytes p → ChallengeBall p.tau,
        𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs p, regGapAvg (oraclePrimitives GB GS) βmin
      = 𝔼 GB : CommitHashBytes p → ChallengeBall p.tau, 𝔼 seed : _root_.MLDSA.Bytes 32,
          𝔼 e : SecretCoeffs p, 𝔼 aHat : TqMatrix p.k p.l,
            ringRegGap (oraclePrims GB) (matrixKey (keyOfCoeffs (sk seed) e) aHat) aHat βmin :=
        Finset.expect_congr rfl fun GB _ => hkey GB
    _ = 𝔼 seed : _root_.MLDSA.Bytes 32, 𝔼 e : SecretCoeffs p,
          𝔼 GB : CommitHashBytes p → ChallengeBall p.tau, 𝔼 aHat : TqMatrix p.k p.l,
            ringRegGap (oraclePrims GB) (matrixKey (keyOfCoeffs (sk seed) e) aHat) aHat βmin := by
        rw [Finset.expect_comm]
        exact Finset.expect_congr rfl fun seed _ => Finset.expect_comm _ _ _
    _ ≤ 𝔼 seed : _root_.MLDSA.Bytes 32, 𝔼 e : SecretCoeffs p,
          𝔼 GB : CommitHashBytes p → ChallengeBall p.tau, c * √(Y GB seed e) :=
        Finset.expect_le_expect fun seed _ => Finset.expect_le_expect fun e _ =>
          Finset.expect_le_expect fun GB _ => hstep GB seed e
    _ ≤ 𝔼 seed : _root_.MLDSA.Bytes 32, c * √B := by
        refine Finset.expect_le_expect fun seed _ => ?_
        simp_rw [← Finset.mul_expect]
        refine mul_le_mul_of_nonneg_left ?_ hc
        calc 𝔼 e : SecretCoeffs p, 𝔼 GB : CommitHashBytes p → ChallengeBall p.tau,
              √(Y GB seed e)
            ≤ 𝔼 e : SecretCoeffs p, √(𝔼 GB : CommitHashBytes p → ChallengeBall p.tau,
                Y GB seed e) :=
              Finset.expect_le_expect fun e _ =>
                Real.expect_sqrt_le_sqrt_expect _ fun GB => hY0 GB seed e
          _ ≤ √(𝔼 e : SecretCoeffs p, 𝔼 GB : CommitHashBytes p → ChallengeBall p.tau,
                Y GB seed e) :=
              Real.expect_sqrt_le_sqrt_expect _ fun e =>
                Finset.expect_nonneg fun GB _ => hY0 GB seed e
          _ ≤ √B := Real.sqrt_le_sqrt (hYB seed)
    _ = c * √B := Finset.expect_const Finset.univ_nonempty _

/-- **The averaged regularity gap at ML-DSA-65** with `ExpandS` and `SampleInBall`
random oracles: `𝔼_{G_B, G_S} regGapAvg ≤ 11 · 2^-199 · (9/2) / β_min` for
`β_min ≤ 1` (`expect_ringRegGap_le_sqrt_mldsa65_seven`,
`expect_expect_floorInvSqBound_le_mldsa65`). -/
theorem expect_regGapAvg_le_mldsa65 {βmin : ℝ≥0∞} (hβ0 : βmin ≠ 0) (hβ1 : βmin ≤ 1) :
    𝔼 GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65,
        regGapAvg (oraclePrimitives GB GS) βmin ≤ 11 / 2 ^ 199 * (9 / 2) / βmin.toReal := by
  have hβt : βmin ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hβ1
  refine (expect_regGapAvg_le_of floorParams_mldsa65 hβ1 (by positivity)
    (fun sk₀ h1 h2 G w hw0 hw => expect_ringRegGap_le_sqrt_mldsa65_seven sk₀ h1 h2
      (sampleInBallShape_oraclePrims G) hβ0 hβt hw0 hw)
    expect_inv_sq_oracleAcceptFloor_le_floorInvSqBound_mldsa65
    expect_expect_floorInvSqBound_le_mldsa65).trans_eq ?_
  rw [Real.sqrt_sq (by norm_num)]
  exact div_mul_eq_mul_div _ _ _

/-- **The averaged regularity gap at ML-DSA-87** with `ExpandS` and `SampleInBall`
random oracles: `𝔼_{G_B, G_S} regGapAvg ≤ 12 · 2^-294 · (33/5) / β_min` for
`β_min ≤ 1` (`expect_ringRegGap_le_sqrt_mldsa87_seven`,
`expect_expect_floorInvSqBound_le_mldsa87`). -/
theorem expect_regGapAvg_le_mldsa87 {βmin : ℝ≥0∞} (hβ0 : βmin ≠ 0) (hβ1 : βmin ≤ 1) :
    𝔼 GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87,
        regGapAvg (oraclePrimitives GB GS) βmin ≤ 12 / 2 ^ 294 * (33 / 5) / βmin.toReal := by
  have hβt : βmin ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hβ1
  refine (expect_regGapAvg_le_of floorParams_mldsa87 hβ1 (by positivity)
    (fun sk₀ h1 h2 G w hw0 hw => expect_ringRegGap_le_sqrt_mldsa87_seven sk₀ h1 h2
      (sampleInBallShape_oraclePrims G) hβ0 hβt hw0 hw)
    expect_inv_sq_oracleAcceptFloor_le_floorInvSqBound_mldsa87
    expect_expect_floorInvSqBound_le_mldsa87).trans_eq ?_
  rw [Real.sqrt_sq (by norm_num)]
  exact div_mul_eq_mul_div _ _ _

/-- **The averaged regularity gap from a weight that may vanish.** For `τ ≤ 256`, a weight
`W G t₀ ≥ 0` that bounds the mean member weights of every bucket vector for `‖t₀‖∞ ≤ 2^12` and is
`0` only where they are all `0`, if
* for every key `sk₀` with `s₁, s₂` in the `η`-box, every `SampleInBall` oracle `G` onto `B_τ` and
  every lower bound `w Â ≥ 0` on the mean member weights that is `0` only where they are all `0`,
  `𝔼_Â ringRegGap ≤ R / β_min · √(𝔼_Â (w Â)⁻²)` (`expect_ringRegGap_le_sqrt_of_nonneg`), and
* `𝔼_{e, Â, G} (W G t₀)⁻² ≤ B` over uniform box secrets `e`, a uniform matrix and a uniform oracle,
  for every key,

then `𝔼_{G_B, G_S} regGapAvg (oraclePrimitives G_B G_S) ≤ R / β_min · √B`. As
`expect_regGapAvg_le_of`, with `W` in place of the acceptance floor. -/
theorem expect_regGapAvg_le_of_weight (hτ : p.tau ≤ ringDegree) {βmin : ℝ≥0∞} {R : ℝ}
    (hR : 0 ≤ R) (W : (CommitHashBytes p → ChallengeBall p.tau) → RqVec p.k → ℝ)
    (hW0 : ∀ G t0, 0 ≤ W G t0)
    (hW : ∀ G t0, polyVecNorm t0 ≤ 4096 → ∀ v,
      W G t0 ≤ 𝔼 c, (memberWeight (oraclePrims G) βmin t0 (v, c)).toReal)
    (hWz : ∀ G t0, W G t0 = 0 → ∀ v,
      𝔼 c, (memberWeight (oraclePrims G) βmin t0 (v, c)).toReal = 0)
    (hgap : ∀ sk₀ : SecretKey p, polyVecBounded sk₀.s1 p.eta → polyVecBounded sk₀.s2 p.eta →
      ∀ (G : CommitHashBytes p → ChallengeBall p.tau) (w : TqMatrix p.k p.l → ℝ),
        (∀ aHat, 0 ≤ w aHat) →
        (∀ aHat v, w aHat ≤ 𝔼 c, (memberWeight (oraclePrims G) βmin
          (matrixKey sk₀ aHat).t0 (v, c)).toReal) →
        (∀ aHat, w aHat = 0 → ∀ v, 𝔼 c, (memberWeight (oraclePrims G) βmin
          (matrixKey sk₀ aHat).t0 (v, c)).toReal = 0) →
        𝔼 aHat, ringRegGap (oraclePrims G) (matrixKey sk₀ aHat) aHat βmin ≤
          R / βmin.toReal * √(𝔼 aHat, (w aHat ^ 2)⁻¹))
    {B : ℝ} (hB : ∀ sk : SecretKey p, 𝔼 e : SecretCoeffs p, 𝔼 aHat : TqMatrix p.k p.l,
      𝔼 G : CommitHashBytes p → ChallengeBall p.tau, (W G (keyOf (keyOfCoeffs sk e)
        (keyMap (fun b => (keyOfCoeffs sk e).s1.get b) (matOfHat aHat))).t0)⁻¹ ^ 2 ≤ B) :
    𝔼 GB : CommitHashBytes p → ChallengeBall p.tau, 𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs p,
        regGapAvg (oraclePrimitives GB GS) βmin ≤ R / βmin.toReal * √B := by
  have := concreteNTTRingLaws
  have := challengeBall_nonempty hτ
  set c := R / βmin.toReal
  have hc : 0 ≤ c := div_nonneg hR ENNReal.toReal_nonneg
  set sk : _root_.MLDSA.Bytes 32 → SecretKey p := fun seed =>
    (keyGenFromSeed p (concretePrimitivesKeyGen p) seed).2
  set w : (CommitHashBytes p → ChallengeBall p.tau) → _root_.MLDSA.Bytes 32 → SecretCoeffs p →
      TqMatrix p.k p.l → ℝ := fun GB seed e aHat =>
    W GB (matrixKey (keyOfCoeffs (sk seed) e) aHat).t0
  set Y : (CommitHashBytes p → ChallengeBall p.tau) → _root_.MLDSA.Bytes 32 → SecretCoeffs p →
      ℝ := fun GB seed e => 𝔼 aHat, (w GB seed e aHat ^ 2)⁻¹
  have ht0 : ∀ (sk₀ : SecretKey p) aHat, polyVecNorm (matrixKey sk₀ aHat).t0 ≤ 4096 :=
    fun sk₀ aHat => by
      rw [matrixKey_t0]
      exact polyVecNorm_edgeT0Of_le _
  -- The gap at the key of key generation is the gap of the regularity argument.
  have hkey : ∀ GB, 𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs p,
      regGapAvg (oraclePrimitives GB GS) βmin =
        𝔼 seed : _root_.MLDSA.Bytes 32, 𝔼 e : SecretCoeffs p, 𝔼 aHat : TqMatrix p.k p.l,
          ringRegGap (oraclePrims GB) (matrixKey (keyOfCoeffs (sk seed) e) aHat) aHat βmin :=
    fun GB => by
      refine (expect_regGapAvg_withExpandS
        (withSampleInBall (concretePrimitivesKeyGen p) fun c => (GB c).1) βmin).trans ?_
      refine Finset.expect_congr rfl fun seed _ => Finset.expect_congr rfl fun e _ =>
        Finset.expect_congr rfl fun aHat _ => ?_
      exact ringRegGap_idealSecretKey_eq (fun c => (GB c).1) _ _ aHat _
        (keyOfCoeffs (sk seed) e) rfl rfl βmin
  -- The Cauchy–Schwarz bound for each key and oracle.
  have hstep : ∀ GB seed e, 𝔼 aHat : TqMatrix p.k p.l,
      ringRegGap (oraclePrims GB) (matrixKey (keyOfCoeffs (sk seed) e) aHat) aHat βmin ≤
        c * √(Y GB seed e) := fun GB seed e =>
    hgap (keyOfCoeffs (sk seed) e) (secretOfCoeffs_bounded e).1 (secretOfCoeffs_bounded e).2 GB
      (w GB seed e) (fun aHat => hW0 _ _) (fun aHat v => hW GB _ (ht0 _ aHat) v)
      (fun aHat h v => hWz GB _ h v)
  have hY0 : ∀ GB seed e, 0 ≤ Y GB seed e := fun GB seed e =>
    Finset.expect_nonneg fun aHat _ => inv_nonneg.2 (sq_nonneg _)
  -- The weight averaged over the oracle, the secret and the matrix.
  have hYB : ∀ seed, 𝔼 e : SecretCoeffs p, 𝔼 GB : CommitHashBytes p → ChallengeBall p.tau,
      Y GB seed e ≤ B := fun seed => by
    refine le_trans (le_of_eq ?_) (hB (sk seed))
    refine Finset.expect_congr rfl fun e _ => ?_
    simp only [Y, w, inv_pow]
    exact Finset.expect_comm _ _ _
  calc 𝔼 GB : CommitHashBytes p → ChallengeBall p.tau,
        𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs p, regGapAvg (oraclePrimitives GB GS) βmin
      = 𝔼 GB : CommitHashBytes p → ChallengeBall p.tau, 𝔼 seed : _root_.MLDSA.Bytes 32,
          𝔼 e : SecretCoeffs p, 𝔼 aHat : TqMatrix p.k p.l,
            ringRegGap (oraclePrims GB) (matrixKey (keyOfCoeffs (sk seed) e) aHat) aHat βmin :=
        Finset.expect_congr rfl fun GB _ => hkey GB
    _ = 𝔼 seed : _root_.MLDSA.Bytes 32, 𝔼 e : SecretCoeffs p,
          𝔼 GB : CommitHashBytes p → ChallengeBall p.tau, 𝔼 aHat : TqMatrix p.k p.l,
            ringRegGap (oraclePrims GB) (matrixKey (keyOfCoeffs (sk seed) e) aHat) aHat βmin := by
        rw [Finset.expect_comm]
        exact Finset.expect_congr rfl fun seed _ => Finset.expect_comm _ _ _
    _ ≤ 𝔼 seed : _root_.MLDSA.Bytes 32, 𝔼 e : SecretCoeffs p,
          𝔼 GB : CommitHashBytes p → ChallengeBall p.tau, c * √(Y GB seed e) :=
        Finset.expect_le_expect fun seed _ => Finset.expect_le_expect fun e _ =>
          Finset.expect_le_expect fun GB _ => hstep GB seed e
    _ ≤ 𝔼 seed : _root_.MLDSA.Bytes 32, c * √B := by
        refine Finset.expect_le_expect fun seed _ => ?_
        simp_rw [← Finset.mul_expect]
        refine mul_le_mul_of_nonneg_left ?_ hc
        calc 𝔼 e : SecretCoeffs p, 𝔼 GB : CommitHashBytes p → ChallengeBall p.tau,
              √(Y GB seed e)
            ≤ 𝔼 e : SecretCoeffs p, √(𝔼 GB : CommitHashBytes p → ChallengeBall p.tau,
                Y GB seed e) :=
              Finset.expect_le_expect fun e _ =>
                Real.expect_sqrt_le_sqrt_expect _ fun GB => hY0 GB seed e
          _ ≤ √(𝔼 e : SecretCoeffs p, 𝔼 GB : CommitHashBytes p → ChallengeBall p.tau,
                Y GB seed e) :=
              Real.expect_sqrt_le_sqrt_expect _ fun e =>
                Finset.expect_nonneg fun GB _ => hY0 GB seed e
          _ ≤ √B := Real.sqrt_le_sqrt (hYB seed)
    _ = c * √B := Finset.expect_const Finset.univ_nonempty _

/-- **The averaged regularity gap at ML-DSA-44** with `ExpandS` and `SampleInBall`
random oracles: `𝔼_{G_B, G_S} regGapAvg ≤ 11 · 2^-101 · (24/5) / β_min` for `β_min ≤ 1`
(`expect_regGapAvg_le_of_weight` with the weight `mldsa44OracleWeight`,
`expect_ringRegGap_le_sqrt_mldsa44_box_seven_of_nonneg`,
`expect_expect_expect_inv_sq_mldsa44OracleWeight_le`). -/
theorem expect_regGapAvg_le_mldsa44 {βmin : ℝ≥0∞} (hβ0 : βmin ≠ 0) (hβ1 : βmin ≤ 1) :
    𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
        regGapAvg (oraclePrimitives GB GS) βmin ≤ 11 / 2 ^ 101 * (24 / 5) / βmin.toReal := by
  have := concreteNTTRingLaws
  have hβt : βmin ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hβ1
  refine (expect_regGapAvg_le_of_weight (p := _root_.MLDSA.mldsa44)
    (by rw [show _root_.MLDSA.mldsa44.tau = 39 from rfl]; norm_num [ringDegree]) (by positivity)
    mldsa44OracleWeight mldsa44OracleWeight_nonneg
    (fun G t0 ht0 v => mldsa44OracleWeight_le_expect_memberWeight (oraclePrims G) G
      (fun _ => rfl) hβ1 t0 ht0 v)
    (fun G t0 h v => expect_memberWeight_eq_zero_of_mldsa44OracleWeight (oraclePrims G) G
      (fun _ => rfl) βmin t0 h v)
    (fun sk₀ h1 h2 G w hw0 hw hz => expect_ringRegGap_le_sqrt_mldsa44_box_seven_of_nonneg sk₀ h1 h2
      (sampleInBallShape_oraclePrims G) hβ0 hβt hw0 hw hz)
    expect_expect_expect_inv_sq_mldsa44OracleWeight_le).trans_eq ?_
  rw [Real.sqrt_sq (by norm_num)]
  exact div_mul_eq_mul_div _ _ _

end RegGap

section BKM06

variable {p : Params} [NeZero (bucketCount p)] [Nonempty (MaskBox p)]
  {Msg : Type} [Fintype Msg] [DecidableEq Msg] {N : ℕ} {βmin : ℝ≥0∞} {reps tol : ℕ}
  {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {n : ℕ}
  {M : ∀ (GB : CommitHashBytes p → ChallengeBall p.tau)
    (GS : _root_.MLDSA.Bytes 64 → SecretCoeffs p)
    (GA : _root_.MLDSA.Bytes 32 → TqMatrix p.k p.l),
    SPBCS Mg P (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
      (concreteEnc p)).Stmt k kN kS L e}
  (A : ∀ GB GS GA, PubAnonAdversary (pubSigner (withExpandA (oraclePrimitives GB GS) GA)
    (Msg := Msg) N βmin reps tol (concreteEnc p)) (M GB GS GA) n 1)
  {E : ∀ GB GS GA, (j : ι) → ((M GB GS GA).comp j).Encoder}
  {V : ∀ GB GS GA, GameOrc (concretePrimitivesKeyGen p) Msg N reps →
    (pubSigner (withExpandA (oraclePrimitives GB GS) GA)
      (Msg := Msg) N βmin reps tol (concreteEnc p)).Stmt → FullTr P τ → Bool}
  {Qs : ∀ GB GS GA H x, (M GB GS GA).IOPQueries (V GB GS GA H) x} {R : Type} [Fintype R]
  [Nonempty R]
  {honest : ∀ GB GS GA, GameOrc (concretePrimitivesKeyGen p) Msg N reps →
    (pubSigner (withExpandA (oraclePrimitives GB GS) GA)
      (Msg := Msg) N βmin reps tol (concreteEnc p)).Wit → R → CausalProver P τ (pubSigner
      (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc p)).Stmt}
  (D : ∀ GB GS GA, (Fin n → _root_.MLDSA.Bytes 32) →
    GameOrc (concretePrimitivesKeyGen p) Msg N reps →
    (Query k kN kS L → Out k e) → PubHist (BucketVec p) (M GB GS GA).NIProof 1 → Prop)

open Classical in
/-- **Anonymity in the sense of BKM06 Definition 4 with three random oracles** (Bender, Katz and
Morselli, "Ring Signatures: Stronger Definitions, and Constructions without Random Oracles",
ePrint 2005/304, p. 5: the adversary chooses a ring and two honest indices and receives one
challenge signature, `Q = 1`): in the game with `SampleInBall = G_B`, `ExpandS = G_S` and
`ExpandA = G_A` random oracles (`oraclePrimitives`, `withExpandA`), the advantage averaged over
the three oracles is at most `2 · (2 / ((1 - s) θ) · n · Rg + 𝔼_{G_B, G_S, G_A, keys}
(√(maxDevVar · log C / 2) + √(maxCountVar · log (C + 1) / 2))) + 𝔼_{G_B, G_S, G_A} wiError δ C +
C · checkError reps tol s x` for every `x ≥ 1` and
any bound `Rg` on `𝔼_{G_B, G_S} regGapAvg` (`advantage_le_ideal_concrete` at each `G_B`,
`G_S`). `expect_regGapAvg_le_mldsa65` and the others give `Rg`. -/
theorem advantage_le_bkm06 (hp : p.isApproved) (hβ0 : βmin ≠ 0) (hβt : βmin ≠ ⊤)
    {s θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs1 : s < 1) {x : ℝ} (hx : 1 ≤ x) [NeZero n]
    (Rv : ∀ GB GS GA H, (M GB GS GA).Reveal (E GB GS GA) (Qs GB GS GA H)) {PubZ : Type}
    {pubZ : ∀ GB GS GA, (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
      reps tol (concreteEnc p)).Stmt → PubZ}
    {sim : ∀ GB GS GA H, CausalJointSimulator (Rv GB GS GA H).MV PubZ} {δ : NNReal}
    (hz : ∀ GB GS GA H, CausalHVZK (Rv GB GS GA H).MV ((pubSigner
      (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc p)).rel H)
      (honest GB GS GA H) (pubZ GB GS GA) (sim GB GS GA H) δ)
    {C : ℕ} (hC : ∀ GB GS GA, (A GB GS GA).choices.card ≤ C)
    {Rg : ℝ} (hR : 𝔼 GB : CommitHashBytes p → ChallengeBall p.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs p, regGapAvg (oraclePrimitives GB GS) βmin ≤ Rg) :
    𝔼 GB : CommitHashBytes p → ChallengeBall p.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs p,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix p.k p.l,
          (A GB GS GA).advantage (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) (D GB GS GA) ≤
      2 * (2 * (1 - s)⁻¹ / θ * (n * Rg) +
        𝔼 GB : CommitHashBytes p → ChallengeBall p.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs p,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix p.k p.l,
              𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
                (√(maxDevVar (withExpandA (oraclePrimitives GB GS) GA) (A GB GS GA)
                    (SigningParams.of_isApproved hp) hβ0 hβt s θ keys * Real.log C / 2) +
                  √(maxCountVar (withExpandA (oraclePrimitives GB GS) GA) (A GB GS GA)
                    (SigningParams.of_isApproved hp) hβ0 hβt s θ keys *
                      Real.log (C + 1) / 2))) +
        𝔼 GB : CommitHashBytes p → ChallengeBall p.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs p,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix p.k p.l, (M GB GS GA).wiError δ C +
          C * checkError reps tol s x := by
  have hG : ∀ GB GS, 𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix p.k p.l,
      (A GB GS GA).advantage (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) (D GB GS GA) ≤
        2 * (2 * (1 - s)⁻¹ / θ * (n * regGapAvg (oraclePrimitives GB GS) βmin) +
          𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix p.k p.l, 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
            (√(maxDevVar (withExpandA (oraclePrimitives GB GS) GA) (A GB GS GA)
                (SigningParams.of_isApproved hp) hβ0 hβt s θ keys * Real.log C / 2) +
              √(maxCountVar (withExpandA (oraclePrimitives GB GS) GA) (A GB GS GA)
                (SigningParams.of_isApproved hp) hβ0 hβt s θ keys * Real.log (C + 1) / 2))) +
          𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix p.k p.l, (M GB GS GA).wiError δ C +
          C * checkError reps tol s x := by
    intro GB GS
    have h := advantage_le_ideal_concrete hp (sampleInBallShape_oraclePrims GB)
      (fun rhoPrime => (secretOfCoeffs_bounded (GS rhoPrime)).2) hβ0 hβt hθ0 hθ1 hs1 hx
      (A GB GS) (Rv GB GS) (hz GB GS) (hC GB GS) (D GB GS)
    unfold idealAnonError at h
    simp only [Nat.cast_one, one_mul, one_add_one_eq_two] at h
    exact h
  have hθ : 0 ≤ 2 * (1 - s)⁻¹ / θ := by positivity
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine (Finset.expect_le_expect fun GB _ => Finset.expect_le_expect fun GS _ =>
    hG GB GS).trans ?_
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]
  gcongr
  rcases Finset.eq_empty_or_nonempty (Finset.univ (α := CommitHashBytes p → ChallengeBall p.tau))
    with h | h
  · rw [h, Finset.expect_empty]
    exact checkError_nonneg reps tol s (zero_le_one.trans hx)
  · rw [Finset.expect_const h]

end BKM06

/-! ### The check parameters -/

/-- **The check error at the check parameters**: at 355 samples per member, tolerance `2`, the
defect budget `1/2` and `x = 89`, `89² · exp(-(88/89) · 177.5) ≤ 2^-240`, from `89² ≤ 2^13` and
`(88/89) · 177.5 ≥ 253 · log 2` (`log 2 < 0.6931471808`, `Real.log_two_lt_d9`). -/
theorem checkError_checkParams_le : checkError 355 2 (1 / 2) 89 ≤ 1 / 2 ^ 240 := by
  have h2 : Real.exp ((253 : ℕ) * Real.log 2) = 2 ^ 253 := by
    rw [Real.exp_nat_mul, Real.exp_log two_pos]
  have hl := Real.log_two_lt_d9
  have he : Real.exp (-((1 - (89 : ℝ)⁻¹) * ((355 : ℕ) * (1 / 2)))) ≤ 1 / 2 ^ 253 :=
    calc Real.exp (-((1 - (89 : ℝ)⁻¹) * ((355 : ℕ) * (1 / 2))))
        ≤ Real.exp (-((253 : ℕ) * Real.log 2)) :=
          Real.exp_le_exp.2 (by push_cast; norm_num at hl ⊢; linarith)
      _ = 1 / 2 ^ 253 := by rw [Real.exp_neg, h2, one_div]
  unfold checkError
  calc (89 : ℝ) ^ 2 * Real.exp (-((1 - (89 : ℝ)⁻¹) * ((355 : ℕ) * (1 / 2))))
      ≤ 2 ^ 13 * (1 / 2 ^ 253) :=
        mul_le_mul (by norm_num) he (Real.exp_pos _).le (by norm_num)
    _ = 1 / 2 ^ 240 := by norm_num

section BKM06_mldsa65

variable {Msg : Type} [Fintype Msg] [DecidableEq Msg] {N : ℕ} {βmin : ℝ≥0∞} {reps tol : ℕ}
  {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {n : ℕ}
  {M : ∀ (GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau)
    (GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65)
    (GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l),
    SPBCS Mg P (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
      (concreteEnc mldsa65)).Stmt k kN kS L e}
  (A : ∀ GB GS GA, PubAnonAdversary (pubSigner (withExpandA (oraclePrimitives GB GS) GA)
    (Msg := Msg) N βmin reps tol (concreteEnc mldsa65)) (M GB GS GA) n 1)
  {E : ∀ GB GS GA, (j : ι) → ((M GB GS GA).comp j).Encoder}
  {V : ∀ GB GS GA, GameOrc (concretePrimitivesKeyGen mldsa65) Msg N reps →
    (pubSigner (withExpandA (oraclePrimitives GB GS) GA)
      (Msg := Msg) N βmin reps tol (concreteEnc mldsa65)).Stmt → FullTr P τ → Bool}
  {Qs : ∀ GB GS GA H x, (M GB GS GA).IOPQueries (V GB GS GA H) x} {R : Type} [Fintype R]
  [Nonempty R]
  {honest : ∀ GB GS GA, GameOrc (concretePrimitivesKeyGen mldsa65) Msg N reps →
    (pubSigner (withExpandA (oraclePrimitives GB GS) GA)
      (Msg := Msg) N βmin reps tol (concreteEnc mldsa65)).Wit → R → CausalProver P τ (pubSigner
      (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa65)).Stmt}
  (D : ∀ GB GS GA, (Fin n → _root_.MLDSA.Bytes 32) →
    GameOrc (concretePrimitivesKeyGen mldsa65) Msg N reps →
    (Query k kN kS L → Out k e) → PubHist (BucketVec mldsa65) (M GB GS GA).NIProof 1 → Prop)

open Classical in
/-- **Anonymity at ML-DSA-65** (BKM06 Definition 4, `Q = 1`) in the game with
`SampleInBall`, `ExpandS` and `ExpandA` random oracles: `advantage_le_bkm06` with the regularity
term `2 / ((1 - s) θ) · n · 11 · 2^-199 · (9/2) / β_min` for `β_min ≤ 1`
(`expect_regGapAvg_le_mldsa65`) and the McDiarmid terms at most
`√(N n log (C + 1)) / (2^2000 · θ (1 - θ) (1 - s) β_min)` (`expect_mcDiarmidTerms_le_of`), at
every defect budget `s < 1` and threshold fraction `θ ∈ (0, 1)`. -/
theorem advantage_le_bkm06_mldsa65 (hβ0 : βmin ≠ 0) (hβ1 : βmin ≤ 1) (hβt : βmin ≠ ⊤)
    {s θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs1 : s < 1) {x : ℝ} (hx : 1 ≤ x) [NeZero n]
    (Rv : ∀ GB GS GA H, (M GB GS GA).Reveal (E GB GS GA) (Qs GB GS GA H)) {PubZ : Type}
    {pubZ : ∀ GB GS GA, (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
      reps tol (concreteEnc mldsa65)).Stmt → PubZ}
    {sim : ∀ GB GS GA H, CausalJointSimulator (Rv GB GS GA H).MV PubZ} {δ : NNReal}
    (hz : ∀ GB GS GA H, CausalHVZK (Rv GB GS GA H).MV ((pubSigner
      (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa65)).rel H)
      (honest GB GS GA H) (pubZ GB GS GA) (sim GB GS GA H) δ)
    {C : ℕ} (hC : ∀ GB GS GA, (A GB GS GA).choices.card ≤ C) :
    𝔼 GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l,
          (A GB GS GA).advantage (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) (D GB GS GA) ≤
      2 * (2 * (1 - s)⁻¹ / θ * (n * (11 / 2 ^ 199 * (9 / 2) / βmin.toReal)) +
        √(N * n * Real.log (C + 1)) / (2 ^ 2000 * (θ * (1 - θ) * (1 - s) * βmin.toReal))) +
        𝔼 GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l, (M GB GS GA).wiError δ C +
          C * checkError reps tol s x := by
  have := concreteNTTRingLaws
  have := challengeBall_nonempty floorParams_mldsa65.tau_le
  have hM : 𝔼 GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l,
          𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
            (√(maxDevVar (withExpandA (oraclePrimitives GB GS) GA) (A GB GS GA)
                (SigningParams.of_isApproved
                  isApproved_mldsa65) hβ0 hβt s θ keys * Real.log C / 2) +
              √(maxCountVar (withExpandA (oraclePrimitives GB GS) GA) (A GB GS GA)
                (SigningParams.of_isApproved
                  isApproved_mldsa65) hβ0 hβt s θ keys *
                  Real.log (C + 1) / 2)) ≤
        √(N * n * Real.log (C + 1)) / (2 ^ 2000 * (θ * (1 - θ) * (1 - s) * βmin.toReal)) :=
    (Finset.expect_le_expect fun GB _ => (Finset.expect_le_expect fun GS _ =>
      expect_mcDiarmidTerms_le_of (oraclePrimitives GB GS) (A GB GS)
        (SigningParams.of_isApproved isApproved_mldsa65) hβ0 hβ1 hβt hθ0 hθ1 hs1 C
        commitCollisionBound_le_mldsa65 one_div_sixteen_le_standinScale_mul_card_mldsa65
        two_pow_le_card_bucketVec_mldsa65).trans_eq
      (Finset.expect_const univ_nonempty _)).trans_eq (Finset.expect_const univ_nonempty _)
  refine (advantage_le_bkm06 A D isApproved_mldsa65 hβ0 hβt hθ0 hθ1 hs1 hx Rv hz hC
    (expect_regGapAvg_le_mldsa65 hβ0 hβ1)).trans ?_
  gcongr

open Classical in
/-- **Anonymity at ML-DSA-65 at the check parameters**: `advantage_le_bkm06_mldsa65` with
`reps = 355` samples per member, at most `tol = 2` failed samples per ring and the defect
budget `s = 1/2`, so the mass ratio factor is `1 / (1 - s) = 2`, the McDiarmid terms at most
`√(N n log (C + 1)) / (2^1999 · θ (1 - θ) β_min)` and the check term at `x = 89`
`C · 89² · exp(-(88/89) · 177.5) ≤ C · 2^-240` (`checkError_checkParams_le`). At `β_min = 1/2` the
regularity term is `2 · 2/θ · n · 11 · 2^-199 · (9/2) · 2`. -/
theorem advantage_le_bkm06_mldsa65_checkParams (hβ0 : βmin ≠ 0) (hβ1 : βmin ≤ 1)
    (hβt : βmin ≠ ⊤)
    (hreps : reps = 355) (htol : tol = 2) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) [NeZero n]
    (Rv : ∀ GB GS GA H, (M GB GS GA).Reveal (E GB GS GA) (Qs GB GS GA H)) {PubZ : Type}
    {pubZ : ∀ GB GS GA, (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
      reps tol (concreteEnc mldsa65)).Stmt → PubZ}
    {sim : ∀ GB GS GA H, CausalJointSimulator (Rv GB GS GA H).MV PubZ} {δ : NNReal}
    (hz : ∀ GB GS GA H, CausalHVZK (Rv GB GS GA H).MV ((pubSigner
      (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa65)).rel H)
      (honest GB GS GA H) (pubZ GB GS GA) (sim GB GS GA H) δ)
    {C : ℕ} (hC : ∀ GB GS GA, (A GB GS GA).choices.card ≤ C) :
    𝔼 GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l,
          (A GB GS GA).advantage (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) (D GB GS GA) ≤
      2 * (2 * 2 / θ * (n * (11 / 2 ^ 199 * (9 / 2) / βmin.toReal)) +
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * βmin.toReal))) +
        𝔼 GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l, (M GB GS GA).wiError δ C +
          C / 2 ^ 240 := by
  have h := advantage_le_bkm06_mldsa65 A D hβ0 hβ1 hβt (s := 1 / 2) hθ0 hθ1 (by norm_num)
    (x := 89) (by norm_num) Rv hz hC
  have h2 : (1 - (1 / 2 : ℝ))⁻¹ = 2 := by norm_num
  rw [h2] at h
  have he : (C : ℝ) * checkError reps tol (1 / 2) 89 ≤ C / 2 ^ 240 := by
    rw [hreps, htol]
    exact (mul_le_mul_of_nonneg_left checkError_checkParams_le (Nat.cast_nonneg _)).trans_eq
      (mul_one_div _ _)
  have hm : √(N * n * Real.log (C + 1)) / (2 ^ 2000 * (θ * (1 - θ) * (1 - 1 / 2) * βmin.toReal)) =
      √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * βmin.toReal)) := by
    rw [show (2 : ℝ) ^ 2000 = 2 ^ 1999 * 2 from pow_succ 2 1999]
    generalize (2 : ℝ) ^ 1999 = T
    ring
  rw [hm] at h
  generalize 11 / 2 ^ 199 * (9 / 2) / βmin.toReal = r at h ⊢
  generalize √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * βmin.toReal)) = m at h ⊢
  linarith

end BKM06_mldsa65

section BKM06_mldsa44

variable {Msg : Type} [Fintype Msg] [DecidableEq Msg] {N : ℕ} {βmin : ℝ≥0∞} {reps tol : ℕ}
  {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {n : ℕ}
  {M : ∀ (GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau)
    (GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44)
    (GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l),
    SPBCS Mg P (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
      (concreteEnc _root_.MLDSA.mldsa44)).Stmt k kN kS L e}
  (A : ∀ GB GS GA, PubAnonAdversary (pubSigner (withExpandA (oraclePrimitives GB GS) GA)
    (Msg := Msg) N βmin reps tol (concreteEnc _root_.MLDSA.mldsa44)) (M GB GS GA) n 1)
  {E : ∀ GB GS GA, (j : ι) → ((M GB GS GA).comp j).Encoder}
  {V : ∀ GB GS GA, GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa44) Msg N reps →
    (pubSigner (withExpandA (oraclePrimitives GB GS) GA)
      (Msg := Msg) N βmin reps tol (concreteEnc _root_.MLDSA.mldsa44)).Stmt → FullTr P τ → Bool}
  {Qs : ∀ GB GS GA H x, (M GB GS GA).IOPQueries (V GB GS GA H) x} {R : Type} [Fintype R]
  [Nonempty R]
  {honest : ∀ GB GS GA, GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa44) Msg N reps →
    (pubSigner (withExpandA (oraclePrimitives GB GS) GA)
      (Msg := Msg) N βmin reps tol (concreteEnc _root_.MLDSA.mldsa44)).Wit → R → CausalProver P τ
          (pubSigner
      (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc _root_.MLDSA.mldsa44)).Stmt}
  (D : ∀ GB GS GA, (Fin n → _root_.MLDSA.Bytes 32) →
    GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa44) Msg N reps →
    (Query k kN kS L → Out k e) → PubHist (BucketVec _root_.MLDSA.mldsa44) (M GB GS GA).NIProof 1 →
        Prop)

open Classical in
/-- **Anonymity at ML-DSA-44** (BKM06 Definition 4, `Q = 1`) in the game with
`SampleInBall`, `ExpandS` and `ExpandA` random oracles: `advantage_le_bkm06` with the regularity
term `2 / ((1 - s) θ) · n · 11 · 2^-101 · (24/5) / β_min` for `β_min ≤ 1`
(`expect_regGapAvg_le_mldsa44`) and the McDiarmid terms at most
`√(N n log (C + 1)) / (2^2000 · θ (1 - θ) (1 - s) β_min)` (`expect_mcDiarmidTerms_le_of`), at
every defect budget `s < 1` and threshold fraction `θ ∈ (0, 1)`. -/
theorem advantage_le_bkm06_mldsa44 (hβ0 : βmin ≠ 0) (hβ1 : βmin ≤ 1) (hβt : βmin ≠ ⊤)
    {s θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs1 : s < 1) {x : ℝ} (hx : 1 ≤ x) [NeZero n]
    (Rv : ∀ GB GS GA H, (M GB GS GA).Reveal (E GB GS GA) (Qs GB GS GA H)) {PubZ : Type}
    {pubZ : ∀ GB GS GA, (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
      reps tol (concreteEnc _root_.MLDSA.mldsa44)).Stmt → PubZ}
    {sim : ∀ GB GS GA H, CausalJointSimulator (Rv GB GS GA H).MV PubZ} {δ : NNReal}
    (hz : ∀ GB GS GA H, CausalHVZK (Rv GB GS GA H).MV ((pubSigner
      (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc _root_.MLDSA.mldsa44)).rel H)
      (honest GB GS GA H) (pubZ GB GS GA) (sim GB GS GA H) δ)
    {C : ℕ} (hC : ∀ GB GS GA, (A GB GS GA).choices.card ≤ C) :
    𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
          (A GB GS GA).advantage (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) (D GB GS GA) ≤
      2 * (2 * (1 - s)⁻¹ / θ * (n * (11 / 2 ^ 101 * (24 / 5) / βmin.toReal)) +
        √(N * n * Real.log (C + 1)) / (2 ^ 2000 * (θ * (1 - θ) * (1 - s) * βmin.toReal))) +
        𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
                (M GB GS GA).wiError δ C +
          C * checkError reps tol s x := by
  have := concreteNTTRingLaws
  have := challengeBall_nonempty (τ := _root_.MLDSA.mldsa44.tau) (by
    rw [show _root_.MLDSA.mldsa44.tau = 39 from rfl]; norm_num [ringDegree])
  have hM : 𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
          𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
            (√(maxDevVar (withExpandA (oraclePrimitives GB GS) GA) (A GB GS GA)
                (SigningParams.of_isApproved
                  isApproved_mldsa44) hβ0 hβt s θ keys * Real.log C / 2) +
              √(maxCountVar (withExpandA (oraclePrimitives GB GS) GA) (A GB GS GA)
                (SigningParams.of_isApproved
                  isApproved_mldsa44) hβ0 hβt s θ keys *
                  Real.log (C + 1) / 2)) ≤
        √(N * n * Real.log (C + 1)) / (2 ^ 2000 * (θ * (1 - θ) * (1 - s) * βmin.toReal)) :=
    (Finset.expect_le_expect fun GB _ => (Finset.expect_le_expect fun GS _ =>
      expect_mcDiarmidTerms_le_of (oraclePrimitives GB GS) (A GB GS)
        (SigningParams.of_isApproved isApproved_mldsa44) hβ0 hβ1 hβt hθ0 hθ1 hs1 C
        commitCollisionBound_le_mldsa44 one_div_sixteen_le_standinScale_mul_card_mldsa44
        two_pow_le_card_bucketVec_mldsa44).trans_eq
      (Finset.expect_const univ_nonempty _)).trans_eq (Finset.expect_const univ_nonempty _)
  refine (advantage_le_bkm06 A D isApproved_mldsa44 hβ0 hβt hθ0 hθ1 hs1 hx Rv hz hC
    (expect_regGapAvg_le_mldsa44 hβ0 hβ1)).trans ?_
  gcongr

open Classical in
/-- **Anonymity at ML-DSA-44 at the check parameters**: `advantage_le_bkm06_mldsa44` with
`reps = 355` samples per member, at most `tol = 2` failed samples per ring and the defect
budget `s = 1/2`, so the mass ratio factor is `1 / (1 - s) = 2`, the McDiarmid terms at most
`√(N n log (C + 1)) / (2^1999 · θ (1 - θ) β_min)` and the check term at `x = 89`
`C · 89² · exp(-(88/89) · 177.5) ≤ C · 2^-240` (`checkError_checkParams_le`). At `β_min = 1/2` the
regularity term is `2 · 2/θ · n · 11 · 2^-101 · (24/5) · 2`. -/
theorem advantage_le_bkm06_mldsa44_checkParams (hβ0 : βmin ≠ 0) (hβ1 : βmin ≤ 1)
    (hβt : βmin ≠ ⊤)
    (hreps : reps = 355) (htol : tol = 2) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) [NeZero n]
    (Rv : ∀ GB GS GA H, (M GB GS GA).Reveal (E GB GS GA) (Qs GB GS GA H)) {PubZ : Type}
    {pubZ : ∀ GB GS GA, (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
      reps tol (concreteEnc _root_.MLDSA.mldsa44)).Stmt → PubZ}
    {sim : ∀ GB GS GA H, CausalJointSimulator (Rv GB GS GA H).MV PubZ} {δ : NNReal}
    (hz : ∀ GB GS GA H, CausalHVZK (Rv GB GS GA H).MV ((pubSigner
      (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc _root_.MLDSA.mldsa44)).rel H)
      (honest GB GS GA H) (pubZ GB GS GA) (sim GB GS GA H) δ)
    {C : ℕ} (hC : ∀ GB GS GA, (A GB GS GA).choices.card ≤ C) :
    𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
          (A GB GS GA).advantage (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) (D GB GS GA) ≤
      2 * (2 * 2 / θ * (n * (11 / 2 ^ 101 * (24 / 5) / βmin.toReal)) +
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * βmin.toReal))) +
        𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
                (M GB GS GA).wiError δ C +
          C / 2 ^ 240 := by
  have h := advantage_le_bkm06_mldsa44 A D hβ0 hβ1 hβt (s := 1 / 2) hθ0 hθ1 (by norm_num)
    (x := 89) (by norm_num) Rv hz hC
  have h2 : (1 - (1 / 2 : ℝ))⁻¹ = 2 := by norm_num
  rw [h2] at h
  have he : (C : ℝ) * checkError reps tol (1 / 2) 89 ≤ C / 2 ^ 240 := by
    rw [hreps, htol]
    exact (mul_le_mul_of_nonneg_left checkError_checkParams_le (Nat.cast_nonneg _)).trans_eq
      (mul_one_div _ _)
  have hm : √(N * n * Real.log (C + 1)) / (2 ^ 2000 * (θ * (1 - θ) * (1 - 1 / 2) * βmin.toReal)) =
      √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * βmin.toReal)) := by
    rw [show (2 : ℝ) ^ 2000 = 2 ^ 1999 * 2 from pow_succ 2 1999]
    generalize (2 : ℝ) ^ 1999 = T
    ring
  rw [hm] at h
  generalize 11 / 2 ^ 101 * (24 / 5) / βmin.toReal = r at h ⊢
  generalize √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * βmin.toReal)) = m at h ⊢
  linarith

end BKM06_mldsa44

section BKM06_mldsa87

variable {Msg : Type} [Fintype Msg] [DecidableEq Msg] {N : ℕ} {βmin : ℝ≥0∞} {reps tol : ℕ}
  {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {n : ℕ}
  {M : ∀ (GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau)
    (GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87)
    (GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l),
    SPBCS Mg P (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
      (concreteEnc mldsa87)).Stmt k kN kS L e}
  (A : ∀ GB GS GA, PubAnonAdversary (pubSigner (withExpandA (oraclePrimitives GB GS) GA)
    (Msg := Msg) N βmin reps tol (concreteEnc mldsa87)) (M GB GS GA) n 1)
  {E : ∀ GB GS GA, (j : ι) → ((M GB GS GA).comp j).Encoder}
  {V : ∀ GB GS GA, GameOrc (concretePrimitivesKeyGen mldsa87) Msg N reps →
    (pubSigner (withExpandA (oraclePrimitives GB GS) GA)
      (Msg := Msg) N βmin reps tol (concreteEnc mldsa87)).Stmt → FullTr P τ → Bool}
  {Qs : ∀ GB GS GA H x, (M GB GS GA).IOPQueries (V GB GS GA H) x} {R : Type} [Fintype R]
  [Nonempty R]
  {honest : ∀ GB GS GA, GameOrc (concretePrimitivesKeyGen mldsa87) Msg N reps →
    (pubSigner (withExpandA (oraclePrimitives GB GS) GA)
      (Msg := Msg) N βmin reps tol (concreteEnc mldsa87)).Wit → R → CausalProver P τ (pubSigner
      (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa87)).Stmt}
  (D : ∀ GB GS GA, (Fin n → _root_.MLDSA.Bytes 32) →
    GameOrc (concretePrimitivesKeyGen mldsa87) Msg N reps →
    (Query k kN kS L → Out k e) → PubHist (BucketVec mldsa87) (M GB GS GA).NIProof 1 → Prop)

open Classical in
/-- **Anonymity at ML-DSA-87** (BKM06 Definition 4, `Q = 1`) in the game with
`SampleInBall`, `ExpandS` and `ExpandA` random oracles: `advantage_le_bkm06` with the regularity
term `2 / ((1 - s) θ) · n · 12 · 2^-294 · (33/5) / β_min` for `β_min ≤ 1`
(`expect_regGapAvg_le_mldsa87`) and the McDiarmid terms at most
`√(N n log (C + 1)) / (2^2000 · θ (1 - θ) (1 - s) β_min)` (`expect_mcDiarmidTerms_le_of`), at
every defect budget `s < 1` and threshold fraction `θ ∈ (0, 1)`. -/
theorem advantage_le_bkm06_mldsa87 (hβ0 : βmin ≠ 0) (hβ1 : βmin ≤ 1) (hβt : βmin ≠ ⊤)
    {s θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs1 : s < 1) {x : ℝ} (hx : 1 ≤ x) [NeZero n]
    (Rv : ∀ GB GS GA H, (M GB GS GA).Reveal (E GB GS GA) (Qs GB GS GA H)) {PubZ : Type}
    {pubZ : ∀ GB GS GA, (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
      reps tol (concreteEnc mldsa87)).Stmt → PubZ}
    {sim : ∀ GB GS GA H, CausalJointSimulator (Rv GB GS GA H).MV PubZ} {δ : NNReal}
    (hz : ∀ GB GS GA H, CausalHVZK (Rv GB GS GA H).MV ((pubSigner
      (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa87)).rel H)
      (honest GB GS GA H) (pubZ GB GS GA) (sim GB GS GA H) δ)
    {C : ℕ} (hC : ∀ GB GS GA, (A GB GS GA).choices.card ≤ C) :
    𝔼 GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l,
          (A GB GS GA).advantage (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) (D GB GS GA) ≤
      2 * (2 * (1 - s)⁻¹ / θ * (n * (12 / 2 ^ 294 * (33 / 5) / βmin.toReal)) +
        √(N * n * Real.log (C + 1)) / (2 ^ 2000 * (θ * (1 - θ) * (1 - s) * βmin.toReal))) +
        𝔼 GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l, (M GB GS GA).wiError δ C +
          C * checkError reps tol s x := by
  have := concreteNTTRingLaws
  have := challengeBall_nonempty floorParams_mldsa87.tau_le
  have hM : 𝔼 GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l,
          𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
            (√(maxDevVar (withExpandA (oraclePrimitives GB GS) GA) (A GB GS GA)
                (SigningParams.of_isApproved
                  isApproved_mldsa87) hβ0 hβt s θ keys * Real.log C / 2) +
              √(maxCountVar (withExpandA (oraclePrimitives GB GS) GA) (A GB GS GA)
                (SigningParams.of_isApproved
                  isApproved_mldsa87) hβ0 hβt s θ keys *
                  Real.log (C + 1) / 2)) ≤
        √(N * n * Real.log (C + 1)) / (2 ^ 2000 * (θ * (1 - θ) * (1 - s) * βmin.toReal)) :=
    (Finset.expect_le_expect fun GB _ => (Finset.expect_le_expect fun GS _ =>
      expect_mcDiarmidTerms_le_of (oraclePrimitives GB GS) (A GB GS)
        (SigningParams.of_isApproved isApproved_mldsa87) hβ0 hβ1 hβt hθ0 hθ1 hs1 C
        commitCollisionBound_le_mldsa87 one_div_sixteen_le_standinScale_mul_card_mldsa87
        two_pow_le_card_bucketVec_mldsa87).trans_eq
      (Finset.expect_const univ_nonempty _)).trans_eq (Finset.expect_const univ_nonempty _)
  refine (advantage_le_bkm06 A D isApproved_mldsa87 hβ0 hβt hθ0 hθ1 hs1 hx Rv hz hC
    (expect_regGapAvg_le_mldsa87 hβ0 hβ1)).trans ?_
  gcongr

open Classical in
/-- **Anonymity at ML-DSA-87 at the check parameters**: `advantage_le_bkm06_mldsa87` with
`reps = 355` samples per member, at most `tol = 2` failed samples per ring and the defect
budget `s = 1/2`, so the mass ratio factor is `1 / (1 - s) = 2`, the McDiarmid terms at most
`√(N n log (C + 1)) / (2^1999 · θ (1 - θ) β_min)` and the check term at `x = 89`
`C · 89² · exp(-(88/89) · 177.5) ≤ C · 2^-240` (`checkError_checkParams_le`). At `β_min = 1/2` the
regularity term is `2 · 2/θ · n · 12 · 2^-294 · (33/5) · 2`. -/
theorem advantage_le_bkm06_mldsa87_checkParams (hβ0 : βmin ≠ 0) (hβ1 : βmin ≤ 1)
    (hβt : βmin ≠ ⊤)
    (hreps : reps = 355) (htol : tol = 2) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) [NeZero n]
    (Rv : ∀ GB GS GA H, (M GB GS GA).Reveal (E GB GS GA) (Qs GB GS GA H)) {PubZ : Type}
    {pubZ : ∀ GB GS GA, (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
      reps tol (concreteEnc mldsa87)).Stmt → PubZ}
    {sim : ∀ GB GS GA H, CausalJointSimulator (Rv GB GS GA H).MV PubZ} {δ : NNReal}
    (hz : ∀ GB GS GA H, CausalHVZK (Rv GB GS GA H).MV ((pubSigner
      (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa87)).rel H)
      (honest GB GS GA H) (pubZ GB GS GA) (sim GB GS GA H) δ)
    {C : ℕ} (hC : ∀ GB GS GA, (A GB GS GA).choices.card ≤ C) :
    𝔼 GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l,
          (A GB GS GA).advantage (E GB GS GA) (Qs GB GS GA) (honest GB GS GA) (D GB GS GA) ≤
      2 * (2 * 2 / θ * (n * (12 / 2 ^ 294 * (33 / 5) / βmin.toReal)) +
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * βmin.toReal))) +
        𝔼 GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l, (M GB GS GA).wiError δ C +
          C / 2 ^ 240 := by
  have h := advantage_le_bkm06_mldsa87 A D hβ0 hβ1 hβt (s := 1 / 2) hθ0 hθ1 (by norm_num)
    (x := 89) (by norm_num) Rv hz hC
  have h2 : (1 - (1 / 2 : ℝ))⁻¹ = 2 := by norm_num
  rw [h2] at h
  have he : (C : ℝ) * checkError reps tol (1 / 2) 89 ≤ C / 2 ^ 240 := by
    rw [hreps, htol]
    exact (mul_le_mul_of_nonneg_left checkError_checkParams_le (Nat.cast_nonneg _)).trans_eq
      (mul_one_div _ _)
  have hm : √(N * n * Real.log (C + 1)) / (2 ^ 2000 * (θ * (1 - θ) * (1 - 1 / 2) * βmin.toReal)) =
      √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * βmin.toReal)) := by
    rw [show (2 : ℝ) ^ 2000 = 2 ^ 1999 * 2 from pow_succ 2 1999]
    generalize (2 : ℝ) ^ 1999 = T
    ring
  rw [hm] at h
  generalize 12 / 2 ^ 294 * (33 / 5) / βmin.toReal = r at h ⊢
  generalize √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * βmin.toReal)) = m at h ⊢
  linarith

end BKM06_mldsa87

end GordieHowe.Ring.MLDSAW1
