-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Signing.Ideal
public import GordieHowe.Applications.MLDSA.Signing.RingSigner
public import GordieHowe.Applications.MLDSA.Spec.ExpandS
public import GordieHowe.Foundations.ToMathlib.ExchangeableDistinguisher

@[expose] public section

/-!
# The challenge hash of an ML-DSA presentation separates every key-independent simulator

**Setting.** In the Nowhere Man / FHLL unlinkability games (ePrint 2026/2472, Fig. 3 and
Definition 8; ePrint 2025/1995, Fig. 2) the adversary chooses the device key-generation coins, so
it knows the device key, in particular `t₀`, and the simulator never sees the key. A real
presentation reveals `(µ, w1)`, from which anyone recomputes the signature's commitment hash
`c̃ = H(µ ‖ w1Encode(w1))`.

**What is formalized** (the commitment-hash layer of the game). The device key is
`keyGenFromSeed` at `concretePrimitivesKeyGen p` (FIPS 204 Algorithm 6 with the FIPS 204 ExpandS)
from a uniform 32-byte seed. A real presentation's `c̃` follows `acceptedChallengeLaw seed`: the
accepted commitment hash of the idealized FIPS 204 signer (`Signing/Ideal.lean`, density
proportional to `acceptProbAt`, `acceptedChallengeLaw_apply`). A simulated presentation's `c̃`
follows some law `Q` that does not depend on the key. The distinguisher draws an independent
second seed and runs `PMF.exchangeableOutput` with the exact per-challenge acceptance weight
`acceptanceScore seed c̃ = Pr_{y ← MaskBox}[signAccept y c̃]` as score, which it can evaluate since
it knows the key. That weight is a finite sum over the mask box, exponential in size; the
polynomial-size stand-in weight (`acceptWeight`, `Signing/Surrogate.lean`) is a function of `w1`
and `c̃` together and is not the score used here.

* `challengeAdvantage_standin_eq` (**the efficient distinguisher**): the observation is the pair
  `(w1, c̃)` a presentation reveals; its real law is the accepted `(HighBits(Â·y), c̃)` of the
  idealized signer (`acceptedCommitLaw`; on acceptance `HighBits(Â·y - c·s₂) = HighBits(Â·y)`,
  `highBitsVec_sub_eq_of_isSome`), the simulated law is any key-independent `Q` on pairs, and the
  score is the stand-in weight `standinScore` (`acceptWeight` of `SampleInBall(c̃)·t₀` at the
  buckets `w1`, the real part of `t0Weight`), computable by a polynomial-size dynamic program
  over the Poisson-binomial count of hints. The advantage is `standinGap p / 2` for every `Q`.
  The positivity and size of `standinGap` are measured (the OpenSSL experiment used this kind of
  score), not proved.
* `challengeAdvantage_eq` (information-theoretic, observation `c̃` alone, exact exponential-size
  score): for every `Q`, the advantage is `challengeGap p / 2`.
* `normalizedChallengeAdvantage_eq`: with the normalized score
  `α/ᾱ = |C| · P_seed` (`uniformDensity_acceptedChallengeLaw`) scaled by any `B > 0`, the
  advantage is `normalizedChallengeGap p / (2B)`; `normalizedChallengeGap_eq` writes the gap as
  half the expected squared `L²(U)` distance between two independent keys' challenge laws,
  `normalizedChallengeGap_nonneg`, and `normalizedChallengeGap_pos_iff`: it is positive exactly
  when two seeds give different accepted-challenge laws.

**What is not formalized.** The DBAC wrapper: commitments, the NIZKs, the issuer, and the fact
that ShowVf2 recomputes exactly the signature's `c̃` (checked on 5.2·10⁸ signatures by our
OpenSSL pipeline, outside Lean). The numerical value of the gaps: the normalized `χ²` quantities
were measured at about `7·10⁻⁵` (ML-DSA-44) and `2.5·10⁻⁶` (ML-DSA-65), outside Lean; this file
proves no positive lower bound and no nonvanishing of the gap for the concrete parameters. Only
one presentation is treated; nothing is stated for several presentations under the same key.
-/

namespace GordieHowe.MLDSA

open _root_.MLDSA LatticeCrypto TransformOps
open scoped ENNReal

section Challenge

variable (p : Params) [nttOps : NTTRingOps] [Nonempty (MaskBox p)]

/-- The device secret key generated from `seed`: FIPS 204 ML-DSA.KeyGen_internal (Algorithm 6)
at `Spec.concretePrimitivesKeyGen p`. -/
def deviceKey (seed : Bytes 32) : SecretKey p :=
  (keyGenFromSeed p (Spec.concretePrimitivesKeyGen p) seed).2

/-- The expanded matrix `Â = ExpandA(ρ)` of the device key generated from `seed`. -/
def deviceMatrix (seed : Bytes 32) : TqMatrix p.k p.l :=
  (Spec.concretePrimitivesKeyGen p).expandA (deviceKey p seed).rho

/-- **The per-challenge acceptance weight** `α_seed(c̃) = Pr_{y ← MaskBox}[signAccept y c̃]` of
the idealized signer under the device key generated from `seed`. -/
noncomputable def acceptanceScore (seed : Bytes 32) (cTilde : CommitHashBytes p) : ℝ :=
  (PMF.acceptProbAt (maskUniform p)
    (attemptAccept (Spec.concretePrimitivesKeyGen p) (deviceKey p seed) (deviceMatrix p seed))
    cTilde).toReal

/-- The acceptance probability `ᾱ_seed` of one idealized attempt under the device key. -/
noncomputable def deviceAcceptProb (seed : Bytes 32) : ℝ≥0∞ :=
  PMF.acceptProb (maskUniform p)
    (attemptAccept (Spec.concretePrimitivesKeyGen p) (deviceKey p seed) (deviceMatrix p seed))

/-- **The accepted commitment-hash law** of the idealized FIPS 204 signer under the device key
generated from `seed`: the `c̃` of the first accepted attempt. If the attempt never accepts
(`deviceAcceptProb = 0`) the signer outputs nothing, and this definition falls back to the
uniform law. -/
noncomputable def acceptedChallengeLaw (seed : Bytes 32) : PMF (CommitHashBytes p) :=
  if h : deviceAcceptProb p seed = 0 then PMF.uniformOfFintype (CommitHashBytes p) else
    (PMF.condSome (PMF.rejectionAttempt (maskUniform p)
        (attemptAccept (Spec.concretePrimitivesKeyGen p) (deviceKey p seed) (deviceMatrix p seed)))
      (PMF.rejectionAttempt_apply_none_ne_one h)).map Prod.snd

/-- The accepted law has density `α_seed(c̃) · |C|⁻¹ / ᾱ_seed` when `ᾱ_seed ≠ 0`. -/
theorem acceptedChallengeLaw_apply {seed : Bytes 32} (h : deviceAcceptProb p seed ≠ 0)
    (cTilde : CommitHashBytes p) :
    acceptedChallengeLaw p seed cTilde =
      PMF.acceptProbAt (maskUniform p)
          (attemptAccept (Spec.concretePrimitivesKeyGen p) (deviceKey p seed)
            (deviceMatrix p seed)) cTilde *
        (Fintype.card (CommitHashBytes p) : ℝ≥0∞)⁻¹ / deviceAcceptProb p seed := by
  simp only [acceptedChallengeLaw, h, ↓reduceDIte]
  exact acceptedChallenge_apply _ _ _ h cTilde

/-- The key law: device keys from a uniform 32-byte seed. -/
noncomputable def seedLaw : PMF (Bytes 32) := PMF.uniformOfFintype (Bytes 32)

/-- **The challenge gap** `E_{k,k'} E_{c̃ ← P_k} (α_k(c̃) - α_{k'}(c̃))` for two independent
uniform seeds, with `P_k = acceptedChallengeLaw` and `α = acceptanceScore`. -/
noncomputable def challengeGap : ℝ :=
  PMF.scoreGap (seedLaw) (acceptedChallengeLaw p) (acceptanceScore p)

/-- **The normalized challenge gap**: `challengeGap` with the score `|C| · P_k = α_k/ᾱ_k`. -/
noncomputable def normalizedChallengeGap : ℝ :=
  PMF.scoreGap (seedLaw) (acceptedChallengeLaw p)
    (PMF.uniformDensity (acceptedChallengeLaw p))

/-- The acceptance weight is a probability. -/
theorem acceptanceScore_mem_Icc (seed : Bytes 32) (cTilde : CommitHashBytes p) :
    acceptanceScore p seed cTilde ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  have hle : PMF.acceptProbAt (maskUniform p)
      (attemptAccept (Spec.concretePrimitivesKeyGen p) (deviceKey p seed) (deviceMatrix p seed))
      cTilde ≤ 1 := by
    rw [PMF.acceptProbAt]
    calc _ ≤ ∑ y, maskUniform p y :=
          Finset.sum_le_sum fun y _ => by split_ifs <;> simp
      _ = 1 := by
          have h := (maskUniform p).tsum_coe
          rwa [tsum_fintype] at h
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hle)

/-- The normalized score is `α_seed / ᾱ_seed` when `ᾱ_seed ≠ 0`. -/
theorem uniformDensity_acceptedChallengeLaw {seed : Bytes 32} (h : deviceAcceptProb p seed ≠ 0)
    (cTilde : CommitHashBytes p) :
    PMF.uniformDensity (acceptedChallengeLaw p) seed cTilde =
      acceptanceScore p seed cTilde / (deviceAcceptProb p seed).toReal := by
  have hN : (Fintype.card (CommitHashBytes p) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [PMF.uniformDensity, acceptedChallengeLaw_apply p h, ENNReal.toReal_div,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, acceptanceScore]
  field_simp

/-- **Any simulator is separated**: for every key-independent law `Q` of the simulated `c̃`, the
distinguisher with score `acceptanceScore` (outputs in `[0, 1]`, `B = 1`) outputs `1` with
probability `1/2` on simulated presentations and `1/2 + challengeGap p / 2` on real ones, so its
advantage is `challengeGap p / 2`. -/
theorem challengeAdvantage_eq (Q : PMF (CommitHashBytes p)) :
    PMF.exchangeableAcceptProb (seedLaw) (fun k _ => acceptedChallengeLaw p k)
        (acceptanceScore p) 1 = 1 / 2 + challengeGap p / 2 ∧
      PMF.exchangeableAcceptProb (seedLaw) (fun _ _ => Q) (acceptanceScore p) 1 = 1 / 2 := by
  refine ⟨?_, PMF.exchangeableAcceptProb_const _ _ _ _⟩
  rw [PMF.exchangeableAcceptProb_real, challengeGap]
  ring

/-- The distinguisher of `challengeAdvantage_eq` outputs a probability. -/
theorem challengeOutput_mem_Icc (k k' : Bytes 32) (cTilde : CommitHashBytes p) :
    PMF.exchangeableOutput (acceptanceScore p) 1 k k' cTilde ∈ Set.Icc (0 : ℝ) 1 :=
  PMF.exchangeableOutput_mem_Icc one_pos (fun k c => acceptanceScore_mem_Icc p k c) k k' cTilde

/-- **Normalized score**: for every key-independent `Q` and every scale `B`, the distinguisher
with score `|C| · P_k = α_k/ᾱ_k` scaled by `B` has advantage `normalizedChallengeGap p / (2B)`.
Its outputs are probabilities when `B` bounds the normalized score (`PMF.exchangeableOutput_mem_Icc`). -/
theorem normalizedChallengeAdvantage_eq (Q : PMF (CommitHashBytes p)) (B : ℝ) :
    PMF.exchangeableAcceptProb (seedLaw) (fun k _ => acceptedChallengeLaw p k)
        (PMF.uniformDensity (acceptedChallengeLaw p)) B -
      PMF.exchangeableAcceptProb (seedLaw) (fun _ _ => Q)
        (PMF.uniformDensity (acceptedChallengeLaw p)) B =
      normalizedChallengeGap p / (2 * B) :=
  PMF.exchangeableAcceptProb_real_sub_const _ _ _ _ _

/-- The normalized challenge gap is half the expected squared `L²(U)` distance between the
accepted-challenge laws of two independent device keys. -/
theorem normalizedChallengeGap_eq :
    normalizedChallengeGap p =
      (1 / 2) * ∑ k, ∑ k', (seedLaw k).toReal * (seedLaw k').toReal *
        ((Fintype.card (CommitHashBytes p) : ℝ)⁻¹ *
          ∑ c, (PMF.uniformDensity (acceptedChallengeLaw p) k c -
            PMF.uniformDensity (acceptedChallengeLaw p) k' c) ^ 2) :=
  PMF.scoreGap_density_eq _ _

/-- The normalized challenge gap is nonnegative. -/
theorem normalizedChallengeGap_nonneg : 0 ≤ normalizedChallengeGap p :=
  PMF.scoreGap_density_nonneg _ _

/-- The normalized challenge gap is positive exactly when two seeds give different
accepted-challenge laws. -/
theorem normalizedChallengeGap_pos_iff :
    0 < normalizedChallengeGap p ↔
      ∃ k k', acceptedChallengeLaw p k ≠ acceptedChallengeLaw p k' := by
  have hpos : ∀ k, seedLaw k ≠ 0 := fun k => by
    rw [seedLaw, PMF.uniformOfFintype_apply]
    exact ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)
  rw [normalizedChallengeGap, PMF.scoreGap_density_pos_iff]
  exact ⟨fun ⟨k, k', _, _, h⟩ => ⟨k, k', h⟩, fun ⟨k, k', h⟩ => ⟨k, k', hpos k, hpos k', h⟩⟩

end Challenge

/-! ### The efficient distinguisher on `(w1, c̃)` -/

section StandIn

variable (p : Params) [NeZero (bucketCount p)] [nttOps : NTTRingOps] [Nonempty (MaskBox p)]

/-- **The accepted commitment law** of the idealized FIPS 204 signer under the device key from
`seed`: the pair `(w1, c̃) = (HighBits(Â·y), c̃)` of the first accepted attempt. If the attempt
never accepts (`deviceAcceptProb = 0`) this definition falls back to the uniform law. -/
noncomputable def acceptedCommitLaw (seed : Bytes 32) : PMF (BucketVec p × CommitHashBytes p) :=
  if h : deviceAcceptProb p seed = 0 then PMF.uniformOfFintype _ else
    (PMF.condSome (PMF.rejectionAttempt (maskUniform p)
        (attemptAccept (Spec.concretePrimitivesKeyGen p) (deviceKey p seed) (deviceMatrix p seed)))
      (PMF.rejectionAttempt_apply_none_ne_one h)).map
      fun yc => (realBuckets (deviceMatrix p seed) yc.1, yc.2)

/-- **The stand-in score** of the device key from `seed` at `(w1, c̃)`: the uniform-`w`
acceptance weight `acceptWeight` of the ct₀ and hint checks with `b = SampleInBall(c̃)·t₀` at
the buckets `w1`; `t0Weight` is its `ENNReal.ofReal`. It is a product of an indicator and a
Poisson-binomial CDF, computable in time polynomial in `256k` and `ω`. -/
noncomputable def standinScore (seed : Bytes 32) (vc : BucketVec p × CommitHashBytes p) : ℝ :=
  acceptWeight p.gamma2 p.beta p.omega
    (centeredCoeffs ((Spec.concretePrimitivesKeyGen p).sampleInBall vc.2 • (deviceKey p seed).t0))
    fun x => (vc.1 x).val

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] in
/-- `t0Weight` of the device key is the stand-in score, as an extended real. -/
theorem t0Weight_deviceKey (seed : Bytes 32) (vc : BucketVec p × CommitHashBytes p) :
    t0Weight (Spec.concretePrimitivesKeyGen p) (deviceKey p seed).t0 vc =
      ENNReal.ofReal (standinScore p seed vc) :=
  rfl

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] in
/-- The stand-in score is in `[0, 1]`. -/
theorem standinScore_mem_Icc (hp : SigningParams p) (seed : Bytes 32)
    (vc : BucketVec p × CommitHashBytes p) : standinScore p seed vc ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨acceptWeight_nonneg hp.beta_lt_gamma2 _ _ _, acceptWeight_le_one hp.beta_lt_gamma2 _ _ _⟩

/-- **The stand-in gap** `E_{k,k'} E_{(w1,c̃) ← P_k} (s_k(w1,c̃) - s_{k'}(w1,c̃))` for two
independent uniform seeds, `P_k = acceptedCommitLaw`, `s = standinScore`. Its positivity and
size are measured outside Lean, not proved. -/
noncomputable def standinGap : ℝ :=
  PMF.scoreGap (seedLaw) (acceptedCommitLaw p) (standinScore p)

/-- **The efficient distinguisher separates every simulator**: for every key-independent law
`Q` of the simulated `(w1, c̃)`, the distinguisher with the stand-in score (`B = 1`) has
advantage `standinGap p / 2`. -/
theorem challengeAdvantage_standin_eq (Q : PMF (BucketVec p × CommitHashBytes p)) :
    PMF.exchangeableAcceptProb (seedLaw) (fun k _ => acceptedCommitLaw p k) (standinScore p) 1 -
      PMF.exchangeableAcceptProb (seedLaw) (fun _ _ => Q) (standinScore p) 1 =
      standinGap p / 2 := by
  rw [PMF.exchangeableAcceptProb_real_sub_const, standinGap]
  ring

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] in
/-- The distinguisher of `challengeAdvantage_standin_eq` outputs a probability. -/
theorem standinOutput_mem_Icc (hp : SigningParams p) (k k' : Bytes 32)
    (vc : BucketVec p × CommitHashBytes p) :
    PMF.exchangeableOutput (standinScore p) 1 k k' vc ∈ Set.Icc (0 : ℝ) 1 :=
  PMF.exchangeableOutput_mem_Icc one_pos (fun k c => standinScore_mem_Icc p hp k c) k k' vc

end StandIn

end GordieHowe.MLDSA
