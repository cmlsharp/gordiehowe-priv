-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import LatticeCrypto.MLDSA.Scheme
public import GordieHowe.Foundations.ToMathlib.ExchangeableDistinguisher
public import Mathlib.Probability.Distributions.Uniform
public import GordieHowe.Foundations.ToMathlib.FintypeBytes

@[expose] public section

/-!
# The decision MLWE advantage

The decision Module-LWE problem as stated by Barbosa, Barthe, Doczkal, Don, Fehr, Grégoire,
Huang, Hülsing, Lee and Wu, *Fixing and Mechanizing the Security Proof of Fiat-Shamir with Aborts
and Dilithium* (CRYPTO 2023, ePrint 2023/246), Section 6.2, Definition 3 ("MLWE Assumption"): the
advantage of an algorithm `A` for the decisional `MLWE_{m,k,D}` problem over `R_q` is
`|Pr[A(A, t) = 1 | A ← R_q^{m×k}, t ← R_q^m] − Pr[A(A, A·s₁ + s₂) = 1 | A ← R_q^{m×k},
s₁ ← D^k, s₂ ← D^m]|`.

This file states it with three generalizations, none of which changes the special case:

* the algorithm is a test `f : T_q^{k×l} → R_q^k → ℝ`, its probability of outputting `1` on
  each input; the advantage is the absolute value of the difference of the means of `f`;
* the secret `(s₁, s₂)` has an arbitrary law `S` on `R_q^l × R_q^k`; Dilithium's `D^l × D^k` is
  one choice, and the ML-DSA instance is the law of `ExpandS` on the key-generation seed;
* the matrix is sampled in the NTT domain `T_q^{k×l}`, as FIPS 204 `ExpandA` (Algorithm 32)
  outputs it, and `A·s₁` is the vendored `Â ∘ NTT(s₁)` product used by key generation
  (`keyGenFromSeed`).

* `mlweRealMean`, `mlweUniformMean`, `mlweAdvantage`: the two means and the advantage.
* `abs_mlweRealMean_sub_mlweUniformMean_le`: for every test, the means differ by at most its
  advantage (the reduction step of a hybrid argument).
* `mlweUniformMean_of_vector`: a test that reads only `t` has its uniform mean over the uniform
  `t` alone.
-/

namespace GordieHowe.MLDSA

open _root_.MLDSA LatticeCrypto TransformOps

variable {k l : ℕ}

/-- **The uniform MLWE mean** of a test `f`: `𝔼[f(Â, t)]` for `Â` uniform on `T_q^{k×l}` and `t`
uniform on `R_q^k`, independent. -/
noncomputable def mlweUniformMean (f : TqMatrix k l → RqVec k → ℝ) : ℝ :=
  ∑ A : TqMatrix k l, ∑ t : RqVec k,
    (PMF.uniformOfFintype (TqMatrix k l) A).toReal * (PMF.uniformOfFintype (RqVec k) t).toReal *
      f A t

/-- A test that reads only `t` has uniform mean `𝔼_{t uniform} g(t)`. -/
theorem mlweUniformMean_of_vector (g : RqVec k → ℝ) :
    mlweUniformMean (l := l) (fun _ t => g t) =
      ∑ t : RqVec k, (PMF.uniformOfFintype (RqVec k) t).toReal * g t := by
  simp only [mlweUniformMean, mul_assoc, ← Finset.mul_sum]
  rw [← Finset.sum_mul, PMF.sum_toReal_eq_one, one_mul]

variable [nttOps : NTTRingOps]

/-- **The real MLWE mean** of a test `f`: `𝔼[f(Â, Â·s₁ + s₂)]` for `Â` uniform on `T_q^{k×l}` and
`(s₁, s₂) ← S`, independent. -/
noncomputable def mlweRealMean (S : PMF (RqVec l × RqVec k))
    (f : TqMatrix k l → RqVec k → ℝ) : ℝ :=
  ∑ A : TqMatrix k l, ∑ s : RqVec l × RqVec k,
    (PMF.uniformOfFintype (TqMatrix k l) A).toReal * (S s).toReal * f A (A * s.1 + s.2)

/-- **The decision MLWE advantage** of a test `f` against secrets with law `S` (Barbosa et al.,
CRYPTO 2023, Definition 3): `|𝔼_uniform f − 𝔼_real f|`. -/
noncomputable def mlweAdvantage (S : PMF (RqVec l × RqVec k))
    (f : TqMatrix k l → RqVec k → ℝ) : ℝ :=
  |mlweUniformMean f - mlweRealMean S f|

/-- **The MLWE hop**: for every test `f`, its real and uniform means differ by at most its MLWE
advantage. -/
theorem abs_mlweRealMean_sub_mlweUniformMean_le (S : PMF (RqVec l × RqVec k))
    (f : TqMatrix k l → RqVec k → ℝ) :
    |mlweRealMean S f - mlweUniformMean f| ≤ mlweAdvantage S f := by
  rw [mlweAdvantage, abs_sub_comm]

end GordieHowe.MLDSA
