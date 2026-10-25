# An ML-DSA ring signature that publishes `w1`

This directory holds a ring signature over unmodified FIPS 204 ML-DSA in which the signer
publishes its commitment `w1`, with a Lean proof of anonymity at ML-DSA-44, ML-DSA-65 and
ML-DSA-87. The lemmas about ML-DSA itself that the proof uses (the signer, regularity, weights) are
under `Applications/MLDSA/`. Paths below are relative to `formal/GordieHowe/`.

Publishing `w1` lets the verifier compute every member's challenge
`c_j = SampleInBall(H(µ_j ‖ w1Encode(w1)))` itself, so the statement proved in zero knowledge
needs no hash evaluation. Published naively, `w1` reveals the signer (the leak behind
[`analysis/nowhereman/`](../../../../../analysis/nowhereman/README.md)). The construction below
removes the leak by rejection sampling, and the proof bounds what remains.

## The result

For every adversary in BKM06 Definition 4 (anonymity against full key exposure; Bender, Katz and
Morselli, ePrint 2005/304, p. 5), in the random-oracle model with `H`, `ExpandA`, `ExpandS` and
`SampleInBall` random oracles, the advantage is at most

```
2 · (8/θ · n · R · C / β_min + McD) + wiError + C_ch / 2^240
```

with `n` honest users, cut-off `β_min`, threshold fraction `θ`, and `C_ch` the number of challenges
the adversary may choose from. The terms:

| Term | ML-DSA-44 | ML-DSA-65 | ML-DSA-87 |
|---|---|---|---|
| Regularity `R` | 11·2^−101 | 11·2^−199 | 12·2^−294 |
| Weight factor `C` | 24/5 | 9/2 | 33/5 |
| Regularity term at `n = 1024`, `θ = β_min = 1/2` | 2^−80.27 | 2^−178.37 | 2^−272.69 |

- `McD ≤ √(N·n·log(C_ch + 1)) / (2^1999 · θ(1 − θ) · β_min)`, with `N` the largest ring size
  (negligible at any feasible `N`, `n`, `C_ch`);
- `wiError` is the witness-indistinguishability error of the proof system for the ring relation,
  left as a parameter;
- `C_ch / 2^240` is the chance that some challenge ring with too many low-weight members passes the
  signer's public check.

The bound is statistical. No computational assumption enters except through `wiError`. The size of
the ring enters only through `McD`. The theorems are
`advantage_le_bkm06_mldsa{44,65,87}_checkParams` in `Applications/Ring/PublicW1/MLDSAPublicW1Regularity.lean`.

## The construction

**Keys.** Ordinary ML-DSA key pairs. Each member publishes `t0` next to its public key `(ρ, t1)`.
FIPS 204 §6.1 notes that `t0` need not be secret.

**Signing** by the member at position `i` of ring `R` on message `m`, with `µ_j = H(tr_j ‖ m)`:

1. **Ring check.** For each member `j` and `r < 355`, derive `c̃ = G(R, j, r)` from a separate
   random oracle `G`, and compute the *check weight* of `t0_j` at `c̃`: zero if
   `‖SampleInBall(c̃)·t0_j‖∞ ≥ γ2`, and otherwise `Pr[Σ_i Bernoulli(p_i) ≤ ω]` with
   `p_i = max(0, |b_i| − β)/(2(γ2 − β) − 1)`, `b = SampleInBall(c̃)·t0_j`. If more than 2 of the
   `355·|R|` check weights are below `β_min = 1/2`, or two members share `tr`, output `⊥`.
2. **Attempt.** Call `ML-DSA.Sign(sk_i, m)` (hedged), and recompute its commitment `w1` from the
   signature as the verifier does.
3. **Flattening.** For every member `j`, let `c̃_j = H(µ_j ‖ w1Encode(w1))` and
   `aw_j = aw(t0_j, w1, c̃_j)`, the probability that the ct₀ and hint-count checks of FIPS 204
   Algorithm 7 pass at challenge `SampleInBall(c̃_j)` when the low bits of `w` are uniform in
   `w1`'s buckets (a Poisson-binomial CDF, computed by dynamic programming). Keep the signature with
   probability

   ```
   min(1, β_min / aw_i) · ∏_{j ≠ i} min(1, aw_j / β_min).
   ```

   Otherwise go back to step 2.
4. **Output** `w1` and a zero-knowledge proof (spBCS, the GordieHowe proof system) of "for some
   position `i`, the signature verifies under `pk_i` with commitment `w1`", with witness
   `(i, signature)`.

**Verification** checks the proof against `(R, m, w1)`.

The signer uses `ML-DSA.Sign` as a black box. Its cost per signature is about `1/β_min = 2` calls to
`ML-DSA.Sign` (for honest rings every `aw_j` is above `β_min`, so only the first factor of the coin
is below one), one Poisson-binomial evaluation per member per call, and the ring check, which is
`355` evaluations per member, done once per ring. We estimate the ring check at about 20 s of one
core for a 1024-member ring at ML-DSA-65, from the 0.06 ms per evaluation measured in the Nowhere
Man analysis; no implementation exists.

Honest rings are almost never refused. At ML-DSA-65 and ML-DSA-87 the ct₀ check cannot fail for an
honest `t0` (`τ·4096 < γ2`). Every honest check weight measured at ML-DSA-65 was at least 0.938, and
we estimate a sample below `β_min` at about 10^−23 by extrapolating the measured tail. At ML-DSA-44
a sample fails for an honest `t0` with probability about 7·10^−9 (the exact 39-fold convolution of
the ct₀ tail), so a 1024-member ring, which may lose two samples, is refused with probability about
3·10^−9.

## Why it works

### Flattening makes the kept law symmetric

Fix the ring and the oracle. Write `(v, c̃)` for a bucket vector `w1` and a commitment hash. If the
signer's accepted mass were exactly `K · aw_i(v, c̃_i)` for a constant `K`, the kept mass would be

```
K · aw_i · min(1, β_min/aw_i) · ∏_{j≠i} min(1, aw_j/β_min) = K · β_min · ∏_j min(1, aw_j/β_min)
```

(`mul_flattenCoin_eq`), the same for every signer `i`. So the law of the published `w1` would not
depend on `i`. The real accepted mass differs from `K·aw_i` in two ways, and the proof bounds both:

- **`y` is uniform on the mask box, not `w` uniform in the bucket.** `w = A·y` with `y` uniform on a
  box. The accepted mass of `(v, c̃)` is `Pr_y[HighBits(A·y) = v, all four checks pass]`. Its
  stand-in replaces `A·y` by a uniform `w`, scaled by the z-check's acceptance fraction `ρ_z`. The
  *regularity gap* `ringRegGap` is the column-wise ℓ1 distance between the two, relative to the
  signer's mean member weight.
- **The loop is random.** Each attempt reads fresh oracle values. The two signers' loops are
  compared attempt by attempt: the distance between the loops' outputs is at most the normalized
  deviation of one attempt's kept mass from the symmetric mass, plus the chance that the ring's
  total weight falls below a fraction `θ` of its mean (`RingPair.tvDist_untilSome_le`). Both
  quantities concentrate over the oracle `H` by McDiarmid's inequality, because each oracle point
  changes one column. Their variance proxies are of order `1/|V|`, where `|V| = 16^1536` at
  ML-DSA-65. The bound uses the collision probability of `HighBits(A·y)` under a uniform matrix
  (`expect_commitCollision_le`, at most 2^−4352), which gives `McD`.

### Regularity: `A·y` looks uniform to the checks

`ExpandA` is a random oracle, so `A` is uniform. For a fixed challenge, the accept indicator of
bucket vector `v` is a product over the coefficients of `w = A·y` of cell functions: the bucket,
the r0 check, and the hint probability. A finite combination of such products expresses it. The
deviation between masks `y` and uniform `w` is then a Fourier sum over the nonzero modes of
`Z_q^{256k}`, and its square summed over `v` is a sum of pair kernels. Averaging over `A` kills
every pair of modes except those the masks `y, y′` can align, leaving a second moment of the cell
kernels over the box (`ZMod.sum_sum_norm_le` and its ℓ² form,
`Foundations/ToMathlib/CharacterSecondMoment.lean`; `Regularity/RqRegularity.lean`). That second
moment is bounded per NTT slot by:
- exact box counts;
- bounds for modes supported on up to seven slots;
- a hybrid term for larger supports.

The bounds are at most `2^−202`, `2^−398` and `2^−588` at ML-DSA-44, 65 and 87
(`Regularity/InstancesSeven.lean`). Their square roots, with the expansion's constants, give `R`: a
bound on `√(𝔼_A (Σ_v 𝔼_c̃ |real − stand-in|)²)` relative to the stand-in scale, for every key.

### The weight: dividing by a mean that can be small

The regularity gap is relative to the signer's mean member weight `𝔼_c̃ min(1, aw/β_min)`, and for
rare keys that mean is small. The proof does not assume a lower bound on it. Cauchy–Schwarz over the
matrix gives

```
𝔼_A ringRegGap ≤ R/β_min · √(𝔼_A w⁻²)
```

for any lower bound `w` on the mean member weight (`expect_ringRegGap_le_sqrt`). It remains to show
that `𝔼 w⁻²` is a small constant, averaged over keys, matrices and the `SampleInBall` oracle. The
weight factor is `C = √(𝔼 w⁻²)`.

- **The law of `t0` under a uniform matrix.** `t = A·s1 + s2`. Off the NTT slots where every
  component of `s1` vanishes, `t` is uniform. A Vandermonde argument shows that the top
  `256 − d` coefficients of every component of `t` are uniform and independent, where `d` is the
  number of such slots (`expect_topCoeffs`, `Regularity/T0Law.lean`). With `ExpandS` a random oracle,
  `Pr[d ≥ d0] ≤ C(256, d0)·9^{−ℓ d0}` (`expect_le_card_secretZeroSlots_le`). This gives
  moment-generating-function bounds on `‖t0‖₂²`, and with them layered Chernoff tails.
- **ML-DSA-65 and ML-DSA-87.** Two floors bound the weight:
  - the Markov bound `aw ≥ 1 − Σ p_i/(ω + 1)`;
  - the product bound `aw ≥ ∏(1 − p_i) ≥ exp(−Σ p_i − κ Σ p_i²)`.

  `Σ p_i` is bounded by `𝔼|b|`. For `b`, a sum of `τ` signed coefficients of `t0`, the bound uses
  the majorant `|x| ≤ A + B x² − C cos(t x)` (`sum_expect_challengeBall_abs_centeredCoeffs_le`),
  which is 25% sharper than `√𝔼 b²`. The ct₀ check never fails there.
- **ML-DSA-44.** The floors above lose about 80 bits, for two reasons:
  - the expected hint count, about 63, is close to `ω = 80`;
  - the ct₀ check can fail, since `τ·4096 > γ2`.

  The proof replaces them with:
  - **Four lines under the Poisson-binomial CDF.** The CDF is affine in each `p_i`, so a line
    `α − σ Σ p_i` lies below it on the box `[0, 21/25]^ι` once it lies below the binomial CDF at
    every vertex count `N` (`sub_sum_le_poissonBinomialCdf`). Each line is certified by finitely
    many exact rational checks (`Regularity/WeightLines44.lean`).
  - **Bounds on ct₀ failure.**
    - Given the support of the challenge, the signs are independent. A cosh chord and Maclaurin's
      inequality then bound the failure probability by 3/4000 for typical keys.
    - For every `t0` with `‖t0‖∞ ≤ 4096`, a convex-comparison argument bounds it by 217/625
      (`Regularity/Ct0Tail44.lean`).
  - **A layered average over keys,** by the largest component norm (`Regularity/WeightTail44.lean`).

  The result is `𝔼 w⁻² ≤ 22.87`, so `C = 24/5`.

### Other members' keys are adversarial

The keys of the other ring members are arbitrary, including their published `t0`. They enter only
through the product `∏_j min(1, aw_j/β_min)`. A ring whose members' weights often fall below
`β_min` would make the symmetric mass small and the normalized errors large. The ring check rules
this out:
- If every member's probability of a check weight below `β_min` sums to at most `s = 1/2`, then
  every column mass is in `[1 − s, 1]` (`RingWeights.massRatio_le_inv_one_sub`), which costs the
  factor 2 in the bound.
- A ring above that passes the 355-sample check with at most 2 failures with probability at most
  `89² · exp(−(88/89)·177.5) ≤ 2^−240` over the check oracle (a Chernoff lower tail,
  `expect_ringCheck_le`).
- A union over the adversary's possible challenges gives `C_ch / 2^240`.

The refusal depends only on the ring and the oracle, so it is the same for both challenge users.

### The game and the proof

The game is BKM06 Definition 4 with the keys given at the start (`PubAnonAdversary`,
`Applications/Ring/PublicW1/PublicValue.lean`):
- The adversary receives every honest user's key-generation coins, both oracles, and the oracle
  of the proof system.
- It chooses any ring holding the two challenge users' keys, adaptively, and sees `⊥` when the
  signer refuses.

Each round is handled by a coupling: when the two users' public values `w1` agree, the statements
proved agree, and witness indistinguishability of the compiled proof hides the witness. Otherwise
the round counts as bad, with probability at most the distance between the two `w1` laws. The
general theorem (`PubAnonAdversary.advantage_le`) handles `Q` adaptive rounds at cost
`(Q + 1)·(regularity + McD) + Q·wiError`. The headlines state `Q = 1`. Under full key exposure
signing queries add nothing, because the adversary holds every honest user's coins.

## Lean statements

| Claim | Theorem | File |
|---|---|---|
| The game, BKM06 Definition 4 with refusals | `PubAnonAdversary`, `PubAnonAdversary.game`, `PubAnonAdversary.advantage_le` | `Applications/Ring/PublicW1/PublicValue.lean` |
| The signer and the flattening identity | `ringLoopSigner`, `memberWeight`, `mul_flattenCoin_eq` | `Applications/MLDSA/Signing/RingSigner.lean` |
| Correctness on accepted rings | `valid_of_mem_support_signLaw`, `ringVerify_attemptOutput` | `Applications/Ring/PublicW1/MLDSAPublicW1.lean`, `RingSigner.lean` |
| The ring check and its error | `RingCheck`, `checkWeight`, `expect_ringCheck_le`, `checkError_checkParams_le` | `Applications/Ring/PublicW1/MLDSAPublicW1.lean`, `MLDSAPublicW1Regularity.lean` |
| Two loops, adversarial members | `RingPair.tvDist_untilSome_le`, `familyBound`, `RingWeights.massRatio_le_inv_one_sub` | `Foundations/ToMathlib/PMFOracleQuenched.lean` |
| McDiarmid terms | `expect_mcDiarmidTerms_le_of`, `expect_commitCollision_le` | `Applications/Ring/PublicW1/MLDSAPublicW1Concentration.lean`, `Applications/MLDSA/Regularity/CommitCollision.lean` |
| Regularity | `expect_ringRegGap_le_sqrt_mldsa{65,87}_seven`, `expect_ringRegGap_le_sqrt_mldsa44_box_seven_of_nonneg` | `Applications/MLDSA/Regularity/InstancesSeven.lean` |
| Cauchy–Schwarz over the matrix | `expect_ringRegGap_le_sqrt`, `expect_ringRegGap_le_sqrt_of_nonneg` | `Applications/MLDSA/Regularity/SignerRegularity.lean` |
| Law of `t0` under a uniform matrix | `expect_topCoeffs`, `expect_exp_t0SqNorm_le`, `expect_le_card_secretZeroSlots_le` | `Applications/MLDSA/Regularity/T0Law.lean` |
| Weight factor at ML-DSA-65/87 | `expect_expect_floorInvSqBound_le_mldsa65`, `…_mldsa87` | `Applications/MLDSA/Regularity/WeightTail.lean` |
| Weight factor at ML-DSA-44 | `sub_sum_le_poissonBinomialCdf`, `one_sub_le_expect_challengeBall_ct0_mldsa44`, `expect_expect_expect_inv_sq_mldsa44OracleWeight_le` | `Applications/MLDSA/Signing/Flatten.lean`, `Regularity/Ct0Tail44.lean`, `Regularity/WeightTail44.lean` |
| Headlines | `advantage_le_bkm06_mldsa{44,65,87}`, `…_checkParams`, `expect_regGapAvg_le_mldsa{44,65,87}` | `Applications/Ring/PublicW1/MLDSAPublicW1Regularity.lean` |

## What is not shown

- **Unforgeability is not instantiated.** `Ring/Unforgeability.lean` reduces the ring games of
  `Ring/Games.lean` to multi-user unforgeability of the base scheme by straight-line extraction. The
  public-`w1` signer is not connected to it.
- **`wiError` is a parameter.** Instantiating it needs the public-`w1` ring circuit and its
  zero-knowledge proof, which do not exist yet.
- **`t0` is not bound to the key.** An adversary may publish a false `t0` under an honest member's
  `(ρ, t1)`. Members could self-certify `(ρ, t1, t0)`; this is not formalized.
- **The model:**
  - It is the classical random-oracle model, with `SampleInBall`, `ExpandA` and `ExpandS` as random
    oracles onto their ranges.
  - The signer is the idealized FIPS 204 signer (`Signing/Ideal.lean`: `y` uniform on the mask box,
    the commitment hash from the oracle), not a byte-level implementation.
  - Efficiency is not formalized.
- **No implementation or measurements.** The signing cost above is an estimate.

The parent directory `Applications/Ring/` holds a generic ring signature over any base scheme,
with its anonymity (`Anonymity.lean`), unforgeability (`Unforgeability.lean`) and games
(`Games.lean`, `Scheme.lean`).
