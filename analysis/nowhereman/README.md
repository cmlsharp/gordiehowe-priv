# Distinguishers against the simulators of Nowhere Man, Theorem 2

This directory contains programs, measurements and pointers to Lean proofs
about the unlinkability claim (Theorem 2) of

> Abou Haidar, Kikuchi, Perez-Kempner, Tiepelt. *Nowhere Man: Device Binding
> for Post-Quantum Anonymous Credentials.* IACR ePrint 2026/2472 (extended
> version).

It gives three results, at the paper's instantiation ML-DSA-65 and at ML-DSA-44
and ML-DSA-87:

1. **The proof's simulator fails.** With the device key generated from the
   all-zero seed, a polynomial-time adversary distinguishes the simulator's
   presentations from real ones with measured advantage 2^−10.68 (z = 8.6) at
   ML-DSA-65, 2^−9.06 (z = 9.2) at ML-DSA-44 and 2^−9.33 (z = 10.8) at
   ML-DSA-87. Theorem 2 bounds this advantage by a sum of terms assumed
   negligible.
2. **Every simulator fails.** In the paper's game (Unlink-1), a
   polynomial-time adversary has the same advantage against every simulator
   that Definition 8 allows, efficient or not. Against real OpenSSL signing
   that advantage is at least 2^−19.94 at ML-DSA-65 and 2^−14.99 at
   ML-DSA-44, with no computational assumption. ML-DSA-87 is not measured
   here. Result 3's adversary is also a legal Unlink-1 adversary, so result 3
   covers ML-DSA-87, under MLWE.
3. **Every simulator fails even in a weaker game,** in which the device key is
   generated honestly and the adversary sees only the public key. There a
   test that reads only `t1` has advantage at least 2^−23.00 (ML-DSA-65),
   2^−20.88 (ML-DSA-44) and 2^−21.83 (ML-DSA-87), measured with `t` uniform.
   Carrying it to real keys costs MLWE advantages and a stand-in error.
   Lean proves the whole step at all three parameter sets. The stand-in error
   is about 2^−56 (ML-DSA-65) and 2^−99 (ML-DSA-87) plus an MLWE term, and
   2^−95 at ML-DSA-44 with no MLWE term (see
   [Why ML-DSA-44 differs](#why-ml-dsa-44-differs)).

The bounds of results 2 and 3 hold with confidence 1 − 2^−40, and all three
results concern one presentation. [Lean statements](#lean-statements) lists
the theorems behind results 2 and 3. Lean paths in this file are relative to
`formal/GordieHowe/`.

## The claim

Definition 8 (Unlink-1, adapted from FHLL25, Def. 4) requires a simulator
`Sim = (Setup, Show)` such that for every PPT adversary `A` the advantage
`|Pr[Unlink-1^{A,b=0} = 1] - Pr[Unlink-1^{A,b=1} = 1]|` is negligible, where
the game is Figure 3:

- line 2: `(st_A, ρ_iss, ρ_se, cred, a) ← A(par)`: the adversary chooses the
  coins of the secure element (SE);
- line 4: `(dsk, dpk) ← DevKGen(par; ρ_se)`;
- line 6: `A` gets oracle `ODoPres(ctx, ϕ)`, which returns `τ_0 ←
  Sim.Show(ipk, ctx, ϕ, L(isk))` if `b = 0` and the honest presentation `τ_1`
  if `b = 1`, and oracle `OShowSE`.

Theorem 2 states

```
Adv^{Unlink-1}_{Π,ℓ,Sim,Q_SE}(A, n) ≤ Adv^{ParInd}_{DB}(B1, n) + Adv^{ParInd}_{CD}(B2, n)
                                     + Adv^{ZK}_{π_DB}(B3, n) + Adv^{ZK}_{π_CD}(B4, n)
                                     + Adv^{wMLWR}(B5).
```

All terms on the right are assumed negligible.

In the construction (Figure 4) the SE signs `M = R ‖ ctx` with
`ML-DSA.Sign(dsk, M, ε)` (`ShowSE1`), and the presentation
`τ = ({C_i}, w1, µ, π_CD, π_DB)` (`ShowUsr2`) contains in the clear
`µ = H(H(dpk, 64) ‖ 0x00 ‖ 0x00 ‖ M, 64)` (`ShowUsr1` lines 6–7) and
`w1 = UseHint(h, A·z − c·t1·2^d)` (`ShowUsr2` lines 5–10). The verifier
computes `c̃′ ← H(µ ‖ w1Encode(w1), λ/4)` and `c′ ← SampleInBall(c̃′)`
(`ShowVf2` line 11).

The simulator in the proof of Theorem 2 outputs
`τ_0 = ({C_i}*, r_w′, r_µ, π*_CD, π*_DB)` with `r_w′ ← HighBits_q(U(R_q^k), 2γ2)`
and `r_µ` uniform in the range of `H`.

## Result 1: the proof's simulator fails

### The distinguisher

For any valid ML-DSA signature `(c̃, z, h)`, FIPS 204 verification
(Algorithm 8) recomputes exactly `c̃ = H(µ ‖ w1Encode(UseHint(h, A·z − c·t1·2^d)))`.
So in a real presentation the verifier's `c̃′` is the challenge hash of the
signature that the SE produced. The FIPS 204 signer (Algorithm 7) draws a
fresh challenge `c` in each attempt and rejects the attempt if
`‖c·t0‖∞ ≥ γ2` or if the hint vector has more than `ω` ones. This is the
second rejection test of Algorithm 7, the `if` after `MakeHint` in the paper's
Figure 5.
Given `c`, the hint count is a sum of nearly independent indicators whose
probabilities grow with `|(c·t0)_i|`, so the acceptance probability
`α_{t0}(c)` of an attempt depends on `c`. The accepted challenge therefore has
density proportional to `α_{t0}(c)` relative to the uniform distribution on
challenges. In a simulated presentation `c̃′ = H(r_µ ‖ w1Encode(r_w′))` is a
fresh random-oracle output, so `c′` is uniform. Figure 7 (`Real`, used in
Game 2 and Lemma 2) checks only `‖z‖∞` and `‖r0‖∞`, whose acceptance
probabilities do not depend on `c` for uniform `y` (because `‖c·s1‖∞ ≤ β`
and `‖c·s2‖∞ ≤ β`), and takes `c` as a fixed input; it omits the `c·t0` and hint-count
checks.

The adversary in Unlink-1 chooses `ρ_se`, hence knows `dsk` and `t0`. Its
distinguisher, given a presentation's `(µ, w1)`:

1. computes `c̃′ = H(µ ‖ w1Encode(w1), λ/4)` and `c = SampleInBall(c̃′)`
   (the verifier's own computation);
2. computes `b = c·t0` over the integers in `Z[X]/(X^256 + 1)`, for each of
   the `k` polynomials;
3. scores `α(c) = 0` if `‖b‖∞ ≥ γ2`, and otherwise
   `α(c) = Pr[Σ_i Bernoulli(p_i) ≤ ω]` with
   `p_i = max(0, |b_i| − β − 1) / (2(γ2 − β) − 1)` (Poisson-binomial
   distribution, computed exactly by dynamic programming over the `256k`
   coordinates). `p_i` is the probability that coordinate `i` needs a hint
   when the low bits of `w − c·s2` are uniform in the accepted range; it is
   exact up to a `±1` count (`bucket_hint_card`,
   `Applications/MLDSA/Signing/Counting.lean`). The score need not be exact,
   because the advantage is measured;
4. outputs "real" iff `α(c) > θ`, where `θ` is the median of `α` over
   2,000,000 uniformly random challenges (`c̃` uniform), computed before the
   test samples are drawn.

The adversary is PPT: per presentation it evaluates two SHAKE256 calls,
`k·τ·256` integer additions for `c·t0`, and a `256k × (ω + 1)` dynamic
program (about 0.06 ms per presentation on one core at ML-DSA-65, from
the calibration timings). The calibration step is
a fixed polynomial amount of work.

**The key.** The adversary chooses `ρ_se`, and it fixes the all-zero seed
`ξ_0 = 0^32`.

In Unlink-1, `ρ_se` are the coins of `DevKGen`; here `DevKGen(par; ρ_se)` is
ML-DSA `KeyGen_internal(ξ)` with `ξ = ρ_se` (OpenSSL key generation from the
32-byte seed). The rest of the game (credential issuance, commitments,
NIZK proofs) does not enter: after Game 1 of the proof the proofs are
simulated and the remaining components are independent of `(µ, w1)`, and the
distinguisher reads only `(µ, w1)`. Each `ODoPres` query returns one
presentation; the experiment estimates the per-query distinguishing
probability, which is the advantage of an adversary that makes one
`ODoPres` query.

### The experiment

`nm_attack.cc` (C++17, OpenSSL 3.6.4 `libcrypto`) implements, for each of
ML-DSA-44/65/87 (FIPS 204 Table 1, flag `--param`):

- **Key.** `EVP_PKEY` key generation from the seed `ξ` (`OSSL_PKEY_PARAM_ML_DSA_SEED`),
  export of the encoded `pk` and `sk`, and `skDecode` (Algorithm 25) to
  obtain `t0`. The self-test checks that OpenSSL's `pk` and `sk` are
  byte-equal to an independent implementation of `KeyGen_internal`
  (Algorithm 6: `ExpandA`, `ExpandS`, NTT, `Power2Round`, `pkEncode`,
  `skEncode`) for 9 seeds, and that every `t0` coefficient lies in
  `(−2^12, 2^12]`.
- **Real presentations.** `R`, `ctx` ← 16 random bytes each, `M = R ‖ ctx`,
  `σ ← ML-DSA.Sign(dsk, M, ε)` with OpenSSL's default hedged signing. Each
  `σ` is verified with OpenSSL. The presentation's `µ` and `w1` are computed
  as in `ShowUsr1`/`ShowUsr2` (`sigDecode`, `HintBitUnpack`, `ExpandA`, NTT,
  `UseHint`), and the distinguisher computes `c̃′` from them. The program
  also counts samples with `c̃′ ≠ c̃(σ)`; there were none in any run.
- **Simulated presentations.** `u` uniform in `R_q^k`, `r_w′ = HighBits(u, 2γ2)`,
  `r_µ` 64 uniform bytes; the distinguisher computes
  `c̃′ = SHAKE256(r_µ ‖ w1Encode(r_w′), λ/4)`.
- **Statistics.** With `N` real and `N` simulated presentations, the
  advantage is `p_real − p_sim` where `p_x` is the fraction of class `x` on
  which the distinguisher outputs "real"; standard error
  `sqrt(p_real(1−p_real)/N + p_sim(1−p_sim)/N)`, `z` = advantage / standard
  error. The program also reports the predicted advantage of the median test
  under the model `density = α/E_U[α]`,
  `E_U[(α/E_U[α] − 1)·1{α > θ}]`, from the calibration challenges.

Randomness comes from OpenSSL `RAND_bytes`.

### Results

All runs: host B (AMD EPYC 9754, 256 hardware threads, shared with other jobs), 48 threads,
OpenSSL 3.6.4, g++ 15.3.0, 2026-10-23. Raw outputs are in `results/`.

**Pipeline and key checks.** For each parameter set, OpenSSL's encoded keys
equal those of the independent `KeyGen_internal` for 9 seeds; on 1000
signatures per parameter set, and on every one of the real presentations in
the tests below (5.24·10^8 signatures in total), the verifier's
recomputed `c̃′ = H(µ ‖ w1Encode(w1), λ/4)` equals the signature's `c̃`
(0 mismatches), and every signature verified under OpenSSL.

**The test, at the all-zero seed.** `N` is the number of real presentations
and also the number of simulated ones. "Predicted" is
`E_U[(α/E_U[α] − 1)·1{α > θ}]` on the 2,000,000 calibration challenges.

| Parameter set | Predicted advantage | N | p_real | p_sim | Advantage | Std. error | z |
|---|---|---|---|---|---|---|---|
| ML-DSA-44 | 2^−9.00 | 1.2·10^7 | 0.5020500 | 0.5001705 | 2^−9.06 | 2.04e-4 | 9.21 |
| ML-DSA-65 | 2^−10.86 | 10^8 | 0.5005981 | 0.4999876 | 2^−10.68 | 7.07e-5 | 8.63 |
| ML-DSA-87 | 2^−9.45 | 2.4·10^7 | 0.5013382 | 0.4997837 | 2^−9.33 | 1.44e-4 | 10.77 |

The measured advantages agree with the predicted ones within 2.3 standard
errors.

**The all-zero seed is not special.** Over the 64 seeds
`ξ_j = (j as 4 little-endian bytes) ‖ 0^28`, every key's tilt
`δ(ξ) = ½·E_U|α/E_U[α] − 1|` (the statistical distance between the uniform
and the accepted challenge distributions, on 20,000 challenges) is above
2^−11.6 at every parameter set. Testing the seed with the largest `δ` raises
the advantage by a factor of 1.2 to 2.9, for example to 2^−10.09 (z = 8.2) at
ML-DSA-65; `results/<44|65|87>/select.txt` and `test_seed<j>.txt` hold these
runs. Result 2 uses fresh random keys throughout.

## Result 2: every simulator fails

Definition 8 asks for one simulator `Sim` that works against every PPT
adversary, and `Sim.Show` receives only `(ipk, ctx, ϕ, L(isk))`. None of these
depends on the coins `ρ_se`. An adversary that draws `ρ_se` uniformly, and
independently of everything else it passes to the game, therefore faces a law
`Q` of the simulated `(w1, c̃′)` that does not depend on the device key. The
test below outputs 1 with probability exactly 1/2 on every such `Q`, and with a
larger probability on real presentations. Its advantage is the same against
every simulator, efficient or not, and the measurement bounds that advantage
from below. The test of result 1 is specific to the proof's simulator, whose
`c′` is uniform; this one is not.

### The stand-in gap

The distinguisher:

1. draws the device seed `k` uniformly as `ρ_se`, and a second seed `k′`
   uniformly, which it keeps to itself;
2. on a presentation, computes `c̃′` as the verifier does and reads `w1`;
3. outputs 1 with probability `(1 + s_k(w1, c̃′) − s_k′(w1, c̃′)) / 2`.

The score `s_k = standinScore` is a polynomial-time stand-in for the
probability that an attempt with this `(w1, c̃)` passes the `ct0` and hint
checks under key `k`. It is 0 if `‖c·t0‖∞ ≥ γ2`, and otherwise the
Poisson-binomial probability that the hint count is at most `ω`, with each
coordinate's hint probability given by its bucket of `w1` (`hintCount` in
`Signing/Surrogate.lean`). It lies in `[0, 1]`.

`challengeAdvantage_standin_eq`
(`Applications/MLDSA/Signing/ChallengeDistinguisher.lean`) proves two
statements:
- on any key-independent `Q`, the distinguisher outputs 1 with probability
  exactly 1/2, because `k` and `k′` are exchangeable;
- on presentations of the idealized FIPS 204 signer (`Signing/Ideal.lean`),
  it outputs 1 with probability `1/2 + standinGap/2`, where

`standinGap = E_{k,k′} E_{(w1, c̃) ← P_k} [s_k(w1, c̃) − s_k′(w1, c̃)]`

and `P_k` is the law of the first accepted attempt's `(HighBits(A·y), c̃)`. The
identity behind it (`PMF.exchangeableAcceptProb_real`) holds for every
key-dependent law `P_k`, so with `P_k` the law of real OpenSSL presentations
the advantage against real signing is that law's gap. Lean does not prove that
the gap is positive; `standin_gap.cc` measures it.

**Measurement.** Each i.i.d. unit draws two fresh seeds `k`, `k′`, one
presentation `x ← P_k` and one `x′ ← P_k′`, and records
`Z = ½[(s_k − s_k′)(x) + (s_k′ − s_k)(x′)]`, which lies in `[−1, 1]` and has
mean `standinGap`. Maurer and Pontil (2009, Theorem 4), applied to
`(Z + 1)/2` with the sample variance, give a lower bound that holds with
probability at least 1 − 2^−40. `N` was fixed per host before the production
runs, and pilot data is excluded. Keys come from `KeyGen_internal` on uniform
seeds, so no MLWE step enters. Two signers:

- **ideal**: the sampler of `Ideal.lean`. Each attempt draws `y` uniform on the
  mask box and `c̃` uniform, applies the `z`, `r0`, `ct0` and hint checks, and
  the output is `(HighBits(A·y), c̃)` of the first accepted attempt.
- **deployed**: OpenSSL `ML-DSA.Sign` with hedged randomness on a random
  message, with `(w1, c̃′)` computed from the signature as in
  `ShowUsr1`/`ShowUsr2`. All 1.6·10^9 signatures verified under OpenSSL, and
  `c̃′ = c̃` on every one.

| Parameter set | Signer | N | Mean | Gap ≥ | Advantage ≥ |
|---|---|---|---|---|---|
| ML-DSA-44 | ideal | 4.0·10^8 | 2^−13.86 | 2^−13.94 | 2^−14.94 |
| ML-DSA-44 | deployed | 2.0·10^8 | 2^−13.87 | 2^−13.99 | 2^−14.99 |
| ML-DSA-65 | ideal | 6.0·10^9 | 2^−18.67 | 2^−18.79 | 2^−19.79 |
| ML-DSA-65 | deployed | 1.2·10^9 | 2^−18.64 | 2^−18.94 | 2^−19.94 |

The deployed and ideal means differ by 0.7 (ML-DSA-44) and 1.0 (ML-DSA-65)
standard errors, and the per-host means by at most 1.3 standard errors in every
phase. ML-DSA-87 was not measured. The program's self-tests, run on both hosts
at both parameter sets, check:

- the NTT against schoolbook products;
- key generation against an exact-arithmetic implementation and OpenSSL's keys
  on 200 seeds;
- the score against an independent long-double reference;
- the hint count against a brute-force `MakeHint` count over whole buckets;
- the fast attempt against an exact one on 1000 `(y, c̃)` pairs.

Runs: host A (200 threads) and host B (AMD EPYC 9754, 180 threads), OpenSSL
3.6.4, g++ 15.3.0, 2026-10-24/25, about 11.5 h and 10 h of wall time. Each
host's master seed is recorded in its `env.txt`. Raw outputs and `bounds.txt`
are in `results/<44|65>/standin/`.

## Result 3: every simulator fails in a weaker game

The weaker game is Unlink-1 (Figure 3) with two changes: the device key is
generated with honest coins, `(dsk, dpk) ← DevKGen(par)`, and the adversary
receives `dpk` (that is, `ρ` and `t1`) in place of choosing `ρ_se`. The
adversary therefore does not know `t0`. An Unlink-1 adversary can play this
game by choosing `ρ_se` uniformly and reading only `t1`, so a bound here is
also a bound in Unlink-1. As in result 2, `Sim.Show` never sees the device
key, so the law `Q` of its presentations does not depend on it.

### The edge test

`Power2Round` writes each coefficient of `t` as `t1·2^13 + t0` with `t0` in
`(−2^12, 2^12]`, and `q = 1023·8192 + 1`. A coefficient with `t1 = 0` has
`t0 ≥ 0`, and one with `t1 = 1023` has `t0 ≤ 0`. Such an *edge* coefficient
occurs with probability `8193/q` (about 2^−10), and its sign of `t0` is visible
in the public key.

The sign of a single edge does not affect the law of the accepted challenge,
because that law is symmetric under `c → −c`. The relative sign of two edges
`j1`, `j2` in the same polynomial does: the tilt of the accepted challenge
contains the term `t0[j1]·t0[j2]` times the negacyclic autocorrelation
`A(c) = ⟨c·X^j1, c·X^j2⟩`. Let `E` be the event that some polynomial of `t` has
exactly two edges. On `E`, the test takes the two edges of the lowest such
polynomial, with sign product `ρ`, and outputs 1 with probability
`(1 − ρ·sign A(c))/2`. Off `E` it outputs a fair coin. `Pr[E]` is 0.0938
(ML-DSA-44), 0.1374 (ML-DSA-65) and 0.1789 (ML-DSA-87), computed exactly.

**Model.** `t` is uniform on `R_q^k` (the MLWE step), and presentations follow
the stand-in law `P_t0`, whose density against the uniform law on bucket
vectors and hashes is proportional to `standinScore`.

**Measurement** (`edge_test.cc`). Each unit draws a key configuration on `E`
and replaces the second edge by a twin pair with opposite signs, drawn so that
each twin has its exact conditional law. It draws observations from both twins
by coupled rejection sampling (common proposals and common uniforms). The
recorded value `Y` has mean exactly `E[m | E]` up to a term of size at most
`8193^−2`, where `m` is the test's advantage given the configuration. The
coupling cancels the variation between keys and lowers the variance by about
1000×. `Y` is bounded by a proved range `B` (1.39 to 1.51), and Maurer and
Pontil at confidence 1 − 2^−40 give

`Adv(g) ≥ ½·Pr[E]·(LCB − 2·8193^−2)`.

There is no expansion in the tilt and no approximation of the normalizer.

| Parameter set | Units | Mean `E[m \| E]` | Lower bound | Advantage ≥ |
|---|---|---|---|---|
| ML-DSA-44 | 5.4·10^8 | 2^−16.39 | 2^−16.46 | 2^−20.88 |
| ML-DSA-65 | 2.4·10^9 | 2^−19.03 | 2^−19.11 | 2^−23.00 |
| ML-DSA-87 | 1.6·10^9 | 2^−18.26 | 2^−18.33 | 2^−21.83 |

The means agree with the leading-order prediction from the autocorrelation
term within about one standard error. All self-tests passed on both hosts, and
no recorded value left its proved range (largest `|Y|` about 0.12). Runs:
ML-DSA-65 and ML-DSA-87 on host A (200 threads) and host B (180 threads),
2026-10-25, about 40 min. ML-DSA-44 pools 3·10^8 units from host B with
2.4·10^8 from a laptop, each under its own seed. Each host's master seed is
recorded in its `env.txt`. Raw outputs and `bounds.txt` are in
`results/<44|65|87>/edge/`.

### From the hybrid to real keys

Real keys and the real signer differ from the hybrid in two ways:

1. **Real `t` in place of uniform `t`.** A test that reads only `(Â, t)`
   changes its acceptance probability by at most its MLWE advantage
   (`abs_mlweRealMean_sub_mlweUniformMean_le`, `Signing/MLWE.lean`). The
   advantage is defined after Barbosa et al., CRYPTO 2023, Definition 3. Three
   tests pay this cost:
   - `B_g`, the edge test on stand-in presentations;
   - the edge test at each fixed presentation `x`, which covers the
     simulator's side. A simulator need not be efficient, but each fixed-`x`
     test is.
   - `B_typ`, the indicator of an atypical `t0` (ML-DSA-65 and ML-DSA-87 only).
2. **The real signer in place of the stand-in law.** A test's acceptance
   probability moves by at most the TV distance between the two laws of
   `(w1, c̃)`, the stand-in error.

**The stand-in error** (`Regularity/StandinError.lean`). The setting has
`SampleInBall` as a random oracle (`withSampleInBall`,
`Ring/PublicW1/MLDSAPublicW1.lean`) and averages over real keys.

| Parameter set | Stand-in error ≤ | Theorem |
|---|---|---|
| ML-DSA-44 | 2^−95 | `sum_expect_tvDist_standin_le_mldsa44` |
| ML-DSA-65 | 2^−60 + Adv^MLWE(B_typ) + 2^−56 | `sum_expect_tvDist_standin_le_mldsa65` |
| ML-DSA-87 | 2^−100 + Adv^MLWE(B_typ) + 2^−100 | `sum_expect_tvDist_standin_le_mldsa87` |

At ML-DSA-65 and ML-DSA-87 the proof has four steps:

1. **The TV distance is a ratio.** It is at most the regularity numerator
   `Σ_v 𝔼_c |realMass − ρ_z·standinMass|` divided by the key's acceptance
   probability (`tvDist_le_numerator_div`).
2. **The numerator is small.** It is at most `K·|V|·11·2^−148` (ML-DSA-65)
   and `K·|V|·12·2^−244` (ML-DSA-87)
   (`sum_expect_abs_realMass_sub_le_mldsa65_five`, `…_mldsa87_five`). This is
   the ring-signature regularity bound without its division by a mean member
   weight, so it needs no `μ` hypothesis.
3. **Typical keys accept often enough.** A key whose `‖t0‖₂²` is at most 9/20
   (ML-DSA-65) or 1/2 (ML-DSA-87) of its maximum accepts with probability at
   least e^−60, resp. e^−95 (`exp_neg_le_expect_acceptWeight_mldsa65`). The
   bound comes from four facts:
   - the Poisson-binomial CDF is at least the probability of no hint
     (`prod_one_sub_le_poissonBinomialCdf`);
   - Jensen;
   - in every bucket the hint probability is at most `|b|/(2(γ₂−β)−1)`
     (`sum_hintProb_le`);
   - the exact second moment of challenge products
     (`expect_challengeBall_centeredCoeffs_sq`, `Signing/ChallengeMoments.lean`).

   The ct₀ check never fails at these parameter sets, because `τ·4096 < γ₂`.
4. **Atypical keys are rare.** With `t` uniform they have probability at most
   2^−60, resp. 2^−100 (`hybridEventProb_atypical_le_mldsa65`, `…_mldsa87`).
   For real keys this costs `Adv^MLWE(B_typ)` (`mlweRealMean_atypicalTest_le`).

**The composed theorem.** The single theorems are
`edgeTest_real_sub_simulator_ge_mldsa65` and `…_mldsa87`
(`Regularity/EdgeTestRealKeys.lean`). The setting:
- `SampleInBall` and `ExpandA` are random oracles.
- The device secret comes from ExpandS on a uniform seed.
- Presentations come from the idealized FIPS 204 signer
  (`realPresentationLaw`).

For every simulator law `Q` that may depend on the oracle but not on the
device key, at ML-DSA-65:

    Pr_real[g = 1] − Pr_Q[g = 1]
      ≥ oracleEdgeHybridAdv − Pr[E]/(2·8193²) − Adv^MLWE(B_g) − ε
        − (2^−60 + Adv^MLWE(B_typ) + 2^−56),

where `ε` bounds the MLWE advantage of every fixed-presentation test. At
ML-DSA-87 the last term is `2^−100 + Adv^MLWE(B_typ) + 2^−100`. At ML-DSA-44
(`edgeTest_real_sub_simulator_ge_mldsa44`) it is `2^−95`, and the device
secret comes from `ExpandS` as a random oracle as well (`oracleSecretLaw`),
so the MLWE advantages of `B_g` and of the fixed-presentation tests are taken
under that secret law.

Apart from Lean's own definitions, the theorem rests on three things:
- `oracleEdgeHybridAdv`, the measured quantity;
- the MLWE advantages, which appear as terms;
- the tests' efficiency, which is not formalized.

**Two steps outside Lean.**
- `oracleEdgeHybridAdv` averages over a uniform oracle `G`, with `c = G(c̃)`.
  `edge_test.cc` draws `c̃` uniformly and computes `c` with the real
  SHAKE-based `SampleInBall`. Treating the measured value as
  `oracleEdgeHybridAdv` is the random-oracle heuristic for `SampleInBall`.
- The real presentations in the theorem come from the idealized signer, not
  OpenSSL. Result 2's two signer modes agree to within one standard error.

### Why ML-DSA-44 differs

At ML-DSA-44 steps 3 and 4 above do not work:
- **The ct₀ check can fail,** because `τ·4096 = 159744 > γ₂ = 95232`.
- **The zero-hint floor collapses.** The expected hint count of a typical key,
  about 63, is too close to `ω = 80`. The floor gives about 2^−170 even for
  typical keys, and the ratio of step 1 exceeds 1.

The weakness is in the proof route, not in the signer. Real ML-DSA-44 keys
accept with high probability (see the measurement below). The proof at
ML-DSA-44 replaces steps 3 and 4 with the weight bounds of the ring signature
in [`formal/GordieHowe/Applications/Ring/PublicW1/README.md`](../../formal/GordieHowe/Applications/Ring/PublicW1/README.md):

1. **Divide by a weight, then average.** The TV distance is at most the
   regularity numerator divided by any lower bound `W` on the key's mean
   acceptance weight, plus the indicator of `W = 0`
   (`tvDist_le_indicator_add_mul_inv`). Cauchy–Schwarz over the matrix leaves
   `ε·√(𝔼 W⁻²)`, with `ε = 11·2^−101` the ℓ² regularity numerator
   (`expect_tvDist_standin_le_of_weight`).
2. **`𝔼 W⁻² ≤ (24/5)²`** over keys, matrices and the `SampleInBall` oracle
   (`expect_expect_expect_inv_sq_mldsa44OracleWeight_le`). The weight `W` is
   the largest of five lines below the Poisson-binomial CDF, each certified by
   finitely many exact rational checks, evaluated at the oracle averages of the
   ct₀ indicator and of the hint fractions. The proof then averages over keys
   in layers by the largest component norm of `t0`.
3. **`W = 0` is negligible.** It happens only if every commitment hash fails
   the ct₀ check. For every `t0` each hash fails independently with probability
   at most 217/625 (`one_sub_le_expect_challengeBall_ct0_mldsa44`, a convex
   comparison), so `Pr[W = 0] ≤ (217/625)^(2^256) ≤ 2^−1000`.

The result is a stand-in error of at most `11·2^−101·(24/5) + 2^−1000 ≤ 2^−95`
(`sum_expect_tvDist_standin_le_mldsa44`). The keys come from `ExpandS` as a
random oracle with `Â` uniform, and the bound averages over them, so no
atypical-key test and no MLWE step enter.

**A measurement of the same fact.** `lowacc.cc` counts low-acceptance keys
directly, without the proof:
- **Keys.** It draws keys as the Lean key model does: `(s1, s2)` from
  `ExpandS` on a uniform seed, `Â` uniform.
- **Score.** For each key it averages the acceptance weight over 16 uniform
  challenges with uniform bucket vectors.
- **Run.** It covers `N = 2^31` keys on host A (200 threads) and host B
  (180 threads), 2026-10-25, about 1.5 h each. The master seed is
  SHA-256("lowacc 2026-10-25 p44"), and the hosts split the key range.
- **Result.** No key averaged below 1/2. The smallest average was 0.902, and
  the mean was 0.9854. Raw outputs are in `results/44/lowacc/`.

By Markov's inequality, a key with acceptance below 1/4 averages at least 1/2
with probability at most 1/2. With no key below 1/2 among `2^31`, at
confidence `1 − 2^−40`, a key has acceptance below 1/4 with probability at
most `2·27.7/2^31 = 2^−25.2`.

## Lean statements

Paths are relative to `formal/GordieHowe/`.

| Claim | Theorem | File |
|---|---|---|
| Result 2: the distinguisher accepts with probability 1/2 on every key-independent `Q` and with probability 1/2 + `standinGap`/2 on the idealized signer | `challengeAdvantage_standin_eq` | `Applications/MLDSA/Signing/ChallengeDistinguisher.lean` |
| Result 2: the identity for any key-dependent law, used for OpenSSL signing | `PMF.exchangeableAcceptProb_real`, `PMF.exchangeableAcceptProb_const` | `Foundations/ToMathlib/ExchangeableDistinguisher.lean` |
| Result 3: 8193 edge values, mean edge sign 1/8193 | `card_filter_isEdgeHigh`, `sum_filter_isEdgeHigh_edgeSign` | `Applications/MLDSA/Signing/EdgeTest.lean` |
| Result 3: edge signs independent given the positions | `abs_sum_prod_mul_prod_sign_le` | `Foundations/ToMathlib/SignSymmetry.lean` |
| Result 3: every key-independent `Q` is accepted with probability within `Pr[E]/(2·8193²)` of 1/2 | `abs_edgeAcceptProb_const_sub_half_le` | `Applications/MLDSA/Signing/EdgeTest.lean` |
| Result 3: hybrid advantage against every `Q` | `abs_edgeAcceptProb_sub_const_sub_edgeHybridAdv_le` | `Applications/MLDSA/Signing/EdgeTest.lean` |
| Result 3: the MLWE hops | `abs_mlweRealMean_sub_mlweUniformMean_le`, `edgeHybridAdv_sub_le_mlweRealMean_standinTest_sub_simulatorTest`, `mlweRealMean_atypicalTest_le` | `Applications/MLDSA/Signing/MLWE.lean`, `EdgeTest.lean` |
| Result 3: `SampleInBall` as a random oracle | `withSampleInBall`, `expect_withSampleInBall` | `Applications/Ring/PublicW1/MLDSAPublicW1.lean` |
| Result 3: second moment and sub-Gaussian bound of challenge products | `expect_challengeBall_centeredCoeffs_sq`, `expect_challengeBall_exp_centeredCoeffs_le` | `Applications/MLDSA/Signing/ChallengeMoments.lean` |
| Result 3: regularity numerators | `sum_expect_abs_realMass_sub_le_mldsa44`, `sum_expect_abs_realMass_sub_le_mldsa65_five`, `sum_expect_abs_realMass_sub_le_mldsa87_five` | `Applications/MLDSA/Regularity/Instances.lean`, `InstancesFive.lean` |
| Result 3: stand-in error at ML-DSA-65 / ML-DSA-87 | `sum_expect_tvDist_standin_le_mldsa65`, `sum_expect_tvDist_standin_le_mldsa87` | `Applications/MLDSA/Regularity/StandinError.lean` |
| Result 3: stand-in error at ML-DSA-44 | `tvDist_le_indicator_add_mul_inv`, `expect_tvDist_standin_le_of_weight`, `sum_expect_tvDist_standin_le_mldsa44` | `Applications/MLDSA/Regularity/StandinError44.lean` |
| Result 3: the weight at ML-DSA-44 | `expect_expect_expect_inv_sq_mldsa44OracleWeight_le`, `one_sub_le_expect_challengeBall_ct0_mldsa44` | `Applications/MLDSA/Regularity/WeightTail44.lean`, `Ct0Tail44.lean` |
| Result 3, composed: generic form and the instances at ML-DSA-44 / ML-DSA-65 / ML-DSA-87 | `oracleEdgeHybridAdv_sub_le_realKeyEdgeAdvantage`, `edgeTest_real_sub_simulator_ge_mldsa44`, `edgeTest_real_sub_simulator_ge_mldsa65`, `edgeTest_real_sub_simulator_ge_mldsa87` | `Applications/MLDSA/Regularity/EdgeTestRealKeys.lean` |

The measured quantities `standinGap` and `oracleEdgeHybridAdv` are
definitions in Lean. Lean proves neither their sign nor their size.

## Runtime

For result 1, the full `run.sh` took 4 h 41 min of wall time on host B with 48 threads.
A pair of presentations costs about 1.0 ms (ML-DSA-44), 1.6 ms (ML-DSA-65)
and 2.1 ms (ML-DSA-87) of one core. The pair is one real presentation with
signing, OpenSSL verification and the presentation computation, and one
simulated presentation, both scored. Scoring one presentation with `α` takes
about 0.06 ms of that.

## Reproduction

Inside a shell providing g++ and OpenSSL ≥ 3.5 on Linux:

```
bash ./run.sh
```

`run.sh` compiles `nm_attack`, runs the self-tests, the seed selection, the
calibrations and the tests for all three parameter sets, and writes
`results/<44|65|87>/*.txt` and `results/summary.txt`. `THREADS` (default 48)
sets the thread count; `SCALE=100` divides every test size by 100 for a quick
check. The results of the run reported above are in `results/`.

`standin_run.sh` and `edge_test_run.sh` run the two further tests on one host
inside a shell providing g++ with OpenMP and OpenSSL ≥ 3.5 (with
`NIX_ENFORCE_NO_NATIVE=0` inside a Nix shell, for `-march=native`). `LABEL`
names the host and fixes its seed, `SEED` optionally overrides that seed with
the one recorded in an `env.txt`, `THREADS` sets the thread count, and
`N44I N44D N65I N65D` (stand-in gap) or `N44 N65 N87` (edge test) set the
number of units. The commands used were:

```
LABEL=host-a THREADS=200 N44I=220000000 N44D=110000000 N65I=3300000000 N65D=660000000 bash ./standin_run.sh
LABEL=host-b THREADS=180 N44I=180000000 N44D=90000000  N65I=2700000000 N65D=540000000 bash ./standin_run.sh
LABEL=host-a THREADS=200 N65=1200000000 N87=800000000 bash ./edge_test_run.sh
LABEL=host-b THREADS=180 N44=300000000 N65=1200000000 N87=800000000 bash ./edge_test_run.sh
```

`lowacc_run.sh` runs the ML-DSA-44 low-acceptance count; `LABEL`, `THREADS`,
`K0` and `N` (the first key and the number of keys) as above. The commands
used were:

```
LABEL=host-a THREADS=200 K0=0 N=1073741824 bash ./lowacc_run.sh
LABEL=host-b THREADS=180 K0=1073741824 N=1073741824 bash ./lowacc_run.sh
```

`standin_bound.py` and `edge_test_bound.py` pool the output files of one
parameter set (from several hosts) and print the bounds, for example
`python3 edge_test_bound.py results/65/edge/host-a/edge_65.txt results/65/edge/host-b/edge_65.txt`.

## What the experiments do not show

- **One presentation only.** Every bound concerns one presentation. Several
  presentations under one key presumably leak more; that is not measured.
- **Gap sizes are measured, not proved.** The lower bounds are measurements at
  confidence 1 − 2^−40. Lean proves the identities that turn the gaps into
  advantages against every simulator, but not the gaps' size or sign.
- **No assumption-free bound at ML-DSA-87.** The stand-in gap is not measured
  there, so the only bound for every simulator is result 3's, under MLWE.
- **What result 3 assumes:**
  - MLWE, for three explicit tests at ML-DSA-65 and ML-DSA-87, and two at
    ML-DSA-44;
  - at ML-DSA-44, `ExpandS` as a random oracle in the key model;
  - the random-oracle heuristic for `SampleInBall` in its measurement;
  - the idealized signer in place of OpenSSL.

  The tests' efficiency is not formalized.
