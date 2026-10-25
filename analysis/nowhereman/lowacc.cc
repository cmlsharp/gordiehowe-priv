// Acceptance weight of ML-DSA's ct0 and hint checks over uniform challenges,
// key by key.  Mode "lowacc" is the ML-DSA-44 low-acceptance count of README.md.
//
// For a key with t0 and a challenge c uniform on B_tau (tau positions as a
// uniform tau-subset, independent uniform signs; no SHAKE), b = c * t0 over
// the integers (negacyclic), and
//
//   acceptWeight(b, v) = 0 if some |b_i| >= gamma2, else Pr[sum Bernoulli(p_i) <= omega],
//   p_i = hintCount(beta, v_i, b_i) / (2(gamma2 - beta) - 1),
//
// computed by standin_score of standin_gap.cc (checked there against the Lean
// formula).  The worst bucket vector takes v_i != 0 everywhere (it maximizes
// every hintCount, and the Poisson-binomial CDF decreases in every p_i).  The
// program estimates per key
//
//   mu_w = E_c acceptWeight(b, worst v),  mu_u = E_c acceptWeight(b, v uniform),
//   mean, std, skew of m(c) = sum_i p_i at worst v (and the mean at uniform v),
//   Pr_c[ct0 failure], Pr_c[m(c) > omega],
//
// with adaptive stopping at 1% relative standard error of mu_w.
//
// Families (--fam): 0 real KeyGen_internal keys on random seeds; 1 t0 = +-4096
// with random signs; 2 t0 = +4096 everywhere; 3 t0 uniform on (-4096, 4096];
// 4 t0 i.i.d. with weight exp(theta x^2 / 4096^2) on (-4096, 4096] (the
// exponential tilt that realizes a large ||t0||_2 most cheaply).
// 5 t0 = 4096 * (periodic sign pattern), period 1 + idx % 256, random base
// pattern per component.
//
// Randomness: key idx uses AES-256-CTR(master, IV = idx || 0xA000+fam);
// replica r of key idx draws challenges from IV = idx || 0xB000+r.
//
// Build: g++ -O3 -march=native -fopenmp -std=c++17 lowacc.cc -lcrypto (lowacc_run.sh)

#define main standin_gap_main
#include "standin_gap.cc"
#undef main

namespace aw {

struct KeyStats {
  double l2[KMAX], l4[KMAX];
  int linf;
  double rho_max;   // max |corr(b_a, b_b)| over distinct coordinate pairs a != b
  double sd_gauss;  // Gaussian-proxy sd of sum_i |b_i| / D from the covariance of b
};

// Cov(|X|, |Y|) for a standard bivariate normal pair with correlation r.
inline double cov_abs(double r) {
  if (r > 1) r = 1;
  if (r < -1) r = -1;
  return (2.0 / M_PI) * (sqrt(1 - r * r) + r * asin(r) - 1);
}

// Covariance over c of b = c * t0: Cov(b_{j,i}, b_{j',i+d}) = +-(tau/256) C(j,j',d) with
// C(j,j',d) = sum_m s(0,m) s(d,m) t0_j[-m] t0_j'[d-m] (negacyclic signs s); the sign
// does not matter below because cov_abs is even.
double corr_C(const Key& key, int a, int b, int d) {
  double c = 0;
  for (int m = 0; m < N; m++) {
    int ia = (N - m) % N, ib = (d - m + N) % N;
    double sg = ((m > 0) ? -1.0 : 1.0) * ((d - m < 0) ? -1.0 : 1.0);
    c += sg * (double)key.t0[a][ia] * (double)key.t0[b][ib];
  }
  return c;
}

void corr_stats(const Key& key, KeyStats* ks) {
  const int k = P->k;
  const double D = 2.0 * (P->gamma2 - P->beta) - 1.0;
  double v = 0, rmax = 0;
  for (int a = 0; a < k; a++)
    for (int b = 0; b < k; b++) {
      double na = ks->l2[a], nb = ks->l2[b];
      if (na == 0 || nb == 0) continue;
      double sa = sqrt(P->tau * na / 256.0), sb = sqrt(P->tau * nb / 256.0);
      for (int d = 0; d < N; d++) {
        double c = corr_C(key, a, b, d);
        double r = c / sqrt(na * nb);
        if (!(a == b && d == 0)) rmax = std::max(rmax, fabs(r));
        v += N * sa * sb * cov_abs(r);
      }
    }
  ks->rho_max = rmax;
  ks->sd_gauss = sqrt(std::max(0.0, v)) / D;
}

struct Result {
  long idx, rep, n;
  double mu_w, m2_w, mu_u, m2_u;  // Welford of the two acceptance weights
  double mm, mm2, mm3;            // m(c) at worst v: mean, central 2nd, 3rd moment sums
  double mmu;                     // mean of m(c) at uniform v
  long fail, over;                // ct0 failures, m(c) > omega
  KeyStats ks;
};

// Uniform 16-bit value below `bound` by rejection.
inline uint32_t uniform_below(Stream& rs, uint32_t bound) {
  const uint32_t lim = 65536u / bound * bound;
  for (;;) {
    uint16_t v;
    rs.bytes((uint8_t*)&v, 2);
    if (v < lim) return v % bound;
  }
}

// c uniform on B_tau: partial Fisher-Yates over the 256 positions, then tau signs.
void uniform_challenge(Stream& rs, Challenge* ch) {
  uint8_t perm[N];
  for (int i = 0; i < N; i++) perm[i] = (uint8_t)i;
  for (int i = 0; i < P->tau; i++) {
    int j = i + (int)uniform_below(rs, N - i);
    std::swap(perm[i], perm[j]);
  }
  uint64_t s;
  rs.bytes((uint8_t*)&s, 8);
  ch->ntau = P->tau;
  for (int i = 0; i < P->tau; i++) {
    ch->pos[i] = perm[i];
    ch->sgn[i] = (int8_t)(((s >> i) & 1) ? -1 : 1);
  }
}

// Tilted sampler: CDF over x in (-4096, 4096] with weight exp(theta (x/4096)^2).
struct Tilt {
  std::vector<double> cdf;  // 8192 entries, x = i - 4095
  void init(double theta) {
    cdf.resize(8192);
    double s = 0;
    for (int i = 0; i < 8192; i++) {
      double x = (i - 4095) / 4096.0;
      s += exp(theta * x * x);
      cdf[i] = s;
    }
    for (double& c : cdf) c /= s;
  }
  int32_t draw(Stream& rs) const {
    uint64_t u;
    rs.bytes((uint8_t*)&u, 8);
    double r = (u >> 11) * (1.0 / 9007199254740992.0);
    int i = (int)(std::upper_bound(cdf.begin(), cdf.end(), r) - cdf.begin());
    if (i > 8191) i = 8191;
    return i - 4095;
  }
};

Tilt g_tilt;

void make_key(int fam, const uint8_t master[32], long idx, Key* key) {
  Stream rs;
  rs.init(master, (uint64_t)idx, 0xA000u + (uint32_t)fam);
  if (fam == 0) {
    uint8_t xi[32];
    rs.bytes(xi, 32);
    keygen_fast(xi, key);
    return;
  }
  for (int i = 0; i < P->k; i++)
    for (int j = 0; j < N; j++) {
      int32_t x = 0;
      if (fam == 1) {
        uint8_t b;
        rs.bytes(&b, 1);
        x = (b & 1) ? 4096 : -4096;
      } else if (fam == 2) {
        x = 4096;
      } else if (fam == 3) {
        x = (int32_t)uniform_below(rs, 8192) - 4095;
      } else if (fam == 5) {
        // Periodic sign pattern of period 1 + idx % 256 (random base pattern per component).
        int per = 1 + (int)(idx % 256);
        static thread_local int8_t base[N];
        if (j == 0)
          for (int u = 0; u < per; u++) {
            uint8_t bb;
            rs.bytes(&bb, 1);
            base[u] = (bb & 1) ? 1 : -1;
          }
        x = 4096 * base[j % per];
      } else {
        x = g_tilt.draw(rs);
      }
      key->t0[i][j] = x;
    }
}

KeyStats key_stats(const Key& key) {
  KeyStats ks{};
  for (int i = 0; i < P->k; i++) {
    double a = 0, b = 0;
    for (int j = 0; j < N; j++) {
      double x = key.t0[i][j];
      a += x * x;
      b += x * x * x * x;
      ks.linf = std::max(ks.linf, std::abs(key.t0[i][j]));
    }
    ks.l2[i] = a;
    ks.l4[i] = b;
  }
  corr_stats(key, &ks);
  return ks;
}

// m(c) = sum_i hintCount / (2(gamma2-beta)-1) for buckets w1.
double hint_mass(const int32_t b[][N], const uint8_t w1[][N]) {
  long s = 0;
  for (int i = 0; i < P->k; i++)
    for (int j = 0; j < N; j++) {
      int32_t bb = b[i][j];
      int32_t a = bb < 0 ? -bb : bb;
      int32_t hc = (bb < 0 && w1[i][j] != 0) ? (a - P->beta) : (a - P->beta - 1);
      if (hc > 0) s += hc;
    }
  return s / (2.0 * (P->gamma2 - P->beta) - 1.0);
}

bool ct0_fail(const int32_t b[][N]) {
  for (int i = 0; i < P->k; i++)
    for (int j = 0; j < N; j++)
      if (b[i][j] >= P->gamma2 || b[i][j] <= -P->gamma2) return true;
  return false;
}

uint8_t g_ones[KMAX][N];

Result run_key(int fam, const uint8_t master[32], long idx, long rep, long nmin, long nmax,
               double rel) {
  static thread_local Key* key = nullptr;
  if (!key) key = new Key();
  make_key(fam, master, idx, key);
  Result r{};
  r.idx = idx;
  r.rep = rep;
  r.ks = key_stats(*key);
  Stream rs;
  rs.init(master, (uint64_t)idx, 0xB000u + (uint32_t)rep);
  Acc aw, au, am;
  double mu_sum = 0;
  const int m = P->buckets();
  Challenge ch;
  int32_t b[KMAX][N];
  uint8_t w1[KMAX][N];
  long n = 0;
  double sum3 = 0;  // third moment about a shift (first sample)
  double shift = 0;
  for (;;) {
    for (int t = 0; t < 256; t++) {
      uniform_challenge(rs, &ch);
      sparse_mul(ch, key->t0, P->k, b);
      for (int i = 0; i < P->k; i++)
        for (int j = 0; j < N; j++) w1[i][j] = (uint8_t)uniform_below(rs, m);
      double sw = standin_score(b, g_ones);
      double su = standin_score(b, w1);
      double mw = hint_mass(b, g_ones);
      double mu = hint_mass(b, w1);
      if (n == 0 && t == 0) shift = mw;
      aw.add(sw);
      au.add(su);
      am.add(mw);
      sum3 += (mw - shift) * (mw - shift) * (mw - shift);
      mu_sum += mu;
      r.fail += ct0_fail(b);
      r.over += mw > P->omega;
    }
    n += 256;
    if (n >= nmax) break;
    if (n >= nmin) {
      double se = sqrt(aw.m2 / (aw.n - 1) / aw.n);
      if (aw.mean > 0 && se <= rel * aw.mean) break;
    }
  }
  r.n = n;
  r.mu_w = aw.mean;
  r.m2_w = aw.m2;
  r.mu_u = au.mean;
  r.m2_u = au.m2;
  r.mm = am.mean;
  r.mm2 = am.m2;
  // Central third moment from the shifted raw moments.
  {
    double d = am.mean - shift;
    double e2 = am.m2 / n + d * d;  // E (x-shift)^2
    double e3 = sum3 / n;
    r.mm3 = e3 - 3 * d * e2 + 2 * d * d * d;  // E (x - mean)^3
  }
  r.mmu = mu_sum / n;
  return r;
}

// ------------------------------------------------------------------ selftests

int selftest(const uint8_t master[32], long nch) {
  int fails = 0;
  Stream rs;
  rs.init(master, 0xfffffffffff7ull, 1);
  // 1. Challenge sampler: weight tau, distinct positions, position and sign
  //    marginals uniform (chi-square over 256 positions).
  {
    std::vector<long> cnt(N, 0);
    long pos_sgn = 0, bad = 0;
    long pair01 = 0;
    for (long t = 0; t < nch; t++) {
      Challenge ch;
      uniform_challenge(rs, &ch);
      bool seen[N] = {false};
      bool has0 = false, has1 = false;
      for (int i = 0; i < ch.ntau; i++) {
        if (seen[ch.pos[i]]) bad++;
        seen[ch.pos[i]] = true;
        cnt[ch.pos[i]]++;
        pos_sgn += ch.sgn[i] > 0;
        has0 |= ch.pos[i] == 0;
        has1 |= ch.pos[i] == 1;
      }
      pair01 += has0 && has1;
    }
    double e = (double)nch * P->tau / N, chi = 0;
    for (int i = 0; i < N; i++) chi += (cnt[i] - e) * (cnt[i] - e) / e;
    double pplus = (double)pos_sgn / ((double)nch * P->tau);
    double ppair = (double)pair01 / nch;
    double epair = (double)P->tau * (P->tau - 1) / (N * (N - 1.0));
    double zpair = (ppair - epair) / sqrt(epair * (1 - epair) / nch);
    bool ok = bad == 0 && chi < 255 + 6 * sqrt(2 * 255.0) && fabs(pplus - 0.5) < 5 * 0.5 / sqrt(nch * P->tau) &&
              fabs(zpair) < 5;
    fails += !ok;
    printf("aw selftest challenge sampler %ld draws: duplicate positions %ld, position chi2 %.1f "
           "(df 255), Pr[+] %.5f, Pr[0,1 in S] z %.2f: %s\n",
           nch, bad, chi, pplus, zpair, ok ? "ok" : "FAIL");
  }
  // 2. sparse_mul vs the exact NTT product mod q (centered), on t0 = +-4096 and uniform.
  {
    long bad = 0;
    for (int rep = 0; rep < 200; rep++) {
      int32_t x[N], b1[KMAX][N];
      static int32_t t0[KMAX][N];
      for (int j = 0; j < N; j++)
        x[j] = rep & 1 ? ((rs.words(1)[0] & 1) ? 4096 : -4096) : (int32_t)uniform_below(rs, 8192) - 4095;
      memcpy(t0[0], x, sizeof x);
      Challenge ch;
      uniform_challenge(rs, &ch);
      sparse_mul(ch, t0, 1, b1);
      int32_t c[N] = {0}, t[N];
      for (int u = 0; u < ch.ntau; u++) c[ch.pos[u]] = modq(ch.sgn[u]);
      for (int j = 0; j < N; j++) t[j] = modq(x[j]);
      ntt_ref(c);
      ntt_ref(t);
      for (int j = 0; j < N; j++) t[j] = (int32_t)((int64_t)t[j] * c[j] % Q);
      intt_ref(t);
      for (int j = 0; j < N; j++) bad += centered(t[j]) != b1[0][j];
    }
    fails += bad != 0;
    printf("aw selftest sparse_mul vs exact NTT product mod q, 200 products: mismatches %ld: %s\n",
           bad, bad ? "FAIL" : "ok");
  }
  // 3. Second moment: E_c (c*x)_i^2 = tau/256 * ||x||^2 (Monte Carlo, all i pooled).
  {
    static int32_t t0[KMAX][N];
    double nx = 0;
    for (int j = 0; j < N; j++) {
      t0[0][j] = (int32_t)uniform_below(rs, 8192) - 4095;
      nx += (double)t0[0][j] * t0[0][j];
    }
    Acc a;
    int32_t b[KMAX][N];
    for (long t = 0; t < nch / 4; t++) {
      Challenge ch;
      uniform_challenge(rs, &ch);
      sparse_mul(ch, t0, 1, b);
      double s = 0;
      for (int j = 0; j < N; j++) s += (double)b[0][j] * b[0][j];
      a.add(s / N);
    }
    double want = P->tau / 256.0 * nx;
    double se = sqrt(a.m2 / (a.n - 1) / a.n);
    bool ok = fabs(a.mean - want) < 5 * se;
    fails += !ok;
    printf("aw selftest E (c*x)_i^2 = tau ||x||^2/256: measured %.6e want %.6e (z %.2f): %s\n",
           a.mean, want, (a.mean - want) / se, ok ? "ok" : "FAIL");
  }
  // 4. Worst bucket vector: score at all-ones <= score at every random v, and
  //    equal at r1 != 0 patterns other than all-ones; m(c) via hint_mass vs the DP's p_i.
  {
    Key* key = new Key();
    make_key(0, master, 123456789, key);
    long bad = 0;
    const int m = P->buckets();
    for (int t = 0; t < 500; t++) {
      Challenge ch;
      uniform_challenge(rs, &ch);
      int32_t b[KMAX][N];
      sparse_mul(ch, key->t0, P->k, b);
      uint8_t v[KMAX][N], v2[KMAX][N];
      for (int i = 0; i < P->k; i++)
        for (int j = 0; j < N; j++) {
          v[i][j] = (uint8_t)uniform_below(rs, m);
          v2[i][j] = (uint8_t)(1 + uniform_below(rs, m - 1));
        }
      double sw = standin_score(b, g_ones), su = standin_score(b, v), s2 = standin_score(b, v2);
      if (su < sw - 1e-15 || fabs(s2 - sw) > 1e-15) bad++;
      if (hint_mass(b, g_ones) < hint_mass(b, v) - 1e-12) bad++;
    }
    fails += bad != 0;
    printf("aw selftest worst bucket vector, 500 challenges: violations %ld: %s\n", bad,
           bad ? "FAIL" : "ok");
    // 5. Real-key ct0 bound: tau * ||t0||_inf vs (q-1)/2, so integer product = centered mod q.
    printf("aw selftest tau*4096 = %d, (q-1)/2 = %d: integer product equals centered product: %s\n",
           P->tau * 4096, (Q - 1) / 2, P->tau * 4096 < (Q - 1) / 2 ? "ok" : "FAIL");
    fails += !(P->tau * 4096 < (Q - 1) / 2);
    delete key;
  }
  // 6. Cov_c(b_{a,0}, b_{b,d}) = (tau/256) C(a,b,d) on the all-+4096 key (large
  //    correlations) and a real key, Monte Carlo.
  for (int fam : {2, 0}) {
    Key* key = new Key();
    make_key(fam, master, 7, key);
    const int trip[4][3] = {{0, 0, 1}, {0, 1, 0}, {1, 0, 37}, {0, 0, 200}};
    double sxy[4] = {0};
    long nn = nch / 4;
    int32_t b[KMAX][N];
    for (long t = 0; t < nn; t++) {
      Challenge ch;
      uniform_challenge(rs, &ch);
      sparse_mul(ch, key->t0, P->k, b);
      for (int u = 0; u < 4; u++) sxy[u] += (double)b[trip[u][0]][0] * b[trip[u][1]][trip[u][2]];
    }
    double worst = 0;
    for (int u = 0; u < 4; u++) {
      double want = P->tau / 256.0 * corr_C(*key, trip[u][0], trip[u][1], trip[u][2]);
      double got = sxy[u] / nn;
      // Scale: sd of one product is about tau/256 * ||t0||^2; compare in those units.
      double unit = P->tau / 256.0 * 256 * 4096.0 * 4096.0 / sqrt((double)nn);
      worst = std::max(worst, fabs(got - want) / unit);
    }
    bool ok = worst < 6;
    fails += !ok;
    printf("aw selftest covariance of b vs (tau/256) C, fam %d, 4 (a,b,d): max |diff| %.2f units of "
           "tau*4096^2/sqrt(n): %s\n", fam, worst, ok ? "ok" : "FAIL");
    delete key;
  }
  printf("aw selftest %s\n", fails ? "FAILED" : "PASSED");
  return fails ? 1 : 0;
}

void print_result(const Result& r) {
  double n = r.n;
  double sew = sqrt(r.m2_w / (n - 1) / n), seu = sqrt(r.m2_u / (n - 1) / n);
  double sd = sqrt(r.mm2 / (n - 1));
  printf("key %ld rep %ld n %ld mu_w %.6e se_w %.3e mu_u %.6e se_u %.3e m_mean %.5f m_sd %.5f "
         "m_skew %.4f mu_mean %.5f pfail %.6e pover %.6e linf %d rho_max %.5f sd_gauss %.5f l2",
         r.idx, r.rep, r.n, r.mu_w, sew, r.mu_u, seu, r.mm, sd,
         sd > 0 ? r.mm3 / (sd * sd * sd) : 0.0, r.mmu, r.fail / n, r.over / n, r.ks.linf,
         r.ks.rho_max, r.ks.sd_gauss);
  for (int i = 0; i < P->k; i++) printf("%c%.0f", i ? ',' : ' ', r.ks.l2[i]);
  printf(" l4");
  for (int i = 0; i < P->k; i++) printf("%c%.6e", i ? ',' : ' ', r.ks.l4[i]);
  printf("\n");
}

}  // namespace aw


using namespace aw;
// ------------------------------------------------------------------ lowacc
// Low-acceptance keys in the Lean key model (StandinError.lean): (s1, s2) = ExpandS of a
// uniform seed (FIPS 204 Algorithm 33 via keygen's seed expansion), A-hat uniform on T_q^{k x l}
// (ExpandA as a random oracle), t = A s1 + s2, t0 = Power2Round low part. Per key: M
// challenges c uniform on B_tau with bucket vectors v uniform, the sample mean of
// acceptWeight(c * t0, v) (standin_score: ct0 indicator times the Poisson-binomial CDF).
// Counts keys whose sample mean is below 1/2 (and below 0.7, 0.9), and the minimum.
inline uint32_t uniform_mod_q(Stream& rs) {
  for (;;) {
    uint32_t v;
    rs.bytes((uint8_t*)&v, 4);
    v &= (1u << 23) - 1;
    if (v < (uint32_t)Q) return v;
  }
}

void lean_model_key(const uint8_t master[32], long idx, Key* key) {
  Stream rs;
  rs.init(master, (uint64_t)idx, 0xC000u);
  uint8_t xi[32];
  rs.bytes(xi, 32);
  uint8_t in[34], seeds[128];
  memcpy(in, xi, 32);
  in[32] = (uint8_t)P->k;
  in[33] = (uint8_t)P->l;
  shake256(in, 34, seeds, 128);
  for (int i = 0; i < P->k; i++)
    for (int s = 0; s < P->l; s++)
      for (int j = 0; j < N; j++) key->ahat[i][s][j] = (int32_t)uniform_mod_q(rs);
  uint8_t sd[66];
  memcpy(sd, seeds + 32, 64);
  for (int r = 0; r < P->l + P->k; r++) {
    sd[64] = (uint8_t)(r & 0xff);
    sd[65] = (uint8_t)(r >> 8);
    rej_bounded_poly(sd, r < P->l ? key->s1[r] : key->s2[r - P->l]);
  }
  int32_t s1hat[LMAX][N];
  for (int r = 0; r < P->l; r++) {
    memcpy(s1hat[r], key->s1[r], sizeof s1hat[r]);
    ntt_fast(s1hat[r]);
  }
  for (int i = 0; i < P->k; i++) {
    int32_t t[N];
    for (int j = 0; j < N; j++) {
      int64_t acc = 0;
      for (int s = 0; s < P->l; s++) acc += mont_reduce((int64_t)key->ahat[i][s][j] * s1hat[s][j]);
      t[j] = reduce32((int32_t)acc);
    }
    invntt_tomont(t);
    for (int j = 0; j < N; j++) {
      int32_t r = modq((int64_t)t[j] + key->s2[i][j]);
      int32_t lo = r & ((1 << D) - 1);
      if (lo > (1 << (D - 1))) lo -= 1 << D;
      key->t0[i][j] = lo;
      key->t1[i][j] = (r - lo) >> D;
    }
  }
}

double lowacc_key(const uint8_t master[32], long idx, int M) {
  static thread_local Key* key = nullptr;
  if (!key) key = new Key();
  lean_model_key(master, idx, key);
  Stream rs;
  rs.init(master, (uint64_t)idx, 0xC100u);
  const int m = P->buckets();
  Challenge ch;
  int32_t b[KMAX][N];
  uint8_t w1[KMAX][N];
  double s = 0;
  for (int t = 0; t < M; t++) {
    uniform_challenge(rs, &ch);
    sparse_mul(ch, key->t0, P->k, b);
    for (int i = 0; i < P->k; i++)
      for (int j = 0; j < N; j++) w1[i][j] = (uint8_t)uniform_below(rs, m);
    s += standin_score(b, w1);
  }
  return s / M;
}

int lowacc_run(const uint8_t master[32], long k0, long n, int M, long block) {
  printf("lowacc %s keys %ld..%ld M %d block %ld threads %d\n", P->name, k0, k0 + n, M, block,
         omp_get_max_threads());
  fflush(stdout);
  long tot = 0, c5 = 0, c7 = 0, c9 = 0;
  double mn = 2, sum = 0;
  double t0s = now_s();
  for (long b0 = k0; b0 < k0 + n; b0 += block) {
    long bn = std::min(block, k0 + n - b0);
    long l5 = 0, l7 = 0, l9 = 0;
    double lmn = 2, lsum = 0;
#pragma omp parallel for schedule(dynamic, 4096) reduction(+ : l5, l7, l9, lsum) reduction(min : lmn)
    for (long i = 0; i < bn; i++) {
      double a = lowacc_key(master, b0 + i, M);
      lsum += a;
      if (a < lmn) lmn = a;
      l5 += a < 0.5;
      l7 += a < 0.7;
      l9 += a < 0.9;
    }
    tot += bn; c5 += l5; c7 += l7; c9 += l9; sum += lsum;
    if (lmn < mn) mn = lmn;
    printf("block k0 %ld n %ld below0.5 %ld below0.7 %ld below0.9 %ld min %.6f mean %.6f | total %ld below0.5 %ld below0.7 %ld below0.9 %ld min %.6f secs %.1f\n",
           b0, bn, l5, l7, l9, lmn, lsum / bn, tot, c5, c7, c9, mn, now_s() - t0s);
    fflush(stdout);
  }
  printf("done total %ld below0.5 %ld min %.6f mean %.6f secs %.1f\n", tot, c5, mn, sum / tot,
         now_s() - t0s);
  return 0;
}

int main(int argc, char** argv) {
  // usage: aw_study --param P --seed HEX64 MODE ...
  //   selftest NCH                       (own selftests)
  //   standin ARGS...                    (standin_gap's own modes, e.g. selftest ...)
  //   keys FAM K0 NKEYS REPS NMIN NMAX REL [THETA]
  if (argc >= 6 && !strcmp(argv[5], "standin")) {
    // standin_gap_main --param P --seed S <rest>
    std::vector<char*> av;
    av.push_back(argv[0]);
    for (int i = 1; i < 5; i++) av.push_back(argv[i]);
    for (int i = 6; i < argc; i++) av.push_back(argv[i]);
    return standin_gap_main((int)av.size(), av.data());
  }
  if (argc < 7 || strcmp(argv[1], "--param") || strcmp(argv[3], "--seed")) {
    fprintf(stderr, "usage: aw_study --param {44,65,87} --seed HEX64 {selftest NCH | standin ... | "
                    "keys FAM K0 NKEYS REPS NMIN NMAX REL [THETA]}\n");
    return 2;
  }
  int level = atoi(argv[2]);
  std::string hex = argv[4];
  if (hex.size() != 64) return 2;
  uint8_t master[32];
  for (int b = 0; b < 32; b++) master[b] = (uint8_t)strtol(hex.substr(2 * b, 2).c_str(), nullptr, 16);
  for (const Params& p : kParams)
    if (p.level == level) P = &p;
  if (!P) return 2;
  init_zetas();
  g_shake128 = EVP_MD_fetch(nullptr, "SHAKE128", nullptr);
  g_shake256 = EVP_MD_fetch(nullptr, "SHAKE256", nullptr);
  g_aes = EVP_CIPHER_fetch(nullptr, "AES-256-CTR", nullptr);
  if (!g_shake128 || !g_shake256 || !g_aes) die("fetch");
  memset(aw::g_ones, 1, sizeof aw::g_ones);
  std::string mode = argv[5];
  if (mode == "selftest") return aw::selftest(master, atol(argv[6]));
  if (mode == "lowacc") return lowacc_run(master, atol(argv[6]), atol(argv[7]), atoi(argv[8]), atol(argv[9]));
  if (mode != "keys" || argc < 13) return 2;
  int fam = atoi(argv[6]);
  long k0 = atol(argv[7]), nkeys = atol(argv[8]), reps = atol(argv[9]);
  long nmin = atol(argv[10]), nmax = atol(argv[11]);
  double rel = atof(argv[12]);
  double theta = argc > 13 ? atof(argv[13]) : 0.0;
  if (fam == 4) aw::g_tilt.init(theta);
  printf("run %s fam %d keys %ld..%ld reps %ld nmin %ld nmax %ld rel %g theta %g master %s threads %d\n",
         P->name, fam, k0, k0 + nkeys, reps, nmin, nmax, rel, theta, hex.c_str(),
         omp_get_max_threads());
  fflush(stdout);
  double t = now_s();
  long total = nkeys * reps;
  std::vector<aw::Result> res(total);
#pragma omp parallel for schedule(dynamic, 1)
  for (long w = 0; w < total; w++)
    res[w] = aw::run_key(fam, master, k0 + w / reps, w % reps, nmin, nmax, rel);
  for (const auto& r : res) aw::print_result(r);
  printf("done secs %.1f\n", now_s() - t);
  return 0;
}
