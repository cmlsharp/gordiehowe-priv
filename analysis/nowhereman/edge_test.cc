// Rigorous lower bound on the advantage of the edge-pair test g against every
// key-independent simulator, in the stand-in model after the MLWE hop.
//
// Model.  The device key is t = A s1 + s2 replaced by t uniform on R_q^k (the
// MLWE hop); (t1, t0) = Power2Round(t).  An edge is a coefficient with
// t1 in {0, 1023} (Pr = 8193/q); its sign is + for t1 = 0 (t0 in [0, 4096]) and
// - for t1 = 1023 (t0 in [-4095, 0]).  The observation x = (w1, c~) has the
// stand-in law P_t0 = u * s_t0 / Z_t0 (Signing/Surrogate.lean acceptWeight,
// ChallengeDistinguisher.lean standinScore), u uniform on buckets x hashes,
// c = SampleInBall(c~) (FIPS 204 Algorithm 29, SHAKE256 via OpenSSL).
//
// The test (knows t1 only).  E = {some component has exactly two edges}; on E
// let (j1, j2) be the two edges of the lowest such component kp, rho their sign
// product, A(c) = <c X^j1, c X^j2>; g = -rho * sign A(c), and g = 0 off E.  It
// outputs 1 with probability (1 + g)/2.  For every key-independent Q,
//   Adv(g) = (1/2) (E_t1 E_{P_t1} g - E_Q gbar),  |gbar| <= Pr[E] / 8193^2.
//
// The i.i.d. unit.  A key configuration drawn from the hybrid law conditioned
// on E: t uniform until E holds; then the coefficient t0[kp][j2] is replaced by
// a twin pair (+a_p, -a_m) with r uniform on [0, 4096 * 4097), a_p = r / 4096
// (uniform on 0..4096), a_m = r / 4097 (uniform on 0..4095): the + twin and the
// - twin have exactly the conditional laws given sigma2 = + and sigma2 = -.
// With p+ = 4097/8193, p- = 4096/8193, h = -sigma1 sign A, g+ = h, g- = -h,
//   m = p+ E_{P+} g+ + p- E_{P-} g-   (= E[E_{P_t0} g | all but sigma2]).
// For any constant Zr > 0 and each twin sigma,
//   E_{P_sigma} g = E_u[s_sigma g]/Zr + E_{P_sigma}[g] (Zr - Z_sigma)/Zr      (exact).
// The unit draws x ~ u and, by coupled rejection sampling (common proposals and
// common uniforms), x+* ~ P+ and x-* ~ P- exactly, independent of x, and records
//   Y = { h(x) [ (p+ - p-)(s+(x) - Zr) + p- (s+(x) - s-(x)) ]
//         + p+ h(x+*) (Zr - s+(x)) - p- h(x-*) (Zr - s-(x)) } / Zr.
// Then E Y = E[m | E] - (p+ - p-) E[h(x)], and |(p+ - p-) E h| <= 8193^-2
// because sigma1 is independent of the positions and of c, with E sigma1 = 1/8193.
// No expansion, no pair additivity, no normalizer approximation.
//
// Range.  |Y| <= B = 1 + ((p+ - p-) Zr + p- L) / Zr (Zr >= 1/2), with
// L = min(1, tau * 8192 / (2(gamma2 - beta) - 1)) when tau * 4096 < gamma2 (the
// ct0 check never fails: 65, 87), else L = 1 (44): flipping t0[kp][j2] moves b
// by at most 8191 on tau coordinates, hintCount by at most 8192, and the
// Poisson-binomial CDF is 1-Lipschitz in l1 (partials in [-1, 0]).
//
// Bound (Maurer & Pontil 2009, Theorem 4, applied to (Y + B)/(2B) in [0, 1]):
// with probability >= 1 - delta,
//   E Y >= mean - sqrt(2 V ln(2/delta) / n) - 2B * 7 ln(2/delta) / (3 (n - 1)),
// V the unbiased sample variance.  Then
//   Adv(g) >= (1/2) Pr[E] (LCB - 2 / 8193^2),  Pr[E] exact (edge_test_bound.py).
//
// Reuses standin_gap.cc (primitives, score, its self-tests) by inclusion.
//
// Build: g++ -O3 -march=native -fopenmp -std=c++17 edge_test.cc -lcrypto

#define main standin_gap_main
#include "standin_gap.cc"
#undef main

namespace {

constexpr uint32_t TAG_UNIT = 0xED6E0001u;
constexpr int64_t TWIN_R = 4096LL * 4097LL;

struct Words {
  Stream* rs;
  const uint32_t* w = nullptr;
  int left = 0;
  uint32_t next() {
    if (!left) {
      w = rs->words(1024);
      left = 1024;
    }
    left--;
    return *w++;
  }
  // Exactly uniform on [0, n), n <= 2^31.
  uint32_t below(uint32_t n) {
    uint64_t lim = ((uint64_t)1 << 32) / n * n;
    for (;;) {
      uint32_t v = next();
      if (v < lim) return v % n;
    }
  }
  uint64_t below64(uint64_t n) {  // n < 2^62
    uint64_t lim = (~(uint64_t)0) / n * n;
    for (;;) {
      uint64_t v = ((uint64_t)next() << 32) | next();
      if (v < lim) return v % n;
    }
  }
  uint64_t u64() { return ((uint64_t)next() << 32) | next(); }
};

struct PairKey {
  int32_t t0[KMAX][N];  // + twin: t0[kp][j2] = ap
  int kp, j1, j2, s1, ap, am;
  int edges[KMAX];
  long attempts;
};

// Power2Round, as keygen_fast.
inline void p2r(int32_t r, int32_t* t0, int32_t* t1) {
  int32_t lo = r & ((1 << D) - 1);
  if (lo > (1 << (D - 1))) lo -= 1 << D;
  *t0 = lo;
  *t1 = (r - lo) >> D;
}

void draw_key(Words& W, PairKey* key) {
  int32_t t1[KMAX][N];
  key->attempts = 0;
  for (;;) {
    key->attempts++;
    for (int i = 0; i < P->k; i++) {
      key->edges[i] = 0;
      for (int j = 0; j < N; j++) {
        uint32_t v;
        do v = W.next() & 0x7fffff; while (v >= (uint32_t)Q);
        p2r((int32_t)v, &key->t0[i][j], &t1[i][j]);
        if (t1[i][j] == 0 || t1[i][j] == 1023) key->edges[i]++;
      }
    }
    key->kp = -1;
    for (int i = 0; i < P->k; i++)
      if (key->edges[i] == 2) {
        key->kp = i;
        break;
      }
    if (key->kp >= 0) break;
  }
  int i = key->kp, found = 0;
  for (int j = 0; j < N; j++)
    if (t1[i][j] == 0 || t1[i][j] == 1023) {
      if (found == 0) {
        key->j1 = j;
        key->s1 = t1[i][j] == 0 ? 1 : -1;
      } else
        key->j2 = j;
      found++;
    }
  if (found != 2) die("pair");
  uint64_t r = W.below64(TWIN_R);
  key->ap = (int)(r / 4096);
  key->am = (int)(r / 4097);
  key->t0[i][key->j2] = key->ap;
}

struct Obs {
  uint8_t ct[64];
  uint8_t w1[KMAX][N];  // bucket indices
};

void draw_obs(Words& W, Obs* x) {
  for (int b = 0; b < P->ctilde_bytes(); b += 4) {
    uint32_t v = W.next();
    for (int t = 0; t < 4 && b + t < P->ctilde_bytes(); t++) x->ct[b + t] = (uint8_t)(v >> (8 * t));
  }
  for (int i = 0; i < P->k; i++)
    for (int j = 0; j < N; j++) x->w1[i][j] = (uint8_t)W.below((uint32_t)P->buckets());
}

// Signed column c X^j, dense.
void column(const Challenge& ch, int j, int8_t v[N]) {
  memset(v, 0, N);
  for (int u = 0; u < ch.ntau; u++) {
    int p = ch.pos[u] + j;
    int s = ch.sgn[u];
    if (p >= N) {
      p -= N;
      s = -s;
    }
    v[p] = (int8_t)s;
  }
}

struct Eval {
  double sp, sm;  // s of the + and - twins
  int h;          // -sigma1 sign A
  int A;
};

inline void dp_push(double* dp, int& hi, int32_t bb, int w1, int om, int g2, int be, double inv,
                    bool& zero) {
  int32_t a = bb < 0 ? -bb : bb;
  if (a >= g2) {
    zero = true;
    return;
  }
  int32_t hc = (bb < 0 && w1 != 0) ? (a - be) : (a - be - 1);
  if (hc <= 0) return;
  double p = hc * inv, q1 = 1.0 - p;
  int top = hi < om ? hi + 1 : om;
  for (int c = top; c >= 1; c--) dp[c] = dp[c] * q1 + dp[c - 1] * p;
  dp[0] *= q1;
  hi = top;
}

void evaluate(const PairKey& key, const Obs& x, Eval* e) {
  Challenge ch;
  sample_in_ball(x.ct, &ch);
  int8_t v1[N], v2[N];
  column(ch, key.j1, v1);
  column(ch, key.j2, v2);
  int A = 0;
  for (int i = 0; i < N; i++) A += v1[i] * v2[i];
  e->A = A;
  e->h = -key.s1 * (A > 0 ? 1 : (A < 0 ? -1 : 0));
  int32_t b[KMAX][N];
  sparse_mul(ch, key.t0, P->k, b);
  const int g2 = P->gamma2, be = P->beta, om = P->omega;
  const double inv = 1.0 / (2.0 * (g2 - be) - 1.0);
  alignas(64) double dp[136];
  for (int c = 0; c <= om + 1; c++) dp[c] = 0;
  dp[0] = 1;
  int hi = 0;
  bool zero = false;
  for (int i = 0; i < P->k && !zero; i++)
    for (int j = 0; j < N; j++) {
      if (i == key.kp && v2[j]) continue;
      dp_push(dp, hi, b[i][j], x.w1[i][j], om, g2, be, inv, zero);
      if (zero) break;
    }
  if (zero) {
    e->sp = e->sm = 0;
    return;
  }
  const int d = key.ap + key.am;
  for (int tw = 0; tw < 2; tw++) {
    alignas(64) double q[136];
    memcpy(q, dp, sizeof(double) * (om + 1));
    int hq = hi;
    bool zq = false;
    for (int j = 0; j < N && !zq; j++)
      if (v2[j]) {
        int32_t bb = b[key.kp][j] - (tw ? d * v2[j] : 0);
        dp_push(q, hq, bb, x.w1[key.kp][j], om, g2, be, inv, zq);
      }
    double s = 0;
    if (!zq)
      for (int c = 0; c <= hq; c++) s += q[c];
    (tw ? e->sm : e->sp) = s;
  }
}

struct Run {
  double Zr, pp, pm, B, L;
};

struct UnitOut {
  double Y, main, corr;
  long proposals;
  int diverge;
  long keyatt;
};

thread_local Stream* tl_rs = nullptr;
thread_local PairKey* tl_key = nullptr;

UnitOut run_unit(const Config& cf, const Run& R, uint64_t u) {
  if (!tl_rs) {
    tl_rs = new Stream();
    tl_key = new PairKey();
  }
  Stream& rs = *tl_rs;
  rs.init(cf.master, u, TAG_UNIT);
  Words W{&rs};
  PairKey& key = *tl_key;
  draw_key(W, &key);
  Obs x;
  Eval ex;
  draw_obs(W, &x);
  evaluate(key, x, &ex);
  // coupled rejection sampling of x+* ~ P+ and x-* ~ P-.
  int hp = 0, hm = 0;
  long ip = -1, im = -1, props = 0;
  while (ip < 0 || im < 0) {
    Obs y;
    Eval ey;
    draw_obs(W, &y);
    uint64_t U = W.u64();
    evaluate(key, y, &ey);
    long double Ul = (long double)U * 0x1p-64L;
    if (ip < 0 && Ul < (long double)ey.sp) {
      ip = props;
      hp = ey.h;
    }
    if (im < 0 && Ul < (long double)ey.sm) {
      im = props;
      hm = ey.h;
    }
    props++;
  }
  int div = ip != im;
  const double Zr = R.Zr;
  double main = ex.h * ((R.pp - R.pm) * (ex.sp - Zr) + R.pm * (ex.sp - ex.sm)) / Zr;
  double corr = (R.pp * hp * (Zr - ex.sp) - R.pm * hm * (Zr - ex.sm)) / Zr;
  return UnitOut{main + corr, main, corr, props, div, key.attempts};
}

// ------------------------------------------------------------- self-tests

int edge_selftest(const Config& cf, const Run& R, long n) {
  int fails = 0;
  // 1. Twin coupling marginals, exhaustively.
  {
    std::vector<int> cp(4097, 0), cm(4096, 0);
    long close = 0;
    for (int64_t r = 0; r < TWIN_R; r++) {
      int ap = (int)(r / 4096), am = (int)(r / 4097);
      cp[ap]++;
      cm[am]++;
      if (std::abs(ap - am) <= 1) close++;
    }
    bool ok = true;
    for (int v : cp) ok &= v == 4096;
    for (int v : cm) ok &= v == 4097;
    printf("edge selftest twin marginals exact over all %lld r: %s (|ap-am|<=1 for %.6f)\n",
           (long long)TWIN_R, ok ? "ok" : "FAIL", (double)close / TWIN_R);
    fails += !ok;
  }
  // 2. evaluate() against standin_score (fast) and standin_score_ref (long double, exact NTT),
  //    and A against a dense negacyclic computation.
  long bad = 0, badref = 0, badA = 0, badrange = 0;
  double maxd = 0;
#pragma omp parallel for schedule(dynamic, 16) reduction(+ : bad, badref, badA, badrange)
  for (long t = 0; t < n; t++) {
    Stream rs;
    rs.init(cf.master, 0xfffffffff000ull + t, 0xED6E00FFu);
    Words W{&rs};
    PairKey key;
    draw_key(W, &key);
    Obs x;
    draw_obs(W, &x);
    Eval e;
    evaluate(key, x, &e);
    int32_t t0m[KMAX][N];
    memcpy(t0m, key.t0, sizeof t0m);
    t0m[key.kp][key.j2] = -key.am;
    Challenge ch;
    sample_in_ball(x.ct, &ch);
    int32_t b[KMAX][N];
    sparse_mul(ch, key.t0, P->k, b);
    double s1 = standin_score(b, x.w1);
    sparse_mul(ch, t0m, P->k, b);
    double s2 = standin_score(b, x.w1);
    if (std::fabs(s1 - e.sp) > 1e-12 || std::fabs(s2 - e.sm) > 1e-12) bad++;
    // |s+ - s-| <= L
    if (std::fabs(e.sp - e.sm) > R.L + 1e-12) badrange++;
    if (t % 8 == 0) {
      long double r1 = standin_score_ref(x.ct, key.t0, x.w1);
      long double r2 = standin_score_ref(x.ct, t0m, x.w1);
      if (std::fabs((double)(r1 - e.sp)) > 1e-10 || std::fabs((double)(r2 - e.sm)) > 1e-10) badref++;
    }
    // dense A: c X^j1 and c X^j2 as full negacyclic products with the monomials
    int32_t c[N] = {0}, m1[N] = {0}, m2[N] = {0}, p1[N], p2[N];
    for (int u = 0; u < ch.ntau; u++) c[ch.pos[u]] = modq(ch.sgn[u]);
    m1[key.j1] = 1;
    m2[key.j2] = 1;
    poly_mul_school(c, m1, p1);
    poly_mul_school(c, m2, p2);
    long A = 0;
    for (int i = 0; i < N; i++) A += (long)centered(p1[i]) * centered(p2[i]);
    if (A != e.A) badA++;
  }
  printf("edge selftest %ld keys: fold-DP twins vs standin_score %s, vs standin_score_ref %s, "
         "A vs dense %s, |s+ - s-| <= L=%.4f %s\n",
         n, bad ? "FAIL" : "ok", badref ? "FAIL" : "ok", badA ? "FAIL" : "ok", R.L,
         badrange ? "FAIL" : "ok");
  fails += (bad || badref || badA || badrange);
  (void)maxd;
  // 3. Key sampler: E-acceptance rate and edge frequency (informational).
  {
    Stream rs;
    rs.init(cf.master, 0xfffffffff800ull, 0xED6E00FEu);
    Words W{&rs};
    PairKey key;
    long att = 0, edges = 0, keys = 2000;
    for (long t = 0; t < keys; t++) {
      draw_key(W, &key);
      att += key.attempts;
      for (int i = 0; i < P->k; i++) edges += key.edges[i];
    }
    printf("edge selftest key sampler: %ld E-keys, %.3f attempts per key (expect 1/Pr[E])\n", keys,
           (double)att / keys);
  }
  printf("edge selftest %s\n", fails ? "FAILED" : "PASSED");
  return fails ? 1 : 0;
}

// ------------------------------------------------------------------ driver

int mode_run(const Config& cf, const Run& R, uint64_t u0, uint64_t n, uint64_t block) {
  printf("run edge_test param %s master %s units %llu..%llu block %llu threads %d Zr %.6f B %.6f L %.6f\n",
         P->name, cf.master_hex.c_str(), (unsigned long long)u0, (unsigned long long)(u0 + n),
         (unsigned long long)block, omp_get_max_threads(), R.Zr, R.B, R.L);
  long double S = 0, S2 = 0, Sm = 0, Sc = 0, Sm2 = 0, Sc2 = 0;
  long double props = 0, keyatt = 0;
  uint64_t done = 0, div = 0;
  double maxabs = 0;
  double t0 = now_s();
  for (uint64_t b0 = 0; b0 < n; b0 += block) {
    uint64_t nb = std::min(block, n - b0);
    double s = 0, s2 = 0, sm = 0, sc = 0, sm2 = 0, sc2 = 0, pr = 0, ka = 0, mx = 0;
    uint64_t dv = 0;
#pragma omp parallel for schedule(dynamic, 256) reduction(+ : s, s2, sm, sc, sm2, sc2, pr, ka, dv) \
    reduction(max : mx)
    for (long long i = 0; i < (long long)nb; i++) {
      UnitOut o = run_unit(cf, R, u0 + b0 + i);
      s += o.Y;
      s2 += o.Y * o.Y;
      sm += o.main;
      sm2 += o.main * o.main;
      sc += o.corr;
      sc2 += o.corr * o.corr;
      pr += o.proposals;
      ka += o.keyatt;
      dv += o.diverge;
      double a = std::fabs(o.Y);
      if (a > mx) mx = a;
    }
    S += s;
    S2 += s2;
    Sm += sm;
    Sm2 += sm2;
    Sc += sc;
    Sc2 += sc2;
    props += pr;
    keyatt += ka;
    div += dv;
    if (mx > maxabs) maxabs = mx;
    done += nb;
    long double mean = S / done, var = (S2 - S * S / done) / (done - 1);
    printf("block units %llu sumY %.12Le sumY2 %.12Le mean %.6Le var %.6Le maxabs %.6e "
           "main %.6Le corr %.6Le var_main %.4Le var_corr %.4Le proposals/unit %.6Lf "
           "keyatt/unit %.4Lf diverge %llu elapsed %.1f\n",
           (unsigned long long)done, S, S2, mean, var, maxabs, Sm / done, Sc / done,
           (Sm2 - Sm * Sm / done) / (done - 1), (Sc2 - Sc * Sc / done) / (done - 1),
           props / done, keyatt / done, (unsigned long long)div, now_s() - t0);
    fflush(stdout);
  }
  if (maxabs > R.B) {
    printf("RANGE VIOLATION maxabs %.6e > B %.6e\n", maxabs, R.B);
    return 1;
  }
  return 0;
}

}  // namespace

int main(int argc, char** argv) {
  int level = 65;
  Config cf;
  bool have_seed = false;
  double Zr = -1;
  int i = 1;
  for (; i < argc; i++) {
    if (!strcmp(argv[i], "--param") && i + 1 < argc)
      level = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--zref") && i + 1 < argc)
      Zr = atof(argv[++i]);
    else if (!strcmp(argv[i], "--seed") && i + 1 < argc) {
      cf.master_hex = argv[++i];
      if (cf.master_hex.size() != 64) die("seed");
      for (int b = 0; b < 32; b++)
        cf.master[b] = (uint8_t)strtol(cf.master_hex.substr(2 * b, 2).c_str(), nullptr, 16);
      have_seed = true;
    } else
      break;
  }
  for (const Params& p : kParams)
    if (p.level == level) P = &p;
  if (!P || i >= argc || !have_seed) {
    fprintf(stderr,
            "usage: edge_test --param {44,65,87} --seed HEX64 [--zref Z] MODE ...\n"
            "  selftest NKEYS          (also runs standin_gap's selftest at small sizes)\n"
            "  run U0 NUNITS BLOCK\n");
    return 2;
  }
  if (Zr < 0) Zr = level == 44 ? 0.9856 : (level == 65 ? 0.9962 : 0.9922);
  if (Zr < 0.5 || Zr > 1) die("zref must be in [1/2, 1]");
  init_zetas();
  g_shake128 = EVP_MD_fetch(nullptr, "SHAKE128", nullptr);
  g_shake256 = EVP_MD_fetch(nullptr, "SHAKE256", nullptr);
  g_sigalg = EVP_SIGNATURE_fetch(nullptr, P->name, nullptr);
  g_aes = EVP_CIPHER_fetch(nullptr, "AES-256-CTR", nullptr);
  if (!g_shake128 || !g_shake256 || !g_sigalg || !g_aes) die("fetch");
  Run R;
  R.Zr = Zr;
  R.pp = 4097.0 / 8193.0;
  R.pm = 4096.0 / 8193.0;
  const double Nd = 2.0 * (P->gamma2 - P->beta) - 1.0;
  R.L = ((int64_t)P->tau * 4096 < P->gamma2) ? std::min(1.0, P->tau * 8192.0 / Nd) : 1.0;
  R.B = 1.0 + ((R.pp - R.pm) * Zr + R.pm * R.L) / Zr;
  std::string mode = argv[i++];
  if (mode == "selftest") {
    if (i >= argc) die("selftest NKEYS");
    int f = edge_selftest(cf, R, atol(argv[i]));
    // standin_gap's own self-tests (NTT, keygen vs OpenSSL, score vs ref, hintCount, attempts).
    f |= mode_selftest(cf, 2000, 20, 200, 2000, 20);
    return f;
  }
  if (mode == "run") {
    if (i + 2 >= argc) die("run U0 NUNITS BLOCK");
    return mode_run(cf, R, strtoull(argv[i], nullptr, 10), strtoull(argv[i + 1], nullptr, 10),
                    strtoull(argv[i + 2], nullptr, 10));
  }
  die("mode");
}
