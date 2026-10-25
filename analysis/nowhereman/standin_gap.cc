// Monte Carlo estimate of standinGap (GordieHowe/Applications/MLDSA/Signing/
// ChallengeDistinguisher.lean, section StandIn):
//
//   standinGap = E_{k,k'} E_{(w1,c~) <- P_k} [ s_k(w1,c~) - s_{k'}(w1,c~) ],
//
// k, k' independent uniform 32-byte KeyGen_internal seeds, P_k the law of
// (HighBits(A y), c~) for the first accepted attempt of the idealized FIPS 204
// signer (Signing/Ideal.lean: y uniform on the mask box, c~ uniform and fresh
// in every attempt, the four checks of Algorithm 7), and s_k = standinScore =
// acceptWeight(gamma2, beta, omega) of b = centered(SampleInBall(c~) t0_k) at
// the buckets w1 (Signing/Surrogate.lean).  For every key-independent
// simulator the Lean distinguisher's advantage is standinGap / 2
// (challengeAdvantage_standin_eq).
//
// The i.i.d. unit is one draw of K independent keys k_0..k_{K-1}.  For each
// key i the unit draws M samples x_{i,m} <- P_{k_i} and records
//
//   Z = (1/(K M)) sum_i sum_m [ s_{k_i}(x_{i,m}) - (1/(K-1)) sum_{j != i} s_{k_j}(x_{i,m}) ].
//
// E[Z] = standinGap because every ordered pair (k_i, k_j) of distinct keys is
// an independent uniform pair, and Z lies in [-1, 1] because scores lie in
// [0, 1].  The program also records Z_asym, the same average restricted to
// i = 0, j = 1 (the unsymmetrized estimator, also unbiased and in [-1, 1]).
//
// Modes: selftest, ideal (experiment 1), deployed (experiment 2, OpenSSL
// ML-DSA signatures), uniform (route without signing: x uniform on
// buckets x challenges, records the per-unit plug-in ideal gap), bench.
//
// Randomness: every unit u draws all of its randomness (key seeds, masks,
// challenge hashes, messages) from AES-256-CTR keyed with the 32-byte master
// seed (--seed, hex) with IV = u (8 bytes LE) || tag (4 bytes) || 0^4, so a
// run is reproducible from (master seed, unit range).  The deployed signer's
// own hedging randomness comes from OpenSSL's RAND and is not reproducible.
//
// Build: g++ -O3 -march=native -fopenmp -std=c++17 standin_gap.cc -lcrypto

#include <omp.h>
#include <openssl/core_names.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/params.h>
#include <openssl/rand.h>

#include <algorithm>
#include <atomic>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

namespace {

constexpr int32_t Q = 8380417;
constexpr int D = 13;
constexpr int N = 256;
constexpr int KMAX = 8;
constexpr int LMAX = 7;
constexpr int KEYMAX = 16;

// FIPS 204 Table 1.
struct Params {
  int level;
  const char* name;
  int k, l, tau, eta, gamma1, gamma2, beta, omega, lambda;
  int ctilde_bytes() const { return lambda / 4; }
  int eta_bits() const { return eta == 2 ? 3 : 4; }
  int z_bits() const { return gamma1 == (1 << 17) ? 18 : 20; }
  int w1_bits() const { return gamma2 == (Q - 1) / 88 ? 6 : 4; }
  int pk_bytes() const { return 32 + k * 320; }
  int sk_bytes() const { return 128 + (k + l) * 32 * eta_bits() + k * 416; }
  int sig_bytes() const { return ctilde_bytes() + l * 32 * z_bits() + omega + k; }
  int w1enc_bytes() const { return k * 32 * w1_bits(); }
  int buckets() const { return (Q - 1) / (2 * gamma2); }
};

const Params kParams[3] = {
    {44, "ML-DSA-44", 4, 4, 39, 2, 1 << 17, (Q - 1) / 88, 78, 80, 128},
    {65, "ML-DSA-65", 6, 5, 49, 4, 1 << 19, (Q - 1) / 32, 196, 55, 192},
    {87, "ML-DSA-87", 8, 7, 60, 2, 1 << 19, (Q - 1) / 32, 120, 75, 256},
};

const Params* P = nullptr;

void die(const char* msg) {
  fprintf(stderr, "fatal: %s\n", msg);
  ERR_print_errors_fp(stderr);
  exit(1);
}

EVP_MD* g_shake128 = nullptr;
EVP_MD* g_shake256 = nullptr;
EVP_SIGNATURE* g_sigalg = nullptr;
EVP_CIPHER* g_aes = nullptr;

double now_s() {
  return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count();
}

// ---------------------------------------------------------------- arithmetic

int32_t modq(int64_t a) {
  int64_t r = a % Q;
  if (r < 0) r += Q;
  return (int32_t)r;
}

int32_t centered(int32_t a) {
  a = modq(a);
  return a > Q / 2 ? a - Q : a;
}

int32_t zetas[N];       // zeta^brv8(i) mod q, in [0, q)
int32_t zetas_mont[N];  // zetas[i] * 2^32 mod q, centered

int brv8(int x) {
  int r = 0;
  for (int i = 0; i < 8; i++) r |= ((x >> i) & 1) << (7 - i);
  return r;
}

void init_zetas() {
  for (int i = 0; i < N; i++) {
    int64_t e = brv8(i);
    int64_t r = 1, b = 1753;
    while (e) {
      if (e & 1) r = r * b % Q;
      b = b * b % Q;
      e >>= 1;
    }
    zetas[i] = (int32_t)r;
    zetas_mont[i] = centered((int32_t)(((__int128)r << 32) % Q));
  }
}

// Exact reference NTT (FIPS 204 Algorithms 41, 42), inputs/outputs in [0, q).
void ntt_ref(int32_t w[N]) {
  int m = 0;
  for (int len = 128; len >= 1; len >>= 1)
    for (int start = 0; start < N; start += 2 * len) {
      m++;
      int64_t z = zetas[m];
      for (int j = start; j < start + len; j++) {
        int32_t t = (int32_t)(z * w[j + len] % Q);
        w[j + len] = modq((int64_t)w[j] - t);
        w[j] = modq((int64_t)w[j] + t);
      }
    }
}

void intt_ref(int32_t w[N]) {
  int m = 256;
  for (int len = 1; len < N; len <<= 1)
    for (int start = 0; start < N; start += 2 * len) {
      m--;
      int64_t z = Q - zetas[m];
      for (int j = start; j < start + len; j++) {
        int32_t t = w[j];
        w[j] = modq((int64_t)t + w[j + len]);
        w[j + len] = modq((int64_t)t - w[j + len]);
        w[j + len] = (int32_t)(z * w[j + len] % Q);
      }
    }
  const int64_t f = 8347681;
  for (int j = 0; j < N; j++) w[j] = (int32_t)(f * w[j] % Q);
}

void poly_mul_school(const int32_t a[N], const int32_t b[N], int32_t c[N]) {
  std::vector<int64_t> acc(N, 0);
  for (int i = 0; i < N; i++)
    for (int j = 0; j < N; j++) {
      int64_t p = (int64_t)a[i] * b[j] % Q;
      if (i + j < N)
        acc[i + j] += p;
      else
        acc[i + j - N] -= p;
    }
  for (int i = 0; i < N; i++) c[i] = modq(acc[i]);
}

// Fast Montgomery NTT (CRYSTALS-Dilithium reference arithmetic).
constexpr int32_t QINV = 58728449;  // q^-1 mod 2^32

inline int32_t mont_reduce(int64_t a) {
  int32_t t = (int32_t)((uint32_t)(uint64_t)a * (uint32_t)QINV);
  return (int32_t)((a - (int64_t)t * Q) >> 32);
}

inline int32_t reduce32(int32_t a) {
  int32_t t = (a + (1 << 22)) >> 23;
  return a - t * Q;
}

inline int32_t caddq(int32_t a) { return a + ((a >> 31) & Q); }

// Input |a_i| < 2^20 (or in [0, q)); output |a_i| < 9q.
void ntt_fast(int32_t a[N]) {
  int k = 0;
  for (int len = 128; len > 0; len >>= 1)
    for (int start = 0; start < N; start += 2 * len) {
      int32_t zeta = zetas_mont[++k];
      for (int j = start; j < start + len; ++j) {
        int32_t t = mont_reduce((int64_t)zeta * a[j + len]);
        a[j + len] = a[j] - t;
        a[j] = a[j] + t;
      }
    }
}

// Inverse NTT times 2^32 (Montgomery factor); input |a_i| < q.
void invntt_tomont(int32_t a[N]) {
  const int32_t f = 41978;  // 2^64 / 256 mod q
  int k = 256;
  for (int len = 1; len < N; len <<= 1)
    for (int start = 0; start < N; start += 2 * len) {
      int32_t zeta = -zetas_mont[--k];
      for (int j = start; j < start + len; ++j) {
        int32_t t = a[j];
        a[j] = t + a[j + len];
        a[j + len] = t - a[j + len];
        a[j + len] = mont_reduce((int64_t)zeta * a[j + len]);
      }
    }
  for (int j = 0; j < N; ++j) a[j] = mont_reduce((int64_t)f * a[j]);
}

// FIPS 204 Algorithm 36.
inline void decompose(int32_t rp, int32_t* r1, int32_t* r0) {
  // rp in [0, q).
  int32_t a = 2 * P->gamma2;
  int32_t lo = rp % a;
  if (lo > a / 2) lo -= a;
  if (rp - lo == Q - 1) {
    *r1 = 0;
    *r0 = lo - 1;
  } else {
    *r1 = (rp - lo) / a;
    *r0 = lo;
  }
}

inline int32_t high_bits(int32_t r) {
  int32_t r1, r0;
  decompose(modq(r), &r1, &r0);
  return r1;
}

// FIPS 204 Algorithm 40.
int32_t use_hint(int h, int32_t r) {
  int32_t m = P->buckets();
  int32_t r1, r0;
  decompose(modq(r), &r1, &r0);
  if (h == 1 && r0 > 0) return (r1 + 1) % m;
  if (h == 1 && r0 <= 0) return (r1 - 1 + m) % m;
  return r1;
}

// ------------------------------------------------------------ bit packing

void pack_bits(const uint32_t* v, int count, int bits, uint8_t* out) {
  memset(out, 0, (size_t)count * bits / 8);
  size_t pos = 0;
  for (int i = 0; i < count; i++)
    for (int b = 0; b < bits; b++, pos++)
      if ((v[i] >> b) & 1) out[pos >> 3] |= (uint8_t)(1u << (pos & 7));
}

void unpack_bits(const uint8_t* in, int count, int bits, uint32_t* v) {
  size_t pos = 0;
  for (int i = 0; i < count; i++) {
    uint32_t x = 0;
    for (int b = 0; b < bits; b++, pos++) x |= (uint32_t)((in[pos >> 3] >> (pos & 7)) & 1) << b;
    v[i] = x;
  }
}

void bitpack(const int32_t* w, int bnd_b, int bits, uint8_t* out) {
  uint32_t v[N];
  for (int i = 0; i < N; i++) v[i] = (uint32_t)(bnd_b - w[i]);
  pack_bits(v, N, bits, out);
}

void bitunpack(const uint8_t* in, int bnd_b, int bits, int32_t* w) {
  uint32_t v[N];
  unpack_bits(in, N, bits, v);
  for (int i = 0; i < N; i++) w[i] = bnd_b - (int32_t)v[i];
}

// ----------------------------------------------------------------- hashing

struct Xof {
  EVP_MD_CTX* ctx;
  Xof() : ctx(EVP_MD_CTX_new()) {}
  ~Xof() { EVP_MD_CTX_free(ctx); }
  void init(EVP_MD* md) {
    if (!EVP_DigestInit_ex2(ctx, md, nullptr)) die("DigestInit");
  }
  void absorb(const void* p, size_t n) {
    if (!EVP_DigestUpdate(ctx, p, n)) die("DigestUpdate");
  }
  void squeeze(uint8_t* out, size_t n) {
    if (!EVP_DigestSqueeze(ctx, out, n)) die("DigestSqueeze");
  }
  void final(uint8_t* out, size_t n) {
    if (!EVP_DigestFinalXOF(ctx, out, n)) die("DigestFinalXOF");
  }
};

thread_local Xof* tl_xof = nullptr;
Xof& xof() {
  if (!tl_xof) tl_xof = new Xof();
  return *tl_xof;
}

void shake256(const uint8_t* in, size_t inlen, uint8_t* out, size_t outlen) {
  Xof& x = xof();
  x.init(g_shake256);
  x.absorb(in, inlen);
  x.final(out, outlen);
}

// FIPS 204 Algorithm 29: positions and signs of the tau nonzeros.
struct Challenge {
  int ntau;
  uint8_t pos[64];
  int8_t sgn[64];
};

void sample_in_ball(const uint8_t* ct, Challenge* ch) {
  Xof& x = xof();
  x.init(g_shake256);
  x.absorb(ct, P->ctilde_bytes());
  uint8_t buf[136];
  x.squeeze(buf, sizeof buf);
  uint64_t h = 0;
  for (int i = 0; i < 8; i++) h |= (uint64_t)buf[i] << (8 * i);
  size_t p = 8;
  int8_t c[N];
  memset(c, 0, sizeof c);
  for (int i = N - P->tau; i < N; i++) {
    int j;
    do {
      if (p == sizeof buf) {
        x.squeeze(buf, sizeof buf);
        p = 0;
      }
      j = buf[p++];
    } while (j > i);
    c[i] = c[j];
    c[j] = (int8_t)(1 - 2 * (int)((h >> (i + P->tau - N)) & 1));
  }
  ch->ntau = 0;
  for (int i = 0; i < N; i++)
    if (c[i]) {
      ch->pos[ch->ntau] = (uint8_t)i;
      ch->sgn[ch->ntau] = c[i];
      ch->ntau++;
    }
  if (ch->ntau != P->tau) die("SampleInBall weight");
}

// FIPS 204 Algorithm 30.
void rej_ntt_poly(const uint8_t seed[34], int32_t a[N]) {
  Xof& x = xof();
  x.init(g_shake128);
  x.absorb(seed, 34);
  uint8_t buf[168 * 5];
  x.squeeze(buf, sizeof buf);
  int j = 0;
  size_t len = sizeof buf;
  for (;;) {
    for (size_t p = 0; p + 3 <= len && j < N; p += 3) {
      int32_t z = buf[p] | (buf[p + 1] << 8) | ((buf[p + 2] & 0x7f) << 16);
      if (z < Q) a[j++] = z;
    }
    if (j == N) return;
    x.squeeze(buf, 168);
    len = 168;
  }
}

// FIPS 204 Algorithm 31.
void rej_bounded_poly(const uint8_t seed[66], int32_t a[N]) {
  Xof& x = xof();
  x.init(g_shake256);
  x.absorb(seed, 66);
  uint8_t buf[136];
  int j = 0;
  auto coeff = [](int b, int32_t* out) {
    if (P->eta == 2) {
      if (b < 15) {
        *out = 2 - (b % 5);
        return true;
      }
      return false;
    }
    if (b < 9) {
      *out = 4 - b;
      return true;
    }
    return false;
  };
  while (j < N) {
    x.squeeze(buf, sizeof buf);
    for (int p = 0; p < 136 && j < N; p++) {
      int32_t v;
      if (coeff(buf[p] & 15, &v)) a[j++] = v;
      if (j < N && coeff(buf[p] >> 4, &v)) a[j++] = v;
    }
  }
}

// ------------------------------------------------------------- unit stream

// AES-256-CTR keystream; IV = unit (8 bytes LE) || tag (4 bytes LE) || 0^4.
struct Stream {
  EVP_CIPHER_CTX* ctx = EVP_CIPHER_CTX_new();
  alignas(64) uint8_t buf[16384];
  size_t pos = sizeof buf;
  ~Stream() { EVP_CIPHER_CTX_free(ctx); }
  void init(const uint8_t master[32], uint64_t unit, uint32_t tag) {
    uint8_t iv[16] = {0};
    for (int i = 0; i < 8; i++) iv[i] = (uint8_t)(unit >> (8 * i));
    for (int i = 0; i < 4; i++) iv[8 + i] = (uint8_t)(tag >> (8 * i));
    if (!EVP_EncryptInit_ex2(ctx, g_aes, master, iv, nullptr)) die("aes init");
    pos = sizeof buf;
  }
  void refill() {
    static const uint8_t zero[sizeof buf] = {0};
    int outl = 0;
    if (!EVP_EncryptUpdate(ctx, buf, &outl, zero, sizeof buf) || outl != (int)sizeof buf)
      die("aes update");
    pos = 0;
  }
  void bytes(uint8_t* out, size_t n) {
    while (n) {
      if (pos == sizeof buf) refill();
      size_t m = std::min(n, sizeof buf - pos);
      memcpy(out, buf + pos, m);
      pos += m;
      out += m;
      n -= m;
    }
  }
  // n 32-bit words (n * 4 <= sizeof buf).
  const uint32_t* words(size_t n) {
    size_t nb = 4 * n;
    if (pos + nb > sizeof buf) refill();
    const uint32_t* w = (const uint32_t*)(buf + pos);
    pos += nb;
    return w;
  }
};

// -------------------------------------------------------------- key material

struct Key {
  uint8_t xi[32];
  uint8_t rho[32], kk[32], tr[64];
  int32_t s1[LMAX][N], s2[KMAX][N];  // centered
  int32_t t0[KMAX][N];               // centered, (-2^12, 2^12]
  int32_t t1[KMAX][N];
  int32_t ahat[KMAX][LMAX][N];  // NTT(A), [0, q)
  int32_t t1hat[KMAX][N];       // NTT(t1 2^d), [0, q) (deployed path)
  std::vector<uint8_t> pk, sk;  // OpenSSL encodings (deployed path)
  EVP_PKEY* pkey = nullptr;
};

void expand_a(const uint8_t rho[32], int32_t ahat[KMAX][LMAX][N]) {
  uint8_t seed[34];
  memcpy(seed, rho, 32);
  for (int r = 0; r < P->k; r++)
    for (int s = 0; s < P->l; s++) {
      seed[32] = (uint8_t)s;
      seed[33] = (uint8_t)r;
      rej_ntt_poly(seed, ahat[r][s]);
    }
}

// FIPS 204 KeyGen_internal (Algorithm 6), fast arithmetic.
void keygen_fast(const uint8_t xi[32], Key* key) {
  memcpy(key->xi, xi, 32);
  uint8_t in[34], seeds[128];
  memcpy(in, xi, 32);
  in[32] = (uint8_t)P->k;
  in[33] = (uint8_t)P->l;
  shake256(in, 34, seeds, 128);
  memcpy(key->rho, seeds, 32);
  memcpy(key->kk, seeds + 96, 32);
  expand_a(key->rho, key->ahat);
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

// Reference KeyGen_internal with exact arithmetic, returning pk and sk
// encodings (pkEncode, skEncode) and the decoded t0.
void keygen_ref(const uint8_t xi[32], std::vector<uint8_t>* pk, std::vector<uint8_t>* sk,
                int32_t t0out[KMAX][N]) {
  uint8_t in[34], seeds[128];
  memcpy(in, xi, 32);
  in[32] = (uint8_t)P->k;
  in[33] = (uint8_t)P->l;
  shake256(in, 34, seeds, 128);
  const uint8_t* rho = seeds;
  static thread_local int32_t ahat[KMAX][LMAX][N];
  expand_a(rho, ahat);
  int32_t s1[LMAX][N], s2[KMAX][N], s1hat[LMAX][N];
  uint8_t sd[66];
  memcpy(sd, seeds + 32, 64);
  for (int r = 0; r < P->l + P->k; r++) {
    sd[64] = (uint8_t)(r & 0xff);
    sd[65] = (uint8_t)(r >> 8);
    rej_bounded_poly(sd, r < P->l ? s1[r] : s2[r - P->l]);
  }
  for (int r = 0; r < P->l; r++) {
    for (int j = 0; j < N; j++) s1hat[r][j] = modq(s1[r][j]);
    ntt_ref(s1hat[r]);
  }
  int32_t t1[KMAX][N];
  for (int i = 0; i < P->k; i++) {
    int32_t t[N];
    for (int j = 0; j < N; j++) {
      int64_t acc = 0;
      for (int s = 0; s < P->l; s++) acc += (int64_t)ahat[i][s][j] * s1hat[s][j] % Q;
      t[j] = modq(acc);
    }
    intt_ref(t);
    for (int j = 0; j < N; j++) {
      int32_t r = modq((int64_t)t[j] + s2[i][j]);
      int32_t lo = r & ((1 << D) - 1);
      if (lo > (1 << (D - 1))) lo -= 1 << D;
      t0out[i][j] = lo;
      t1[i][j] = (r - lo) >> D;
    }
  }
  pk->assign(P->pk_bytes(), 0);
  sk->assign(P->sk_bytes(), 0);
  memcpy(pk->data(), rho, 32);
  for (int i = 0; i < P->k; i++) {
    uint32_t v[N];
    for (int j = 0; j < N; j++) v[j] = (uint32_t)t1[i][j];
    pack_bits(v, N, 10, pk->data() + 32 + 320 * i);
  }
  uint8_t tr[64];
  shake256(pk->data(), pk->size(), tr, 64);
  uint8_t* p = sk->data();
  memcpy(p, rho, 32);
  memcpy(p + 32, seeds + 96, 32);
  memcpy(p + 64, tr, 64);
  p += 128;
  int eb = P->eta_bits();
  for (int i = 0; i < P->l; i++, p += 32 * eb) bitpack(s1[i], P->eta, eb, p);
  for (int i = 0; i < P->k; i++, p += 32 * eb) bitpack(s2[i], P->eta, eb, p);
  for (int i = 0; i < P->k; i++, p += 416) bitpack(t0out[i], 1 << (D - 1), D, p);
}

EVP_PKEY* openssl_keygen(const uint8_t xi[32]) {
  EVP_PKEY_CTX* ctx = EVP_PKEY_CTX_new_from_name(nullptr, P->name, nullptr);
  if (!ctx || EVP_PKEY_keygen_init(ctx) <= 0) die("keygen_init");
  OSSL_PARAM params[2];
  params[0] = OSSL_PARAM_construct_octet_string(OSSL_PKEY_PARAM_ML_DSA_SEED, (void*)xi, 32);
  params[1] = OSSL_PARAM_construct_end();
  if (EVP_PKEY_CTX_set_params(ctx, params) <= 0) die("set seed");
  EVP_PKEY* pkey = nullptr;
  if (EVP_PKEY_generate(ctx, &pkey) <= 0) die("generate");
  EVP_PKEY_CTX_free(ctx);
  return pkey;
}

std::vector<uint8_t> get_octets(EVP_PKEY* pkey, const char* name) {
  size_t len = 0;
  if (!EVP_PKEY_get_octet_string_param(pkey, name, nullptr, 0, &len)) die("get param len");
  std::vector<uint8_t> v(len);
  if (!EVP_PKEY_get_octet_string_param(pkey, name, v.data(), len, &len)) die("get param");
  v.resize(len);
  return v;
}

// OpenSSL key from xi; t0, s1, s2, rho, tr, t1 decoded from OpenSSL's encodings
// (skDecode, pkDecode), as in nm_attack.cc.
void load_key_openssl(const uint8_t xi[32], Key* key) {
  if (key->pkey) EVP_PKEY_free(key->pkey);
  memcpy(key->xi, xi, 32);
  key->pkey = openssl_keygen(xi);
  key->pk = get_octets(key->pkey, OSSL_PKEY_PARAM_PUB_KEY);
  key->sk = get_octets(key->pkey, OSSL_PKEY_PARAM_PRIV_KEY);
  if ((int)key->pk.size() != P->pk_bytes() || (int)key->sk.size() != P->sk_bytes())
    die("unexpected key sizes");
  const uint8_t* sk = key->sk.data();
  memcpy(key->rho, sk, 32);
  memcpy(key->kk, sk + 32, 32);
  memcpy(key->tr, sk + 64, 64);
  const uint8_t* p = sk + 128;
  int eb = P->eta_bits();
  for (int i = 0; i < P->l; i++, p += 32 * eb) bitunpack(p, P->eta, eb, key->s1[i]);
  for (int i = 0; i < P->k; i++, p += 32 * eb) bitunpack(p, P->eta, eb, key->s2[i]);
  for (int i = 0; i < P->k; i++, p += 416) bitunpack(p, 1 << (D - 1), D, key->t0[i]);
  const uint8_t* q = key->pk.data() + 32;
  for (int i = 0; i < P->k; i++, q += 320) {
    uint32_t v[N];
    unpack_bits(q, N, 10, v);
    for (int j = 0; j < N; j++) key->t1[i][j] = (int32_t)v[j];
  }
  if (memcmp(key->pk.data(), key->rho, 32)) die("rho mismatch between pk and sk");
  expand_a(key->rho, key->ahat);
  for (int i = 0; i < P->k; i++) {
    for (int j = 0; j < N; j++) key->t1hat[i][j] = modq((int64_t)key->t1[i][j] << D);
    ntt_ref(key->t1hat[i]);
  }
}

// ------------------------------------------------------------ products

// out = c * s over the integers (negacyclic), for `rows` polynomials.
void sparse_mul(const Challenge& ch, const int32_t s[][N], int rows, int32_t out[][N]) {
  for (int i = 0; i < rows; i++) {
    int32_t* o = out[i];
    memset(o, 0, sizeof(int32_t) * N);
    const int32_t* t = s[i];
    for (int u = 0; u < ch.ntau; u++) {
      int p = ch.pos[u];
      if (ch.sgn[u] > 0) {
        for (int j = 0; j < p; j++) o[j] -= t[j - p + N];
        for (int j = p; j < N; j++) o[j] += t[j - p];
      } else {
        for (int j = 0; j < p; j++) o[j] += t[j - p + N];
        for (int j = p; j < N; j++) o[j] -= t[j - p];
      }
    }
  }
}

// ------------------------------------------------------------ the score

// standinScore (ChallengeDistinguisher.lean) = acceptWeight gamma2 beta omega b w1
// (Surrogate.lean): 0 if some |b_i| >= gamma2, else Pr[sum Bernoulli(p_i) <= omega],
// p_i = hintCount(beta, w1_i, b_i) / (2(gamma2 - beta) - 1),
// hintCount = toNat(if b < 0 and r1 != 0 then -b - beta else |b| - beta - 1).
double standin_score(const int32_t b[][N], const uint8_t w1[][N]) {
  const int g2 = P->gamma2, be = P->beta, om = P->omega;
  const double inv = 1.0 / (2.0 * (g2 - be) - 1.0);
  alignas(64) double bufa[136], bufb[136];
  double* dp = bufa;
  double* nd = bufb;
  for (int c = 0; c <= om + 1; c++) dp[c] = nd[c] = 0;
  dp[0] = 1;
  int hi = 0;  // dp[c] == 0 for c > hi
  for (int i = 0; i < P->k; i++)
    for (int j = 0; j < N; j++) {
      int32_t bb = b[i][j];
      int32_t a = bb < 0 ? -bb : bb;
      if (a >= g2) return 0.0;
      int32_t hc = (bb < 0 && w1[i][j] != 0) ? (a - be) : (a - be - 1);
      if (hc <= 0) continue;
      double p = hc * inv, q1 = 1.0 - p;
      int top = hi < om ? hi + 1 : om;
      nd[0] = dp[0] * q1;
      for (int c = 1; c <= top; c++) nd[c] = dp[c] * q1 + dp[c - 1] * p;
      hi = top;
      std::swap(dp, nd);
    }
  double s = 0;
  for (int c = 0; c <= hi; c++) s += dp[c];
  return s;
}

// Slow reference: long double, every coordinate, hint count from the Lean formula
// with an explicit toNat, b from the exact NTT product mod q, centered.
long double standin_score_ref(const uint8_t* ct, const int32_t t0[][N], const uint8_t w1[][N]) {
  Challenge ch;
  sample_in_ball(ct, &ch);
  int32_t c[N] = {0};
  for (int t = 0; t < ch.ntau; t++) c[ch.pos[t]] = modq(ch.sgn[t]);
  ntt_ref(c);
  std::vector<long double> dp(P->omega + 1, 0.0L);
  dp[0] = 1;
  bool ok = true;
  for (int i = 0; i < P->k; i++) {
    int32_t t[N];
    for (int j = 0; j < N; j++) t[j] = modq(t0[i][j]);
    ntt_ref(t);
    for (int j = 0; j < N; j++) t[j] = (int32_t)((int64_t)t[j] * c[j] % Q);
    intt_ref(t);
    for (int j = 0; j < N; j++) {
      int64_t bb = centered(t[j]);
      int64_t a = bb < 0 ? -bb : bb;
      if (a >= P->gamma2) ok = false;
      int64_t v = (bb < 0 && w1[i][j] != 0) ? (-bb - P->beta) : (a - P->beta - 1);
      int64_t hc = v < 0 ? 0 : v;
      long double p = (long double)hc / (long double)(2 * (P->gamma2 - P->beta) - 1);
      for (int cc = P->omega; cc >= 1; cc--) dp[cc] = dp[cc] * (1 - p) + dp[cc - 1] * p;
      dp[0] *= (1 - p);
    }
  }
  if (!ok) return 0.0L;
  long double s = 0;
  for (long double x : dp) s += x;
  return s;
}

// nm_attack.cc's alpha_score (copied verbatim): standinScore at all-zero buckets.
double alpha_score(const Challenge& ch, const int32_t t0[KMAX][N]) {
  int32_t b[KMAX][N];
  sparse_mul(ch, t0, P->k, b);
  const double denom = 2.0 * (P->gamma2 - P->beta) - 1.0;
  double dp[128];
  int om = P->omega;
  for (int c = 0; c <= om; c++) dp[c] = 0;
  dp[0] = 1;
  for (int i = 0; i < P->k; i++)
    for (int j = 0; j < N; j++) {
      int32_t a = b[i][j] < 0 ? -b[i][j] : b[i][j];
      if (a >= P->gamma2) return 0.0;
      if (a <= P->beta + 1) continue;
      double p = (a - P->beta - 1) / denom;
      double q1 = 1.0 - p;
      for (int c = om; c >= 1; c--) dp[c] = dp[c] * q1 + dp[c - 1] * p;
      dp[0] *= q1;
    }
  double s = 0;
  for (int c = 0; c <= om; c++) s += dp[c];
  return s;
}

// ------------------------------------------------------- idealized signer

struct Sample {
  uint8_t ct[64];
  Challenge ch;
  uint8_t w1[KMAX][N];
  int32_t b[KMAX][N];  // c t0 of the signing key (centered integers)
};

struct AttemptStats {
  long attempts = 0, zpass = 0, r0pass = 0, ct0pass = 0;
};

// One attempt of FIPS 204 Algorithm 7 (lines 11-30) with mask y (centered
// coefficients) and challenge hash ct given: Ideal.lean idealAttempt / signAccept.
// On acceptance fills out->w1 = HighBits(A y) and out->b = c t0.
bool attempt_fast(const Key& key, const int32_t y[][N], const uint8_t* ct, Sample* out,
                  AttemptStats* st) {
  const int k = P->k, l = P->l;
  st->attempts++;
  Challenge& ch = out->ch;
  sample_in_ball(ct, &ch);
  // z-check: ||y + c s1|| < gamma1 - beta.
  int32_t cs[KMAX][N];
  const int32_t zb = P->gamma1 - P->beta;
  sparse_mul(ch, key.s1, l, cs);
  for (int i = 0; i < l; i++) {
    int bad = 0;
    for (int j = 0; j < N; j++) {
      int32_t z = y[i][j] + cs[i][j];
      bad |= (z >= zb) | (z <= -zb);
    }
    if (bad) return false;
  }
  st->zpass++;
  // w = A y.
  int32_t yhat[LMAX][N];
  for (int i = 0; i < l; i++) {
    memcpy(yhat[i], y[i], sizeof yhat[i]);
    ntt_fast(yhat[i]);
  }
  int32_t w[KMAX][N];
  for (int i = 0; i < k; i++) {
    for (int j = 0; j < N; j++) {
      int64_t acc = 0;
      for (int s = 0; s < l; s++) acc += mont_reduce((int64_t)key.ahat[i][s][j] * yhat[s][j]);
      w[i][j] = reduce32((int32_t)acc);
    }
    invntt_tomont(w[i]);
    for (int j = 0; j < N; j++) w[i][j] = caddq(reduce32(w[i][j]));
  }
  // r0-check: ||LowBits(w - c s2)|| < gamma2 - beta.
  sparse_mul(ch, key.s2, k, cs);
  const int32_t rb = P->gamma2 - P->beta;
  int32_t r[KMAX][N];
  for (int i = 0; i < k; i++)
    for (int j = 0; j < N; j++) {
      int32_t v = w[i][j] - cs[i][j];
      v += (v >> 31) & Q;
      v -= Q;
      v += (v >> 31) & Q;
      r[i][j] = v;
      int32_t r1, r0;
      decompose(v, &r1, &r0);
      if (r0 >= rb || r0 <= -rb) return false;
    }
  st->r0pass++;
  // ct0-check: ||c t0|| < gamma2.
  sparse_mul(ch, key.t0, k, out->b);
  for (int i = 0; i < k; i++)
    for (int j = 0; j < N; j++) {
      int32_t a = out->b[i][j];
      if (a >= P->gamma2 || a <= -P->gamma2) return false;
    }
  st->ct0pass++;
  // Hint check: h = MakeHint(-ct0, w - cs2 + ct0) = [HighBits(w - cs2) != HighBits(w - cs2 + ct0)].
  int cnt = 0;
  for (int i = 0; i < k; i++)
    for (int j = 0; j < N; j++) {
      int32_t a1 = high_bits(r[i][j]);
      int32_t a2 = high_bits(r[i][j] + out->b[i][j]);
      cnt += a1 != a2;
    }
  if (cnt > P->omega) return false;
  for (int i = 0; i < k; i++)
    for (int j = 0; j < N; j++) {
      int32_t hw = high_bits(w[i][j]);
      // Ideal.lean highBitsVec_sub_eq_of_isSome: HighBits(w - cs2) = HighBits(w).
      if (hw != high_bits(r[i][j])) die("HighBits(w - cs2) != HighBits(w) on acceptance");
      out->w1[i][j] = (uint8_t)hw;
    }
  memcpy(out->ct, ct, P->ctilde_bytes());
  return true;
}

// Independent slow attempt: exact arithmetic, straightforward FIPS 204 steps.
// Returns acceptance and HighBits(A y).
bool attempt_ref(const Key& key, const int32_t y[][N], const uint8_t* ct, uint8_t w1[][N]) {
  const int k = P->k, l = P->l;
  Challenge ch;
  sample_in_ball(ct, &ch);
  int32_t c[N] = {0};
  for (int t = 0; t < ch.ntau; t++) c[ch.pos[t]] = modq(ch.sgn[t]);
  auto mul = [&](const int32_t* a, int32_t* o) {  // o = c * a mod q
    int32_t x[N];
    for (int j = 0; j < N; j++) x[j] = modq(a[j]);
    poly_mul_school(c, x, o);
  };
  bool ok = true;
  for (int i = 0; i < l; i++) {
    int32_t cs1[N];
    mul(key.s1[i], cs1);
    for (int j = 0; j < N; j++) {
      int32_t z = centered((int32_t)modq((int64_t)y[i][j] + cs1[j]));
      if (std::abs(z) >= P->gamma1 - P->beta) ok = false;
    }
  }
  int32_t yh[LMAX][N];
  for (int i = 0; i < l; i++) {
    for (int j = 0; j < N; j++) yh[i][j] = modq(y[i][j]);
    ntt_ref(yh[i]);
  }
  int cnt = 0;
  for (int i = 0; i < k; i++) {
    int32_t w[N];
    for (int j = 0; j < N; j++) {
      int64_t acc = 0;
      for (int s = 0; s < l; s++) acc += (int64_t)key.ahat[i][s][j] * yh[s][j] % Q;
      w[j] = modq(acc);
    }
    intt_ref(w);
    int32_t cs2[N], ct0[N];
    mul(key.s2[i], cs2);
    mul(key.t0[i], ct0);
    for (int j = 0; j < N; j++) {
      w1[i][j] = (uint8_t)high_bits(w[j]);
      int32_t r = modq((int64_t)w[j] - cs2[j]);
      int32_t r1, r0;
      decompose(r, &r1, &r0);
      if (std::abs(r0) >= P->gamma2 - P->beta) ok = false;
      if (std::abs(centered(ct0[j])) >= P->gamma2) ok = false;
      // MakeHint(z, r') = [HighBits(r') != HighBits(r' + z)], z = -ct0, r' = w - cs2 + ct0.
      int32_t rp = modq((int64_t)r + ct0[j]);
      int32_t zz = modq(-(int64_t)ct0[j]);
      if (high_bits(rp) != high_bits(modq((int64_t)rp + zz))) cnt++;
    }
  }
  if (cnt > P->omega) ok = false;
  return ok;
}

struct Masks {
  int32_t y[LMAX][N];
};

void draw_mask(Stream& rs, Masks* m) {
  const uint32_t mask = 2u * P->gamma1 - 1;
  for (int i = 0; i < P->l; i++) {
    const uint32_t* w = rs.words(N);
    for (int j = 0; j < N; j++) m->y[i][j] = P->gamma1 - (int32_t)(w[j] & mask);
  }
}

// The first accepted attempt of the idealized signer under `key`.
void sample_ideal(const Key& key, Stream& rs, Sample* out, AttemptStats* st) {
  Masks m;
  uint8_t ct[64];
  for (;;) {
    draw_mask(rs, &m);
    rs.bytes(ct, P->ctilde_bytes());
    if (attempt_fast(key, m.y, ct, out, st)) return;
  }
}

// ---------------------------------------------------------- deployed signer

struct Signer {
  EVP_PKEY_CTX* sctx = nullptr;
  EVP_PKEY_CTX* vctx = nullptr;
  void bind(EVP_PKEY* pkey) {
    release();
    sctx = EVP_PKEY_CTX_new_from_pkey(nullptr, pkey, nullptr);
    vctx = EVP_PKEY_CTX_new_from_pkey(nullptr, pkey, nullptr);
    if (!sctx || !vctx) die("ctx");
  }
  void release() {
    EVP_PKEY_CTX_free(sctx);
    EVP_PKEY_CTX_free(vctx);
    sctx = vctx = nullptr;
  }
  ~Signer() { release(); }
  void sign(const uint8_t* m, size_t mlen, uint8_t* sig) {
    if (EVP_PKEY_sign_message_init(sctx, g_sigalg, nullptr) <= 0) die("sign init");
    size_t siglen = P->sig_bytes();
    if (EVP_PKEY_sign(sctx, sig, &siglen, m, mlen) <= 0) die("sign");
    if ((int)siglen != P->sig_bytes()) die("sig length");
  }
  bool verify(const uint8_t* m, size_t mlen, const uint8_t* sig) {
    if (EVP_PKEY_verify_message_init(vctx, g_sigalg, nullptr) <= 0) die("verify init");
    return EVP_PKEY_verify(vctx, sig, P->sig_bytes(), m, mlen) == 1;
  }
};

void w1_encode(const uint8_t w1[][N], uint8_t* out) {
  int bits = P->w1_bits();
  for (int i = 0; i < P->k; i++) {
    uint32_t v[N];
    for (int j = 0; j < N; j++) v[j] = w1[i][j];
    pack_bits(v, N, bits, out + i * 32 * bits);
  }
}

// (mu, w1) of a real presentation, as nm_attack.cc real_presentation:
// w1 = UseHint(h, A z - c t1 2^d).  Returns false on a decoding failure.
bool recover_w1(const Key& key, const uint8_t* m, size_t mlen, const uint8_t* sig,
                uint8_t mu[64], uint8_t w1[][N]) {
  uint8_t buf[64 + 2 + 64];
  memcpy(buf, key.tr, 64);
  buf[64] = 0;
  buf[65] = 0;
  memcpy(buf + 66, m, mlen);
  shake256(buf, 66 + mlen, mu, 64);
  const uint8_t* ct = sig;
  const uint8_t* zp = sig + P->ctilde_bytes();
  const uint8_t* hp = zp + P->l * 32 * P->z_bits();
  int32_t zhat[LMAX][N];
  for (int i = 0; i < P->l; i++) {
    bitunpack(zp + i * 32 * P->z_bits(), P->gamma1, P->z_bits(), zhat[i]);
    for (int j = 0; j < N; j++) {
      int32_t z = zhat[i][j];
      if (z >= P->gamma1 - P->beta || z <= -(P->gamma1 - P->beta)) return false;
      zhat[i][j] = modq(z);
    }
    ntt_ref(zhat[i]);
  }
  uint8_t h[KMAX][N];
  memset(h, 0, sizeof h);
  int idx = 0;
  for (int i = 0; i < P->k; i++) {
    int end = hp[P->omega + i];
    if (end < idx || end > P->omega) return false;
    int first = idx;
    while (idx < end) {
      if (idx > first && hp[idx - 1] >= hp[idx]) return false;
      h[i][hp[idx]] = 1;
      idx++;
    }
  }
  for (int i = idx; i < P->omega; i++)
    if (hp[i]) return false;
  Challenge ch;
  sample_in_ball(ct, &ch);
  int32_t chat[N];
  memset(chat, 0, sizeof chat);
  for (int t = 0; t < ch.ntau; t++) chat[ch.pos[t]] = modq(ch.sgn[t]);
  ntt_ref(chat);
  for (int i = 0; i < P->k; i++) {
    int32_t w[N];
    for (int j = 0; j < N; j++) {
      int64_t acc = 0;
      for (int s = 0; s < P->l; s++) acc += (int64_t)key.ahat[i][s][j] * zhat[s][j] % Q;
      acc -= (int64_t)chat[j] * key.t1hat[i][j] % Q;
      w[j] = modq(acc);
    }
    intt_ref(w);
    for (int j = 0; j < N; j++) w1[i][j] = (uint8_t)use_hint(h[i][j], w[j]);
  }
  return true;
}

// ------------------------------------------------------------------ units

struct Config {
  int K = 2;
  int M = 1;
  uint8_t master[32];
  std::string master_hex;
};

struct UnitResult {
  double z, zasym;
  double own;    // mean s_{k_i}(x_i) over the unit
  double other;  // mean s_{k_j}(x_i), j != i
  long attempts;
  long mismatch;
};

thread_local Key* tl_keys = nullptr;
thread_local Stream* tl_stream = nullptr;
thread_local Signer* tl_signers = nullptr;

void unit_keys(Stream& rs, int K, bool openssl, Key* keys) {
  for (int i = 0; i < K; i++) {
    uint8_t xi[32];
    rs.bytes(xi, 32);
    if (openssl)
      load_key_openssl(xi, &keys[i]);
    else
      keygen_fast(xi, &keys[i]);
  }
}

// mode 0: ideal, 1: deployed.
UnitResult run_unit(const Config& cf, uint64_t u, int mode) {
  if (!tl_keys) {
    tl_keys = new Key[KEYMAX];
    tl_stream = new Stream();
    tl_signers = new Signer[KEYMAX];
  }
  Key* keys = tl_keys;
  Stream& rs = *tl_stream;
  rs.init(cf.master, u, (uint32_t)mode);
  const int K = cf.K, M = cf.M;
  unit_keys(rs, K, mode == 1, keys);
  if (mode == 1)
    for (int i = 0; i < K; i++) tl_signers[i].bind(keys[i].pkey);
  UnitResult r{};
  double sum = 0, own = 0, other = 0, asym = 0;
  AttemptStats st;
  Sample smp;
  std::vector<uint8_t> sig(P->sig_bytes());
  for (int i = 0; i < K; i++)
    for (int m = 0; m < M; m++) {
      if (mode == 0) {
        sample_ideal(keys[i], rs, &smp, &st);
      } else {
        uint8_t msg[32], mu[64], ct[64];
        rs.bytes(msg, 32);
        tl_signers[i].sign(msg, 32, sig.data());
        if (!tl_signers[i].verify(msg, 32, sig.data())) die("OpenSSL verify failed");
        if (!recover_w1(keys[i], msg, 32, sig.data(), mu, smp.w1)) die("decode failed");
        uint8_t buf[64 + 8 * 32 * 6];
        memcpy(buf, mu, 64);
        w1_encode(smp.w1, buf + 64);
        shake256(buf, 64 + P->w1enc_bytes(), ct, P->ctilde_bytes());
        if (memcmp(ct, sig.data(), P->ctilde_bytes())) r.mismatch++;
        memcpy(smp.ct, sig.data(), P->ctilde_bytes());
        sample_in_ball(smp.ct, &smp.ch);
        sparse_mul(smp.ch, keys[i].t0, P->k, smp.b);
        st.attempts++;
      }
      double si = standin_score(smp.b, smp.w1);
      double so = 0, s01 = 0;
      int32_t bj[KMAX][N];
      for (int j = 0; j < K; j++) {
        if (j == i) continue;
        sparse_mul(smp.ch, keys[j].t0, P->k, bj);
        double sj = standin_score(bj, smp.w1);
        so += sj;
        if (i == 0 && j == 1) s01 = sj;
      }
      so /= (K - 1);
      sum += si - so;
      own += si;
      other += so;
      if (i == 0) asym += si - s01;
    }
  r.z = sum / (K * M);
  r.zasym = asym / M;
  r.own = own / (K * M);
  r.other = other / (K * M);
  r.attempts = st.attempts;
  return r;
}

// Route without signing: x = (w1, c~) uniform on buckets x challenge hashes,
// R draws per unit, K = 2 keys.  Records the plug-in ideal gap
// 1/2 E_u[(s0 - s1)(s0/abar0 - s1/abar1)] with abar estimated from the same draws,
// and the moments needed to study it.
struct UniformResult {
  double abar0, abar1, g_plugin, e_d2, e_dd;
};

UniformResult run_uniform_unit(const Config& cf, uint64_t u, long R) {
  if (!tl_keys) {
    tl_keys = new Key[KEYMAX];
    tl_stream = new Stream();
    tl_signers = new Signer[KEYMAX];
  }
  Key* keys = tl_keys;
  Stream& rs = *tl_stream;
  rs.init(cf.master, u, 2);
  unit_keys(rs, 2, false, keys);
  double s0s = 0, s1s = 0, s00 = 0, s11 = 0, s01 = 0;
  Sample smp;
  const int m = P->buckets();
  for (long t = 0; t < R; t++) {
    rs.bytes(smp.ct, P->ctilde_bytes());
    sample_in_ball(smp.ct, &smp.ch);
    for (int i = 0; i < P->k; i++) {
      uint32_t w[N];
      memcpy(w, rs.words(N), sizeof w);
      // Uniform bucket by rejection from 32-bit words (unbiased).
      for (int j = 0; j < N; j++) {
        uint64_t x = w[j];
        const uint64_t lim = 0x100000000ull / m * m;
        while (x >= lim) {
          uint32_t v;
          rs.bytes((uint8_t*)&v, 4);
          x = v;
        }
        smp.w1[i][j] = (uint8_t)(x % m);
      }
    }
    int32_t b0[KMAX][N], b1[KMAX][N];
    sparse_mul(smp.ch, keys[0].t0, P->k, b0);
    sparse_mul(smp.ch, keys[1].t0, P->k, b1);
    double a = standin_score(b0, smp.w1), b = standin_score(b1, smp.w1);
    s0s += a;
    s1s += b;
    s00 += a * a;
    s11 += b * b;
    s01 += a * b;
  }
  UniformResult r{};
  r.abar0 = s0s / R;
  r.abar1 = s1s / R;
  double e00 = s00 / R, e11 = s11 / R, e01 = s01 / R;
  // 1/2 [E(s0^2)/a0 - E(s0 s1)/a0 - E(s0 s1)/a1 + E(s1^2)/a1]
  r.g_plugin = 0.5 * ((e00 - e01) / r.abar0 + (e11 - e01) / r.abar1);
  r.e_d2 = e00 - 2 * e01 + e11;
  r.e_dd = r.abar0 - r.abar1;
  return r;
}

// Welford accumulator with Chan merge.
struct Acc {
  double n = 0, mean = 0, m2 = 0;
  void add(double x) {
    n += 1;
    double d = x - mean;
    mean += d / n;
    m2 += d * (x - mean);
  }
};

int mode_units(const Config& cf, int mode, uint64_t u0, uint64_t nunits, uint64_t block) {
  printf("run mode %s param %s K %d M %d master %s units %llu..%llu block %llu threads %d\n",
         mode == 0 ? "ideal" : "deployed", P->name, cf.K, cf.M, cf.master_hex.c_str(),
         (unsigned long long)u0, (unsigned long long)(u0 + nunits), (unsigned long long)block,
         omp_get_max_threads());
  fflush(stdout);
  std::vector<UnitResult> res(block);
  double t_start = now_s();
  for (uint64_t b0 = 0; b0 < nunits; b0 += block) {
    uint64_t nb = std::min(block, nunits - b0);
    double tb = now_s();
#pragma omp parallel for schedule(dynamic, 16)
    for (long long i = 0; i < (long long)nb; i++) res[i] = run_unit(cf, u0 + b0 + i, mode);
    Acc z, za;
    double own = 0, other = 0;
    long att = 0, mism = 0;
    for (uint64_t i = 0; i < nb; i++) {
      z.add(res[i].z);
      za.add(res[i].zasym);
      own += res[i].own;
      other += res[i].other;
      att += res[i].attempts;
      mism += res[i].mismatch;
    }
    printf("block u0 %llu n %llu z_mean %.17g z_m2 %.17g za_mean %.17g za_m2 %.17g "
           "own %.17g other %.17g attempts %ld mismatch %ld secs %.2f\n",
           (unsigned long long)(u0 + b0), (unsigned long long)nb, z.mean, z.m2, za.mean, za.m2,
           own / nb, other / nb, att, mism, now_s() - tb);
    fflush(stdout);
  }
  printf("done secs %.1f\n", now_s() - t_start);
  return 0;
}

int mode_uniform(const Config& cf, uint64_t u0, uint64_t nunits, long R) {
  printf("run mode uniform param %s master %s units %llu..%llu R %ld threads %d\n", P->name,
         cf.master_hex.c_str(), (unsigned long long)u0, (unsigned long long)(u0 + nunits), R,
         omp_get_max_threads());
  std::vector<UniformResult> res(nunits);
  double t = now_s();
#pragma omp parallel for schedule(dynamic, 1)
  for (long long i = 0; i < (long long)nunits; i++) res[i] = run_uniform_unit(cf, u0 + i, R);
  for (uint64_t i = 0; i < nunits; i++)
    printf("uunit %llu abar0 %.12f abar1 %.12f g_plugin %.6e e_d2 %.6e dabar %.6e\n",
           (unsigned long long)(u0 + i), res[i].abar0, res[i].abar1, res[i].g_plugin, res[i].e_d2,
           res[i].e_dd);
  printf("done secs %.1f\n", now_s() - t);
  return 0;
}

// ---------------------------------------------------------------- selftest

int mode_selftest(const Config& cf, long nscore, long nkey, long natt, long nhint, long nsig) {
  int fails = 0;
  Stream rs;
  rs.init(cf.master, 0xffffffffffffull, 99);
  // 1. Fast NTT product against schoolbook.
  for (int rep = 0; rep < 200; rep++) {
    int32_t a[N], b[N], c1[N], ah[N], bh[N], c2[N];
    const uint32_t* w = rs.words(2 * N);
    for (int j = 0; j < N; j++) {
      a[j] = (int32_t)(w[j] % Q);
      b[j] = (int32_t)(w[N + j] % Q);
    }
    poly_mul_school(a, b, c1);
    // Small signed input for one operand, as for y.
    if (rep & 1)
      for (int j = 0; j < N; j++) b[j] = (int32_t)(w[N + j] & ((1 << 20) - 1)) - (1 << 19);
    if (rep & 1) {
      int32_t bm[N];
      for (int j = 0; j < N; j++) bm[j] = modq(b[j]);
      poly_mul_school(a, bm, c1);
    }
    memcpy(ah, a, sizeof a);
    memcpy(bh, b, sizeof b);
    ntt_fast(ah);
    ntt_fast(bh);
    for (int j = 0; j < N; j++) {
      ah[j] = reduce32(ah[j]);
      c2[j] = mont_reduce((int64_t)ah[j] * bh[j]);
    }
    invntt_tomont(c2);
    for (int j = 0; j < N; j++) c2[j] = modq(c2[j]);
    if (memcmp(c1, c2, sizeof c1)) {
      fails++;
      printf("selftest FAIL fast NTT product rep %d\n", rep);
      break;
    }
  }
  printf("selftest ntt_fast 200 products vs schoolbook: %s\n", fails ? "FAIL" : "ok");
  // 2. Keygen: fast, reference and OpenSSL agree.
  long kbad = 0;
#pragma omp parallel for schedule(dynamic, 1) reduction(+ : kbad)
  for (long t = 0; t < nkey; t++) {
    Stream s2;
    s2.init(cf.master, 0xfffffffffff0ull + 0, (uint32_t)(1000 + t));
    uint8_t xi[32];
    s2.bytes(xi, 32);
    if (t < 8) {
      memset(xi, 0, 32);
      for (int i = 0; i < 4; i++) xi[i] = (uint8_t)(t >> (8 * i));
    }
    Key* kf = new Key();
    Key* ko = new Key();
    keygen_fast(xi, kf);
    load_key_openssl(xi, ko);
    std::vector<uint8_t> pk, sk;
    int32_t t0r[KMAX][N];
    keygen_ref(xi, &pk, &sk, t0r);
    bool ok = pk == ko->pk && sk == ko->sk;
    for (int i = 0; i < P->k; i++)
      for (int j = 0; j < N; j++) {
        ok &= kf->t0[i][j] == ko->t0[i][j] && t0r[i][j] == ko->t0[i][j];
        ok &= kf->t1[i][j] == ko->t1[i][j];
        ok &= ko->t0[i][j] > -(1 << (D - 1)) && ko->t0[i][j] <= (1 << (D - 1));
        ok &= kf->s2[i][j] == ko->s2[i][j];
      }
    for (int i = 0; i < P->l; i++) ok &= !memcmp(kf->s1[i], ko->s1[i], sizeof kf->s1[i]);
    ok &= !memcmp(kf->ahat, ko->ahat, sizeof kf->ahat);
    if (!ok) kbad++;
    EVP_PKEY_free(ko->pkey);
    delete kf;
    delete ko;
  }
  fails += kbad != 0;
  printf("selftest keygen %ld seeds (8 index seeds + random): own fast KeyGen t0/t1/s1/s2/A, own "
         "exact KeyGen pk/sk/t0 and OpenSSL pk/sk agree; mismatches %ld\n",
         nkey, kbad);
  // Shared key for the next checks.
  Key* key = new Key();
  Key* key2 = new Key();
  {
    uint8_t xi[32];
    rs.bytes(xi, 32);
    keygen_fast(xi, key);
    rs.bytes(xi, 32);
    keygen_fast(xi, key2);
  }
  // 3. Score: fast vs slow reference at random w1, at accepted samples, and
  //    alpha_score at all-zero buckets.
  long sbad = 0, abad = 0;
  double maxd = 0, maxa = 0;
  const int m = P->buckets();
  for (long t = 0; t < nscore; t++) {
    Sample smp;
    AttemptStats st;
    const Key& kk = (t & 1) ? *key2 : *key;
    if (t % 4 < 2) {
      sample_ideal(kk, rs, &smp, &st);
    } else {
      rs.bytes(smp.ct, P->ctilde_bytes());
      sample_in_ball(smp.ct, &smp.ch);
      const uint32_t* w = rs.words(KMAX * N);
      for (int i = 0; i < P->k; i++)
        for (int j = 0; j < N; j++) {
          // Mix all-zero, edge (0, m-1) and uniform buckets.
          uint32_t v = w[i * N + j];
          smp.w1[i][j] = (uint8_t)(t % 8 == 2 ? 0 : (v & 1 ? v % m : ((v >> 1) & 1 ? m - 1 : 0)));
        }
      sparse_mul(smp.ch, kk.t0, P->k, smp.b);
    }
    double f = standin_score(smp.b, smp.w1);
    long double sr = standin_score_ref(smp.ct, kk.t0, smp.w1);
    double d = fabs((double)(f - sr));
    maxd = std::max(maxd, d);
    if (d > 1e-12) sbad++;
    // Score of the other key at the same x, via the slow path too.
    int32_t b2[KMAX][N];
    const Key& ko = (t & 1) ? *key : *key2;
    sparse_mul(smp.ch, ko.t0, P->k, b2);
    double f2 = standin_score(b2, smp.w1);
    long double sr2 = standin_score_ref(smp.ct, ko.t0, smp.w1);
    if (fabs((double)(f2 - sr2)) > 1e-12) sbad++;
    maxd = std::max(maxd, (double)fabsl(f2 - sr2));
    uint8_t z[KMAX][N] = {{0}};
    double fz = standin_score(smp.b, z);
    double al = alpha_score(smp.ch, kk.t0);
    maxa = std::max(maxa, fabs(fz - al));
    if (fabs(fz - al) > 1e-12) abad++;
  }
  fails += sbad != 0 || abad != 0;
  printf("selftest score %ld inputs (half accepted ideal samples, half random challenges with "
         "zero/edge/uniform buckets), own and other key: fast vs long-double reference max|diff| "
         "%.3e (bad %ld); at zero buckets vs nm_attack alpha_score max|diff| %.3e (bad %ld)\n",
         nscore, maxd, sbad, maxa, abad);
  // 4. Hint count formula vs brute force over a whole bucket with FIPS MakeHint.
  long hbad = 0;
#pragma omp parallel for schedule(dynamic, 1) reduction(+ : hbad)
  for (long t = 0; t < nhint; t++) {
    Stream s3;
    s3.init(cf.master, 0xfffffffffff1ull, (uint32_t)t);
    uint32_t v[4];
    s3.bytes((uint8_t*)v, sizeof v);
    int g2 = P->gamma2, be = P->beta;
    int r1 = (t % 5 == 0) ? 0 : (t % 5 == 1 ? m - 1 : (int)(v[0] % m));
    int32_t a = (int32_t)(v[1] % (2 * be + 1)) - be;
    int32_t b;
    if (t % 7 == 0)
      b = (t & 8) ? g2 - 1 : -(g2 - 1);
    else if (t % 7 == 1)
      b = (int32_t)(v[2] % 7) - 3 + ((t & 8) ? be : -be);
    else
      b = (int32_t)(v[2] % (2 * g2 - 1)) - (g2 - 1);
    long size = 0, pass = 0, fire = 0;
    for (int64_t off = -(int64_t)g2 - 3; off <= g2 + 3; off++) {
      int32_t x = modq((int64_t)r1 * 2 * g2 + off);
      if (high_bits(x) != r1) continue;
      size++;
      int32_t r1x, r0x;
      decompose(modq((int64_t)x - a), &r1x, &r0x);
      if (std::abs(r0x) >= g2 - be) continue;
      pass++;
      int32_t rr = modq((int64_t)x - a + b);
      int32_t zz = modq(-(int64_t)b);
      if (high_bits(rr) != high_bits(modq((int64_t)rr + zz))) fire++;
    }
    int64_t ab = b < 0 ? -b : b;
    int64_t hv = (b < 0 && r1 != 0) ? (-b - be) : (ab - be - 1);
    int64_t hc = hv < 0 ? 0 : hv;
    if (pass != 2 * (g2 - be) - 1 || fire != hc) {
      hbad++;
#pragma omp critical
      printf("selftest hint FAIL r1 %d a %d b %d size %ld pass %ld fire %ld formula %lld\n", r1, a,
             b, size, pass, fire, (long long)hc);
    }
  }
  fails += hbad != 0;
  printf("selftest hintCount %ld (r1, a, b) triples incl. buckets 0 and m-1 and |b| = gamma2-1, "
         "beta+-3: brute-force FIPS MakeHint count over the bucket equals the Lean formula, "
         "r0-pass count equals 2(gamma2-beta)-1; mismatches %ld\n",
         nhint, hbad);
  // 5. Fast attempt vs slow reference attempt.
  long abad2 = 0, acc = 0;
  for (long t = 0; t < natt; t++) {
    Masks mk;
    uint8_t ct[64];
    Sample s1, s2;
    AttemptStats st;
    const Key& kk = (t & 1) ? *key2 : *key;
    if (t % 2 == 0) {
      // Accepted pair from the sampler, re-run through both.
      for (;;) {
        draw_mask(rs, &mk);
        rs.bytes(ct, P->ctilde_bytes());
        if (attempt_fast(kk, mk.y, ct, &s1, &st)) break;
      }
    } else {
      draw_mask(rs, &mk);
      rs.bytes(ct, P->ctilde_bytes());
    }
    bool f = attempt_fast(kk, mk.y, ct, &s1, &st);
    bool r = attempt_ref(kk, mk.y, ct, s2.w1);
    if (f != r || (f && memcmp(s1.w1, s2.w1, P->k * sizeof s1.w1[0]))) {
      if (abad2 < 3) printf("selftest attempt FAIL t %ld fast %d ref %d\n", t, f, r);
      abad2++;
    }
    acc += f;
  }
  fails += abad2 != 0;
  printf("selftest attempt %ld (y, c~) pairs (%ld accepted): fast idealAttempt accept and w1 vs "
         "exact schoolbook reference; mismatches %ld\n",
         natt, acc, abad2);
  // 6. Deployed pipeline: H(mu || w1Encode(w1)) == c~ and w1 = HighBits(w) relation.
  {
    Key* ko = new Key();
    uint8_t xi[32];
    rs.bytes(xi, 32);
    load_key_openssl(xi, ko);
    Signer sg;
    sg.bind(ko->pkey);
    long bad = 0;
    std::vector<uint8_t> sig(P->sig_bytes());
    for (long t = 0; t < nsig; t++) {
      uint8_t msg[32], mu[64], ct[64], w1[KMAX][N];
      rs.bytes(msg, 32);
      sg.sign(msg, 32, sig.data());
      if (!sg.verify(msg, 32, sig.data())) die("verify");
      if (!recover_w1(*ko, msg, 32, sig.data(), mu, w1)) die("decode");
      uint8_t buf[64 + 8 * 32 * 6];
      memcpy(buf, mu, 64);
      w1_encode(w1, buf + 64);
      shake256(buf, 64 + P->w1enc_bytes(), ct, P->ctilde_bytes());
      if (memcmp(ct, sig.data(), P->ctilde_bytes())) bad++;
    }
    fails += bad != 0;
    printf("selftest deployed %ld OpenSSL signatures: verified, H(mu||w1Encode(w1)) = c~ "
           "mismatches %ld\n",
           nsig, bad);
    EVP_PKEY_free(ko->pkey);
    delete ko;
  }
  printf("selftest %s\n", fails ? "FAILED" : "PASSED");
  delete key;
  delete key2;
  return fails ? 1 : 0;
}

// Per-operation timings (single thread).
int mode_bench(const Config& cf, long n) {
  Stream rs;
  rs.init(cf.master, 0xfffffffffff2ull, 0);
  Key* key = new Key();
  Key* key2 = new Key();
  uint8_t xi[32];
  double t = now_s();
  for (long i = 0; i < n; i++) {
    rs.bytes(xi, 32);
    keygen_fast(xi, key);
  }
  double tk = (now_s() - t) / n;
  rs.bytes(xi, 32);
  keygen_fast(xi, key2);
  AttemptStats st;
  Sample smp;
  t = now_s();
  double acc = 0;
  for (long i = 0; i < n; i++) {
    sample_ideal(*key, rs, &smp, &st);
    acc += smp.b[0][0];
  }
  double ts = (now_s() - t) / n;
  int32_t b[KMAX][N];
  t = now_s();
  for (long i = 0; i < n; i++) {
    sparse_mul(smp.ch, key2->t0, P->k, b);
    acc += standin_score(b, smp.w1);
  }
  double tsc = (now_s() - t) / n;
  t = now_s();
  for (long i = 0; i < n; i++) {
    smp.w1[0][i % N] ^= 1;
    acc += standin_score(smp.b, smp.w1);
  }
  double tdp = (now_s() - t) / n;
  t = now_s();
  long nd = std::max(1L, n / 10);
  Key* ko = new Key();
  for (long i = 0; i < nd; i++) {
    rs.bytes(xi, 32);
    load_key_openssl(xi, ko);
  }
  double tko = (now_s() - t) / nd;
  Signer sg;
  sg.bind(ko->pkey);
  std::vector<uint8_t> sig(P->sig_bytes());
  t = now_s();
  for (long i = 0; i < nd; i++) {
    uint8_t msg[32], mu[64], w1[KMAX][N];
    rs.bytes(msg, 32);
    sg.sign(msg, 32, sig.data());
    if (!sg.verify(msg, 32, sig.data())) die("verify");
    recover_w1(*ko, msg, 32, sig.data(), mu, w1);
  }
  double tsig = (now_s() - t) / nd;
  printf("bench %s keygen_fast %.1f us, ideal sample %.1f us (%.3f attempts, zpass %.3f r0pass "
         "%.3f ct0pass %.3f hintpass %.3f per attempt), score (sparse mul + DP) %.1f us, DP only "
         "%.1f us, openssl keygen+decode %.1f us, openssl sign+verify+recover %.1f us [chk %g]\n",
         P->name, tk * 1e6, ts * 1e6, (double)st.attempts / n, (double)st.zpass / st.attempts,
         (double)st.r0pass / st.zpass, (double)st.ct0pass / st.r0pass,
         (double)n / st.ct0pass, tsc * 1e6, tdp * 1e6, tko * 1e6, tsig * 1e6, acc);
  return 0;
}

void usage() {
  fprintf(stderr,
          "usage: standin_gap --param {44,65,87} --seed HEX64 [--K K] [--M M] MODE ...\n"
          "  selftest NSCORE NKEY NATT NHINT NSIG\n"
          "  bench N\n"
          "  ideal U0 NUNITS BLOCK\n"
          "  deployed U0 NUNITS BLOCK\n"
          "  uniform U0 NUNITS R\n");
  exit(2);
}

}  // namespace

int main(int argc, char** argv) {
  int level = 44;
  Config cf;
  bool have_seed = false;
  int i = 1;
  for (; i < argc; i++) {
    if (!strcmp(argv[i], "--param") && i + 1 < argc)
      level = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--K") && i + 1 < argc)
      cf.K = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--M") && i + 1 < argc)
      cf.M = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--seed") && i + 1 < argc) {
      cf.master_hex = argv[++i];
      if (cf.master_hex.size() != 64) usage();
      for (int b = 0; b < 32; b++) cf.master[b] = (uint8_t)strtol(cf.master_hex.substr(2 * b, 2).c_str(), nullptr, 16);
      have_seed = true;
    } else
      break;
  }
  for (const Params& p : kParams)
    if (p.level == level) P = &p;
  if (!P || i >= argc || !have_seed || cf.K < 2 || cf.K > KEYMAX || cf.M < 1) usage();
  init_zetas();
  g_shake128 = EVP_MD_fetch(nullptr, "SHAKE128", nullptr);
  g_shake256 = EVP_MD_fetch(nullptr, "SHAKE256", nullptr);
  g_sigalg = EVP_SIGNATURE_fetch(nullptr, P->name, nullptr);
  g_aes = EVP_CIPHER_fetch(nullptr, "AES-256-CTR", nullptr);
  if (!g_shake128 || !g_shake256 || !g_sigalg || !g_aes) die("fetch");
  std::string mode = argv[i++];
  auto arg = [&](int k) -> const char* {
    if (i + k >= argc) usage();
    return argv[i + k];
  };
  if (mode == "selftest")
    return mode_selftest(cf, atol(arg(0)), atol(arg(1)), atol(arg(2)), atol(arg(3)), atol(arg(4)));
  if (mode == "bench") return mode_bench(cf, atol(arg(0)));
  if (mode == "ideal")
    return mode_units(cf, 0, strtoull(arg(0), nullptr, 10), strtoull(arg(1), nullptr, 10),
                      strtoull(arg(2), nullptr, 10));
  if (mode == "deployed")
    return mode_units(cf, 1, strtoull(arg(0), nullptr, 10), strtoull(arg(1), nullptr, 10),
                      strtoull(arg(2), nullptr, 10));
  if (mode == "uniform")
    return mode_uniform(cf, strtoull(arg(0), nullptr, 10), strtoull(arg(1), nullptr, 10),
                        atol(arg(2)));
  usage();
}
