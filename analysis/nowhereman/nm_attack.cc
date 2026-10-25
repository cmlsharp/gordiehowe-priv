// Distinguisher against the simulator of Theorem 2 (Unlinkability) of
// "Nowhere Man: Device Binding for Post-Quantum Anonymous Credentials"
// (IACR ePrint 2026/2472).
//
// Real presentations carry (mu, w1) with H(mu || w1Encode(w1)) equal to the
// challenge hash of a FIPS 204 signature produced by OpenSSL.  Simulated
// presentations carry (r_mu, HighBits(u)) for uniform r_mu and u, as in the
// simulator of the proof of Theorem 2.  The distinguisher recomputes the
// verifier's challenge c' (ShowVf2 line 11) and scores it.
//
// Build: g++ -O2 -std=c++17 -pthread nm_attack.cc -lcrypto -o nm_attack

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
#include <mutex>
#include <string>
#include <thread>
#include <vector>

namespace {

constexpr int32_t Q = 8380417;
constexpr int D = 13;
constexpr int N = 256;
constexpr int KMAX = 8;
constexpr int LMAX = 7;

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

// ---------------------------------------------------------------- arithmetic

int32_t modq(int64_t a) {
  int64_t r = a % Q;
  if (r < 0) r += Q;
  return (int32_t)r;
}

int32_t zetas[N];

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
  }
}

// FIPS 204 Algorithm 41.  Input and output in [0, q).
void ntt(int32_t w[N]) {
  int m = 0;
  for (int len = 128; len >= 1; len >>= 1) {
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
}

// FIPS 204 Algorithm 42.
void intt(int32_t w[N]) {
  int m = 256;
  for (int len = 1; len < N; len <<= 1) {
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
  }
  const int64_t f = 8347681;
  for (int j = 0; j < N; j++) w[j] = (int32_t)(f * w[j] % Q);
}

// Schoolbook negacyclic product mod q, for testing the NTT.
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

// FIPS 204 Algorithm 36.
void decompose(int32_t r, int32_t* r1, int32_t* r0) {
  int32_t rp = modq(r);
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

int32_t high_bits(int32_t r) {
  int32_t r1, r0;
  decompose(r, &r1, &r0);
  return r1;
}

// FIPS 204 Algorithm 40.
int32_t use_hint(int h, int32_t r) {
  int32_t m = (Q - 1) / (2 * P->gamma2);
  int32_t r1, r0;
  decompose(r, &r1, &r0);
  if (h == 1 && r0 > 0) return (r1 + 1) % m;
  if (h == 1 && r0 <= 0) return (r1 - 1 + m) % m;
  return r1;
}

// ------------------------------------------------------------ bit packing

// Little-endian bit stream of `bits`-bit values (FIPS 204 Algorithms 16-19).
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

// BitPack(w, a, b): stores b - w_i.
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

// FIPS 204 Algorithm 29.  Output: positions and signs of the tau nonzeros.
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
  uint8_t buf[168];
  int j = 0;
  while (j < N) {
    x.squeeze(buf, sizeof buf);
    for (int p = 0; p + 3 <= 168 && j < N; p += 3) {
      int32_t z = buf[p] | (buf[p + 1] << 8) | ((buf[p + 2] & 0x7f) << 16);
      if (z < Q) a[j++] = z;
    }
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

// -------------------------------------------------------------- key material

struct Key {
  std::vector<uint8_t> pk, sk;
  uint8_t rho[32], tr[64];
  int32_t t0[KMAX][N];
  int32_t t1[KMAX][N];
  int32_t s1[LMAX][N], s2[KMAX][N];
  // NTT(A), NTT(t1 * 2^d).
  int32_t ahat[KMAX][LMAX][N];
  int32_t t1hat[KMAX][N];
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

// skDecode (Algorithm 25) and pkDecode (Algorithm 23).
void decode_key(Key* key) {
  const uint8_t* sk = key->sk.data();
  memcpy(key->rho, sk, 32);
  memcpy(key->tr, sk + 64, 64);
  const uint8_t* p = sk + 128;
  int eb = P->eta_bits();
  for (int i = 0; i < P->l; i++, p += 32 * eb) bitunpack(p, P->eta, eb, key->s1[i]);
  for (int i = 0; i < P->k; i++, p += 32 * eb) bitunpack(p, P->eta, eb, key->s2[i]);
  for (int i = 0; i < P->k; i++, p += 416) bitunpack(p, 1 << (D - 1), D, key->t0[i]);
  if (p != sk + P->sk_bytes()) die("sk length");
  const uint8_t* q = key->pk.data() + 32;
  for (int i = 0; i < P->k; i++, q += 320) {
    uint32_t v[N];
    unpack_bits(q, N, 10, v);
    for (int j = 0; j < N; j++) key->t1[i][j] = (int32_t)v[j];
  }
  if (memcmp(key->pk.data(), key->rho, 32)) die("rho mismatch between pk and sk");
}

void precompute_key(Key* key) {
  expand_a(key->rho, key->ahat);
  for (int i = 0; i < P->k; i++) {
    for (int j = 0; j < N; j++) key->t1hat[i][j] = modq((int64_t)key->t1[i][j] << D);
    ntt(key->t1hat[i]);
  }
}

void load_key(const uint8_t xi[32], Key* key) {
  key->pkey = openssl_keygen(xi);
  key->pk = get_octets(key->pkey, OSSL_PKEY_PARAM_PUB_KEY);
  key->sk = get_octets(key->pkey, OSSL_PKEY_PARAM_PRIV_KEY);
  if ((int)key->pk.size() != P->pk_bytes() || (int)key->sk.size() != P->sk_bytes())
    die("unexpected key sizes");
  decode_key(key);
  precompute_key(key);
}

void free_key(Key* key) {
  EVP_PKEY_free(key->pkey);
  key->pkey = nullptr;
}

// Independent FIPS 204 KeyGen_internal (Algorithm 6) and skEncode; returns
// a description of the first mismatch with the OpenSSL key, or "" if equal.
std::string check_key(const uint8_t xi[32], const Key& key) {
  uint8_t in[34], seeds[128];
  memcpy(in, xi, 32);
  in[32] = (uint8_t)P->k;
  in[33] = (uint8_t)P->l;
  shake256(in, 34, seeds, 128);
  const uint8_t* rho = seeds;
  const uint8_t* rhop = seeds + 32;
  const uint8_t* kk = seeds + 96;
  static thread_local int32_t ahat[KMAX][LMAX][N];
  expand_a(rho, ahat);
  int32_t s1[LMAX][N], s2[KMAX][N], s1hat[LMAX][N];
  uint8_t sd[66];
  memcpy(sd, rhop, 64);
  for (int r = 0; r < P->l + P->k; r++) {
    sd[64] = (uint8_t)(r & 0xff);
    sd[65] = (uint8_t)(r >> 8);
    rej_bounded_poly(sd, r < P->l ? s1[r] : s2[r - P->l]);
  }
  for (int r = 0; r < P->l; r++) {
    for (int j = 0; j < N; j++) s1hat[r][j] = modq(s1[r][j]);
    ntt(s1hat[r]);
  }
  int32_t t0[KMAX][N], t1[KMAX][N];
  for (int i = 0; i < P->k; i++) {
    int32_t t[N];
    for (int j = 0; j < N; j++) {
      int64_t acc = 0;
      for (int s = 0; s < P->l; s++) acc += (int64_t)ahat[i][s][j] * s1hat[s][j] % Q;
      t[j] = modq(acc);
    }
    intt(t);
    for (int j = 0; j < N; j++) {
      int32_t r = modq((int64_t)t[j] + s2[i][j]);
      int32_t lo = r & ((1 << D) - 1);
      if (lo > (1 << (D - 1))) lo -= 1 << D;
      t0[i][j] = lo;
      t1[i][j] = (r - lo) >> D;
    }
  }
  std::vector<uint8_t> pk(P->pk_bytes()), sk(P->sk_bytes());
  memcpy(pk.data(), rho, 32);
  for (int i = 0; i < P->k; i++) {
    uint32_t v[N];
    for (int j = 0; j < N; j++) v[j] = (uint32_t)t1[i][j];
    pack_bits(v, N, 10, pk.data() + 32 + 320 * i);
  }
  uint8_t tr[64];
  shake256(pk.data(), pk.size(), tr, 64);
  uint8_t* p = sk.data();
  memcpy(p, rho, 32);
  memcpy(p + 32, kk, 32);
  memcpy(p + 64, tr, 64);
  p += 128;
  int eb = P->eta_bits();
  for (int i = 0; i < P->l; i++, p += 32 * eb) bitpack(s1[i], P->eta, eb, p);
  for (int i = 0; i < P->k; i++, p += 32 * eb) bitpack(s2[i], P->eta, eb, p);
  for (int i = 0; i < P->k; i++, p += 416) bitpack(t0[i], 1 << (D - 1), D, p);
  if (pk != key.pk) return "pk differs from own KeyGen";
  if (sk != key.sk) return "sk differs from own KeyGen";
  for (int i = 0; i < P->k; i++)
    for (int j = 0; j < N; j++) {
      if (t0[i][j] != key.t0[i][j]) return "decoded t0 differs";
      if (t0[i][j] <= -(1 << (D - 1)) || t0[i][j] > (1 << (D - 1))) return "t0 out of range";
    }
  for (int i = 0; i < P->l; i++)
    if (memcmp(s1[i], key.s1[i], sizeof s1[i])) return "decoded s1 differs";
  if (memcmp(tr, key.tr, 64)) return "tr differs";
  return "";
}

// ------------------------------------------------------------ signing

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
  // ML-DSA.Sign(sk, M, ctx = empty), hedged (OpenSSL default).
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

// ------------------------------------------------------- presentations

void w1_encode(const int32_t w1[KMAX][N], uint8_t* out) {
  int bits = P->w1_bits();
  for (int i = 0; i < P->k; i++) {
    uint32_t v[N];
    for (int j = 0; j < N; j++) v[j] = (uint32_t)w1[i][j];
    pack_bits(v, N, bits, out + i * 32 * bits);
  }
}

// H(mu || w1Encode(w1), lambda/4): ShowVf2 line 11.
void challenge_hash(const uint8_t mu[64], const int32_t w1[KMAX][N], uint8_t* ct) {
  uint8_t buf[64 + 8 * 32 * 6];
  memcpy(buf, mu, 64);
  w1_encode(w1, buf + 64);
  shake256(buf, 64 + P->w1enc_bytes(), ct, P->ctilde_bytes());
}

// The (mu, w1) part of a real presentation (ShowUsr1 lines 6-7, ShowUsr2
// lines 1-10).  Returns false if sigDecode rejects or ||z|| is too large.
bool real_presentation(const Key& key, const uint8_t* m, size_t mlen, const uint8_t* sig,
                       uint8_t mu[64], int32_t w1[KMAX][N]) {
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
    ntt(zhat[i]);
  }
  // HintBitUnpack (Algorithm 21).
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
  ntt(chat);
  for (int i = 0; i < P->k; i++) {
    int32_t w[N];
    for (int j = 0; j < N; j++) {
      int64_t acc = 0;
      for (int s = 0; s < P->l; s++) acc += (int64_t)key.ahat[i][s][j] * zhat[s][j] % Q;
      acc -= (int64_t)chat[j] * key.t1hat[i][j] % Q;
      w[j] = modq(acc);
    }
    intt(w);
    for (int j = 0; j < N; j++) w1[i][j] = use_hint(h[i][j], w[j]);
  }
  return true;
}

struct UniformQ {
  uint32_t buf[2048];
  int pos = 2048;
  int32_t next() {
    for (;;) {
      if (pos == 2048) {
        if (RAND_bytes((uint8_t*)buf, sizeof buf) != 1) die("RAND_bytes");
        pos = 0;
      }
      uint32_t v = buf[pos++] & 0x7fffff;
      if (v < (uint32_t)Q) return (int32_t)v;
    }
  }
};

// Simulator of the proof of Theorem 2: r_w' = HighBits(U(R_q^k), 2 gamma2),
// r_mu uniform in {0,1}^512.
void sim_presentation(UniformQ& uq, uint8_t mu[64], int32_t w1[KMAX][N]) {
  if (RAND_bytes(mu, 64) != 1) die("RAND_bytes");
  for (int i = 0; i < P->k; i++)
    for (int j = 0; j < N; j++) w1[i][j] = high_bits(uq.next());
}

// -------------------------------------------------------------- scores

// b = c * t0 over the integers (negacyclic).
void ct0(const Challenge& ch, const int32_t t0[KMAX][N], int32_t b[KMAX][N]) {
  for (int i = 0; i < P->k; i++) {
    int32_t* bi = b[i];
    memset(bi, 0, sizeof(int32_t) * N);
    const int32_t* t = t0[i];
    for (int u = 0; u < ch.ntau; u++) {
      int p = ch.pos[u];
      int32_t s = ch.sgn[u];
      for (int j = 0; j < p; j++) bi[j] -= s * t[j - p + N];
      for (int j = p; j < N; j++) bi[j] += s * t[j - p];
    }
  }
}

// alpha(c): 0 if ||c t0|| >= gamma2, else Pr[sum Bernoulli(p_i) <= omega].
double alpha_score(const Challenge& ch, const int32_t t0[KMAX][N]) {
  int32_t b[KMAX][N];
  ct0(ch, t0, b);
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

// -------------------------------------------------------------- utilities

void seed_from_index(uint32_t j, uint8_t xi[32]) {
  memset(xi, 0, 32);
  for (int i = 0; i < 4; i++) xi[i] = (uint8_t)(j >> (8 * i));
}

double now_s() {
  return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count();
}

template <class F>
void parallel(int threads, F f) {
  std::vector<std::thread> ts;
  for (int t = 0; t < threads; t++) ts.emplace_back(f, t);
  for (auto& t : ts) t.join();
}

void random_challenge(Challenge* ch) {
  uint8_t ct[64];
  if (RAND_bytes(ct, P->ctilde_bytes()) != 1) die("RAND_bytes");
  sample_in_ball(ct, ch);
}

double median(std::vector<double> v) {
  size_t m = v.size() / 2;
  std::nth_element(v.begin(), v.begin() + m, v.end());
  return v[m];
}

struct Delta {
  double mean, delta, theta, pred_adv;
};

// delta = 1/2 E_U |alpha/E_U alpha - 1|; pred_adv = E_U[(alpha/E alpha - 1) 1{alpha > theta}].
Delta delta_stats(const std::vector<double>& a) {
  Delta d{};
  double s = 0;
  for (double x : a) s += x;
  d.mean = s / a.size();
  double dev = 0;
  for (double x : a) dev += fabs(x / d.mean - 1);
  d.delta = 0.5 * dev / a.size();
  d.theta = median(a);
  double pa = 0;
  for (double x : a)
    if (x > d.theta) pa += x / d.mean - 1;
  d.pred_adv = pa / a.size();
  return d;
}

std::vector<double> calib_alphas(const Key& key, long n, int threads) {
  std::vector<double> a(n);
  parallel(threads, [&](int t) {
    for (long i = t; i < n; i += threads) {
      Challenge ch;
      random_challenge(&ch);
      a[i] = alpha_score(ch, key.t0);
    }
  });
  return a;
}

// ---------------------------------------------------------------- modes

int mode_selftest(long nsig) {
  // NTT against schoolbook.
  UniformQ uq;
  for (int rep = 0; rep < 3; rep++) {
    int32_t a[N], b[N], c1[N], c2[N], ah[N], bh[N];
    for (int j = 0; j < N; j++) {
      a[j] = ah[j] = uq.next();
      b[j] = bh[j] = uq.next();
    }
    poly_mul_school(a, b, c1);
    ntt(ah);
    ntt(bh);
    for (int j = 0; j < N; j++) c2[j] = (int32_t)((int64_t)ah[j] * bh[j] % Q);
    intt(c2);
    if (memcmp(c1, c2, sizeof c1)) die("NTT product mismatch");
  }
  printf("selftest ntt ok\n");
  // Key decoding against an independent KeyGen, several seeds.
  for (uint32_t j = 0; j < 8; j++) {
    uint8_t xi[32];
    seed_from_index(j, xi);
    Key* key = new Key();
    load_key(xi, key);
    std::string err = check_key(xi, *key);
    if (!err.empty()) {
      fprintf(stderr, "seed %u: %s\n", j, err.c_str());
      die("key check");
    }
    free_key(key);
    delete key;
  }
  {
    uint8_t xi[32];
    if (RAND_bytes(xi, 32) != 1) die("RAND_bytes");
    Key* key = new Key();
    load_key(xi, key);
    std::string err = check_key(xi, *key);
    if (!err.empty()) die(err.c_str());
    free_key(key);
    delete key;
  }
  printf("selftest keygen ok: OpenSSL pk/sk equal own FIPS 204 KeyGen and skEncode for 9 seeds; "
         "t0 in (-2^12, 2^12]\n");
  // Pipeline: H(mu || w1Encode(UseHint(h, Az - c t1 2^d))) == c~.
  uint8_t xi[32];
  seed_from_index(0, xi);
  Key* key = new Key();
  load_key(xi, key);
  Signer sg;
  sg.bind(key->pkey);
  long ok = 0, bad = 0;
  std::vector<uint8_t> sig(P->sig_bytes());
  for (long i = 0; i < nsig; i++) {
    uint8_t m[32];
    if (RAND_bytes(m, 32) != 1) die("RAND_bytes");
    sg.sign(m, 32, sig.data());
    if (!sg.verify(m, 32, sig.data())) die("verify failed");
    uint8_t mu[64], ct[64];
    int32_t w1[KMAX][N];
    if (!real_presentation(*key, m, 32, sig.data(), mu, w1)) die("decode failed");
    challenge_hash(mu, w1, ct);
    if (memcmp(ct, sig.data(), P->ctilde_bytes()) == 0)
      ok++;
    else
      bad++;
  }
  printf("selftest pipeline %s: %ld of %ld signatures have H(mu||w1Encode(w1)) = c~ (%ld mismatch)\n",
         P->name, ok, nsig, bad);
  free_key(key);
  delete key;
  return bad == 0 ? 0 : 1;
}

int mode_select(int nseeds, long ncal, int threads) {
  std::vector<Delta> ds(nseeds);
  for (int j = 0; j < nseeds; j++) {
    uint8_t xi[32];
    seed_from_index(j, xi);
    Key* key = new Key();
    load_key(xi, key);
    std::vector<double> a = calib_alphas(*key, ncal, threads);
    ds[j] = delta_stats(a);
    printf("seed %d mean_alpha %.6f delta %.6e log2_delta %.3f\n", j, ds[j].mean, ds[j].delta,
           log2(ds[j].delta));
    fflush(stdout);
    free_key(key);
    delete key;
  }
  int best = 0;
  double s = 0, s2 = 0, mn = 1, mx = 0;
  for (int j = 0; j < nseeds; j++) {
    if (ds[j].delta > ds[best].delta) best = j;
    s += ds[j].delta;
    s2 += ds[j].delta * ds[j].delta;
    mn = std::min(mn, ds[j].delta);
    mx = std::max(mx, ds[j].delta);
  }
  double m = s / nseeds;
  double sd = sqrt(std::max(0.0, s2 / nseeds - m * m));
  printf("summary nseeds %d ncal %ld delta_mean %.6e delta_sd %.6e delta_min %.6e delta_max %.6e "
         "best_seed %d best_delta %.6e\n",
         nseeds, ncal, m, sd, mn, mx, best, ds[best].delta);
  return 0;
}

int mode_calib(uint32_t seed, long ncal, int threads) {
  uint8_t xi[32];
  seed_from_index(seed, xi);
  Key* key = new Key();
  load_key(xi, key);
  double t0 = now_s();
  std::vector<double> a = calib_alphas(*key, ncal, threads);
  Delta d = delta_stats(a);
  printf("calib seed %u ncal %ld mean_alpha %.9f delta %.6e log2_delta %.3f theta %.17g "
         "pred_adv %.6e secs %.1f\n",
         seed, ncal, d.mean, d.delta, log2(d.delta), d.theta, d.pred_adv, now_s() - t0);
  free_key(key);
  delete key;
  return 0;
}

struct Counts {
  long n_real = 0, n_sim = 0, pos_real = 0, pos_sim = 0;
  double sa_real = 0, sa2_real = 0, sa_sim = 0, sa2_sim = 0;
  long mismatch = 0;
  void add(const Counts& o) {
    n_real += o.n_real;
    n_sim += o.n_sim;
    pos_real += o.pos_real;
    pos_sim += o.pos_sim;
    sa_real += o.sa_real;
    sa2_real += o.sa2_real;
    sa_sim += o.sa_sim;
    sa2_sim += o.sa2_sim;
    mismatch += o.mismatch;
  }
};

void report(const char* tag, long n1, long k1, long n0, long k0) {
  double p1 = (double)k1 / n1, p0 = (double)k0 / n0;
  double adv = p1 - p0;
  double se = sqrt(p1 * (1 - p1) / n1 + p0 * (1 - p0) / n0);
  printf("%s N_real %ld N_sim %ld p_real %.7f p_sim %.7f adv %.6e se %.3e z %.2f\n", tag, n1, n0,
         p1, p0, adv, se, adv / se);
}

// Key-aware test: a fixed key; output "real" iff alpha > theta.
int mode_test(uint32_t seed, double theta, long n, int threads) {
  Counts total;
  std::mutex mu_lock;
  std::atomic<long> done{0};
  double tstart = now_s();
  uint8_t xi0[32];
  seed_from_index(seed, xi0);
  parallel(threads, [&](int t) {
    Counts c;
    Key* key = new Key();
    Signer sg;
    UniformQ uq;
    long my_n = n / threads + (t < n % threads ? 1 : 0);
    std::vector<uint8_t> sig(P->sig_bytes());
    load_key(xi0, key);
    sg.bind(key->pkey);
    for (long i = 0; i < my_n; i++) {
      uint8_t mu[64], ct[64];
      int32_t w1[KMAX][N];
      Challenge ch;
      // Real: M = R || ctx, sigma = ML-DSA.Sign(dsk, M, empty context).
      uint8_t m[32];
      if (RAND_bytes(m, 32) != 1) die("RAND_bytes");
      sg.sign(m, 32, sig.data());
      if (!sg.verify(m, 32, sig.data())) die("OpenSSL verify failed");
      if (!real_presentation(*key, m, 32, sig.data(), mu, w1)) die("decode failed");
      challenge_hash(mu, w1, ct);
      if (memcmp(ct, sig.data(), P->ctilde_bytes())) c.mismatch++;
      sample_in_ball(ct, &ch);
      double a = alpha_score(ch, key->t0);
      c.n_real++;
      c.pos_real += a > theta;
      c.sa_real += a;
      c.sa2_real += a * a;
      // Simulated.
      sim_presentation(uq, mu, w1);
      challenge_hash(mu, w1, ct);
      sample_in_ball(ct, &ch);
      a = alpha_score(ch, key->t0);
      c.n_sim++;
      c.pos_sim += a > theta;
      c.sa_sim += a;
      c.sa2_sim += a * a;
      long d = ++done;
      if (d % 1000000 == 0) {
        std::lock_guard<std::mutex> g(mu_lock);
        fprintf(stderr, "progress %ld / %ld pairs, %.0f s\n", d, n, now_s() - tstart);
      }
    }
    free_key(key);
    delete key;
    std::lock_guard<std::mutex> g(mu_lock);
    total.add(c);
  });
  double secs = now_s() - tstart;
  printf("test keyaware param %s seed %u theta %.17g threads %d secs %.1f c_mismatch %ld\n",
         P->name, seed, theta, threads, secs, total.mismatch);
  report("RESULT alpha_test", total.n_real, total.pos_real, total.n_sim, total.pos_sim);
  double m1 = total.sa_real / total.n_real, m0 = total.sa_sim / total.n_sim;
  double v1 = total.sa2_real / total.n_real - m1 * m1, v0 = total.sa2_sim / total.n_sim - m0 * m0;
  double se = sqrt(v1 / total.n_real + v0 / total.n_sim);
  printf("aux mean_alpha real %.9f sim %.9f diff %.4e se %.3e z %.2f\n", m1, m0, m1 - m0, se,
         (m1 - m0) / se);
  return total.mismatch == 0 ? 0 : 1;
}

void usage() {
  fprintf(stderr,
          "usage: nm_attack --param {44,65,87} [--threads T] MODE ...\n"
          "  selftest NSIG\n"
          "  select NSEEDS NCAL\n"
          "  calib SEED NCAL\n"
          "  test SEED THETA N\n");
  exit(2);
}

}  // namespace

int main(int argc, char** argv) {
  int level = 65, threads = 1;
  int i = 1;
  for (; i < argc; i++) {
    if (!strcmp(argv[i], "--param") && i + 1 < argc)
      level = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--threads") && i + 1 < argc)
      threads = atoi(argv[++i]);
    else
      break;
  }
  for (const Params& p : kParams)
    if (p.level == level) P = &p;
  if (!P || i >= argc) usage();
  init_zetas();
  g_shake128 = EVP_MD_fetch(nullptr, "SHAKE128", nullptr);
  g_shake256 = EVP_MD_fetch(nullptr, "SHAKE256", nullptr);
  g_sigalg = EVP_SIGNATURE_fetch(nullptr, P->name, nullptr);
  if (!g_shake128 || !g_shake256 || !g_sigalg) die("fetch");
  std::string mode = argv[i++];
  auto arg = [&](int k) -> const char* {
    if (i + k >= argc) usage();
    return argv[i + k];
  };
  if (mode == "selftest") return mode_selftest(atol(arg(0)));
  if (mode == "select") return mode_select(atoi(arg(0)), atol(arg(1)), threads);
  if (mode == "calib") return mode_calib((uint32_t)atol(arg(0)), atol(arg(1)), threads);
  if (mode == "test")
    return mode_test((uint32_t)atol(arg(0)), atof(arg(1)), atol(arg(2)), threads);
  usage();
}
