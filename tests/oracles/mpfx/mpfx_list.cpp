// Copyright (c) 2026 FloatLib. Released under MIT license as described in the file LICENSE.
//
// Compare MPFX with FloatLib on listed operands.
//
//   mpfx_list FORMAT CONTAINER ENGINE OP MODE INPUTS FLOATLIB
//
// FORMAT is e<w>m<f>, an IEEE-style binary format with a w-bit exponent field, f fraction bits,
// and the conventional bias. CONTAINER is double or float, ENGINE is hw (MPFX's native
// round-to-odd emulation) or eft (error-free transformations). MODE is near_even, minMag, min,
// or max. INPUTS has one line of encoded operands per case and FLOATLIB the matching lines
// "value flags" from execFloatOracleList. Flags use FloatLib's bits: inexact 1, underflow 2,
// overflow 4, divide by zero 8, invalid 16. Cases with a NaN operand are compared by value only,
// since MPFX does not model signaling NaNs. With MPFX_ALL set, every difference is printed.
#include <mpfx.hpp>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

static int W, F, BIAS;

static bool is_nan_bits(uint64_t w) {
  return ((w >> F) & ((1ull << W) - 1)) == (1ull << W) - 1 && (w & ((1ull << F) - 1));
}

static double decode(uint64_t w) {
  int s = (w >> (W + F)) & 1; uint64_t ef = (w >> F) & ((1ull << W) - 1), fr = w & ((1ull << F) - 1);
  double v;
  if (ef == (1ull << W) - 1) v = fr ? NAN : INFINITY;
  else if (ef == 0) v = std::ldexp((double)fr, 1 - BIAS - F);
  else v = std::ldexp((double)(fr | (1ull << F)), (int)ef - BIAS - F);
  return s ? -v : v;
}

// Encode a value of the format; returns false if it is not representable.
static bool encode(double v, uint64_t &out) {
  uint64_t s = std::signbit(v) ? 1ull << (W + F) : 0;
  if (std::isnan(v)) { out = ((1ull << W) - 1) << F | 1ull << (F - 1); return true; }
  if (std::isinf(v)) { out = s | ((1ull << W) - 1) << F; return true; }
  if (v == 0) { out = s; return true; }
  double a = std::fabs(v); int e; std::frexp(a, &e); int E = e - 1;
  if (E >= 1 - BIAS) {
    if (E > (1 << W) - 2 - BIAS) return false;
    double m = std::ldexp(a, F - E);
    if (m != std::floor(m)) return false;
    out = s | (uint64_t)(E + BIAS) << F | ((uint64_t)m - (1ull << F));
  } else {
    double m = std::ldexp(a, BIAS - 1 + F);
    if (m != std::floor(m)) return false;
    out = s | (uint64_t)m;
  }
  return true;
}

static mpfx::RM mode_of(const char *m) {
  if (!strcmp(m, "near_even")) return mpfx::RM::RNE;
  if (!strcmp(m, "minMag")) return mpfx::RM::RTZ;
  if (!strcmp(m, "min")) return mpfx::RM::RTN;
  if (!strcmp(m, "max")) return mpfx::RM::RTP;
  fprintf(stderr, "unknown mode %s\n", m); exit(2);
}

static int flags_of_mpfx() {
  using mpfx::flags;
  return (flags.inexact() ? 1 : 0) | (flags.underflow_after_rounding() ? 2 : 0) |
         (flags.overflow() ? 4 : 0) | (flags.div_by_zero() ? 8 : 0) | (flags.invalid() ? 16 : 0);
}

template <mpfx::Engine E, typename T>
static T apply(const std::string &op, T x, T y, T z, const mpfx::Context &c) {
  if (op == "add") return mpfx::add<E, mpfx::Flags::ALL_FLAGS, T>(x, y, c);
  if (op == "sub") return mpfx::sub<E, mpfx::Flags::ALL_FLAGS, T>(x, y, c);
  if (op == "mul") return mpfx::mul<E, mpfx::Flags::ALL_FLAGS, T>(x, y, c);
  if (op == "div") return mpfx::div<E, mpfx::Flags::ALL_FLAGS, T>(x, y, c);
  if (op == "sqrt") return mpfx::sqrt<E, mpfx::Flags::ALL_FLAGS, T>(x, c);
  return mpfx::fma<E, mpfx::Flags::ALL_FLAGS, T>(x, y, z, c);
}

template <mpfx::Engine E, typename T>
static double run1(const std::string &op, uint64_t a, uint64_t b, uint64_t c, const mpfx::Context &ctx) {
  return (double)apply<E, T>(op, (T)decode(a), (T)decode(b), (T)decode(c), ctx);
}

int main(int argc, char **argv) {
  if (argc != 8) { fprintf(stderr, "usage: mpfx_list FORMAT CONTAINER ENGINE OP MODE INPUTS FLOATLIB\n"); return 2; }
  if (sscanf(argv[1], "e%dm%d", &W, &F) != 2) { fprintf(stderr, "bad format\n"); return 2; }
  BIAS = (1 << (W - 1)) - 1;
  std::string container = argv[2], engine = argv[3], op = argv[4];
  mpfx::IEEE754Context ctx(W, 1 + W + F, mode_of(argv[5]));
  FILE *in = fopen(argv[6], "r"), *fl = fopen(argv[7], "r");
  if (!in || !fl) { perror("open"); return 2; }
  int arity = op == "sqrt" ? 1 : op == "fma" ? 3 : 2;
  uint64_t n = 0, match = 0, value_mismatch = 0, flag_mismatch = 0, unrepresentable = 0, nan_input = 0;
  int shown = 0; char line[512];
  while (fgets(line, sizeof line, in)) {
    unsigned long long ops[3] = {0, 0, 0};
    int k = sscanf(line, "%llu %llu %llu", &ops[0], &ops[1], &ops[2]);
    if (k <= 0) continue;
    unsigned long long fv; int ff;
    if (fscanf(fl, "%llu %d", &fv, &ff) != 2) { fprintf(stderr, "FloatLib file too short\n"); return 2; }
    n++;
    mpfx::flags.reset();
    double r;
    if (container == "double") r = engine == "hw" ? run1<mpfx::Engine::FP_RTO, double>(op, ops[0], ops[1], ops[2], ctx)
                                                  : run1<mpfx::Engine::EFT, double>(op, ops[0], ops[1], ops[2], ctx);
    else r = engine == "hw" ? run1<mpfx::Engine::FP_RTO, float>(op, ops[0], ops[1], ops[2], ctx)
                            : run1<mpfx::Engine::EFT, float>(op, ops[0], ops[1], ops[2], ctx);
    int mf = flags_of_mpfx();
    uint64_t mv;
    if (!encode(r, mv)) {
      unrepresentable++;
      if (shown++ < 8) printf("UNREPRESENTABLE %s %llu %llu %llu: mpfx %a\n", op.c_str(), ops[0], ops[1], ops[2], r);
      continue;
    }
    bool nanin = false;
    for (int i = 0; i < arity; i++) nanin |= is_nan_bits(ops[i]);
    if (nanin) nan_input++;
    bool vok = (is_nan_bits(mv) && is_nan_bits(fv)) || mv == fv;
    bool fok = nanin || mf == ff;
    if (vok && fok) match++;
    else {
      if (!vok) value_mismatch++;
      if (!fok) flag_mismatch++;
      if (shown++ < 8 || getenv("MPFX_ALL"))
        printf("MISMATCH %s %a %a %a: mpfx %a flags %02x, floatlib %a flags %02x\n", op.c_str(),
               decode(ops[0]), decode(ops[1]), decode(ops[2]), r, mf, decode(fv), ff);
    }
  }
  printf("RESULT %s %s %s %s %s cases=%llu match=%llu value_mismatch=%llu flag_mismatch=%llu unrepresentable=%llu nan_input=%llu\n",
         argv[1], argv[2], argv[3], argv[4], argv[5], (unsigned long long)n, (unsigned long long)match,
         (unsigned long long)value_mismatch, (unsigned long long)flag_mismatch,
         (unsigned long long)unrepresentable, (unsigned long long)nan_input);
  return 0;
}
