/*
 * Copyright (c) 2026 FloatLib
 * Released under MIT license as described in the file LICENSE.
 * Independent references for the exhaustive 16-bit and binary32 square-root checks.
 */

/* Compare one block written by `execFloatExhaustive` with Berkeley SoftFloat (binary16 pairs,
   binary32 square root) and with an MPFR emulation of the format (binary16 and bfloat16 pairs),
   values and all five IEEE flags.

     exhaustive16_reference pairs f16|bf16 add|sub|mul|div MODE START COUNT FILE
     exhaustive16_reference sqrt f32 sqrt MODE START COUNT FILE

   For binary16 both references run and their disagreements are counted separately, which checks
   the MPFR emulation used for bfloat16 against SoftFloat on every binary16 pair.

   Built with FLOATLIB_WITH_MPFX, each FloatLib result is also compared with MPFX (Saiki et al.,
   "When Double Rounding is Correct") in its native round-to-odd (hw) and error-free-transformation
   (eft) engines, with double and, where the format fits, float containers. Flags are compared
   only when no operand is a NaN, since MPFX does not model signaling NaNs. With FILE "-", the
   reference results stand in for FloatLib's. */
#ifdef FLOATLIB_WITH_MPFX
#include <mpfx.hpp>
#endif
#include <cmath>
#include <gmp.h>
#include <mpfr.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
extern "C" {
#include "softfloat.h"
}

enum { INEXACT = 1, UNDERFLOW = 2, OVERFLOW = 4, DIVZERO = 8, INVALID = 16 };

static int E, F, bias;           /* emulated format: exponent and fraction widths, bias */
static mpfr_exp_t emin, emax;    /* MPFR exponent range of the format, subnormals included */

static int is_nan(uint32_t w) { return ((w >> F) & ((1u << E) - 1)) == (1u << E) - 1 && (w & ((1u << F) - 1)); }
static int is_snan(uint32_t w) { return is_nan(w) && !((w >> (F - 1)) & 1); }
static int is_inf(uint32_t w) { return ((w >> F) & ((1u << E) - 1)) == (1u << E) - 1 && !(w & ((1u << F) - 1)); }
static int is_zero(uint32_t w) { return !(w & ((1u << (E + F)) - 1)); }

static void decode(mpfr_ptr out, uint32_t w) {
  int sign = (w >> (E + F)) & 1; long ef = (w >> F) & ((1u << E) - 1); unsigned long frac = w & ((1u << F) - 1);
  if (ef == (1 << E) - 1) mpfr_set_inf(out, sign ? -1 : 1);
  else if (ef == 0 && frac == 0) mpfr_set_zero(out, sign ? -1 : 1);
  else {
    long ex = ef == 0 ? 1 - bias - F : ef - bias - F; if (ef) frac |= 1ul << F;
    mpfr_set_ui_2exp(out, frac, ex, MPFR_RNDN); if (sign) mpfr_neg(out, out, MPFR_RNDN);
  }
}

static uint32_t encode(mpfr_srcptr v) {
  uint32_t s = mpfr_signbit(v) ? 1u << (E + F) : 0;
  if (mpfr_zero_p(v)) return s;
  if (mpfr_inf_p(v)) return s | (((1u << E) - 1) << F);
  mpz_t m; mpz_init(m); long ex = mpfr_get_z_2exp(m, v); mpz_abs(m, m);
  long k = (long)mpz_sizeinbase(m, 2), shift = (F + 1) - k;
  if (shift > 0) mpz_mul_2exp(m, m, shift); else if (shift < 0) mpz_fdiv_q_2exp(m, m, -shift);
  ex -= shift; long ef = ex + bias + F; uint32_t out;
  if (ef >= 1) { mpz_clrbit(m, F); out = ((uint32_t)ef << F) | (uint32_t)mpz_get_ui(m); }
  else { mpz_fdiv_q_2exp(m, m, 1 - ef); out = (uint32_t)mpz_get_ui(m); }
  mpz_clear(m); return s | out;
}

static int mpfr_op(char op, mpfr_ptr r, mpfr_srcptr a, mpfr_srcptr b, mpfr_rnd_t rnd) {
  switch (op) {
    case 'a': return mpfr_add(r, a, b, rnd);
    case 's': return mpfr_sub(r, a, b, rnd);
    case 'm': return mpfr_mul(r, a, b, rnd);
    default: return mpfr_div(r, a, b, rnd);
  }
}

/* IEEE 754 binary operation on encodings, with tininess detected after rounding. */
static uint32_t emulate(char op, uint32_t a, uint32_t b, mpfr_rnd_t rnd, int *flags) {
  static mpfr_t x, y, r, u; static int init = 0;
  if (!init) { mpfr_inits2(F + 1, x, y, r, u, (mpfr_ptr)0); init = 1; }
  uint32_t qnan = ((1u << E) - 1) << F | 1u << (F - 1);
  *flags = 0;
  if (is_nan(a) || is_nan(b)) { if (is_snan(a) || is_snan(b)) *flags = INVALID; return qnan; }
  uint32_t sa = a >> (E + F), sb = b >> (E + F);
  if ((op == 'a' && is_inf(a) && is_inf(b) && sa != sb) || (op == 's' && is_inf(a) && is_inf(b) && sa == sb) ||
      (op == 'm' && ((is_zero(a) && is_inf(b)) || (is_inf(a) && is_zero(b)))) ||
      (op == 'd' && ((is_zero(a) && is_zero(b)) || (is_inf(a) && is_inf(b))))) { *flags = INVALID; return qnan; }
  if (op == 'd' && is_zero(b) && !is_inf(a)) { *flags = DIVZERO; return (sa ^ sb) << (E + F) | ((1u << E) - 1) << F; }
  mpfr_set_emin(mpfr_get_emin_min()); mpfr_set_emax(mpfr_get_emax_max());
  decode(x, a); decode(y, b);
  mpfr_op(op, u, x, y, rnd);           /* rounded as though the exponent range were unbounded */
  int tiny = !mpfr_zero_p(u) && !mpfr_inf_p(u) && mpfr_get_exp(u) < 2 - bias;
  mpfr_set_emin(emin); mpfr_set_emax(emax); mpfr_clear_flags();
  int t = mpfr_op(op, r, x, y, rnd);
  t = mpfr_check_range(r, t, rnd); t = mpfr_subnormalize(r, t, rnd);
  if (t) *flags |= INEXACT;
  if (mpfr_overflow_p()) *flags |= OVERFLOW;
  if (tiny && t) *flags |= UNDERFLOW;
  return encode(r);
}

static uint_fast8_t softfloat_mode(const char *m) {
  if (!strcmp(m, "near_even")) return softfloat_round_near_even;
  if (!strcmp(m, "minMag")) return softfloat_round_minMag;
  if (!strcmp(m, "min")) return softfloat_round_min;
  if (!strcmp(m, "max")) return softfloat_round_max;
  fprintf(stderr, "unknown mode %s\n", m); exit(2);
}

static mpfr_rnd_t mpfr_mode(const char *m) {
  if (!strcmp(m, "near_even")) return MPFR_RNDN;
  if (!strcmp(m, "minMag")) return MPFR_RNDZ;
  if (!strcmp(m, "min")) return MPFR_RNDD;
  return MPFR_RNDU;
}

static uint16_t softfloat16(char op, uint16_t a, uint16_t b) {
  float16_t x = { a }, y = { b }, r;
  switch (op) {
    case 'a': r = f16_add(x, y); break;
    case 's': r = f16_sub(x, y); break;
    case 'm': r = f16_mul(x, y); break;
    default: r = f16_div(x, y);
  }
  return r.v;
}

#ifdef FLOATLIB_WITH_MPFX
static double decode_double(uint32_t w) {
  int s = (w >> (E + F)) & 1; uint32_t ef = (w >> F) & ((1u << E) - 1), fr = w & ((1u << F) - 1);
  double v;
  if (ef == (1u << E) - 1) v = fr ? NAN : INFINITY;
  else if (ef == 0) v = std::ldexp((double)fr, 1 - bias - F);
  else v = std::ldexp((double)(fr | (1u << F)), (int)ef - bias - F);
  return s ? -v : v;
}

/* Encode a value of the format, or return 0xFFFFFFFF if it is not representable. */
static uint32_t encode_double(double v) {
  uint32_t s = std::signbit(v) ? 1u << (E + F) : 0;
  if (std::isnan(v)) return ((1u << E) - 1) << F | 1u << (F - 1);
  if (std::isinf(v)) return s | ((1u << E) - 1) << F;
  if (v == 0) return s;
  double a = std::fabs(v); int e; std::frexp(a, &e); int X = e - 1;
  if (X >= 1 - bias) {
    if (X > (1 << E) - 2 - bias) return 0xFFFFFFFFu;
    double m = std::ldexp(a, F - X); if (m != std::floor(m)) return 0xFFFFFFFFu;
    return s | (uint32_t)(X + bias) << F | ((uint32_t)m - (1u << F));
  }
  double m = std::ldexp(a, bias - 1 + F); if (m != std::floor(m)) return 0xFFFFFFFFu;
  return s | (uint32_t)m;
}

static int mpfx_flags() {
  using mpfx::flags;
  return (flags.inexact() ? 1 : 0) | (flags.underflow_after_rounding() ? 2 : 0) |
         (flags.overflow() ? 4 : 0) | (flags.div_by_zero() ? 8 : 0) | (flags.invalid() ? 16 : 0);
}

template <mpfx::Engine EN, typename T>
static uint32_t mpfx_eval(char op, uint32_t a, uint32_t b, const mpfx::Context &c, int *fl) {
  using mpfx::Flags;
  T x = (T)decode_double(a), y = (T)decode_double(b), r;
  mpfx::flags.reset();
  switch (op) {
    case 'a': r = mpfx::add<EN, Flags::ALL_FLAGS, T>(x, y, c); break;
    case 's': r = mpfx::sub<EN, Flags::ALL_FLAGS, T>(x, y, c); break;
    case 'm': r = mpfx::mul<EN, Flags::ALL_FLAGS, T>(x, y, c); break;
    case 'd': r = mpfx::div<EN, Flags::ALL_FLAGS, T>(x, y, c); break;
    default: r = mpfx::sqrt<EN, Flags::ALL_FLAGS, T>(x, c);
  }
  *fl = mpfx_flags();
  return encode_double((double)r);
}

static mpfx::RM mpfx_mode(const char *m) {
  if (!strcmp(m, "near_even")) return mpfx::RM::RNE;
  if (!strcmp(m, "minMag")) return mpfx::RM::RTZ;
  if (!strcmp(m, "min")) return mpfx::RM::RTN;
  return mpfx::RM::RTP;
}

#endif

int main(int argc, char **argv) {
  if (argc != 8) { fprintf(stderr, "usage: exhaustive16_reference pairs|sqrt FORMAT OP MODE START COUNT FILE\n"); return 2; }
  const char *kind = argv[1], *fmt = argv[2], *opname = argv[3], *mode = argv[4];
  uint64_t start = strtoull(argv[5], 0, 10), count = strtoull(argv[6], 0, 10);
  int sqrt32 = !strcmp(kind, "sqrt"), f16 = !strcmp(fmt, "f16");
  size_t width = sqrt32 ? 8 : 4;
  int nofile = !strcmp(argv[7], "-");
  unsigned char *buf = (unsigned char *)calloc(count, width);
  if (!nofile) {
    FILE *f = fopen(argv[7], "rb"); if (!f) { perror(argv[7]); return 2; }
    if (fread(buf, width, count, f) != count) { fprintf(stderr, "short block\n"); return 2; }
    fclose(f);
  }
  E = !strcmp(fmt, "f16") ? 5 : 8; F = !strcmp(fmt, "f16") ? 10 : !strcmp(fmt, "bf16") ? 7 : 23;
  bias = (1 << (E - 1)) - 1; emin = 2 - bias - F; emax = (1 << E) - 1 - bias;
  softfloat_detectTininess = softfloat_tininess_afterRounding;
  uint_fast8_t sfm = softfloat_mode(mode); mpfr_rnd_t rnd = mpfr_mode(mode); char op = opname[0];
  uint64_t match = 0, value_mismatch = 0, flag_mismatch = 0, kernel_diff = 0, kernel_nan_diff = 0,
           oracle_disagree = 0, nan_results = 0;
  int shown = 0;
#ifdef FLOATLIB_WITH_MPFX
  mpfx::IEEE754Context mctx(E, 1 + E + F, mpfx_mode(mode));
  const char *vname[4] = {"double_hw", "double_eft", "float_hw", "float_eft"};
  int nvariants = sqrt32 ? 2 : 4;
  uint64_t mval[4] = {0, 0, 0, 0}, mflag[4] = {0, 0, 0, 0};
  int mshown[4] = {0, 0, 0, 0};
#endif
  if (sqrt32) op = 'q';
  for (uint64_t i = 0; i < count; i++) {
    uint64_t w = 0; memcpy(&w, buf + width * i, width);
    uint32_t got, gotflags, kernel, a = 0, b = 0;
    if (sqrt32) { got = (uint32_t)w; gotflags = (w >> 32) & 31; kernel = (w >> 40) & 3; }
    else { got = w & 0xffff; gotflags = (w >> 16) & 31; kernel = (w >> 24) & 3; }
    if (kernel & 1) kernel_diff++;
    if (kernel & 2) kernel_nan_diff++;
    uint32_t ref; int refflags;
    if (sqrt32) {
      a = (uint32_t)(start + i);
      softfloat_roundingMode = sfm; softfloat_exceptionFlags = 0;
      float32_t x = { a }; ref = f32_sqrt(x).v; refflags = softfloat_exceptionFlags;
    } else {
      a = (uint32_t)((start + i) >> 16); b = (uint32_t)((start + i) & 0xffff);
      if (f16) {
        softfloat_roundingMode = sfm; softfloat_exceptionFlags = 0;
        ref = softfloat16(op, a, b); refflags = softfloat_exceptionFlags;
        int mflags; uint32_t m = emulate(op, a, b, rnd, &mflags);
        if (mflags != refflags || (!(is_nan(m) && is_nan(ref)) && m != ref)) {
          oracle_disagree++;
          if (shown++ < 5) printf("ORACLES %04x %c %04x: softfloat %04x/%02x mpfr %04x/%02x\n", a, op, b, ref, refflags, m, mflags);
        }
      } else ref = emulate(op, a, b, rnd, &refflags);
    }
    if (nofile) { got = ref; gotflags = refflags; }
#ifdef FLOATLIB_WITH_MPFX
    for (int v = 0; v < nvariants; v++) {
      int mf; uint32_t mv;
      switch (v) {
        case 0: mv = mpfx_eval<mpfx::Engine::FP_RTO, double>(op, a, b, mctx, &mf); break;
        case 1: mv = mpfx_eval<mpfx::Engine::EFT, double>(op, a, b, mctx, &mf); break;
        case 2: mv = mpfx_eval<mpfx::Engine::FP_RTO, float>(op, a, b, mctx, &mf); break;
        default: mv = mpfx_eval<mpfx::Engine::EFT, float>(op, a, b, mctx, &mf);
      }
      int nanin = is_nan(a) || (!sqrt32 && is_nan(b));
      int vbad = !((is_nan(mv) && is_nan(got)) || mv == got), fbad = !nanin && mf != (int)gotflags;
      if (vbad) mval[v]++;
      if (fbad) mflag[v]++;
      if ((vbad || fbad) && mshown[v]++ < 3)
        printf("MPFX %s %08x %c %08x: mpfx %08x/%02x floatlib %08x/%02x\n", vname[v], a, op, b, mv, mf, got, gotflags);
    }
#endif
    int bothnan = is_nan(got) && is_nan(ref);
    if (bothnan) nan_results++;
    int vok = bothnan || got == ref, fok = (int)gotflags == refflags;
    if (vok && fok) match++;
    else {
      if (!vok) value_mismatch++;
      if (!fok) flag_mismatch++;
      if (shown++ < 5) printf("MISMATCH %08x %c %08x: got %08x/%02x ref %08x/%02x\n", a, op, b, got, gotflags, ref, refflags);
    }
  }
  printf("RESULT %s %s %s %s %llu %llu match=%llu value_mismatch=%llu flag_mismatch=%llu nan_results=%llu "
         "kernel_diff=%llu kernel_nan_diff=%llu oracle_disagree=%llu\n", kind, fmt, opname, mode,
         (unsigned long long)start, (unsigned long long)count, (unsigned long long)match,
         (unsigned long long)value_mismatch, (unsigned long long)flag_mismatch, (unsigned long long)nan_results,
         (unsigned long long)kernel_diff, (unsigned long long)kernel_nan_diff, (unsigned long long)oracle_disagree);
#ifdef FLOATLIB_WITH_MPFX
  printf("MPFXRESULT %s %s %s %s %llu %llu", kind, fmt, opname, mode, (unsigned long long)start, (unsigned long long)count);
  for (int v = 0; v < nvariants; v++)
    printf(" %s_value=%llu %s_flags=%llu", vname[v], (unsigned long long)mval[v], vname[v], (unsigned long long)mflag[v]);
  printf("\n");
#endif
  return value_mismatch || flag_mismatch || kernel_diff || kernel_nan_diff || oracle_disagree ? 1 : 0;
}
