// Copyright (c) 2026 FloatLib. Released under MIT license as described in the file LICENSE.
//
// Standalone reproducers for the four MPFX bugs, checked against MPFR, Berkeley SoftFloat, and the
// host FPU, with no FloatLib code involved. `repro N` runs case N alone, which lets a debug build
// of MPFX abort on case 3 without hiding the others.
#include <mpfx.hpp>
extern "C" {
#include "softfloat.h"
}
#include <cfenv>
#include <cmath>
#include <cstdio>
#include <mpfr.h>
using namespace mpfx;

// MPFR emulation of an IEEE-style format: precision p, exponent range of the format, subnormals.
static double mpfr_round_op(int p, int emin_sub, int emax, char op, double a, double b, double c,
                            mpfr_rnd_t rnd, int *ovf, int *inex) {
  mpfr_set_emin(mpfr_get_emin_min()); mpfr_set_emax(mpfr_get_emax_max());
  mpfr_t x, y, z, r; mpfr_inits2(200, x, y, z, (mpfr_ptr)0); mpfr_init2(r, p);
  mpfr_set_d(x, a, MPFR_RNDN); mpfr_set_d(y, b, MPFR_RNDN); mpfr_set_d(z, c, MPFR_RNDN);
  mpfr_set_emin(emin_sub); mpfr_set_emax(emax); mpfr_clear_flags();
  int t = op == '*' ? mpfr_mul(r, x, y, rnd) : op == 'q' ? mpfr_sqrt(r, x, rnd) : mpfr_fma(r, x, y, z, rnd);
  t = mpfr_check_range(r, t, rnd); t = mpfr_subnormalize(r, t, rnd);
  *ovf = mpfr_overflow_p(); *inex = t != 0;
  double out = mpfr_get_d(r, MPFR_RNDN);
  mpfr_set_emin(mpfr_get_emin_min()); mpfr_set_emax(mpfr_get_emax_max());
  mpfr_clears(x, y, z, r, (mpfr_ptr)0); return out;
}

int main(int argc, char **argv) {
  setvbuf(stdout, nullptr, _IONBF, 0);
  int only = argc > 1 ? atoi(argv[1]) : 0;
  if (!only || only == 1) {
    printf("1. Exact zero sum under round toward negative (IEEE 754-2019 6.3 requires -0)\n");
    IEEE754Context h(5, 16, RM::RTN);
    double hw = add<Engine::FP_RTO>(1.0, -1.0, h), eft = add<Engine::EFT>(1.0, -1.0, h);
    double hwsub = sub<Engine::FP_RTO>(1.0, 1.0, h);
    double hwfma = fma<Engine::FP_RTO>(1.0, 1.0, -1.0, h);
    mpfr_t r, a, b; mpfr_inits2(11, r, a, b, (mpfr_ptr)0); mpfr_set_d(a, 1.0, MPFR_RNDN); mpfr_set_d(b, -1.0, MPFR_RNDN);
    mpfr_add(r, a, b, MPFR_RNDD); int mpfr_neg = mpfr_signbit(r); mpfr_clears(r, a, b, (mpfr_ptr)0);
    softfloat_roundingMode = softfloat_round_min; float16_t one = {0x3c00}, mone = {0xbc00};
    uint16_t sf = f16_add(one, mone).v;
    std::fesetround(FE_DOWNWARD); volatile double u = 1.0, v = -1.0; double host = u + v; std::fesetround(FE_TONEAREST);
    printf("   binary16 1 + (-1): MPFX hw %s, eft %s; 1 - 1 hw %s; fma(1,1,-1) hw %s\n",
           std::signbit(hw) ? "-0" : "+0", std::signbit(eft) ? "-0" : "+0", std::signbit(hwsub) ? "-0" : "+0", std::signbit(hwfma) ? "-0" : "+0");
    printf("   MPFR RNDD %s, SoftFloat f16_add 0x%04x, host FPU %s\n", mpfr_neg ? "-0" : "+0", sf, std::signbit(host) ? "-0" : "+0");
  }
  if (!only || only == 2) {
    printf("2. sqrt(-inf) must signal invalid (IEEE 754-2019 7.2; C Annex F.10.4.5)\n");
    IEEE754Context h(5, 16, RM::RNE);
    flags.reset(); double r1 = mpfx::sqrt<Engine::FP_RTO>(-INFINITY, h); bool i1 = flags.invalid();
    flags.reset(); double r2 = mpfx::sqrt<Engine::FP_RTO>(-1.0, h); bool i2 = flags.invalid();
    softfloat_roundingMode = softfloat_round_near_even; softfloat_exceptionFlags = 0;
    float16_t ninf = {0xfc00}; f16_sqrt(ninf); bool sfinv = softfloat_exceptionFlags & softfloat_flag_invalid;
    std::feclearexcept(FE_ALL_EXCEPT); volatile double m = -INFINITY; volatile double s = std::sqrt(m); (void)s;
    bool hostinv = std::fetestexcept(FE_INVALID);
    printf("   MPFX sqrt(-inf) = %g invalid=%d; sqrt(-1) = %g invalid=%d; SoftFloat invalid=%d; host invalid=%d\n", r1, i1, r2, i2, sfinv, hostinv);
  }
  if (!only || only == 3) {
    printf("3. bfloat16 overflow must raise the overflow flag (IEEE 754-2019 7.4)\n");
    IEEE754Context bf(8, 16, RM::RNE);
    flags.reset(); float rf = mul<Engine::FP_RTO, Flags::ALL_FLAGS, float>(0x1p100f, 0x1p100f, bf); bool of = flags.overflow();
    flags.reset(); double rd = mul<Engine::FP_RTO>(0x1p100, 0x1p100, bf); bool od = flags.overflow();
    int ovf, inex; double ref = mpfr_round_op(8, -132, 128, '*', 0x1p100, 0x1p100, 0, MPFR_RNDN, &ovf, &inex);
    printf("   2^100 * 2^100: MPFX float container %g overflow=%d; double container %g overflow=%d; MPFR %g overflow=%d\n", rf, of, rd, od, ref, ovf);
  }
  if (!only || only == 4) {
    printf("4. EFT engine: error terms that underflow the container\n");
    IEEE754Context c(11, 62, RM::RNE);   // A(51, -1072): 11-bit exponent, 50 fraction bits
    double x = std::ldexp(3.0, -1072);
    flags.reset(); double hw = mpfx::sqrt<Engine::FP_RTO>(x, c); bool hwi = flags.inexact();
    flags.reset(); double eft = mpfx::sqrt<Engine::EFT>(x, c); bool efti = flags.inexact();
    int ovf, inex; double ref = mpfr_round_op(51, -1071, 1024, 'q', x, 0, 0, MPFR_RNDN, &ovf, &inex);
    printf("   sqrt(3*2^-1072) at 51 bits RNE: MPFR %a inexact=%d; MPFX hw %a inexact=%d; eft %a inexact=%d\n", ref, inex, hw, hwi, eft, efti);
    IEEE754Context bf(8, 16, RM::RTP);
    float a = 0x1.8ep-63f, b = 0x1.bap-90f, z = -0x1.4p-55f;
    flags.reset(); float fh = fma<Engine::FP_RTO, Flags::ALL_FLAGS, float>(a, b, z, bf); bool fhi = flags.inexact();
    flags.reset(); float fe = fma<Engine::EFT, Flags::ALL_FLAGS, float>(a, b, z, bf); bool fei = flags.inexact();
    double ref2 = mpfr_round_op(8, -132, 128, 'f', a, b, z, MPFR_RNDU, &ovf, &inex);
    printf("   bfloat16 fma(%a, %a, %a) RTP: MPFR %a inexact=%d; MPFX float hw %a inexact=%d; eft %a inexact=%d\n", a, b, z, ref2, inex, fh, fhi, fe, fei);
    IEEE754Context bfz(8, 16, RM::RTP);
    flags.reset(); float m1 = mul<Engine::EFT, Flags::ALL_FLAGS, float>(0x1p-70f, 0x1p-90f, bfz); bool m1i = flags.inexact(), m1u = flags.underflow_after_rounding();
    double ref3 = mpfr_round_op(8, -132, 128, '*', 0x1p-70, 0x1p-90, 0, MPFR_RNDU, &ovf, &inex);
    printf("   bfloat16 2^-70 * 2^-90 RTP: MPFR %a inexact=%d; MPFX float eft %a inexact=%d underflow=%d\n", ref3, inex, m1, m1i, m1u);
  }
}
