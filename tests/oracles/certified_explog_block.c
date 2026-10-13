/*
 * Copyright (c) 2026 FloatLib
 * Released under MIT license as described in the file LICENSE.
 */

/* Compare a block of certified binary32 results written by `execFloatCertifiedExpLog range` with
   MPFR's correctly rounded values. 0xFFFFFFFF in the block means the call returned nothing.

     certified_explog_block exp|log|expm1|log1p START COUNT BLOCK */
#include <gmp.h>
#include <mpfr.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static uint32_t encode(mpfr_srcptr v) {
  uint32_t s = mpfr_signbit(v) ? 0x80000000u : 0;
  if (mpfr_zero_p(v)) return s;
  mpz_t m; mpz_init(m); long ex = mpfr_get_z_2exp(m, v); mpz_abs(m, m);
  long k = (long)mpz_sizeinbase(m, 2), shift = 24 - k;
  if (shift > 0) mpz_mul_2exp(m, m, shift); else if (shift < 0) mpz_fdiv_q_2exp(m, m, -shift);
  ex -= shift; long ef = ex + 127 + 23; uint32_t out;
  if (ef >= 1) { mpz_clrbit(m, 23); out = ((uint32_t)ef << 23) | (uint32_t)mpz_get_ui(m); }
  else { mpz_fdiv_q_2exp(m, m, 1 - ef); out = (uint32_t)mpz_get_ui(m); }
  mpz_clear(m); return s | out;
}
static int apply(const char *fn, mpfr_ptr r, mpfr_srcptr x) {
  if (!strcmp(fn, "exp")) return mpfr_exp(r, x, MPFR_RNDN);
  if (!strcmp(fn, "log")) return mpfr_log(r, x, MPFR_RNDN);
  if (!strcmp(fn, "expm1")) return mpfr_expm1(r, x, MPFR_RNDN);
  if (!strcmp(fn, "log1p")) return mpfr_log1p(r, x, MPFR_RNDN);
  fprintf(stderr, "unknown function %s\n", fn); exit(2);
}
int main(int argc, char **argv) {
  if (argc != 5) { fprintf(stderr, "usage: certified_explog_block exp|log|expm1|log1p START COUNT BLOCK\n"); return 2; }
  const char *fn = argv[1]; uint64_t start = strtoull(argv[2], 0, 10), count = strtoull(argv[3], 0, 10);
  FILE *f = fopen(argv[4], "rb"); if (!f) { perror(argv[4]); return 2; }
  uint32_t *got = malloc(4 * count); if (fread(got, 4, count, f) != count) { fprintf(stderr, "short chunk\n"); return 2; } fclose(f);
  mpfr_set_emin(-148); mpfr_set_emax(128);
  mpfr_t x, r; mpfr_init2(x, 24); mpfr_init2(r, 24);
  uint64_t match = 0, mismatch = 0, none_ok_ref = 0, none_nonfinite_in = 0, none_finite_ref = 0, value_nonfinite_ref = 0;
  int shown = 0;
  for (uint64_t i = 0; i < count; i++) {
    uint32_t b = (uint32_t)(start + i), g = got[i];
    if (((b >> 23) & 0xff) == 0xff) { if (g == 0xFFFFFFFFu) none_nonfinite_in++; else { mismatch++; if (shown++ < 5) printf("MISMATCH nonfinite-input %08x got %08x\n", b, g); } continue; }
    float xf; memcpy(&xf, &b, 4); mpfr_set_flt(x, xf, MPFR_RNDN);
    int t = apply(argv[1], r, x);
    t = mpfr_check_range(r, t, MPFR_RNDN); mpfr_subnormalize(r, t, MPFR_RNDN);
    if (mpfr_nan_p(r) || mpfr_inf_p(r)) { if (g == 0xFFFFFFFFu) none_ok_ref++; else { value_nonfinite_ref++; if (shown++ < 5) printf("VALUE-FOR-NONFINITE %08x got %08x\n", b, g); } continue; }
    uint32_t e = encode(r);
    if (g == 0xFFFFFFFFu) { none_finite_ref++; if (shown++ < 5) printf("NONE-FOR-FINITE %08x ref %08x\n", b, e); }
    else if (g == e) match++;
    else { mismatch++; if (shown++ < 5) printf("MISMATCH %08x got %08x ref %08x\n", b, g, e); }
  }
  printf("RESULT %s %llu %llu match=%llu mismatch=%llu none_overflow_or_undefined=%llu none_nonfinite_input=%llu none_finite_ref=%llu value_nonfinite_ref=%llu\n", fn,
    (unsigned long long)start, (unsigned long long)count, (unsigned long long)match, (unsigned long long)mismatch, (unsigned long long)none_ok_ref,
    (unsigned long long)none_nonfinite_in, (unsigned long long)none_finite_ref, (unsigned long long)value_nonfinite_ref);
  return mismatch || none_finite_ref || value_nonfinite_ref ? 1 : 0;
}
