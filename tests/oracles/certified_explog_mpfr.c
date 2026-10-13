/*
 * Copyright (c) 2026 FloatLib
 * Released under MIT license as described in the file LICENSE.
 */

/* Correctly rounded MPFR reference for exp, log, expm1, and log1p in binary16, bfloat16, binary32,
   and binary64. Reads one encoded input per line on stdin and prints the encoded result, or inf or
   nan for a non-finite reference.

     certified_explog_mpfr exp|log|expm1|log1p 16|bf16|32|64 < WORDS */
#include <gmp.h>
#include <mpfr.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static long E, F, bias, width;
static void decode(mpfr_t out, unsigned long long n) {
  int sign = (n >> (width - 1)) & 1; long ef = (long)((n >> F) & ((1ULL << E) - 1));
  unsigned long long frac = n & ((1ULL << F) - 1); mpz_t m; mpz_init(m); mpz_set_ui(m, 0);
  if (ef == (1L << E) - 1) {
    if (frac) mpfr_set_nan(out); else mpfr_set_inf(out, sign ? -1 : 1);
    mpz_clear(m);
    return;
  }
  mpz_import(m, 1, 1, sizeof frac, 0, 0, &frac); long ex;
  if (ef == 0) ex = 1 - bias - F; else { mpz_setbit(m, F); ex = ef - bias - F; }
  mpfr_set_z_2exp(out, m, ex, MPFR_RNDN); if (sign) mpfr_neg(out, out, MPFR_RNDN); mpz_clear(m);
}
static unsigned long long encode(mpfr_srcptr v) {
  unsigned long long s = mpfr_signbit(v) ? 1ULL << (width - 1) : 0;
  if (mpfr_zero_p(v)) return s;
  if (mpfr_inf_p(v)) return s | (((1ULL << E) - 1) << F);
  mpz_t m; mpz_init(m); long ex = mpfr_get_z_2exp(m, v); mpz_abs(m, m);
  long k = (long)mpz_sizeinbase(m, 2), shift = (F + 1) - k;
  if (shift > 0) mpz_mul_2exp(m, m, shift); else if (shift < 0) mpz_fdiv_q_2exp(m, m, -shift);
  ex -= shift; long ef = ex + bias + F; unsigned long long out;
  if (ef >= 1) { mpz_clrbit(m, F); out = ((unsigned long long)ef << F) | mpz_get_ui(m); }
  else { mpz_fdiv_q_2exp(m, m, 1 - ef); out = mpz_get_ui(m); }
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
  if (argc != 3) { fprintf(stderr, "usage: certified_explog_mpfr exp|log|expm1|log1p 16|bf16|32|64 < WORDS\n"); return 2; }
  if (!strcmp(argv[2], "bf16")) { width = 16; E = 8; } else { width = atol(argv[2]); E = width == 16 ? 5 : width == 32 ? 8 : 11; }
  F = width - 1 - E; bias = (1L << (E - 1)) - 1;
  mpfr_set_emin(2 - bias - F); mpfr_set_emax((1L << E) - 1 - bias);
  mpfr_t x, r; mpfr_init2(x, F + 1); mpfr_init2(r, F + 1);
  unsigned long long n;
  while (scanf("%llu", &n) == 1) {
    decode(x, n);
    int t = apply(argv[1], r, x);
    t = mpfr_check_range(r, t, MPFR_RNDN); mpfr_subnormalize(r, t, MPFR_RNDN);
    if (mpfr_nan_p(r)) printf("nan\n"); else if (mpfr_inf_p(r)) printf("inf\n"); else printf("%llu\n", encode(r));
  }
  return 0;
}
