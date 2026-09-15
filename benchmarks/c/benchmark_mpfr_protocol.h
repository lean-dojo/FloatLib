#ifndef FLOATLIB_BENCHMARK_MPFR_PROTOCOL_H
#define FLOATLIB_BENCHMARK_MPFR_PROTOCOL_H

/*
 * MPFR half of the shared scalar benchmark protocol.
 *
 * We read one deterministic 64-bit window from MPFR's normalized
 * significand. That keeps the result observable without allocating a GMP
 * integer or converting through the host FPU inside the timed loop. MPFR
 * documents this representation through its custom interface:
 * https://www.mpfr.org/mpfr-current/mpfr.html
 *
 * This is deliberately a fingerprint, not a lossless encoding of an
 * arbitrary-width value. Before timing, we evaluate all sixteen possible
 * results and reject the row if unequal MPFR values share a fingerprint.
 * Equal results are common in the smallest formats and are not collisions.
 */

#include <mpfr.h>

#include "benchmark_protocol.h"

static inline uint64_t floatlib_benchmark_mpfr_low_significand_bits(
    mpfr_srcptr value) {
  if (mpfr_zero_p(value)) {
    return 0;
  }
  mpfr_prec_t precision = mpfr_get_prec(value);
  size_t limb_count =
      ((size_t)precision + GMP_NUMB_BITS - 1) / GMP_NUMB_BITS;
  unsigned padding =
      (unsigned)(limb_count * GMP_NUMB_BITS - (size_t)precision);
  const mp_limb_t *limbs =
      (const mp_limb_t *)mpfr_custom_get_significand(value);

#if GMP_NUMB_BITS == 64
  uint64_t low = (uint64_t)(limbs[0] >> padding);
  if (padding != 0 && limb_count > 1) {
    low |= (uint64_t)limbs[1] << (64 - padding);
  }
  return low;
#elif GMP_NUMB_BITS == 32
  uint64_t low = (uint64_t)(limbs[0] >> padding);
  if (padding == 0) {
    if (limb_count > 1) {
      low |= (uint64_t)limbs[1] << 32;
    }
    return low;
  }
  if (limb_count > 1) {
    low |= (uint64_t)limbs[1] << (32 - padding);
  }
  if (limb_count > 2) {
    low |= (uint64_t)limbs[2] << (64 - padding);
  }
  return low;
#else
#error "The benchmark protocol supports GMP limbs of 32 or 64 bits."
#endif
}

static inline uint64_t floatlib_benchmark_mpfr_result_fingerprint(
    mpfr_srcptr value) {
  int negative = mpfr_signbit(value) != 0;
  if (mpfr_nan_p(value)) {
    return FLOATLIB_BENCHMARK_FINGERPRINT_NAN;
  }
  if (mpfr_inf_p(value)) {
    return floatlib_benchmark_special_fingerprint(
        FLOATLIB_BENCHMARK_FINGERPRINT_INFINITY, negative);
  }
  if (mpfr_zero_p(value)) {
    return floatlib_benchmark_special_fingerprint(
        FLOATLIB_BENCHMARK_FINGERPRINT_ZERO, negative);
  }
  /*
   * Above one machine word, the low normalized-significand word is exactly
   * the low stored fraction word used by FloatLib. Keeping the dependency
   * token at that boundary avoids charging either implementation for a
   * full arbitrary-precision decode inside the timed loop.
   */
  if (mpfr_get_prec(value) > 64) {
    return floatlib_benchmark_mpfr_low_significand_bits(value);
  }
  return floatlib_benchmark_finite_fingerprint(
      negative, (int64_t)mpfr_get_exp(value),
      floatlib_benchmark_mpfr_low_significand_bits(value));
}

#endif
