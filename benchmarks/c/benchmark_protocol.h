#ifndef FLOATLIB_BENCHMARK_PROTOCOL_H
#define FLOATLIB_BENCHMARK_PROTOCOL_H

/*
 * One scalar benchmark protocol for every adapter.
 *
 * We wanted the Lean, native C, MPFR, SoftFloat, Flocq, CPython, and
 * Stillwater rows to carry the same dependency. The result stays observable
 * and chooses the next ordinary fixture, so the next operation cannot begin
 * before the current one finishes.
 *
 * We adapted the dependency-chain part directly from the uops.info latency
 * methodology:
 * Andreas Abel and Jan Reineke, "uops.info", ASPLOS 2019.
 * https://doi.org/10.1145/3297858.3304062
 *
 * The finite fixture set is our addition. Feeding one floating-point result
 * back as the next operand makes multiplication, division, and square root
 * drift into overflow, underflow, or a fixed point. That would benchmark the
 * recurrence instead of the operation we wanted to compare.
 */

#include <stddef.h>
#include <stdint.h>

#define FLOATLIB_BENCHMARK_DEPENDENCY_SEED UINT64_C(14695981039346656037)
#define FLOATLIB_BENCHMARK_FIXTURE_TRACE_SEED \
  FLOATLIB_BENCHMARK_DEPENDENCY_SEED
#define FLOATLIB_BENCHMARK_FINGERPRINT_EXPONENT_MIX \
  UINT64_C(0x9e3779b97f4a7c15)
#define FLOATLIB_BENCHMARK_FINGERPRINT_SIGN \
  UINT64_C(0x8000000000000000)
#define FLOATLIB_BENCHMARK_FINGERPRINT_ZERO \
  UINT64_C(0x2d358dccaa6c78a5)
#define FLOATLIB_BENCHMARK_FINGERPRINT_INFINITY \
  UINT64_C(0x8bb84b93962eacc9)
#define FLOATLIB_BENCHMARK_FINGERPRINT_NAN \
  UINT64_C(0x4f1bbcdc6764c1ab)

#define FLOATLIB_BENCHMARK_REQUIRE_POWER_OF_TWO(FIXTURE_COUNT) \
  _Static_assert( \
      ((FIXTURE_COUNT) & ((FIXTURE_COUNT) - 1)) == 0, \
      "benchmark fixture count must be a power of two")

static inline uint64_t floatlib_benchmark_mix_sink(
    uint64_t sink, uint64_t value) {
  return (sink ^ value) * UINT64_C(1099511628211);
}

/*
 * We keep the selected fixture indices separately from the result checksum.
 * The old benchmark only followed the loop counter, and a final checksum did
 * not make that mistake obvious. This trace lets the runner reject that old
 * sequence without asking every numeric format for the same representation.
 */
static inline uint64_t floatlib_benchmark_mix_fixture_trace(
    uint64_t trace, size_t index) {
  return floatlib_benchmark_mix_sink(trace, (uint64_t)index);
}

struct floatlib_benchmark_result {
  uint64_t sink;
  uint64_t fixture_trace;
};

/*
 * We let the result select an existing input instead of becoming the input.
 * This preserves the latency chain while keeping every operation on the same
 * small set of ordinary values.
 */
static inline size_t floatlib_benchmark_dependent_index(
    uint64_t sink, size_t fixture_count) {
  uint64_t folded = sink ^ (sink >> 32);
  folded ^= folded >> 16;
  return (size_t)folded & (fixture_count - 1);
}

/*
 * Native IEEE values expose bits, while MPFR exposes a sign, exponent, and
 * significand. We normalize both here so the binary32 and binary64 preflight
 * can check that native C and MPFR followed exactly the same chain.
 */
static inline uint64_t floatlib_benchmark_finite_fingerprint(
    int negative, int64_t exponent, uint64_t significand) {
  return significand ^
      ((uint64_t)exponent * FLOATLIB_BENCHMARK_FINGERPRINT_EXPONENT_MIX) ^
      (negative ? FLOATLIB_BENCHMARK_FINGERPRINT_SIGN : 0);
}

static inline uint64_t floatlib_benchmark_special_fingerprint(
    uint64_t tag, int negative) {
  return tag ^ (negative ? FLOATLIB_BENCHMARK_FINGERPRINT_SIGN : 0);
}

static inline uint64_t floatlib_benchmark_binary32_fingerprint(
    uint32_t bits) {
  int negative = (bits >> 31) != 0;
  uint32_t exponent_field = (bits >> 23) & UINT32_C(0xff);
  uint32_t significand = bits & UINT32_C(0x7fffff);

  if (exponent_field == UINT32_C(0xff)) {
    return significand == 0
        ? floatlib_benchmark_special_fingerprint(
              FLOATLIB_BENCHMARK_FINGERPRINT_INFINITY, negative)
        : FLOATLIB_BENCHMARK_FINGERPRINT_NAN;
  }
  if (exponent_field == 0) {
    if (significand == 0) {
      return floatlib_benchmark_special_fingerprint(
          FLOATLIB_BENCHMARK_FINGERPRINT_ZERO, negative);
    }
    unsigned shift = 0;
    while ((significand & (UINT32_C(1) << 23)) == 0) {
      significand <<= 1;
      ++shift;
    }
    return floatlib_benchmark_finite_fingerprint(
        negative, -INT64_C(125) - (int64_t)shift, significand);
  }
  return floatlib_benchmark_finite_fingerprint(
      negative, (int64_t)exponent_field - INT64_C(126),
      (UINT64_C(1) << 23) | significand);
}

static inline uint64_t floatlib_benchmark_binary64_fingerprint(
    uint64_t bits) {
  int negative = (bits >> 63) != 0;
  uint64_t exponent_field = (bits >> 52) & UINT64_C(0x7ff);
  uint64_t significand = bits & UINT64_C(0x000fffffffffffff);

  if (exponent_field == UINT64_C(0x7ff)) {
    return significand == 0
        ? floatlib_benchmark_special_fingerprint(
              FLOATLIB_BENCHMARK_FINGERPRINT_INFINITY, negative)
        : FLOATLIB_BENCHMARK_FINGERPRINT_NAN;
  }
  if (exponent_field == 0) {
    if (significand == 0) {
      return floatlib_benchmark_special_fingerprint(
          FLOATLIB_BENCHMARK_FINGERPRINT_ZERO, negative);
    }
    unsigned shift = 0;
    while ((significand & (UINT64_C(1) << 52)) == 0) {
      significand <<= 1;
      ++shift;
    }
    return floatlib_benchmark_finite_fingerprint(
        negative, -INT64_C(1021) - (int64_t)shift, significand);
  }
  return floatlib_benchmark_finite_fingerprint(
      negative, (int64_t)exponent_field - INT64_C(1022),
      (UINT64_C(1) << 52) | significand);
}

#endif
