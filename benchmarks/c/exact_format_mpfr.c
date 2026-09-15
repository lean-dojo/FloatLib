#define _POSIX_C_SOURCE 200809L

#include <errno.h>
#include <inttypes.h>
#include <mpfr.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "benchmark_mpfr_protocol.h"

#define ARRAY_SIZE 16
FLOATLIB_BENCHMARK_REQUIRE_POWER_OF_TWO(ARRAY_SIZE);

#if defined(__GNUC__) || defined(__clang__)
#define NOINLINE __attribute__((noinline))
#else
#define NOINLINE
#endif

/*
 * We use MPFR as the binary software reference for the exact cross-format
 * workload. The input formula below is the C counterpart of
 * FloatLibBenchmarks.Support.ExactWorkload. Each rational goes through
 * mpfr_set_q once before timing, so input conversion is not charged to MPFR.
 *
 * MPFR's precision and rounding model is documented here:
 * https://www.mpfr.org/mpfr-current/mpfr.html
 */

static volatile uint64_t benchmark_warmup_sink;

struct format_case {
  unsigned total_bits;
  unsigned exponent_bits;
  mpfr_prec_t precision;
};

static const struct format_case format_cases[] = {
    {4, 2, 2},
    {5, 2, 3},
    {6, 3, 3},
    {7, 3, 4},
    {8, 4, 4},
    {16, 5, 11},
    {32, 8, 24},
    {64, 11, 53},
    {128, 15, 113},
    /*
     * Equal-storage companions for the custom wide binary rows. Their
     * 19-bit exponent field leaves total_bits - 19 significand bits,
     * including the implicit leading bit.
     */
    {256, 19, 237},
    {512, 19, 493},
    {1024, 19, 1005},
    {2048, 19, 2029},
    {4096, 19, 4077},
};

static const char *operations[] = {
    "add",
    "sub",
    "mul",
    "div",
    "sqrt",
    "fma",
};

static uint64_t monotonic_nanos(void) {
  struct timespec value;
  if (clock_gettime(CLOCK_MONOTONIC, &value) != 0) {
    perror("clock_gettime");
    exit(EXIT_FAILURE);
  }
  return (uint64_t)value.tv_sec * UINT64_C(1000000000) +
         (uint64_t)value.tv_nsec;
}

static size_t positive_size_text(const char *name, const char *text) {
  char *end = NULL;
  uintmax_t parsed;

  errno = 0;
  parsed = strtoumax(text, &end, 10);
  if (errno != 0 || end == text || *end != '\0' ||
      parsed == 0 || parsed > SIZE_MAX) {
    fprintf(stderr, "%s must be a positive size_t: %s\n", name, text);
    exit(EXIT_FAILURE);
  }
  return (size_t)parsed;
}

static size_t positive_size_env(const char *name, size_t fallback) {
  const char *text = getenv(name);
  return text == NULL || *text == '\0'
             ? fallback
             : positive_size_text(name, text);
}

static unsigned optional_width_env(void) {
  const char *text = getenv("FORMAT_COMPARE_WIDTH");
  if (text == NULL || *text == '\0') {
    return 0;
  }
  size_t width = positive_size_text("FORMAT_COMPARE_WIDTH", text);
  for (size_t i = 0;
       i < sizeof(format_cases) / sizeof(format_cases[0]);
       ++i) {
    if (width == format_cases[i].total_bits) {
      return (unsigned)width;
    }
  }
  fprintf(stderr, "unsupported FORMAT_COMPARE_WIDTH: %zu\n", width);
  exit(EXIT_FAILURE);
}

static const char *optional_operation_env(void) {
  const char *operation = getenv("FORMAT_COMPARE_OPERATION");
  if (operation == NULL || *operation == '\0') {
    return NULL;
  }
  for (size_t i = 0; i < sizeof(operations) / sizeof(operations[0]); ++i) {
    if (strcmp(operation, operations[i]) == 0) {
      return operation;
    }
  }
  fprintf(stderr, "unsupported FORMAT_COMPARE_OPERATION: %s\n", operation);
  exit(EXIT_FAILURE);
}

static size_t default_iterations(unsigned total_bits) {
  if (total_bits <= 64) {
    return 250000;
  }
  if (total_bits <= 256) {
    return 100000;
  }
  if (total_bits <= 1024) {
    return 50000;
  }
  return 20000;
}

static void set_exact_input(
    mpfr_t result, size_t index, size_t salt, int negative) {
  unsigned long numerator =
      (unsigned long)((index * salt + salt + 1) % 113 + 7);
  unsigned long denominator =
      (unsigned long)((index * 11 + salt) % 29 + 32);
  mpq_t exact;

  mpq_init(exact);
  mpq_set_ui(exact, numerator, denominator);
  if (negative) {
    mpq_neg(exact, exact);
  }
  int ternary = mpfr_set_q(result, exact, MPFR_RNDN);
  mpfr_subnormalize(result, ternary, MPFR_RNDN);
  mpq_clear(exact);
}

/*
 * MPFR lets us choose an exponent range as well as a precision. We set the
 * range to the compared binary format and call mpfr_subnormalize after every
 * rounding operation. This matters at four through eight bits: a precision-
 * only MPFR row has an effectively unbounded exponent range, so overflow and
 * gradual underflow would choose a different dependency chain.
 *
 * MPFR's exponent is one greater than the usual unbiased binary exponent.
 * mpfr_subnormalize treats `emin` through `emin + precision - 2` as the
 * subnormal interval, so `emin` must be the exponent of the smallest
 * subnormal rather than the smallest normal. The largest normal exponent is
 * still 2^exponent_bits - 1 - bias.
 */
static void select_format_range(const struct format_case *format) {
  mpfr_exp_t bias =
      ((mpfr_exp_t)1 << (format->exponent_bits - 1)) - 1;
  mpfr_exp_t minimum_exponent =
      2 - bias - (mpfr_exp_t)(format->precision - 1);
  mpfr_exp_t maximum_exponent =
      ((mpfr_exp_t)1 << format->exponent_bits) - 1 - bias;
  if (mpfr_set_emin(minimum_exponent) != 0 ||
      mpfr_set_emax(maximum_exponent) != 0) {
    fprintf(
        stderr,
        "MPFR cannot represent the exponent range for binary%u\n",
        format->total_bits);
    exit(EXIT_FAILURE);
  }
}

static void init_inputs(
    mpfr_prec_t precision,
    mpfr_t xs[ARRAY_SIZE],
    mpfr_t ys[ARRAY_SIZE],
    mpfr_t sqrt_xs[ARRAY_SIZE]) {
  for (size_t i = 0; i < ARRAY_SIZE; ++i) {
    mpfr_init2(xs[i], precision);
    mpfr_init2(ys[i], precision);
    mpfr_init2(sqrt_xs[i], precision);
    set_exact_input(xs[i], i, 37, i % 5 == 0);
    set_exact_input(ys[i], i, 61, i % 3 == 0);
    set_exact_input(sqrt_xs[i], i, 43, 0);
  }
}

static void clear_inputs(
    mpfr_t xs[ARRAY_SIZE],
    mpfr_t ys[ARRAY_SIZE],
    mpfr_t sqrt_xs[ARRAY_SIZE]) {
  for (size_t i = 0; i < ARRAY_SIZE; ++i) {
    mpfr_clear(xs[i]);
    mpfr_clear(ys[i]);
    mpfr_clear(sqrt_xs[i]);
  }
}

#define DEFINE_BINARY_RUNNER(NAME, OPERATION)                              \
  static NOINLINE struct floatlib_benchmark_result NAME(                  \
      size_t iterations,                                                   \
      mpfr_prec_t precision,                                               \
      mpfr_t xs[ARRAY_SIZE],                                               \
      mpfr_t ys[ARRAY_SIZE]) {                                             \
    struct floatlib_benchmark_result result = {                           \
        FLOATLIB_BENCHMARK_DEPENDENCY_SEED,                               \
        FLOATLIB_BENCHMARK_FIXTURE_TRACE_SEED,                            \
    };                                                                     \
    mpfr_t rounded;                                                        \
                                                                           \
    mpfr_init2(rounded, precision);                                        \
    while (iterations != 0) {                                              \
      --iterations;                                                        \
      size_t index = floatlib_benchmark_dependent_index(                  \
          result.sink, ARRAY_SIZE);                                        \
      result.fixture_trace = floatlib_benchmark_mix_fixture_trace(        \
          result.fixture_trace, index);                                    \
      int ternary = OPERATION(rounded, xs[index], ys[index], MPFR_RNDN);   \
      mpfr_subnormalize(rounded, ternary, MPFR_RNDN);                      \
      result.sink = floatlib_benchmark_mix_sink(                          \
          result.sink, floatlib_benchmark_mpfr_result_fingerprint(rounded)); \
    }                                                                      \
    mpfr_clear(rounded);                                                   \
    return result;                                                         \
  }

DEFINE_BINARY_RUNNER(run_add, mpfr_add)
DEFINE_BINARY_RUNNER(run_sub, mpfr_sub)
DEFINE_BINARY_RUNNER(run_mul, mpfr_mul)
DEFINE_BINARY_RUNNER(run_div, mpfr_div)

#undef DEFINE_BINARY_RUNNER

static NOINLINE struct floatlib_benchmark_result run_sqrt(
    size_t iterations,
    mpfr_prec_t precision,
    mpfr_t xs[ARRAY_SIZE]) {
  struct floatlib_benchmark_result result = {
      FLOATLIB_BENCHMARK_DEPENDENCY_SEED,
      FLOATLIB_BENCHMARK_FIXTURE_TRACE_SEED,
  };
  mpfr_t rounded;

  mpfr_init2(rounded, precision);
  while (iterations != 0) {
    --iterations;
    size_t index =
        floatlib_benchmark_dependent_index(result.sink, ARRAY_SIZE);
    result.fixture_trace = floatlib_benchmark_mix_fixture_trace(
        result.fixture_trace, index);
    int ternary = mpfr_sqrt(rounded, xs[index], MPFR_RNDN);
    mpfr_subnormalize(rounded, ternary, MPFR_RNDN);
    result.sink = floatlib_benchmark_mix_sink(
        result.sink, floatlib_benchmark_mpfr_result_fingerprint(rounded));
  }
  mpfr_clear(rounded);
  return result;
}

static NOINLINE struct floatlib_benchmark_result run_fma(
    size_t iterations,
    mpfr_prec_t precision,
    mpfr_t xs[ARRAY_SIZE],
    mpfr_t ys[ARRAY_SIZE]) {
  struct floatlib_benchmark_result result = {
      FLOATLIB_BENCHMARK_DEPENDENCY_SEED,
      FLOATLIB_BENCHMARK_FIXTURE_TRACE_SEED,
  };
  mpfr_t rounded;

  mpfr_init2(rounded, precision);
  while (iterations != 0) {
    --iterations;
    size_t index =
        floatlib_benchmark_dependent_index(result.sink, ARRAY_SIZE);
    result.fixture_trace = floatlib_benchmark_mix_fixture_trace(
        result.fixture_trace, index);
    int ternary = mpfr_fma(
        rounded, xs[index], ys[index], xs[ARRAY_SIZE - 1 - index],
        MPFR_RNDN);
    mpfr_subnormalize(rounded, ternary, MPFR_RNDN);
    result.sink = floatlib_benchmark_mix_sink(
        result.sink, floatlib_benchmark_mpfr_result_fingerprint(rounded));
  }
  mpfr_clear(rounded);
  return result;
}

static struct floatlib_benchmark_result run_operation(
    const char *operation,
    size_t iterations,
    mpfr_prec_t precision,
    mpfr_t xs[ARRAY_SIZE],
    mpfr_t ys[ARRAY_SIZE],
    mpfr_t sqrt_xs[ARRAY_SIZE]) {
  if (strcmp(operation, "add") == 0) {
    return run_add(iterations, precision, xs, ys);
  }
  if (strcmp(operation, "sub") == 0) {
    return run_sub(iterations, precision, xs, ys);
  }
  if (strcmp(operation, "mul") == 0) {
    return run_mul(iterations, precision, xs, ys);
  }
  if (strcmp(operation, "div") == 0) {
    return run_div(iterations, precision, xs, ys);
  }
  if (strcmp(operation, "sqrt") == 0) {
    return run_sqrt(iterations, precision, sqrt_xs);
  }
  if (strcmp(operation, "fma") == 0) {
    return run_fma(iterations, precision, xs, ys);
  }
  abort();
}

/*
 * We only keep a compact MPFR fingerprint in the timed loop. Rather than
 * pretending that it is lossless, we check every possible fixture result
 * first and refuse to time a row when two unequal values collide. Equal
 * results are common at tiny precisions and are, of course, allowed.
 */
static void validate_fixture_fingerprints(
    const struct format_case *format,
    const char *operation,
    mpfr_t xs[ARRAY_SIZE],
    mpfr_t ys[ARRAY_SIZE],
    mpfr_t sqrt_xs[ARRAY_SIZE]) {
  uint64_t fingerprints[ARRAY_SIZE];
  mpfr_t rounded[ARRAY_SIZE];

  for (size_t index = 0; index < ARRAY_SIZE; ++index) {
    mpfr_init2(rounded[index], format->precision);
    int ternary;
    if (strcmp(operation, "add") == 0) {
      ternary = mpfr_add(rounded[index], xs[index], ys[index], MPFR_RNDN);
    } else if (strcmp(operation, "sub") == 0) {
      ternary = mpfr_sub(rounded[index], xs[index], ys[index], MPFR_RNDN);
    } else if (strcmp(operation, "mul") == 0) {
      ternary = mpfr_mul(rounded[index], xs[index], ys[index], MPFR_RNDN);
    } else if (strcmp(operation, "div") == 0) {
      ternary = mpfr_div(rounded[index], xs[index], ys[index], MPFR_RNDN);
    } else if (strcmp(operation, "sqrt") == 0) {
      ternary = mpfr_sqrt(rounded[index], sqrt_xs[index], MPFR_RNDN);
    } else if (strcmp(operation, "fma") == 0) {
      ternary = mpfr_fma(
          rounded[index], xs[index], ys[index],
          xs[ARRAY_SIZE - 1 - index],
          MPFR_RNDN);
    } else {
      abort();
    }
    mpfr_subnormalize(rounded[index], ternary, MPFR_RNDN);
    fingerprints[index] =
        floatlib_benchmark_mpfr_result_fingerprint(rounded[index]);
    for (size_t previous = 0; previous < index; ++previous) {
      if (fingerprints[index] == fingerprints[previous] &&
          !mpfr_equal_p(rounded[index], rounded[previous])) {
        fprintf(
            stderr,
            "MPFR fixture fingerprint collision at p%ld %s: "
            "vectors %zu and %zu both hash to %" PRIu64 "\n",
            (long)format->precision, operation, previous, index,
            fingerprints[index]);
        for (size_t clear_index = 0;
             clear_index <= index;
             ++clear_index) {
          mpfr_clear(rounded[clear_index]);
        }
        exit(EXIT_FAILURE);
      }
    }
  }
  for (size_t index = 0; index < ARRAY_SIZE; ++index) {
    mpfr_clear(rounded[index]);
  }
}

static void time_row(
    const struct format_case *format,
    const char *operation,
    size_t iterations,
    size_t warmup_iterations,
    size_t agreement_iterations) {
  mpfr_t xs[ARRAY_SIZE];
  mpfr_t ys[ARRAY_SIZE];
  mpfr_t sqrt_xs[ARRAY_SIZE];

  select_format_range(format);
  init_inputs(format->precision, xs, ys, sqrt_xs);
  validate_fixture_fingerprints(format, operation, xs, ys, sqrt_xs);
  benchmark_warmup_sink =
      run_operation(
          operation, warmup_iterations, format->precision,
          xs, ys, sqrt_xs).sink;
  struct floatlib_benchmark_result agreement =
      run_operation(
          operation, agreement_iterations, format->precision,
          xs, ys, sqrt_xs);
  uint64_t start = monotonic_nanos();
  struct floatlib_benchmark_result result =
      run_operation(
          operation, iterations, format->precision,
          xs, ys, sqrt_xs);
  uint64_t stop = monotonic_nanos();
  printf(
      "MPFR,binary-reference,mpfr-binary%u-p%ld-e%u,%u,%s,"
      "software-reference,MPFR %s RNDN with matched exponent range and "
      "gradual underflow,result-dependent-fixture-chain,"
      "%zu,%" PRIu64 ",%" PRIu64 ",%" PRIu64
      ",%zu,%" PRIu64 ",%" PRIu64 "\n",
      format->total_bits, (long)format->precision, format->exponent_bits,
      format->total_bits, operation,
      MPFR_VERSION_STRING, iterations, stop - start, result.sink,
      result.fixture_trace, agreement_iterations, agreement.sink,
      agreement.fixture_trace);
  clear_inputs(xs, ys, sqrt_xs);
}

int main(void) {
  unsigned selected_width = optional_width_env();
  const char *selected_operation = optional_operation_env();
  size_t warmup_iterations =
      positive_size_env("FORMAT_COMPARE_WARMUP_ITERATIONS", 64);
  size_t agreement_iterations =
      positive_size_env("FORMAT_COMPARE_AGREEMENT_ITERATIONS", 256);

  puts(
      "implementation,family,format,totalBits,operation,executionClass,"
      "backend,measurementMethod,iterations,totalNanos,sink,fixtureTraceDigest,"
      "agreementIterations,agreementSink,agreementFixtureTraceDigest");
  for (size_t i = 0;
       i < sizeof(format_cases) / sizeof(format_cases[0]);
       ++i) {
    const struct format_case *format = &format_cases[i];
    if (selected_width != 0 && selected_width != format->total_bits) {
      continue;
    }
    size_t iterations =
        positive_size_env(
            "FORMAT_COMPARE_ITERATIONS",
            default_iterations(format->total_bits));
    for (size_t j = 0;
         j < sizeof(operations) / sizeof(operations[0]);
         ++j) {
      const char *operation = operations[j];
      if (selected_operation != NULL &&
          strcmp(selected_operation, operation) != 0) {
        continue;
      }
      time_row(
          format, operation, iterations, warmup_iterations,
          agreement_iterations);
    }
  }

  mpfr_free_cache();
  return EXIT_SUCCESS;
}
