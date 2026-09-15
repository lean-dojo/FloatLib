#define _POSIX_C_SOURCE 200809L

/*
 * We only call a row hardware when the host provides that format. This adapter
 * therefore measures native binary32 and binary64 only.
 *
 * Input construction mirrors FloatLibBenchmarks.Support.ExactWorkload. MPFR
 * rounds each exact rational once before timing, then a preflight checks every
 * native result against MPFR on those already-rounded inputs. MPFR is only the
 * checker here; the measured loop contains native C arithmetic and result
 * mixing.
 *
 * MPFR reference: https://www.mpfr.org/mpfr-current/mpfr.html
 */

#include <errno.h>
#include <fenv.h>
#include <float.h>
#include <inttypes.h>
#include <math.h>
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

static volatile uint64_t benchmark_warmup_sink;

enum operation {
  OP_ADD,
  OP_SUB,
  OP_MUL,
  OP_DIV,
  OP_SQRT,
  OP_FMA,
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

static unsigned selected_width(void) {
  const char *text = getenv("FORMAT_COMPARE_WIDTH");
  if (text == NULL || *text == '\0') {
    fprintf(stderr, "FORMAT_COMPARE_WIDTH is required\n");
    exit(EXIT_FAILURE);
  }
  size_t width = positive_size_text("FORMAT_COMPARE_WIDTH", text);
  if (width != 32 && width != 64) {
    fprintf(stderr, "native C comparison supports only width 32 or 64\n");
    exit(EXIT_FAILURE);
  }
  return (unsigned)width;
}

static enum operation selected_operation(void) {
  const char *text = getenv("FORMAT_COMPARE_OPERATION");
  if (text == NULL) {
    fprintf(stderr, "FORMAT_COMPARE_OPERATION is required\n");
    exit(EXIT_FAILURE);
  }
  if (strcmp(text, "add") == 0) return OP_ADD;
  if (strcmp(text, "sub") == 0) return OP_SUB;
  if (strcmp(text, "mul") == 0) return OP_MUL;
  if (strcmp(text, "div") == 0) return OP_DIV;
  if (strcmp(text, "sqrt") == 0) return OP_SQRT;
  if (strcmp(text, "fma") == 0) return OP_FMA;
  fprintf(stderr, "unsupported FORMAT_COMPARE_OPERATION: %s\n", text);
  exit(EXIT_FAILURE);
}

static const char *operation_name(enum operation operation) {
  switch (operation) {
    case OP_ADD: return "add";
    case OP_SUB: return "sub";
    case OP_MUL: return "mul";
    case OP_DIV: return "div";
    case OP_SQRT: return "sqrt";
    case OP_FMA: return "fma";
  }
  abort();
}

static uint32_t float32_to_bits(float value) {
  uint32_t bits;
  memcpy(&bits, &value, sizeof(bits));
  return bits;
}

static uint64_t float64_to_bits(double value) {
  uint64_t bits;
  memcpy(&bits, &value, sizeof(bits));
  return bits;
}

static void require_ieee_binary_host(void) {
  if (sizeof(float) != 4 || sizeof(double) != 8 ||
      FLT_RADIX != 2 || FLT_MANT_DIG != 24 || DBL_MANT_DIG != 53 ||
      FLT_MAX_EXP != 128 || DBL_MAX_EXP != 1024 ||
      float32_to_bits(1.0f) != UINT32_C(0x3f800000) ||
      float64_to_bits(1.0) != UINT64_C(0x3ff0000000000000)) {
    fprintf(
        stderr,
        "native C comparison requires IEEE binary32 and binary64 host types\n");
    exit(EXIT_FAILURE);
  }
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
  mpfr_set_q(result, exact, MPFR_RNDN);
  mpq_clear(exact);
}

static void init_float32_inputs(
    float xs[ARRAY_SIZE],
    float ys[ARRAY_SIZE],
    float zs[ARRAY_SIZE],
    float sqrt_xs[ARRAY_SIZE]) {
  mpfr_t exact;
  mpfr_init2(exact, 24);
  for (size_t index = 0; index < ARRAY_SIZE; ++index) {
    set_exact_input(exact, index, 37, index % 5 == 0);
    xs[index] = mpfr_get_flt(exact, MPFR_RNDN);
    set_exact_input(exact, index, 61, index % 3 == 0);
    ys[index] = mpfr_get_flt(exact, MPFR_RNDN);
    set_exact_input(exact, index, 43, 0);
    sqrt_xs[index] = mpfr_get_flt(exact, MPFR_RNDN);
  }
  for (size_t index = 0; index < ARRAY_SIZE; ++index) {
    zs[index] = xs[ARRAY_SIZE - 1 - index];
  }
  mpfr_clear(exact);
}

static void init_float64_inputs(
    double xs[ARRAY_SIZE],
    double ys[ARRAY_SIZE],
    double zs[ARRAY_SIZE],
    double sqrt_xs[ARRAY_SIZE]) {
  mpfr_t exact;
  mpfr_init2(exact, 53);
  for (size_t index = 0; index < ARRAY_SIZE; ++index) {
    set_exact_input(exact, index, 37, index % 5 == 0);
    xs[index] = mpfr_get_d(exact, MPFR_RNDN);
    set_exact_input(exact, index, 61, index % 3 == 0);
    ys[index] = mpfr_get_d(exact, MPFR_RNDN);
    set_exact_input(exact, index, 43, 0);
    sqrt_xs[index] = mpfr_get_d(exact, MPFR_RNDN);
  }
  for (size_t index = 0; index < ARRAY_SIZE; ++index) {
    zs[index] = xs[ARRAY_SIZE - 1 - index];
  }
  mpfr_clear(exact);
}

static float evaluate_float32(
    enum operation operation, float x, float y, float z, float sqrt_x) {
  switch (operation) {
    case OP_ADD: return x + y;
    case OP_SUB: return x - y;
    case OP_MUL: return x * y;
    case OP_DIV: return x / y;
    case OP_SQRT: return sqrtf(sqrt_x);
    case OP_FMA: return fmaf(x, y, z);
  }
  abort();
}

static double evaluate_float64(
    enum operation operation, double x, double y, double z, double sqrt_x) {
  switch (operation) {
    case OP_ADD: return x + y;
    case OP_SUB: return x - y;
    case OP_MUL: return x * y;
    case OP_DIV: return x / y;
    case OP_SQRT: return sqrt(sqrt_x);
    case OP_FMA: return fma(x, y, z);
  }
  abort();
}

static void evaluate_reference(
    mpfr_ptr result,
    enum operation operation,
    mpfr_srcptr x,
    mpfr_srcptr y,
    mpfr_srcptr z,
    mpfr_srcptr sqrt_x) {
  switch (operation) {
    case OP_ADD:
      mpfr_add(result, x, y, MPFR_RNDN);
      return;
    case OP_SUB:
      mpfr_sub(result, x, y, MPFR_RNDN);
      return;
    case OP_MUL:
      mpfr_mul(result, x, y, MPFR_RNDN);
      return;
    case OP_DIV:
      mpfr_div(result, x, y, MPFR_RNDN);
      return;
    case OP_SQRT:
      mpfr_sqrt(result, sqrt_x, MPFR_RNDN);
      return;
    case OP_FMA:
      mpfr_fma(result, x, y, z, MPFR_RNDN);
      return;
  }
  abort();
}

static void validate_float32(
    enum operation operation,
    const float xs[ARRAY_SIZE],
    const float ys[ARRAY_SIZE],
    const float zs[ARRAY_SIZE],
    const float sqrt_xs[ARRAY_SIZE]) {
  mpfr_t x;
  mpfr_t y;
  mpfr_t z;
  mpfr_t sqrt_x;
  mpfr_t result;
  mpfr_inits2(24, x, y, z, sqrt_x, result, (mpfr_ptr)0);
  for (size_t index = 0; index < ARRAY_SIZE; ++index) {
    mpfr_set_flt(x, xs[index], MPFR_RNDN);
    mpfr_set_flt(y, ys[index], MPFR_RNDN);
    mpfr_set_flt(z, zs[index], MPFR_RNDN);
    mpfr_set_flt(sqrt_x, sqrt_xs[index], MPFR_RNDN);
    evaluate_reference(result, operation, x, y, z, sqrt_x);
    uint32_t expected =
        float32_to_bits(mpfr_get_flt(result, MPFR_RNDN));
    uint32_t actual =
        float32_to_bits(evaluate_float32(
            operation, xs[index], ys[index], zs[index], sqrt_xs[index]));
    uint64_t expected_fingerprint =
        floatlib_benchmark_binary32_fingerprint(expected);
    uint64_t actual_fingerprint =
        floatlib_benchmark_binary32_fingerprint(actual);
    int both_nan =
        ((actual & UINT32_C(0x7fffffff)) > UINT32_C(0x7f800000)) &&
        ((expected & UINT32_C(0x7fffffff)) > UINT32_C(0x7f800000));
    if ((!both_nan && actual != expected) ||
        actual_fingerprint != expected_fingerprint) {
      fprintf(
          stderr,
          "native binary32 %s disagrees with MPFR at vector %zu: "
          "expected %08" PRIx32 " (fingerprint %" PRIu64
          "), received %08" PRIx32 " (fingerprint %" PRIu64 ")\n",
          operation_name(operation), index, expected, expected_fingerprint,
          actual, actual_fingerprint);
      exit(EXIT_FAILURE);
    }
  }
  mpfr_clears(x, y, z, sqrt_x, result, (mpfr_ptr)0);
}

static void validate_float64(
    enum operation operation,
    const double xs[ARRAY_SIZE],
    const double ys[ARRAY_SIZE],
    const double zs[ARRAY_SIZE],
    const double sqrt_xs[ARRAY_SIZE]) {
  mpfr_t x;
  mpfr_t y;
  mpfr_t z;
  mpfr_t sqrt_x;
  mpfr_t result;
  mpfr_inits2(53, x, y, z, sqrt_x, result, (mpfr_ptr)0);
  for (size_t index = 0; index < ARRAY_SIZE; ++index) {
    mpfr_set_d(x, xs[index], MPFR_RNDN);
    mpfr_set_d(y, ys[index], MPFR_RNDN);
    mpfr_set_d(z, zs[index], MPFR_RNDN);
    mpfr_set_d(sqrt_x, sqrt_xs[index], MPFR_RNDN);
    evaluate_reference(result, operation, x, y, z, sqrt_x);
    uint64_t expected =
        float64_to_bits(mpfr_get_d(result, MPFR_RNDN));
    uint64_t actual =
        float64_to_bits(evaluate_float64(
            operation, xs[index], ys[index], zs[index], sqrt_xs[index]));
    uint64_t expected_fingerprint =
        floatlib_benchmark_binary64_fingerprint(expected);
    uint64_t actual_fingerprint =
        floatlib_benchmark_binary64_fingerprint(actual);
    int both_nan =
        ((actual & UINT64_C(0x7fffffffffffffff)) >
         UINT64_C(0x7ff0000000000000)) &&
        ((expected & UINT64_C(0x7fffffffffffffff)) >
         UINT64_C(0x7ff0000000000000));
    if ((!both_nan && actual != expected) ||
        actual_fingerprint != expected_fingerprint) {
      fprintf(
          stderr,
          "native binary64 %s disagrees with MPFR at vector %zu: "
          "expected %016" PRIx64 " (fingerprint %" PRIu64
          "), received %016" PRIx64 " (fingerprint %" PRIu64 ")\n",
          operation_name(operation), index, expected, expected_fingerprint,
          actual, actual_fingerprint);
      exit(EXIT_FAILURE);
    }
  }
  mpfr_clears(x, y, z, sqrt_x, result, (mpfr_ptr)0);
}

#define DEFINE_FLOAT32_RUNNER(NAME, EXPRESSION)                            \
  static NOINLINE struct floatlib_benchmark_result NAME(                  \
      size_t iterations,                                                   \
      const float xs[ARRAY_SIZE],                                          \
      const float ys[ARRAY_SIZE],                                          \
      const float zs[ARRAY_SIZE],                                          \
      const float sqrt_xs[ARRAY_SIZE]) {                                   \
    (void)xs;                                                              \
    (void)ys;                                                              \
    (void)zs;                                                              \
    (void)sqrt_xs;                                                         \
    struct floatlib_benchmark_result result = {                           \
        FLOATLIB_BENCHMARK_DEPENDENCY_SEED,                               \
        FLOATLIB_BENCHMARK_FIXTURE_TRACE_SEED,                            \
    };                                                                     \
    while (iterations != 0) {                                              \
      --iterations;                                                        \
      size_t index = floatlib_benchmark_dependent_index(                  \
          result.sink, ARRAY_SIZE);                                        \
      result.fixture_trace = floatlib_benchmark_mix_fixture_trace(        \
          result.fixture_trace, index);                                    \
      float rounded = (EXPRESSION);                                        \
      result.sink = floatlib_benchmark_mix_sink(                          \
          result.sink,                                                     \
          floatlib_benchmark_binary32_fingerprint(                        \
              float32_to_bits(rounded)));                                  \
    }                                                                      \
    return result;                                                         \
  }

DEFINE_FLOAT32_RUNNER(run_float32_add, xs[index] + ys[index])
DEFINE_FLOAT32_RUNNER(run_float32_sub, xs[index] - ys[index])
DEFINE_FLOAT32_RUNNER(run_float32_mul, xs[index] * ys[index])
DEFINE_FLOAT32_RUNNER(run_float32_div, xs[index] / ys[index])
DEFINE_FLOAT32_RUNNER(run_float32_sqrt, sqrtf(sqrt_xs[index]))
DEFINE_FLOAT32_RUNNER(run_float32_fma, fmaf(xs[index], ys[index], zs[index]))

#undef DEFINE_FLOAT32_RUNNER

#define DEFINE_FLOAT64_RUNNER(NAME, EXPRESSION)                            \
  static NOINLINE struct floatlib_benchmark_result NAME(                  \
      size_t iterations,                                                   \
      const double xs[ARRAY_SIZE],                                         \
      const double ys[ARRAY_SIZE],                                         \
      const double zs[ARRAY_SIZE],                                         \
      const double sqrt_xs[ARRAY_SIZE]) {                                  \
    (void)xs;                                                              \
    (void)ys;                                                              \
    (void)zs;                                                              \
    (void)sqrt_xs;                                                         \
    struct floatlib_benchmark_result result = {                           \
        FLOATLIB_BENCHMARK_DEPENDENCY_SEED,                               \
        FLOATLIB_BENCHMARK_FIXTURE_TRACE_SEED,                            \
    };                                                                     \
    while (iterations != 0) {                                              \
      --iterations;                                                        \
      size_t index = floatlib_benchmark_dependent_index(                  \
          result.sink, ARRAY_SIZE);                                        \
      result.fixture_trace = floatlib_benchmark_mix_fixture_trace(        \
          result.fixture_trace, index);                                    \
      double rounded = (EXPRESSION);                                       \
      result.sink = floatlib_benchmark_mix_sink(                          \
          result.sink,                                                     \
          floatlib_benchmark_binary64_fingerprint(                        \
              float64_to_bits(rounded)));                                  \
    }                                                                      \
    return result;                                                         \
  }

DEFINE_FLOAT64_RUNNER(run_float64_add, xs[index] + ys[index])
DEFINE_FLOAT64_RUNNER(run_float64_sub, xs[index] - ys[index])
DEFINE_FLOAT64_RUNNER(run_float64_mul, xs[index] * ys[index])
DEFINE_FLOAT64_RUNNER(run_float64_div, xs[index] / ys[index])
DEFINE_FLOAT64_RUNNER(run_float64_sqrt, sqrt(sqrt_xs[index]))
DEFINE_FLOAT64_RUNNER(run_float64_fma, fma(xs[index], ys[index], zs[index]))

#undef DEFINE_FLOAT64_RUNNER

typedef struct floatlib_benchmark_result (*float32_runner)(
    size_t,
    const float[ARRAY_SIZE],
    const float[ARRAY_SIZE],
    const float[ARRAY_SIZE],
    const float[ARRAY_SIZE]);

typedef struct floatlib_benchmark_result (*float64_runner)(
    size_t,
    const double[ARRAY_SIZE],
    const double[ARRAY_SIZE],
    const double[ARRAY_SIZE],
    const double[ARRAY_SIZE]);

static float32_runner select_float32_runner(enum operation operation) {
  switch (operation) {
    case OP_ADD: return run_float32_add;
    case OP_SUB: return run_float32_sub;
    case OP_MUL: return run_float32_mul;
    case OP_DIV: return run_float32_div;
    case OP_SQRT: return run_float32_sqrt;
    case OP_FMA: return run_float32_fma;
  }
  abort();
}

static float64_runner select_float64_runner(enum operation operation) {
  switch (operation) {
    case OP_ADD: return run_float64_add;
    case OP_SUB: return run_float64_sub;
    case OP_MUL: return run_float64_mul;
    case OP_DIV: return run_float64_div;
    case OP_SQRT: return run_float64_sqrt;
    case OP_FMA: return run_float64_fma;
  }
  abort();
}

static void time_float32(
    enum operation operation,
    size_t iterations,
    size_t warmup_iterations,
    size_t agreement_iterations) {
  float xs[ARRAY_SIZE];
  float ys[ARRAY_SIZE];
  float zs[ARRAY_SIZE];
  float sqrt_xs[ARRAY_SIZE];
  init_float32_inputs(xs, ys, zs, sqrt_xs);
  validate_float32(operation, xs, ys, zs, sqrt_xs);
  float32_runner run = select_float32_runner(operation);
  benchmark_warmup_sink =
      run(warmup_iterations, xs, ys, zs, sqrt_xs).sink;
  struct floatlib_benchmark_result agreement =
      run(agreement_iterations, xs, ys, zs, sqrt_xs);
  uint64_t start = monotonic_nanos();
  struct floatlib_benchmark_result result =
      run(iterations, xs, ys, zs, sqrt_xs);
  uint64_t stop = monotonic_nanos();
  printf(
      "Native C,binary-interchange,binary32,32,%s,native-fpu,"
      "C float host FPU,result-dependent-fixture-chain,%zu,%" PRIu64
      ",%" PRIu64 ",%" PRIu64 ",%zu,%" PRIu64 ",%" PRIu64 "\n",
      operation_name(operation), iterations, stop - start, result.sink,
      result.fixture_trace, agreement_iterations, agreement.sink,
      agreement.fixture_trace);
}

static void time_float64(
    enum operation operation,
    size_t iterations,
    size_t warmup_iterations,
    size_t agreement_iterations) {
  double xs[ARRAY_SIZE];
  double ys[ARRAY_SIZE];
  double zs[ARRAY_SIZE];
  double sqrt_xs[ARRAY_SIZE];
  init_float64_inputs(xs, ys, zs, sqrt_xs);
  validate_float64(operation, xs, ys, zs, sqrt_xs);
  float64_runner run = select_float64_runner(operation);
  benchmark_warmup_sink =
      run(warmup_iterations, xs, ys, zs, sqrt_xs).sink;
  struct floatlib_benchmark_result agreement =
      run(agreement_iterations, xs, ys, zs, sqrt_xs);
  uint64_t start = monotonic_nanos();
  struct floatlib_benchmark_result result =
      run(iterations, xs, ys, zs, sqrt_xs);
  uint64_t stop = monotonic_nanos();
  printf(
      "Native C,binary-interchange,binary64,64,%s,native-fpu,"
      "C double host FPU,result-dependent-fixture-chain,%zu,%" PRIu64
      ",%" PRIu64 ",%" PRIu64 ",%zu,%" PRIu64 ",%" PRIu64 "\n",
      operation_name(operation), iterations, stop - start, result.sink,
      result.fixture_trace, agreement_iterations, agreement.sink,
      agreement.fixture_trace);
}

int main(void) {
  require_ieee_binary_host();
  if (fegetround() != FE_TONEAREST) {
    fprintf(stderr, "native C comparison requires round-to-nearest mode\n");
    return EXIT_FAILURE;
  }

  unsigned width = selected_width();
  enum operation operation = selected_operation();
  size_t iterations =
      positive_size_env("FORMAT_COMPARE_ITERATIONS", 1000000);
  size_t warmup_iterations =
      positive_size_env("FORMAT_COMPARE_WARMUP_ITERATIONS", 256);
  size_t agreement_iterations =
      positive_size_env("FORMAT_COMPARE_AGREEMENT_ITERATIONS", 256);

  puts(
      "implementation,family,format,totalBits,operation,executionClass,"
      "backend,measurementMethod,iterations,totalNanos,sink,fixtureTraceDigest,"
      "agreementIterations,agreementSink,agreementFixtureTraceDigest");
  if (width == 32) {
    time_float32(
        operation, iterations, warmup_iterations, agreement_iterations);
  } else {
    time_float64(
        operation, iterations, warmup_iterations, agreement_iterations);
  }

  mpfr_free_cache();
  return EXIT_SUCCESS;
}
