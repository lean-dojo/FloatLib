#define _POSIX_C_SOURCE 200809L

/*
 * Berkeley SoftFloat is the executable reference paired with TestFloat:
 * https://www.jhauser.us/arithmetic/SoftFloat-3/doc/SoftFloat.html
 * https://github.com/ucb-bar/berkeley-testfloat-3
 *
 * We use the same exact-rational fixtures, result fingerprint, and dependent
 * fixture chain as the native C and MPFR adapters. Equal arithmetic must
 * therefore produce the same final sink and the same fixture trace.
 */

#include <errno.h>
#include <inttypes.h>
#include <mpfr.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "softfloat.h"

#include "benchmark_protocol.h"

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
    fprintf(stderr, "SoftFloat comparison supports only width 32 or 64\n");
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

static float bits_to_float32(uint32_t bits) {
  float value;
  memcpy(&value, &bits, sizeof(value));
  return value;
}

static double bits_to_float64(uint64_t bits) {
  double value;
  memcpy(&value, &bits, sizeof(value));
  return value;
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
    float32_t xs[ARRAY_SIZE],
    float32_t ys[ARRAY_SIZE],
    float32_t zs[ARRAY_SIZE],
    float32_t sqrt_xs[ARRAY_SIZE]) {
  mpfr_t exact;
  mpfr_init2(exact, 24);
  for (size_t index = 0; index < ARRAY_SIZE; ++index) {
    set_exact_input(exact, index, 37, index % 5 == 0);
    xs[index].v = float32_to_bits(mpfr_get_flt(exact, MPFR_RNDN));
    set_exact_input(exact, index, 61, index % 3 == 0);
    ys[index].v = float32_to_bits(mpfr_get_flt(exact, MPFR_RNDN));
    set_exact_input(exact, index, 43, 0);
    sqrt_xs[index].v = float32_to_bits(mpfr_get_flt(exact, MPFR_RNDN));
  }
  for (size_t index = 0; index < ARRAY_SIZE; ++index) {
    zs[index] = xs[ARRAY_SIZE - 1 - index];
  }
  mpfr_clear(exact);
}

static void init_float64_inputs(
    float64_t xs[ARRAY_SIZE],
    float64_t ys[ARRAY_SIZE],
    float64_t zs[ARRAY_SIZE],
    float64_t sqrt_xs[ARRAY_SIZE]) {
  mpfr_t exact;
  mpfr_init2(exact, 53);
  for (size_t index = 0; index < ARRAY_SIZE; ++index) {
    set_exact_input(exact, index, 37, index % 5 == 0);
    xs[index].v = float64_to_bits(mpfr_get_d(exact, MPFR_RNDN));
    set_exact_input(exact, index, 61, index % 3 == 0);
    ys[index].v = float64_to_bits(mpfr_get_d(exact, MPFR_RNDN));
    set_exact_input(exact, index, 43, 0);
    sqrt_xs[index].v = float64_to_bits(mpfr_get_d(exact, MPFR_RNDN));
  }
  for (size_t index = 0; index < ARRAY_SIZE; ++index) {
    zs[index] = xs[ARRAY_SIZE - 1 - index];
  }
  mpfr_clear(exact);
}

static float32_t evaluate_float32(
    enum operation operation,
    float32_t x,
    float32_t y,
    float32_t z,
    float32_t sqrt_x) {
  switch (operation) {
    case OP_ADD: return f32_add(x, y);
    case OP_SUB: return f32_sub(x, y);
    case OP_MUL: return f32_mul(x, y);
    case OP_DIV: return f32_div(x, y);
    case OP_SQRT: return f32_sqrt(sqrt_x);
    case OP_FMA: return f32_mulAdd(x, y, z);
  }
  abort();
}

static float64_t evaluate_float64(
    enum operation operation,
    float64_t x,
    float64_t y,
    float64_t z,
    float64_t sqrt_x) {
  switch (operation) {
    case OP_ADD: return f64_add(x, y);
    case OP_SUB: return f64_sub(x, y);
    case OP_MUL: return f64_mul(x, y);
    case OP_DIV: return f64_div(x, y);
    case OP_SQRT: return f64_sqrt(sqrt_x);
    case OP_FMA: return f64_mulAdd(x, y, z);
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
    const float32_t xs[ARRAY_SIZE],
    const float32_t ys[ARRAY_SIZE],
    const float32_t zs[ARRAY_SIZE],
    const float32_t sqrt_xs[ARRAY_SIZE]) {
  mpfr_t x;
  mpfr_t y;
  mpfr_t z;
  mpfr_t sqrt_x;
  mpfr_t result;
  mpfr_inits2(24, x, y, z, sqrt_x, result, (mpfr_ptr)0);
  for (size_t index = 0; index < ARRAY_SIZE; ++index) {
    mpfr_set_flt(x, bits_to_float32(xs[index].v), MPFR_RNDN);
    mpfr_set_flt(y, bits_to_float32(ys[index].v), MPFR_RNDN);
    mpfr_set_flt(z, bits_to_float32(zs[index].v), MPFR_RNDN);
    mpfr_set_flt(sqrt_x, bits_to_float32(sqrt_xs[index].v), MPFR_RNDN);
    evaluate_reference(result, operation, x, y, z, sqrt_x);
    uint32_t expected = float32_to_bits(mpfr_get_flt(result, MPFR_RNDN));
    softfloat_exceptionFlags = 0;
    uint32_t actual =
        evaluate_float32(
            operation, xs[index], ys[index], zs[index], sqrt_xs[index]).v;
    int both_nan =
        ((actual & UINT32_C(0x7fffffff)) > UINT32_C(0x7f800000)) &&
        ((expected & UINT32_C(0x7fffffff)) > UINT32_C(0x7f800000));
    if (!both_nan && actual != expected) {
      fprintf(
          stderr,
          "SoftFloat binary32 %s disagrees with MPFR at vector %zu: "
          "expected %08" PRIx32 ", received %08" PRIx32 "\n",
          operation_name(operation), index, expected, actual);
      exit(EXIT_FAILURE);
    }
  }
  mpfr_clears(x, y, z, sqrt_x, result, (mpfr_ptr)0);
}

static void validate_float64(
    enum operation operation,
    const float64_t xs[ARRAY_SIZE],
    const float64_t ys[ARRAY_SIZE],
    const float64_t zs[ARRAY_SIZE],
    const float64_t sqrt_xs[ARRAY_SIZE]) {
  mpfr_t x;
  mpfr_t y;
  mpfr_t z;
  mpfr_t sqrt_x;
  mpfr_t result;
  mpfr_inits2(53, x, y, z, sqrt_x, result, (mpfr_ptr)0);
  for (size_t index = 0; index < ARRAY_SIZE; ++index) {
    mpfr_set_d(x, bits_to_float64(xs[index].v), MPFR_RNDN);
    mpfr_set_d(y, bits_to_float64(ys[index].v), MPFR_RNDN);
    mpfr_set_d(z, bits_to_float64(zs[index].v), MPFR_RNDN);
    mpfr_set_d(sqrt_x, bits_to_float64(sqrt_xs[index].v), MPFR_RNDN);
    evaluate_reference(result, operation, x, y, z, sqrt_x);
    uint64_t expected = float64_to_bits(mpfr_get_d(result, MPFR_RNDN));
    softfloat_exceptionFlags = 0;
    uint64_t actual =
        evaluate_float64(
            operation, xs[index], ys[index], zs[index], sqrt_xs[index]).v;
    int both_nan =
        ((actual & UINT64_C(0x7fffffffffffffff)) >
         UINT64_C(0x7ff0000000000000)) &&
        ((expected & UINT64_C(0x7fffffffffffffff)) >
         UINT64_C(0x7ff0000000000000));
    if (!both_nan && actual != expected) {
      fprintf(
          stderr,
          "SoftFloat binary64 %s disagrees with MPFR at vector %zu: "
          "expected %016" PRIx64 ", received %016" PRIx64 "\n",
          operation_name(operation), index, expected, actual);
      exit(EXIT_FAILURE);
    }
  }
  mpfr_clears(x, y, z, sqrt_x, result, (mpfr_ptr)0);
}

#define DEFINE_FLOAT32_RUNNER(NAME, EXPRESSION)                            \
  static NOINLINE struct floatlib_benchmark_result NAME(                  \
      size_t iterations,                                                   \
      const float32_t xs[ARRAY_SIZE],                                      \
      const float32_t ys[ARRAY_SIZE],                                      \
      const float32_t zs[ARRAY_SIZE],                                      \
      const float32_t sqrt_xs[ARRAY_SIZE]) {                               \
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
      float32_t rounded = (EXPRESSION);                                    \
      result.sink = floatlib_benchmark_mix_sink(                          \
          result.sink, floatlib_benchmark_binary32_fingerprint(rounded.v)); \
    }                                                                      \
    return result;                                                         \
  }

DEFINE_FLOAT32_RUNNER(run_float32_add, f32_add(xs[index], ys[index]))
DEFINE_FLOAT32_RUNNER(run_float32_sub, f32_sub(xs[index], ys[index]))
DEFINE_FLOAT32_RUNNER(run_float32_mul, f32_mul(xs[index], ys[index]))
DEFINE_FLOAT32_RUNNER(run_float32_div, f32_div(xs[index], ys[index]))
DEFINE_FLOAT32_RUNNER(run_float32_sqrt, f32_sqrt(sqrt_xs[index]))
DEFINE_FLOAT32_RUNNER(
    run_float32_fma, f32_mulAdd(xs[index], ys[index], zs[index]))

#undef DEFINE_FLOAT32_RUNNER

#define DEFINE_FLOAT64_RUNNER(NAME, EXPRESSION)                            \
  static NOINLINE struct floatlib_benchmark_result NAME(                  \
      size_t iterations,                                                   \
      const float64_t xs[ARRAY_SIZE],                                      \
      const float64_t ys[ARRAY_SIZE],                                      \
      const float64_t zs[ARRAY_SIZE],                                      \
      const float64_t sqrt_xs[ARRAY_SIZE]) {                               \
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
      float64_t rounded = (EXPRESSION);                                    \
      result.sink = floatlib_benchmark_mix_sink(                          \
          result.sink, floatlib_benchmark_binary64_fingerprint(rounded.v)); \
    }                                                                      \
    return result;                                                         \
  }

DEFINE_FLOAT64_RUNNER(run_float64_add, f64_add(xs[index], ys[index]))
DEFINE_FLOAT64_RUNNER(run_float64_sub, f64_sub(xs[index], ys[index]))
DEFINE_FLOAT64_RUNNER(run_float64_mul, f64_mul(xs[index], ys[index]))
DEFINE_FLOAT64_RUNNER(run_float64_div, f64_div(xs[index], ys[index]))
DEFINE_FLOAT64_RUNNER(run_float64_sqrt, f64_sqrt(sqrt_xs[index]))
DEFINE_FLOAT64_RUNNER(
    run_float64_fma, f64_mulAdd(xs[index], ys[index], zs[index]))

#undef DEFINE_FLOAT64_RUNNER

typedef struct floatlib_benchmark_result (*float32_runner)(
    size_t,
    const float32_t[ARRAY_SIZE],
    const float32_t[ARRAY_SIZE],
    const float32_t[ARRAY_SIZE],
    const float32_t[ARRAY_SIZE]);

typedef struct floatlib_benchmark_result (*float64_runner)(
    size_t,
    const float64_t[ARRAY_SIZE],
    const float64_t[ARRAY_SIZE],
    const float64_t[ARRAY_SIZE],
    const float64_t[ARRAY_SIZE]);

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
  float32_t xs[ARRAY_SIZE];
  float32_t ys[ARRAY_SIZE];
  float32_t zs[ARRAY_SIZE];
  float32_t sqrt_xs[ARRAY_SIZE];
  init_float32_inputs(xs, ys, zs, sqrt_xs);
  validate_float32(operation, xs, ys, zs, sqrt_xs);
  float32_runner run = select_float32_runner(operation);
  softfloat_exceptionFlags = 0;
  benchmark_warmup_sink =
      run(warmup_iterations, xs, ys, zs, sqrt_xs).sink;
  softfloat_exceptionFlags = 0;
  struct floatlib_benchmark_result agreement =
      run(agreement_iterations, xs, ys, zs, sqrt_xs);
  softfloat_exceptionFlags = 0;
  uint64_t start = monotonic_nanos();
  struct floatlib_benchmark_result result =
      run(iterations, xs, ys, zs, sqrt_xs);
  uint64_t stop = monotonic_nanos();
  printf(
      "Berkeley SoftFloat,binary-interchange,binary32,32,%s,"
      "external-software,SoftFloat 3e,result-dependent-fixture-chain,"
      "%zu,%" PRIu64 ",%" PRIu64 ",%" PRIu64
      ",%zu,%" PRIu64 ",%" PRIu64 "\n",
      operation_name(operation), iterations, stop - start, result.sink,
      result.fixture_trace, agreement_iterations, agreement.sink,
      agreement.fixture_trace);
}

static void time_float64(
    enum operation operation,
    size_t iterations,
    size_t warmup_iterations,
    size_t agreement_iterations) {
  float64_t xs[ARRAY_SIZE];
  float64_t ys[ARRAY_SIZE];
  float64_t zs[ARRAY_SIZE];
  float64_t sqrt_xs[ARRAY_SIZE];
  init_float64_inputs(xs, ys, zs, sqrt_xs);
  validate_float64(operation, xs, ys, zs, sqrt_xs);
  float64_runner run = select_float64_runner(operation);
  softfloat_exceptionFlags = 0;
  benchmark_warmup_sink =
      run(warmup_iterations, xs, ys, zs, sqrt_xs).sink;
  softfloat_exceptionFlags = 0;
  struct floatlib_benchmark_result agreement =
      run(agreement_iterations, xs, ys, zs, sqrt_xs);
  softfloat_exceptionFlags = 0;
  uint64_t start = monotonic_nanos();
  struct floatlib_benchmark_result result =
      run(iterations, xs, ys, zs, sqrt_xs);
  uint64_t stop = monotonic_nanos();
  printf(
      "Berkeley SoftFloat,binary-interchange,binary64,64,%s,"
      "external-software,SoftFloat 3e,result-dependent-fixture-chain,"
      "%zu,%" PRIu64 ",%" PRIu64 ",%" PRIu64
      ",%zu,%" PRIu64 ",%" PRIu64 "\n",
      operation_name(operation), iterations, stop - start, result.sink,
      result.fixture_trace, agreement_iterations, agreement.sink,
      agreement.fixture_trace);
}

int main(void) {
  softfloat_roundingMode = softfloat_round_near_even;
  softfloat_detectTininess = softfloat_tininess_afterRounding;
  softfloat_exceptionFlags = 0;

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
