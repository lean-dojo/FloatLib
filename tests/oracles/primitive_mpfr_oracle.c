/*
 * Copyright (c) 2026 FloatLib
 * Released under MIT license as described in the file LICENSE.
 * Independent MPFR oracle for primitive IEEE arithmetic and exception status.
 */

#define _POSIX_C_SOURCE 200809L

#include <errno.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <mpfr.h>

#include "ieee_flags.h"

enum operation {
  OP_ADD,
  OP_SUB,
  OP_MUL,
  OP_DIV,
  OP_SQRT,
  OP_FMA,
};

struct format {
  unsigned exponent_bits;
  unsigned fraction_bits;
  unsigned bias;
};

static void fail_line(size_t line_number, const char *message) {
  fprintf(stderr, "primitive MPFR vector line %zu: %s\n", line_number,
          message);
  exit(EXIT_FAILURE);
}

static char *next_token(size_t line_number, char **cursor,
                        const char *name) {
  if (*cursor == NULL) {
    fprintf(stderr, "primitive MPFR vector line %zu: missing %s\n",
            line_number, name);
    exit(EXIT_FAILURE);
  }
  char *token = *cursor;
  char *tab = strchr(token, '\t');
  char *line_end = strpbrk(token, "\r\n");
  if (tab != NULL && (line_end == NULL || tab < line_end)) {
    *tab = '\0';
    *cursor = tab + 1;
  } else {
    if (line_end != NULL) {
      *line_end = '\0';
    }
    *cursor = NULL;
  }
  if (*token == '\0') {
    fprintf(stderr, "primitive MPFR vector line %zu: empty %s\n",
            line_number, name);
    exit(EXIT_FAILURE);
  }
  return token;
}

static uint64_t parse_u64(size_t line_number, const char *name,
                          const char *text) {
  char *end = NULL;
  errno = 0;
  unsigned long long value = strtoull(text, &end, 10);
  if (errno != 0 || end == text || *end != '\0') {
    fprintf(stderr, "primitive MPFR vector line %zu: invalid %s: %s\n",
            line_number, name, text);
    exit(EXIT_FAILURE);
  }
  return (uint64_t)value;
}

static int parse_flag(size_t line_number, const char *name,
                      const char *text) {
  uint64_t value = parse_u64(line_number, name, text);
  if (value > 1) {
    fprintf(stderr,
            "primitive MPFR vector line %zu: %s must be zero or one\n",
            line_number, name);
    exit(EXIT_FAILURE);
  }
  return (int)value;
}

static enum operation parse_operation(size_t line_number,
                                      const char *text) {
  if (strcmp(text, "add") == 0) return OP_ADD;
  if (strcmp(text, "sub") == 0) return OP_SUB;
  if (strcmp(text, "mul") == 0) return OP_MUL;
  if (strcmp(text, "div") == 0) return OP_DIV;
  if (strcmp(text, "sqrt") == 0) return OP_SQRT;
  if (strcmp(text, "fma") == 0) return OP_FMA;
  fail_line(line_number, "unknown operation");
  return OP_ADD;
}

static size_t operation_arity(enum operation operation) {
  if (operation == OP_SQRT) return 1;
  if (operation == OP_FMA) return 3;
  return 2;
}

/*
 * A FloatLib rounding direction. MPFR has no rounding to nearest with ties away
 * from zero that supports subnormalization, so `nearestAway` runs MPFR_RNDN and
 * corrects the value at an exact tie (see nearest_away_tie).
 */
struct rounding {
  mpfr_rnd_t mpfr;
  int nearest_away;
};

static struct rounding parse_rounding(size_t line_number, const char *text) {
  struct rounding rounding = {MPFR_RNDN, 0};
  if (strcmp(text, "nearestEven") == 0) return rounding;
  if (strcmp(text, "nearestAway") == 0) {
    rounding.nearest_away = 1;
    return rounding;
  }
  if (strcmp(text, "awayFromZero") == 0) {
    rounding.mpfr = MPFR_RNDA;
    return rounding;
  }
  if (strcmp(text, "towardZero") == 0) {
    rounding.mpfr = MPFR_RNDZ;
    return rounding;
  }
  if (strcmp(text, "towardPositive") == 0) {
    rounding.mpfr = MPFR_RNDU;
    return rounding;
  }
  if (strcmp(text, "towardNegative") == 0) {
    rounding.mpfr = MPFR_RNDD;
    return rounding;
  }
  fail_line(line_number, "unknown rounding mode");
  return rounding;
}

static uint64_t fraction_mask(const struct format *format) {
  return (UINT64_C(1) << format->fraction_bits) - UINT64_C(1);
}

static uint64_t exponent_field(uint64_t bits, const struct format *format) {
  const uint64_t mask =
      (UINT64_C(1) << format->exponent_bits) - UINT64_C(1);
  return (bits >> format->fraction_bits) & mask;
}

static int sign_bit(uint64_t bits, const struct format *format) {
  return (int)((bits >> (format->exponent_bits + format->fraction_bits)) & 1);
}

static int is_nan(uint64_t bits, const struct format *format) {
  const uint64_t exponent_all_ones =
      (UINT64_C(1) << format->exponent_bits) - UINT64_C(1);
  return exponent_field(bits, format) == exponent_all_ones &&
         (bits & fraction_mask(format)) != 0;
}

static int is_signaling_nan(uint64_t bits, const struct format *format) {
  const uint64_t quiet_bit =
      UINT64_C(1) << (format->fraction_bits - 1);
  return is_nan(bits, format) && (bits & quiet_bit) == 0;
}

static int is_infinity(uint64_t bits, const struct format *format) {
  const uint64_t exponent_all_ones =
      (UINT64_C(1) << format->exponent_bits) - UINT64_C(1);
  return exponent_field(bits, format) == exponent_all_ones &&
         (bits & fraction_mask(format)) == 0;
}

static int is_zero(uint64_t bits, const struct format *format) {
  const unsigned magnitude_bits =
      format->exponent_bits + format->fraction_bits;
  const uint64_t magnitude_mask =
      (UINT64_C(1) << magnitude_bits) - UINT64_C(1);
  return (bits & magnitude_mask) == 0;
}

/*
 * MPFR has one NaN class, so its NaN flag cannot separate an invalid arithmetic
 * combination from propagation of a quiet NaN operand. Decode the IEEE causes
 * directly. MPFR's flag remains a consistency check only when no NaN operand
 * changes MPFR's exception precedence.
 */
static int generated_invalid(enum operation operation,
                             const uint64_t operands[3],
                             const struct format *format) {
  switch (operation) {
    case OP_ADD:
      return is_infinity(operands[0], format) &&
             is_infinity(operands[1], format) &&
             sign_bit(operands[0], format) != sign_bit(operands[1], format);
    case OP_SUB:
      return is_infinity(operands[0], format) &&
             is_infinity(operands[1], format) &&
             sign_bit(operands[0], format) == sign_bit(operands[1], format);
    case OP_MUL:
      return (is_infinity(operands[0], format) &&
              is_zero(operands[1], format)) ||
             (is_infinity(operands[1], format) &&
              is_zero(operands[0], format));
    case OP_DIV:
      return (is_zero(operands[0], format) &&
              is_zero(operands[1], format)) ||
             (is_infinity(operands[0], format) &&
              is_infinity(operands[1], format));
    case OP_SQRT:
      return sign_bit(operands[0], format) &&
             !is_zero(operands[0], format) &&
             !is_nan(operands[0], format);
    case OP_FMA: {
      const int invalid_product =
          (is_infinity(operands[0], format) ||
           is_infinity(operands[1], format)) &&
          (is_zero(operands[0], format) ||
           is_zero(operands[1], format));
      const int product_is_infinite =
          (is_infinity(operands[0], format) ||
           is_infinity(operands[1], format)) &&
          !(is_zero(operands[0], format) ||
            is_zero(operands[1], format));
      const int product_sign =
          sign_bit(operands[0], format) ^ sign_bit(operands[1], format);
      const int opposite_infinite_addend =
          product_is_infinite && is_infinity(operands[2], format) &&
          sign_bit(operands[2], format) != product_sign;
      /*
       * FloatLib raises invalid for the product 0 x infinity even beside a
       * quiet NaN addend (Model.fma with status := true), but a NaN operand
       * propagates instead of an opposite infinite addend.
       */
      const int any_nan = is_nan(operands[0], format) ||
                          is_nan(operands[1], format) ||
                          is_nan(operands[2], format);
      return invalid_product || (!any_nan && opposite_infinite_addend);
    }
  }
  return 0;
}

static void decode(mpfr_t value, uint64_t bits,
                   const struct format *format) {
  const int negative = sign_bit(bits, format);
  const uint64_t exponent = exponent_field(bits, format);
  const uint64_t fraction = bits & fraction_mask(format);
  const uint64_t exponent_all_ones =
      (UINT64_C(1) << format->exponent_bits) - UINT64_C(1);
  if (exponent == exponent_all_ones) {
    if (fraction == 0) {
      mpfr_set_inf(value, negative ? -1 : 1);
    } else {
      mpfr_set_nan(value);
    }
    return;
  }
  if (exponent == 0 && fraction == 0) {
    mpfr_set_zero(value, negative ? -1 : 1);
    return;
  }

  uint64_t significand = fraction;
  intmax_t power = 1 - (intmax_t)format->bias -
                   (intmax_t)format->fraction_bits;
  if (exponent != 0) {
    significand += UINT64_C(1) << format->fraction_bits;
    power = (intmax_t)exponent - (intmax_t)format->bias -
            (intmax_t)format->fraction_bits;
  }
  mpfr_set_uj_2exp(value, (uintmax_t)significand, (mpfr_exp_t)power,
                   MPFR_RNDN);
  if (negative) {
    mpfr_neg(value, value, MPFR_RNDN);
  }
}

/* MPFR's exponent range when the program starts, used for exact reference arithmetic. */
static mpfr_exp_t wide_emin;
static mpfr_exp_t wide_emax;

/* Apply one primitive operation with MPFR's own rounding and return its ternary value. */
static int run_operation(mpfr_ptr result, enum operation operation,
                         mpfr_t operands[3], mpfr_rnd_t rounding) {
  switch (operation) {
    case OP_ADD:
      return mpfr_add(result, operands[0], operands[1], rounding);
    case OP_SUB:
      return mpfr_sub(result, operands[0], operands[1], rounding);
    case OP_MUL:
      return mpfr_mul(result, operands[0], operands[1], rounding);
    case OP_DIV:
      return mpfr_div(result, operands[0], operands[1], rounding);
    case OP_SQRT:
      return mpfr_sqrt(result, operands[0], rounding);
    case OP_FMA:
      return mpfr_fma(result, operands[0], operands[1], operands[2], rounding);
  }
  return 0;
}

/*
 * Round in the destination: one MPFR rounding in the destination exponent range, then IEEE
 * subnormal rounding. Zero, infinity, and NaN results are already final, so only regular values
 * are subnormalized.
 */
static int round_in_destination(mpfr_ptr result, enum operation operation,
                                mpfr_t operands[3], mpfr_rnd_t rounding) {
  int ternary = run_operation(result, operation, operands, rounding);
  if (mpfr_regular_p(result)) {
    ternary = mpfr_subnormalize(result, ternary, rounding);
  }
  return ternary;
}

/* Lowest and highest bit positions of a nonzero finite value: |x| < 2^high, x in 2^low Z. */
static void bit_span(mpfr_srcptr x, mpfr_exp_t *low, mpfr_exp_t *high) {
  *high = mpfr_get_exp(x);
  *low = *high - (mpfr_exp_t)mpfr_min_prec(x);
}

/*
 * A precision at which addition, subtraction, multiplication, or fused multiply-add of these
 * finite operands is exact: the span from the lowest bit of the terms to the highest, plus one
 * bit for a carry. Binary64 fused multiply-add needs up to about 3,200 bits.
 */
static mpfr_prec_t exact_precision(enum operation operation, mpfr_t operands[3]) {
  int have_term = 0;
  mpfr_exp_t low = 0;
  mpfr_exp_t high = 0;
  mpfr_exp_t term_low = 0;
  mpfr_exp_t term_high = 0;
  mpfr_exp_t other_low = 0;
  mpfr_exp_t other_high = 0;
#define FLOATLIB_ADD_TERM(term_low_value, term_high_value)          \
  do {                                                              \
    if (!have_term || (term_low_value) < low) low = (term_low_value); \
    if (!have_term || (term_high_value) > high) high = (term_high_value); \
    have_term = 1;                                                  \
  } while (0)
  switch (operation) {
    case OP_ADD:
    case OP_SUB:
      for (size_t index = 0; index < 2; ++index) {
        if (mpfr_regular_p(operands[index])) {
          bit_span(operands[index], &term_low, &term_high);
          FLOATLIB_ADD_TERM(term_low, term_high);
        }
      }
      break;
    case OP_MUL:
    case OP_FMA:
      if (mpfr_regular_p(operands[0]) && mpfr_regular_p(operands[1])) {
        bit_span(operands[0], &term_low, &term_high);
        bit_span(operands[1], &other_low, &other_high);
        FLOATLIB_ADD_TERM(term_low + other_low, term_high + other_high);
      }
      if (operation == OP_FMA && mpfr_regular_p(operands[2])) {
        bit_span(operands[2], &term_low, &term_high);
        FLOATLIB_ADD_TERM(term_low, term_high);
      }
      break;
    case OP_DIV:
    case OP_SQRT:
      break;
  }
#undef FLOATLIB_ADD_TERM
  if (!have_term) {
    return MPFR_PREC_MIN;
  }
  mpfr_exp_t required = high - low + 1;
  if (required < MPFR_PREC_MIN) {
    return MPFR_PREC_MIN;
  }
  return (mpfr_prec_t)required;
}

/*
 * Whether the exact result of an inexact finite operation lies exactly halfway between its two
 * destination neighbours, `toward_zero` from MPFR_RNDZ and `away` from MPFR_RNDA, both rounded
 * in the destination range. An infinite `away` stands for the first grid value above the largest
 * finite one, 2^maximum_exponent in MPFR's exponent convention, as in FloatLib's overflowLimit.
 *
 * Every comparison is exact in MPFR's wide exponent range. Addition, subtraction, multiplication,
 * and fused multiply-add compute the exact result at exact_precision. Division compares the
 * dividend with the midpoint times the divisor, and square root compares the radicand with the
 * squared midpoint, which is nonnegative. The caller restores the destination range.
 */
static int nearest_away_tie(size_t line_number, enum operation operation,
                            mpfr_t operands[3], mpfr_srcptr toward_zero,
                            mpfr_srcptr away, mpfr_exp_t maximum_exponent,
                            mpfr_prec_t precision) {
  if (mpfr_set_emin(wide_emin) != 0 || mpfr_set_emax(wide_emax) != 0) {
    fail_line(line_number, "could not restore MPFR's wide exponent range");
  }
  mpfr_t upper;
  mpfr_t midpoint;
  mpfr_init2(upper, precision);
  mpfr_init2(midpoint, precision + 2);
  if (mpfr_inf_p(away)) {
    mpfr_set_ui_2exp(upper, 1, maximum_exponent, MPFR_RNDN);
    if (mpfr_signbit(away)) {
      mpfr_neg(upper, upper, MPFR_RNDN);
    }
  } else {
    mpfr_set(upper, away, MPFR_RNDN);
  }
  if (mpfr_add(midpoint, toward_zero, upper, MPFR_RNDN) != 0) {
    fail_line(line_number, "inexact nearest-away midpoint");
  }
  mpfr_div_2ui(midpoint, midpoint, 1, MPFR_RNDN);
  int tie = 0;
  switch (operation) {
    case OP_ADD:
    case OP_SUB:
    case OP_MUL:
    case OP_FMA: {
      mpfr_t exact;
      mpfr_init2(exact, exact_precision(operation, operands));
      if (run_operation(exact, operation, operands, MPFR_RNDN) != 0) {
        fail_line(line_number, "exact reference precision was too small");
      }
      tie = mpfr_equal_p(exact, midpoint);
      mpfr_clear(exact);
      break;
    }
    case OP_DIV: {
      mpfr_t product;
      mpfr_init2(product, mpfr_get_prec(midpoint) + mpfr_get_prec(operands[1]));
      if (mpfr_mul(product, midpoint, operands[1], MPFR_RNDN) != 0) {
        fail_line(line_number, "inexact midpoint times divisor");
      }
      tie = mpfr_equal_p(product, operands[0]);
      mpfr_clear(product);
      break;
    }
    case OP_SQRT: {
      mpfr_t square;
      mpfr_init2(square, 2 * mpfr_get_prec(midpoint));
      if (mpfr_sqr(square, midpoint, MPFR_RNDN) != 0) {
        fail_line(line_number, "inexact squared midpoint");
      }
      tie = mpfr_equal_p(square, operands[0]);
      mpfr_clear(square);
      break;
    }
  }
  mpfr_clear(upper);
  mpfr_clear(midpoint);
  return tie;
}

static void check_flag(size_t line_number, const char *case_name,
                       const char *operation, const char *rounding,
                       const char *flag_name, int expected, int actual) {
  if ((expected != 0) != (actual != 0)) {
    fprintf(stderr,
            "primitive MPFR flag mismatch at line %zu (%s, %s, %s): "
            "%s Lean=%d MPFR=%d\n",
            line_number, case_name, operation, rounding, flag_name,
            expected != 0, actual != 0);
    exit(EXIT_FAILURE);
  }
}

static void check_result(size_t line_number, const char *case_name,
                         const char *operation, const char *rounding,
                         uint64_t lean_bits, const struct format *format,
                         mpfr_srcptr result, mpfr_srcptr lean_result) {
  int matches = 0;
  if (mpfr_nan_p(result)) {
    const uint64_t quiet_bit =
        UINT64_C(1) << (format->fraction_bits - 1);
    matches = is_nan(lean_bits, format) && (lean_bits & quiet_bit) != 0;
  } else if (mpfr_inf_p(result)) {
    matches = is_infinity(lean_bits, format) &&
              sign_bit(lean_bits, format) == mpfr_signbit(result);
  } else if (mpfr_zero_p(result)) {
    matches = is_zero(lean_bits, format) &&
              sign_bit(lean_bits, format) == mpfr_signbit(result);
  } else {
    matches = !is_nan(lean_bits, format) &&
              !is_infinity(lean_bits, format) &&
              mpfr_equal_p(result, lean_result);
  }
  if (!matches) {
    fprintf(stderr,
            "primitive MPFR value mismatch at line %zu (%s, %s, %s): "
            "Lean bits=0x%016" PRIx64 " MPFR=",
            line_number, case_name, operation, rounding, lean_bits);
    mpfr_out_str(stderr, 16, 0, result, MPFR_RNDN);
    fputc('\n', stderr);
    exit(EXIT_FAILURE);
  }
}

static void check_line(size_t line_number, char *line) {
  char *cursor = line;
  const char *case_name = next_token(line_number, &cursor, "case name");
  const char *operation_text = next_token(line_number, &cursor, "operation");
  const enum operation operation =
      parse_operation(line_number, operation_text);
  const char *rounding_text =
      next_token(line_number, &cursor, "rounding mode");
  const struct rounding rounding = parse_rounding(line_number, rounding_text);
  struct format format;
  format.exponent_bits = (unsigned)parse_u64(
      line_number, "exponent width",
      next_token(line_number, &cursor, "exponent width"));
  format.fraction_bits = (unsigned)parse_u64(
      line_number, "fraction width",
      next_token(line_number, &cursor, "fraction width"));
  format.bias = (unsigned)parse_u64(
      line_number, "exponent bias",
      next_token(line_number, &cursor, "exponent bias"));
  if (!((format.exponent_bits == 8 && format.fraction_bits == 23 &&
         format.bias == 127) ||
        (format.exponent_bits == 11 && format.fraction_bits == 52 &&
         format.bias == 1023))) {
    fail_line(line_number, "oracle accepts only IEEE binary32 or binary64");
  }

  const uint64_t lean_bits = parse_u64(
      line_number, "Lean result bits",
      next_token(line_number, &cursor, "Lean result bits"));
  const int lean_invalid = parse_flag(
      line_number, "invalid",
      next_token(line_number, &cursor, "invalid"));
  const int lean_divide_by_zero = parse_flag(
      line_number, "divideByZero",
      next_token(line_number, &cursor, "divideByZero"));
  const int lean_overflow = parse_flag(
      line_number, "overflow",
      next_token(line_number, &cursor, "overflow"));
  const int lean_underflow = parse_flag(
      line_number, "underflow",
      next_token(line_number, &cursor, "underflow"));
  const int lean_inexact = parse_flag(
      line_number, "inexact",
      next_token(line_number, &cursor, "inexact"));
  const size_t arity = (size_t)parse_u64(
      line_number, "operand count",
      next_token(line_number, &cursor, "operand count"));
  if (arity != operation_arity(operation)) {
    fail_line(line_number, "operand count does not match operation");
  }

  const mpfr_prec_t precision = (mpfr_prec_t)(format.fraction_bits + 1);
  const mpfr_exp_t minimum_exponent =
      (mpfr_exp_t)(2 - (intmax_t)format.bias -
                   (intmax_t)format.fraction_bits);
  const mpfr_exp_t maximum_exponent =
      (mpfr_exp_t)(((UINT64_C(1) << format.exponent_bits) - 1) -
                   format.bias);
  if (mpfr_set_emin(minimum_exponent) != 0 ||
      mpfr_set_emax(maximum_exponent) != 0) {
    fail_line(line_number, "MPFR rejected the IEEE exponent range");
  }

  uint64_t operand_bits[3] = {0, 0, 0};
  mpfr_t operands[3];
  mpfr_t result;
  mpfr_t lean_result;
  for (size_t index = 0; index < 3; ++index) {
    mpfr_init2(operands[index], precision);
  }
  mpfr_init2(result, precision);
  mpfr_init2(lean_result, precision);
  int any_nan = 0;
  int any_signaling_nan = 0;
  for (size_t index = 0; index < arity; ++index) {
    operand_bits[index] = parse_u64(
        line_number, "operand bits",
        next_token(line_number, &cursor, "operand bits"));
    any_nan |= is_nan(operand_bits[index], &format);
    any_signaling_nan |= is_signaling_nan(operand_bits[index], &format);
    decode(operands[index], operand_bits[index], &format);
  }
  if (cursor != NULL) {
    fail_line(line_number, "trailing vector fields");
  }

  /*
   * Rounding to nearest with ties away from zero differs from MPFR_RNDN only in the value
   * delivered at an exact tie of the destination grid. Its flags are those of MPFR_RNDN for these
   * IEEE formats: both nearest rules overflow from the midpoint above the largest finite value,
   * whose significand is odd, and both are tiny exactly below the midpoint under the smallest
   * normal value, which both round up. The neighbours and the tie test come first, so their
   * MPFR operations stay outside the flag window of the checked operation.
   */
  int nearest_away_takes_away = 0;
  mpfr_t away;
  mpfr_init2(away, precision);
  if (rounding.nearest_away) {
    mpfr_t toward_zero;
    mpfr_init2(toward_zero, precision);
    const int toward_zero_ternary =
        round_in_destination(toward_zero, operation, operands, MPFR_RNDZ);
    (void)round_in_destination(away, operation, operands, MPFR_RNDA);
    if (toward_zero_ternary != 0 && !mpfr_nan_p(toward_zero)) {
      nearest_away_takes_away =
          nearest_away_tie(line_number, operation, operands, toward_zero, away,
                           maximum_exponent, precision);
      if (mpfr_set_emin(minimum_exponent) != 0 ||
          mpfr_set_emax(maximum_exponent) != 0) {
        fail_line(line_number, "MPFR rejected the IEEE exponent range");
      }
    }
    mpfr_clear(toward_zero);
  }

  mpfr_clear_flags();
  (void)round_in_destination(result, operation, operands, rounding.mpfr);

  const struct ieee_flags flags = ieee_flags_from_mpfr();
  if (nearest_away_takes_away) {
    mpfr_set(result, away, MPFR_RNDN);
  }
  mpfr_clear(away);
  const int invalid_combination =
      generated_invalid(operation, operand_bits, &format);
  if (!any_nan && (invalid_combination != flags.invalid)) {
    fail_line(line_number,
              "decoded IEEE invalid cause disagrees with MPFR NaN flag");
  }
  const int oracle_invalid = any_signaling_nan || invalid_combination;
  const int oracle_divide_by_zero = flags.divide_by_zero;
  const int oracle_overflow = flags.overflow;
  const int oracle_underflow = flags.underflow;
  const int oracle_inexact = flags.inexact;

  decode(lean_result, lean_bits, &format);
  check_result(line_number, case_name, operation_text, rounding_text,
               lean_bits, &format, result, lean_result);
  check_flag(line_number, case_name, operation_text, rounding_text,
             "invalid", lean_invalid, oracle_invalid);
  check_flag(line_number, case_name, operation_text, rounding_text,
             "divideByZero", lean_divide_by_zero, oracle_divide_by_zero);
  check_flag(line_number, case_name, operation_text, rounding_text,
             "overflow", lean_overflow, oracle_overflow);
  check_flag(line_number, case_name, operation_text, rounding_text,
             "underflow", lean_underflow, oracle_underflow);
  check_flag(line_number, case_name, operation_text, rounding_text,
             "inexact", lean_inexact, oracle_inexact);

  for (size_t index = 0; index < 3; ++index) {
    mpfr_clear(operands[index]);
  }
  mpfr_clear(result);
  mpfr_clear(lean_result);
}

int main(void) {
  const mpfr_exp_t original_emin = mpfr_get_emin();
  const mpfr_exp_t original_emax = mpfr_get_emax();
  wide_emin = original_emin;
  wide_emax = original_emax;
  char *line = NULL;
  size_t capacity = 0;
  size_t line_number = 0;
  size_t checked = 0;
  while (getline(&line, &capacity, stdin) >= 0) {
    ++line_number;
    if (line[0] == '#') {
      continue;
    }
    check_line(line_number, line);
    ++checked;
  }
  free(line);
  (void)mpfr_set_emin(original_emin);
  (void)mpfr_set_emax(original_emax);
  if (ferror(stdin)) {
    perror("reading primitive MPFR vectors");
    return EXIT_FAILURE;
  }
  fprintf(stderr, "primitive MPFR validation passed: %zu cases\n", checked);
  return EXIT_SUCCESS;
}
