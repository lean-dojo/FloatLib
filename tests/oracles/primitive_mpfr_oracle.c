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

static mpfr_rnd_t parse_rounding(size_t line_number, const char *text) {
  if (strcmp(text, "nearestEven") == 0) return MPFR_RNDN;
  if (strcmp(text, "towardZero") == 0) return MPFR_RNDZ;
  if (strcmp(text, "towardPositive") == 0) return MPFR_RNDU;
  if (strcmp(text, "towardNegative") == 0) return MPFR_RNDD;
  fail_line(line_number, "unknown rounding mode");
  return MPFR_RNDN;
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
      return invalid_product || opposite_infinite_addend;
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
  const mpfr_rnd_t rounding = parse_rounding(line_number, rounding_text);
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

  mpfr_clear_flags();
  int ternary = 0;
  switch (operation) {
    case OP_ADD:
      ternary = mpfr_add(result, operands[0], operands[1], rounding);
      break;
    case OP_SUB:
      ternary = mpfr_sub(result, operands[0], operands[1], rounding);
      break;
    case OP_MUL:
      ternary = mpfr_mul(result, operands[0], operands[1], rounding);
      break;
    case OP_DIV:
      ternary = mpfr_div(result, operands[0], operands[1], rounding);
      break;
    case OP_SQRT:
      ternary = mpfr_sqrt(result, operands[0], rounding);
      break;
    case OP_FMA:
      ternary = mpfr_fma(result, operands[0], operands[1], operands[2],
                         rounding);
      break;
  }
  (void)mpfr_subnormalize(result, ternary, rounding);

  const struct ieee_flags flags = ieee_flags_from_mpfr();
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
