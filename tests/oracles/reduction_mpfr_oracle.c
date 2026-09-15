/*
 * Copyright (c) 2026 FloatLib
 * Released under MIT license as described in the file LICENSE.
 * Independent MPFR oracle for correctly rounded finite reductions.
 */

#define _POSIX_C_SOURCE 200809L

#include <errno.h>
#include <inttypes.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <mpfr.h>

#include "ieee_flags.h"

enum operation {
  OP_SUM,
  OP_DOT,
};

struct exact_value {
  int negative;
  mpz_t significand;
  long exponent;
};

static void fail_line(size_t line_number, const char *message) {
  fprintf(stderr, "reduction MPFR vector line %zu: %s\n", line_number,
          message);
  exit(EXIT_FAILURE);
}

static unsigned long parse_ulong(size_t line_number, const char *name,
                                 const char *text) {
  char *end = NULL;
  errno = 0;
  unsigned long value = strtoul(text, &end, 10);
  if (errno != 0 || end == text || *end != '\0') {
    fprintf(stderr, "reduction MPFR vector line %zu: invalid %s: %s\n",
            line_number, name, text);
    exit(EXIT_FAILURE);
  }
  return value;
}

static long parse_long(size_t line_number, const char *name,
                       const char *text) {
  char *end = NULL;
  errno = 0;
  long value = strtol(text, &end, 10);
  if (errno != 0 || end == text || *end != '\0') {
    fprintf(stderr, "reduction MPFR vector line %zu: invalid %s: %s\n",
            line_number, name, text);
    exit(EXIT_FAILURE);
  }
  return value;
}

static int parse_flag(size_t line_number, const char *name,
                      const char *text) {
  unsigned long value = parse_ulong(line_number, name, text);
  if (value > 1) {
    fprintf(stderr, "reduction MPFR vector line %zu: %s must be 0 or 1\n",
            line_number, name);
    exit(EXIT_FAILURE);
  }
  return (int)value;
}

static char *next_token(size_t line_number, char **cursor,
                        const char *name) {
  if (*cursor == NULL) {
    fprintf(stderr, "reduction MPFR vector line %zu: missing %s\n",
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
    fprintf(stderr, "reduction MPFR vector line %zu: missing %s\n",
            line_number, name);
    exit(EXIT_FAILURE);
  }
  return token;
}

static enum operation parse_operation(size_t line_number,
                                      const char *text) {
  if (strcmp(text, "sum") == 0) {
    return OP_SUM;
  }
  if (strcmp(text, "dot") == 0) {
    return OP_DOT;
  }
  fail_line(line_number, "operation must be sum or dot");
  return OP_SUM;
}

static mpfr_rnd_t parse_rounding(size_t line_number, const char *text) {
  if (strcmp(text, "nearestEven") == 0) {
    return MPFR_RNDN;
  }
  if (strcmp(text, "towardZero") == 0) {
    return MPFR_RNDZ;
  }
  if (strcmp(text, "towardPositive") == 0) {
    return MPFR_RNDU;
  }
  if (strcmp(text, "towardNegative") == 0) {
    return MPFR_RNDD;
  }
  fail_line(line_number, "unknown rounding mode");
  return MPFR_RNDN;
}

static void parse_exact(size_t line_number, char **cursor,
                        struct exact_value *value) {
  value->negative =
      parse_flag(line_number, "input sign",
                 next_token(line_number, cursor, "input sign"));
  const char *significand =
      next_token(line_number, cursor, "input significand");
  mpz_init(value->significand);
  if (mpz_set_str(value->significand, significand, 10) != 0) {
    fail_line(line_number, "invalid input significand");
  }
  value->exponent =
      parse_long(line_number, "input exponent",
                 next_token(line_number, cursor, "input exponent"));
}

static void clear_exact(struct exact_value *value) {
  mpz_clear(value->significand);
}

static mpfr_prec_t exact_precision(const mpz_t significand) {
  size_t bits = mpz_sizeinbase(significand, 2);
  if (bits < MPFR_PREC_MIN) {
    return MPFR_PREC_MIN;
  }
  if (bits > (size_t)MPFR_PREC_MAX) {
    fprintf(stderr, "reduction MPFR input exceeds MPFR_PREC_MAX\n");
    exit(EXIT_FAILURE);
  }
  return (mpfr_prec_t)bits;
}

/*
 * Bound the significant-bit span of the exact reduction. At this
 * precision, mpfr_sum or mpfr_dot must return the mathematical result
 * without rounding, including after cancellation.
 */
static mpfr_prec_t reduction_precision(size_t line_number,
                                       enum operation operation,
                                       const struct exact_value *values,
                                       size_t count) {
  int have_nonzero = 0;
  __int128 minimum_low = 0;
  __int128 maximum_high = 0;
  size_t nonzero_terms = 0;

  for (size_t index = 0; index < count; ++index) {
    const struct exact_value *left = &values[index];
    if (mpz_sgn(left->significand) == 0) {
      continue;
    }

    __int128 low = left->exponent;
    __int128 high = low + (__int128)mpz_sizeinbase(left->significand, 2);
    if (operation == OP_DOT) {
      const struct exact_value *right = &values[count + index];
      if (mpz_sgn(right->significand) == 0) {
        continue;
      }
      low += right->exponent;
      high = low + (__int128)mpz_sizeinbase(left->significand, 2) +
             (__int128)mpz_sizeinbase(right->significand, 2);
    }

    if (!have_nonzero || low < minimum_low) {
      minimum_low = low;
    }
    if (!have_nonzero || high > maximum_high) {
      maximum_high = high;
    }
    have_nonzero = 1;
    ++nonzero_terms;
  }

  if (!have_nonzero) {
    return MPFR_PREC_MIN;
  }

  size_t carry_bits = 0;
  for (size_t terms = nonzero_terms; terms > 1;
       terms = terms / 2 + terms % 2) {
    ++carry_bits;
  }
  __int128 required =
      maximum_high - minimum_low + (__int128)carry_bits + 1;
  if (required < MPFR_PREC_MIN || required > MPFR_PREC_MAX) {
    fail_line(line_number, "exact reduction exceeds MPFR_PREC_MAX");
  }
  return (mpfr_prec_t)required;
}

static void set_exact(mpfr_t result, const struct exact_value *value) {
  mpfr_set_z_2exp(result, value->significand, value->exponent, MPFR_RNDN);
  if (value->negative) {
    mpfr_neg(result, result, MPFR_RNDN);
  }
}

static void report_value_mismatch(size_t line_number, const char *name,
                                  const char *operation,
                                  const char *rounding,
                                  const char *bits,
                                  mpfr_srcptr actual) {
  fprintf(stderr,
          "reduction MPFR mismatch at line %zu (%s, %s, %s, Lean bits=%s): "
          "MPFR=",
          line_number, name, operation, rounding, bits);
  mpfr_out_str(stderr, 16, 0, actual, MPFR_RNDN);
  fputc('\n', stderr);
  exit(EXIT_FAILURE);
}

static void check_flag(size_t line_number, const char *case_name,
                       const char *operation, const char *rounding,
                       const char *bits, const char *flag_name,
                       int expected, int actual) {
  if ((actual != 0) != (expected != 0)) {
    fprintf(stderr,
            "reduction MPFR flag mismatch at line %zu "
            "(%s, %s, %s, Lean bits=%s): "
            "%s expected=%d actual=%d\n",
            line_number, case_name, operation, rounding, bits,
            flag_name, expected, actual != 0);
    exit(EXIT_FAILURE);
  }
}

static void check_line(size_t line_number, char *line,
                       mpfr_exp_t original_emin,
                       mpfr_exp_t original_emax) {
  char *cursor = line;
  const char *case_name = next_token(line_number, &cursor, "case name");
  const char *operation_text =
      next_token(line_number, &cursor, "operation");
  enum operation operation = parse_operation(line_number, operation_text);
  const char *rounding_text =
      next_token(line_number, &cursor, "rounding mode");
  mpfr_rnd_t rounding = parse_rounding(line_number, rounding_text);
  unsigned long exponent_bits =
      parse_ulong(line_number, "exponent width",
                  next_token(line_number, &cursor, "exponent width"));
  unsigned long fraction_bits =
      parse_ulong(line_number, "fraction width",
                  next_token(line_number, &cursor, "fraction width"));
  unsigned long bias =
      parse_ulong(line_number, "exponent bias",
                  next_token(line_number, &cursor, "exponent bias"));
  unsigned long count =
      parse_ulong(line_number, "input count",
                  next_token(line_number, &cursor, "input count"));
  const char *result_class =
      next_token(line_number, &cursor, "result class");
  int expected_negative =
      parse_flag(line_number, "result sign",
                 next_token(line_number, &cursor, "result sign"));
  const char *expected_significand_text =
      next_token(line_number, &cursor, "result significand");
  long expected_exponent =
      parse_long(line_number, "result exponent",
                 next_token(line_number, &cursor, "result exponent"));
  const char *expected_bits =
      next_token(line_number, &cursor, "result bits");
  int expected_invalid =
      parse_flag(line_number, "invalid",
                 next_token(line_number, &cursor, "invalid"));
  int expected_divide_by_zero =
      parse_flag(line_number, "divideByZero",
                 next_token(line_number, &cursor, "divideByZero"));
  int expected_overflow =
      parse_flag(line_number, "overflow",
                 next_token(line_number, &cursor, "overflow"));
  int expected_underflow =
      parse_flag(line_number, "underflow",
                 next_token(line_number, &cursor, "underflow"));
  int expected_inexact =
      parse_flag(line_number, "inexact",
                 next_token(line_number, &cursor, "inexact"));

  if (exponent_bits < 2 || exponent_bits >= sizeof(unsigned long) * CHAR_BIT ||
      fraction_bits == 0 || fraction_bits >= (unsigned long)MPFR_PREC_MAX ||
      count > SIZE_MAX / sizeof(struct exact_value) ||
      (operation == OP_DOT && count > SIZE_MAX / 2)) {
    fail_line(line_number, "unsupported descriptor or input count");
  }

  size_t value_count = operation == OP_SUM ? count : 2 * count;
  struct exact_value *exact =
      calloc(value_count == 0 ? 1 : value_count, sizeof(*exact));
  mpfr_t *values =
      calloc(value_count == 0 ? 1 : value_count, sizeof(*values));
  mpfr_ptr *left =
      calloc(count == 0 ? 1 : count, sizeof(*left));
  mpfr_ptr *right =
      operation == OP_DOT
          ? calloc(count == 0 ? 1 : count, sizeof(*right))
          : NULL;
  if (exact == NULL || values == NULL || left == NULL ||
      (operation == OP_DOT && right == NULL)) {
    fail_line(line_number, "allocation failure");
  }

  if (mpfr_set_emin(original_emin) != 0 ||
      mpfr_set_emax(original_emax) != 0) {
    fail_line(line_number, "could not restore the MPFR exponent range");
  }
  for (size_t index = 0; index < value_count; ++index) {
    parse_exact(line_number, &cursor, &exact[index]);
    mpfr_init2(values[index], exact_precision(exact[index].significand));
    set_exact(values[index], &exact[index]);
  }
  if (cursor != NULL && *cursor != '\0' && *cursor != '\n' &&
      *cursor != '\r') {
    fail_line(line_number, "trailing vector fields");
  }
  for (size_t index = 0; index < count; ++index) {
    left[index] = values[index];
    if (operation == OP_DOT) {
      right[index] = values[count + index];
    }
  }

  mpfr_prec_t precision = (mpfr_prec_t)(fraction_bits + 1);
  mpfr_prec_t work_precision =
      reduction_precision(line_number, operation, exact, count);
  mpfr_t exact_result;
  mpfr_t result;
  mpfr_init2(exact_result, work_precision);
  mpfr_init2(result, precision);

  mpfr_clear_flags();
  int exact_ternary =
      operation == OP_SUM
          ? mpfr_sum(exact_result, (const mpfr_ptr *)left, count, MPFR_RNDN)
          : mpfr_dot(exact_result, (const mpfr_ptr *)left,
                     (const mpfr_ptr *)right, count, MPFR_RNDN);
  if (exact_ternary != 0) {
    fail_line(line_number, "internal MPFR exact-precision bound was too small");
  }

  mpz_t exact_significand;
  mpz_init(exact_significand);
  mpfr_exp_t exact_exponent =
      mpfr_get_z_2exp(exact_significand, exact_result);
  int exact_zero_negative = 0;
  if (mpz_sgn(exact_significand) == 0) {
    mpfr_t zero_probe;
    mpfr_init2(zero_probe, precision);
    int zero_ternary =
        operation == OP_SUM
            ? mpfr_sum(zero_probe, (const mpfr_ptr *)left, count, rounding)
            : mpfr_dot(zero_probe, (const mpfr_ptr *)left,
                       (const mpfr_ptr *)right, count, rounding);
    if (zero_ternary != 0 || !mpfr_zero_p(zero_probe)) {
      fail_line(line_number, "MPFR zero-sign probe was not exact zero");
    }
    exact_zero_negative = mpfr_signbit(zero_probe) != 0;
    mpfr_clear(zero_probe);
  }
  mpfr_exp_t minimum_exponent =
      (mpfr_exp_t)2 - (mpfr_exp_t)bias - (mpfr_exp_t)fraction_bits;
  mpfr_exp_t maximum_exponent =
      (mpfr_exp_t)(((unsigned long)1 << exponent_bits) - 1 - bias);
  if (mpfr_set_emin(minimum_exponent) != 0 ||
      mpfr_set_emax(maximum_exponent) != 0) {
    fail_line(line_number, "MPFR rejected the destination exponent range");
  }

  mpfr_clear_flags();
  int ternary = 0;
  if (mpz_sgn(exact_significand) == 0) {
    mpfr_set_zero(result, exact_zero_negative ? -1 : 1);
  } else {
    ternary =
        mpfr_set_z_2exp(result, exact_significand, exact_exponent, rounding);
    ternary = mpfr_check_range(result, ternary, rounding);
    /*
     * Values in the extended exponent range still need IEEE subnormal
     * rounding. Zero and infinity are already final, and MPFR 4.1 rejects
     * subnormalization of an underflowed zero with a nonzero ternary value.
     */
    if (mpfr_regular_p(result)) {
      ternary = mpfr_subnormalize(result, ternary, rounding);
    }
  }
  (void)ternary;

  const struct ieee_flags flags = ieee_flags_from_mpfr();
  int actual_invalid = flags.invalid;
  int actual_divide_by_zero = flags.divide_by_zero;
  int actual_overflow = flags.overflow;
  int actual_inexact = flags.inexact;
  int actual_underflow = flags.underflow;

  int value_matches = 0;
  if (strcmp(result_class, "infinity") == 0) {
    value_matches =
        mpfr_inf_p(result) && (mpfr_signbit(result) != 0) == expected_negative;
  } else if (strcmp(result_class, "finite") == 0) {
    mpz_t expected_significand;
    mpz_init(expected_significand);
    if (mpz_set_str(expected_significand, expected_significand_text, 10) != 0) {
      fail_line(line_number, "invalid result significand");
    }
    if (mpz_sgn(expected_significand) == 0) {
      value_matches =
          mpfr_zero_p(result) &&
          (mpfr_signbit(result) != 0) == expected_negative;
    } else {
      mpfr_t expected;
      mpfr_init2(expected, exact_precision(expected_significand));
      mpfr_set_z_2exp(expected, expected_significand, expected_exponent,
                     MPFR_RNDN);
      if (expected_negative) {
        mpfr_neg(expected, expected, MPFR_RNDN);
      }
      value_matches = mpfr_cmp(result, expected) == 0;
      mpfr_clear(expected);
    }
    mpz_clear(expected_significand);
  } else {
    fail_line(line_number, "result class must be finite or infinity");
  }

  if (!value_matches) {
    report_value_mismatch(line_number, case_name, operation_text,
                          rounding_text, expected_bits, result);
  }
  check_flag(line_number, case_name, operation_text, rounding_text,
             expected_bits, "invalid", expected_invalid, actual_invalid);
  check_flag(line_number, case_name, operation_text, rounding_text,
             expected_bits, "divideByZero", expected_divide_by_zero,
             actual_divide_by_zero);
  check_flag(line_number, case_name, operation_text, rounding_text,
             expected_bits, "overflow", expected_overflow, actual_overflow);
  check_flag(line_number, case_name, operation_text, rounding_text,
             expected_bits, "underflow", expected_underflow,
             actual_underflow);
  check_flag(line_number, case_name, operation_text, rounding_text,
             expected_bits, "inexact", expected_inexact, actual_inexact);

  mpz_clear(exact_significand);
  mpfr_clear(exact_result);
  mpfr_clear(result);
  for (size_t index = 0; index < value_count; ++index) {
    mpfr_clear(values[index]);
    clear_exact(&exact[index]);
  }
  free(right);
  free(left);
  free(values);
  free(exact);
}

int main(void) {
  const mpfr_exp_t original_emin = mpfr_get_emin();
  const mpfr_exp_t original_emax = mpfr_get_emax();
  char *line = NULL;
  size_t capacity = 0;
  size_t line_number = 0;
  size_t cases = 0;

  while (getline(&line, &capacity, stdin) >= 0) {
    ++line_number;
    if (line[0] == '#' || line[0] == '\n' || line[0] == '\0') {
      continue;
    }
    check_line(line_number, line, original_emin, original_emax);
    ++cases;
  }
  if (ferror(stdin)) {
    perror("reading reduction MPFR vectors");
    free(line);
    return EXIT_FAILURE;
  }
  free(line);
  if (cases == 0) {
    fprintf(stderr, "reduction MPFR oracle received no cases\n");
    return EXIT_FAILURE;
  }
  fprintf(stderr, "reduction MPFR oracle passed: %zu cases\n", cases);
  return EXIT_SUCCESS;
}
