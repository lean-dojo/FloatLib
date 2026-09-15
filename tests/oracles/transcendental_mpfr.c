/*
 * Copyright (c) 2026 FloatLib
 * Released under MIT license as described in the file LICENSE.
 *
 * Correctly rounded MPFR references for the bounded transcendental comparison.
 */

#define _POSIX_C_SOURCE 200809L

#include <errno.h>
#include <float.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <mpfr.h>

enum format_kind {
  FORMAT_BINARY32,
  FORMAT_BINARY64,
};

enum operation {
  OP_EXP,
  OP_LOG,
  OP_SIN,
  OP_COS,
  OP_SINH,
  OP_COSH,
  OP_TANH,
};

struct format {
  enum format_kind kind;
  unsigned exponent_bits;
  unsigned fraction_bits;
  unsigned bias;
};

static void fail_line(size_t line_number, const char *message) {
  fprintf(stderr, "transcendental MPFR line %zu: %s\n", line_number,
          message);
  exit(EXIT_FAILURE);
}

static char *next_token(size_t line_number, char **cursor,
                        const char *name) {
  if (*cursor == NULL) {
    fprintf(stderr, "transcendental MPFR line %zu: missing %s\n",
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
    fprintf(stderr, "transcendental MPFR line %zu: empty %s\n",
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
    fprintf(stderr, "transcendental MPFR line %zu: invalid %s: %s\n",
            line_number, name, text);
    exit(EXIT_FAILURE);
  }
  return (uint64_t)value;
}

static struct format parse_format(size_t line_number, const char *text) {
  if (strcmp(text, "binary32") == 0) {
    return (struct format){FORMAT_BINARY32, 8, 23, 127};
  }
  if (strcmp(text, "binary64") == 0) {
    return (struct format){FORMAT_BINARY64, 11, 52, 1023};
  }
  fail_line(line_number, "unknown format");
  return (struct format){FORMAT_BINARY32, 8, 23, 127};
}

static enum operation parse_operation(size_t line_number,
                                      const char *text) {
  if (strcmp(text, "exp") == 0) return OP_EXP;
  if (strcmp(text, "log") == 0) return OP_LOG;
  if (strcmp(text, "sin") == 0) return OP_SIN;
  if (strcmp(text, "cos") == 0) return OP_COS;
  if (strcmp(text, "sinh") == 0) return OP_SINH;
  if (strcmp(text, "cosh") == 0) return OP_COSH;
  if (strcmp(text, "tanh") == 0) return OP_TANH;
  fail_line(line_number, "unknown operation");
  return OP_EXP;
}

static uint64_t fraction_mask(const struct format *format) {
  return (UINT64_C(1) << format->fraction_bits) - UINT64_C(1);
}

static uint64_t exponent_field(uint64_t bits,
                               const struct format *format) {
  const uint64_t mask =
      (UINT64_C(1) << format->exponent_bits) - UINT64_C(1);
  return (bits >> format->fraction_bits) & mask;
}

static int sign_bit(uint64_t bits, const struct format *format) {
  return (int)((bits >> (format->exponent_bits + format->fraction_bits)) &
               UINT64_C(1));
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

static int evaluate(mpfr_t result, mpfr_srcptr input,
                    enum operation operation) {
  switch (operation) {
    case OP_EXP:
      return mpfr_exp(result, input, MPFR_RNDN);
    case OP_LOG:
      return mpfr_log(result, input, MPFR_RNDN);
    case OP_SIN:
      return mpfr_sin(result, input, MPFR_RNDN);
    case OP_COS:
      return mpfr_cos(result, input, MPFR_RNDN);
    case OP_SINH:
      return mpfr_sinh(result, input, MPFR_RNDN);
    case OP_COSH:
      return mpfr_cosh(result, input, MPFR_RNDN);
    case OP_TANH:
      return mpfr_tanh(result, input, MPFR_RNDN);
  }
  return 0;
}

static uint64_t encode(mpfr_srcptr value, const struct format *format) {
  if (mpfr_nan_p(value)) {
    if (format->kind == FORMAT_BINARY32) return UINT32_C(0x7fc00000);
    return UINT64_C(0x7ff8000000000000);
  }

  if (format->kind == FORMAT_BINARY32) {
    const float converted = mpfr_get_flt(value, MPFR_RNDN);
    uint32_t bits = 0;
    memcpy(&bits, &converted, sizeof(bits));
    return bits;
  }

  const double converted = mpfr_get_d(value, MPFR_RNDN);
  uint64_t bits = 0;
  memcpy(&bits, &converted, sizeof(bits));
  return bits;
}

static void check_host_ieee(void) {
  if (FLT_RADIX != 2 || sizeof(float) != sizeof(uint32_t) ||
      sizeof(double) != sizeof(uint64_t)) {
    fprintf(stderr, "the MPFR adapter requires IEEE binary32/binary64 host types\n");
    exit(EXIT_FAILURE);
  }
  const float one32 = 1.0f;
  const double one64 = 1.0;
  uint32_t bits32 = 0;
  uint64_t bits64 = 0;
  memcpy(&bits32, &one32, sizeof(bits32));
  memcpy(&bits64, &one64, sizeof(bits64));
  if (bits32 != UINT32_C(0x3f800000) ||
      bits64 != UINT64_C(0x3ff0000000000000)) {
    fprintf(stderr, "unsupported host floating-point encoding\n");
    exit(EXIT_FAILURE);
  }
}

static void process_line(size_t line_number, char *line) {
  char *cursor = line;
  const char *case_name = next_token(line_number, &cursor, "case name");
  const char *format_text = next_token(line_number, &cursor, "format");
  const char *operation_text =
      next_token(line_number, &cursor, "operation");
  const uint64_t input_bits = parse_u64(
      line_number, "input bits",
      next_token(line_number, &cursor, "input bits"));
  const uint64_t floatlib_bits = parse_u64(
      line_number, "FloatLib result bits",
      next_token(line_number, &cursor, "FloatLib result bits"));
  if (cursor != NULL) {
    fail_line(line_number, "trailing vector fields");
  }

  const struct format format = parse_format(line_number, format_text);
  const enum operation operation =
      parse_operation(line_number, operation_text);
  const unsigned width =
      format.exponent_bits + format.fraction_bits + 1;
  if (width < 64 && (input_bits >> width) != 0) {
    fail_line(line_number, "input bits exceed the format width");
  }
  if (width < 64 && (floatlib_bits >> width) != 0) {
    fail_line(line_number, "FloatLib result bits exceed the format width");
  }

  const mpfr_prec_t precision =
      (mpfr_prec_t)(format.fraction_bits + 1);
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

  mpfr_t input;
  mpfr_t result;
  mpfr_init2(input, precision);
  mpfr_init2(result, precision);
  decode(input, input_bits, &format);
  mpfr_clear_flags();
  const int ternary = evaluate(result, input, operation);
  (void)mpfr_subnormalize(result, ternary, MPFR_RNDN);
  const uint64_t reference_bits = encode(result, &format);
  mpfr_clear(input);
  mpfr_clear(result);

  printf("%s\t%s\t%s\t%" PRIu64 "\t%" PRIu64 "\t%" PRIu64 "\n",
         case_name, format_text, operation_text, input_bits,
         floatlib_bits, reference_bits);
}

int main(void) {
  check_host_ieee();
  const mpfr_exp_t original_emin = mpfr_get_emin();
  const mpfr_exp_t original_emax = mpfr_get_emax();
  char *line = NULL;
  size_t capacity = 0;
  size_t line_number = 0;
  size_t cases = 0;

  puts("# case\tformat\top\tinput_bits\tfloatlib_bits\tmpfr_bits");
  while (getline(&line, &capacity, stdin) >= 0) {
    ++line_number;
    if (line[0] == '#') continue;
    process_line(line_number, line);
    ++cases;
  }
  free(line);
  (void)mpfr_set_emin(original_emin);
  (void)mpfr_set_emax(original_emax);
  if (ferror(stdin)) {
    perror("reading transcendental vectors");
    return EXIT_FAILURE;
  }
  fprintf(stderr, "MPFR transcendental references generated: %zu cases\n",
          cases);
  return EXIT_SUCCESS;
}
