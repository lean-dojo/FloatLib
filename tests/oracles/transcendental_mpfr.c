/*
 * Copyright (c) 2026 FloatLib
 * Released under MIT license as described in the file LICENSE.
 *
 * Correctly rounded MPFR references for the transcendental comparison.
 *
 * Every line is one request. Fields are separated by single spaces or tabs.
 *
 *   case ID op NAME mode MODE format EXPWIDTH FRACWIDTH BIAS ENCODING
 *        args K BITS... [floatlib BITS [ternary T]]
 *
 * NAME is exp, log, sin, cos, sinh, cosh, tanh (one argument), pow (two)
 * or pi (none); MODE is RNDN, RNDZ, RNDU, RNDD or RNDA. BITS are stored
 * encodings, written in hexadecimal with a 0x prefix or in decimal. Inputs
 * are decoded exactly with GMP; the result is rounded once into the
 * described format, whose exponent range and gradual underflow are emulated
 * with mpfr_set_emin, mpfr_set_emax, mpfr_check_range and
 * mpfr_subnormalize. The ternary value is threaded through all three
 * steps. The output repeats the request and appends
 *
 *   mpfr BITS T
 *
 * where BITS is the exact encoding of the rounded result and T the sign of
 * the final ternary value: -1 when the result is below the exact value,
 * 1 when above, and 0 when exact or NaN. MPFR has a single NaN; a NaN result
 * is written as the format's canonical quiet NaN.
 *
 *   contain ID op NAME format EXPWIDTH FRACWIDTH BIAS ENCODING
 *           args K BITS... lower M E upper M E
 *
 * asks whether the exact value of the function lies in the closed interval
 * whose endpoints are the signed dyadics M * 2^E after `lower` and `upper`
 * (M and E are integers, with an optional minus sign). The oracle
 * brackets the value by rounding down and up at doubling precision, from
 * max(64, 2 * (fracWidth + 1)) bits up to 2^20 bits, until the bracket
 * decides the question, and appends
 *
 *   result inside|outside|undecided|nan|range precision P
 *
 * `nan` marks a domain error, `range` a value outside MPFR's exponent range,
 * and `undecided` a value still straddling an endpoint at the largest
 * precision tried. A single rounded value is never used as a witness.
 *
 * Only the IEEE encoding of exceptional values is supported: MPFR has no
 * model of the saturating or NaN-on-overflow policies of the other
 * FloatLib encodings. Lines starting with `#` are copied unchanged, and a
 * line containing a NUL byte is rejected.
 */

#define _POSIX_C_SOURCE 200809L

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <gmp.h>
#include <mpfr.h>

enum operation {
  OP_EXP,
  OP_LOG,
  OP_SIN,
  OP_COS,
  OP_SINH,
  OP_COSH,
  OP_TANH,
  OP_POW,
  OP_PI,
};

struct operation_name {
  const char *name;
  enum operation operation;
  unsigned arity;
};

static const struct operation_name OPERATIONS[] = {
    {"exp", OP_EXP, 1},   {"log", OP_LOG, 1},   {"sin", OP_SIN, 1},
    {"cos", OP_COS, 1},   {"sinh", OP_SINH, 1}, {"cosh", OP_COSH, 1},
    {"tanh", OP_TANH, 1}, {"pow", OP_POW, 2},   {"pi", OP_PI, 0},
};

struct mode_name {
  const char *name;
  mpfr_rnd_t mode;
};

static const struct mode_name MODES[] = {
    {"RNDN", MPFR_RNDN}, {"RNDZ", MPFR_RNDZ}, {"RNDU", MPFR_RNDU},
    {"RNDD", MPFR_RNDD}, {"RNDA", MPFR_RNDA},
};

/* Widest exponent field accepted; wider fields would overflow mpfr_exp_t. */
#define MAX_EXPONENT_WIDTH 60
/* Widest fraction field accepted. */
#define MAX_FRACTION_WIDTH 1000000
/* Largest number of arguments of any operation. */
#define MAX_ARGUMENTS 2
/* Precision limits of the containment search. */
#define CONTAIN_START_PRECISION 64
#define CONTAIN_MAX_PRECISION 1048576

struct format {
  unsigned long exponent_width;
  unsigned long fraction_width;
  mpz_t bias;
  /* The exponents below are MPFR exponents: a value 2^k has exponent k+1. */
  mpfr_exp_t emin;
  mpfr_exp_t emax;
  long minimum_normal_exponent; /* IEEE exponent of the smallest normal */
  long bias_value;
};

static size_t current_line;

static void fail(const char *message, const char *detail) {
  if (detail != NULL) {
    fprintf(stderr, "transcendental MPFR line %zu: %s: %s\n", current_line,
            message, detail);
  } else {
    fprintf(stderr, "transcendental MPFR line %zu: %s\n", current_line,
            message);
  }
  exit(EXIT_FAILURE);
}

/* Split a line into fields separated by spaces or tabs. */
static size_t split_fields(char *line, char **fields, size_t capacity) {
  size_t count = 0;
  char *cursor = line;
  while (*cursor != '\0') {
    while (*cursor == ' ' || *cursor == '\t') ++cursor;
    if (*cursor == '\0') break;
    if (count == capacity) fail("too many fields", NULL);
    fields[count++] = cursor;
    while (*cursor != '\0' && *cursor != ' ' && *cursor != '\t') ++cursor;
    if (*cursor != '\0') *cursor++ = '\0';
  }
  return count;
}

struct cursor {
  char **fields;
  size_t count;
  size_t index;
};

static const char *take(struct cursor *cursor, const char *what) {
  if (cursor->index >= cursor->count) fail("missing field", what);
  return cursor->fields[cursor->index++];
}

static void expect_keyword(struct cursor *cursor, const char *keyword) {
  const char *field = take(cursor, keyword);
  if (strcmp(field, keyword) != 0) fail("expected keyword", keyword);
}

static int has_keyword(struct cursor *cursor, const char *keyword) {
  return cursor->index < cursor->count &&
         strcmp(cursor->fields[cursor->index], keyword) == 0;
}

/* Parse a nonnegative integer in decimal or 0x-prefixed hexadecimal. */
static void parse_natural(mpz_t value, const char *text, const char *what) {
  const char *digits = text;
  int base = 10;
  if (text[0] == '0' && (text[1] == 'x' || text[1] == 'X')) {
    digits = text + 2;
    base = 16;
  } else if (text[0] == '0' && text[1] != '\0') {
    fail("decimal numbers have no leading zeros", what);
  }
  if (*digits == '\0') fail("empty number", what);
  for (const char *p = digits; *p != '\0'; ++p) {
    const int ok = base == 16 ? (strchr("0123456789abcdefABCDEF", *p) != NULL)
                              : (*p >= '0' && *p <= '9');
    if (!ok) fail("invalid number", what);
  }
  if (mpz_set_str(value, digits, base) != 0) fail("invalid number", what);
}

/* Parse a signed integer: an optional minus sign before a natural number. */
static void parse_integer(mpz_t value, const char *text, const char *what) {
  if (text[0] == '-') {
    parse_natural(value, text + 1, what);
    mpz_neg(value, value);
  } else {
    parse_natural(value, text, what);
  }
}

static unsigned long parse_small(const char *text, const char *what,
                                 unsigned long minimum,
                                 unsigned long maximum) {
  mpz_t value;
  mpz_init(value);
  parse_natural(value, text, what);
  if (mpz_cmp_ui(value, minimum) < 0 || mpz_cmp_ui(value, maximum) > 0) {
    fail("value out of range", what);
  }
  const unsigned long result = mpz_get_ui(value);
  mpz_clear(value);
  return result;
}

static const struct operation_name *parse_operation(const char *text) {
  for (size_t i = 0; i < sizeof OPERATIONS / sizeof OPERATIONS[0]; ++i) {
    if (strcmp(text, OPERATIONS[i].name) == 0) return &OPERATIONS[i];
  }
  fail("unknown operation", text);
  return NULL;
}

static mpfr_rnd_t parse_mode(const char *text) {
  for (size_t i = 0; i < sizeof MODES / sizeof MODES[0]; ++i) {
    if (strcmp(text, MODES[i].name) == 0) return MODES[i].mode;
  }
  fail("unknown rounding mode", text);
  return MPFR_RNDN;
}

/*
 * Read EXPWIDTH FRACWIDTH BIAS ENCODING and derive the emulated range.
 * IEEE exponents: normal values have exponents 1 - bias .. 2^w - 2 - bias,
 * the smallest subnormal is 2^(1 - bias - fracWidth). MPFR exponents are one
 * larger, so emin = 2 - bias - fracWidth and emax = 2^w - 1 - bias.
 */
static void parse_format(struct cursor *cursor, struct format *format) {
  format->exponent_width =
      parse_small(take(cursor, "exponent width"), "exponent width", 2,
                  MAX_EXPONENT_WIDTH);
  format->fraction_width =
      parse_small(take(cursor, "fraction width"), "fraction width", 1,
                  MAX_FRACTION_WIDTH);
  parse_natural(format->bias, take(cursor, "bias"), "bias");
  const char *encoding = take(cursor, "encoding");
  if (strcmp(encoding, "ieee") != 0) {
    fail("only the ieee encoding has an MPFR emulation", encoding);
  }
  mpz_t largest_biased;
  mpz_init(largest_biased);
  mpz_ui_pow_ui(largest_biased, 2, format->exponent_width);
  mpz_sub_ui(largest_biased, largest_biased, 2);
  if (mpz_sgn(format->bias) <= 0 || mpz_cmp(format->bias, largest_biased) > 0) {
    fail("bias must lie in 1 .. 2^expWidth - 2", NULL);
  }
  if (!mpz_fits_slong_p(format->bias)) fail("bias too large", NULL);
  format->bias_value = mpz_get_si(format->bias);
  const long largest = mpz_get_si(largest_biased);
  mpz_clear(largest_biased);
  const long fraction = (long)format->fraction_width;
  format->minimum_normal_exponent = 1 - format->bias_value;
  format->emin = (mpfr_exp_t)(2 - format->bias_value - fraction);
  format->emax = (mpfr_exp_t)(largest - format->bias_value + 1);
  if (format->emin < mpfr_get_emin_min() || format->emax > mpfr_get_emax_max()) {
    fail("exponent range exceeds MPFR's limits", NULL);
  }
}

static void check_width(const mpz_t bits, const struct format *format,
                        const char *what) {
  if (mpz_sizeinbase(bits, 2) >
          1 + format->exponent_width + format->fraction_width &&
      mpz_sgn(bits) != 0) {
    fail("encoding exceeds the format width", what);
  }
}

/* Decode an encoding exactly; `value` must have at least fracWidth+1 bits. */
static void decode(mpfr_t value, const mpz_t bits, const struct format *format) {
  const unsigned long fraction_width = format->fraction_width;
  const unsigned long exponent_width = format->exponent_width;
  const int negative = mpz_tstbit(bits, exponent_width + fraction_width);
  mpz_t field;
  mpz_t fraction;
  mpz_inits(field, fraction, NULL);
  mpz_fdiv_q_2exp(field, bits, fraction_width);
  mpz_fdiv_r_2exp(field, field, exponent_width);
  mpz_fdiv_r_2exp(fraction, bits, fraction_width);
  const unsigned long biased = mpz_get_ui(field);
  const unsigned long all_ones = (1UL << exponent_width) - 1UL;
  if (biased == all_ones) {
    if (mpz_sgn(fraction) == 0) {
      mpfr_set_inf(value, negative ? -1 : 1);
    } else {
      mpfr_set_nan(value);
    }
  } else if (biased == 0 && mpz_sgn(fraction) == 0) {
    mpfr_set_zero(value, negative ? -1 : 1);
  } else {
    long power = format->minimum_normal_exponent - (long)fraction_width;
    if (biased != 0) {
      mpz_setbit(fraction, fraction_width);
      power = (long)biased - format->bias_value - (long)fraction_width;
    }
    if (mpfr_set_z_2exp(value, fraction, (mpfr_exp_t)power, MPFR_RNDN) != 0) {
      fail("input decoding was inexact", NULL);
    }
    if (negative) mpfr_neg(value, value, MPFR_RNDN);
  }
  mpz_clears(field, fraction, NULL);
}

/* Encode a value already rounded into the format. */
static void encode(mpz_t bits, mpfr_srcptr value, const struct format *format) {
  const unsigned long fraction_width = format->fraction_width;
  const unsigned long exponent_width = format->exponent_width;
  const unsigned long all_ones = (1UL << exponent_width) - 1UL;
  mpz_set_ui(bits, 0);
  if (mpfr_nan_p(value)) {
    mpz_set_ui(bits, all_ones);
    mpz_mul_2exp(bits, bits, fraction_width);
    mpz_setbit(bits, fraction_width - 1);
    return;
  }
  if (mpfr_inf_p(value)) {
    mpz_set_ui(bits, all_ones);
    mpz_mul_2exp(bits, bits, fraction_width);
  } else if (!mpfr_zero_p(value)) {
    mpz_t significand;
    mpz_init(significand);
    long exponent = (long)mpfr_get_z_2exp(significand, value);
    mpz_abs(significand, significand);
    /* Remove trailing zeros, then place the value on the format's grid. */
    const unsigned long trailing = mpz_scan1(significand, 0);
    mpz_fdiv_q_2exp(significand, significand, trailing);
    exponent += (long)trailing;
    const long leading = exponent + (long)mpz_sizeinbase(significand, 2) - 1;
    long quantum = leading - (long)fraction_width;
    unsigned long biased = 0;
    if (leading < format->minimum_normal_exponent) {
      quantum = format->minimum_normal_exponent - (long)fraction_width;
    } else {
      biased = (unsigned long)(leading + format->bias_value);
      if (biased >= all_ones) fail("rounded result exceeds the format", NULL);
    }
    if (exponent < quantum) fail("rounded result is off the format grid", NULL);
    mpz_mul_2exp(significand, significand, (unsigned long)(exponent - quantum));
    if (biased != 0) mpz_clrbit(significand, fraction_width);
    if (mpz_sizeinbase(significand, 2) > fraction_width &&
        mpz_sgn(significand) != 0) {
      fail("rounded result is off the format grid", NULL);
    }
    mpz_set_ui(bits, biased);
    mpz_mul_2exp(bits, bits, fraction_width);
    mpz_ior(bits, bits, significand);
    mpz_clear(significand);
  }
  if (mpfr_signbit(value)) mpz_setbit(bits, exponent_width + fraction_width);
}

static int sign_of(int ternary) { return (ternary > 0) - (ternary < 0); }

/* Evaluate one operation; returns MPFR's ternary value. */
static int evaluate(mpfr_t result, enum operation operation, mpfr_t *arguments,
                    mpfr_rnd_t mode) {
  switch (operation) {
    case OP_EXP:
      return mpfr_exp(result, arguments[0], mode);
    case OP_LOG:
      return mpfr_log(result, arguments[0], mode);
    case OP_SIN:
      return mpfr_sin(result, arguments[0], mode);
    case OP_COS:
      return mpfr_cos(result, arguments[0], mode);
    case OP_SINH:
      return mpfr_sinh(result, arguments[0], mode);
    case OP_COSH:
      return mpfr_cosh(result, arguments[0], mode);
    case OP_TANH:
      return mpfr_tanh(result, arguments[0], mode);
    case OP_POW:
      return mpfr_pow(result, arguments[0], arguments[1], mode);
    case OP_PI:
      return mpfr_const_pi(result, mode);
  }
  return 0;
}

static void restore_range(void) {
  (void)mpfr_set_emin(mpfr_get_emin_min());
  (void)mpfr_set_emax(mpfr_get_emax_max());
}

static void print_hex(const mpz_t bits) { gmp_printf("0x%Zx", bits); }

/* Read `args K BITS...` into decoded MPFR values. */
static size_t parse_arguments(struct cursor *cursor,
                              const struct operation_name *operation,
                              const struct format *format, mpfr_t *arguments) {
  expect_keyword(cursor, "args");
  const unsigned long count =
      parse_small(take(cursor, "argument count"), "argument count", 0,
                  MAX_ARGUMENTS);
  if (count != operation->arity) fail("wrong argument count", operation->name);
  mpz_t bits;
  mpz_init(bits);
  for (unsigned long i = 0; i < count; ++i) {
    parse_natural(bits, take(cursor, "argument"), "argument");
    check_width(bits, format, "argument");
    mpfr_init2(arguments[i], (mpfr_prec_t)(format->fraction_width + 1));
    decode(arguments[i], bits, format);
  }
  mpz_clear(bits);
  return count;
}

static void process_case(struct cursor *cursor, const char *line) {
  (void)take(cursor, "case id");
  expect_keyword(cursor, "op");
  const struct operation_name *operation = parse_operation(take(cursor, "op"));
  expect_keyword(cursor, "mode");
  const mpfr_rnd_t mode = parse_mode(take(cursor, "mode"));
  expect_keyword(cursor, "format");
  struct format format;
  mpz_init(format.bias);
  parse_format(cursor, &format);

  restore_range();
  mpfr_t arguments[MAX_ARGUMENTS];
  const size_t count = parse_arguments(cursor, operation, &format, arguments);

  mpz_t bits;
  mpz_init(bits);
  if (has_keyword(cursor, "floatlib")) {
    ++cursor->index;
    parse_natural(bits, take(cursor, "FloatLib result"), "FloatLib result");
    check_width(bits, &format, "FloatLib result");
    if (has_keyword(cursor, "ternary")) {
      ++cursor->index;
      const char *text = take(cursor, "FloatLib ternary");
      if (strcmp(text, "-1") != 0 && strcmp(text, "0") != 0 &&
          strcmp(text, "1") != 0) {
        fail("ternary must be -1, 0 or 1", text);
      }
    }
  }
  if (cursor->index != cursor->count) {
    fail("unexpected trailing field", cursor->fields[cursor->index]);
  }

  /* All inputs lie in the emulated range, so they stay valid after the switch. */
  if (mpfr_set_emin(format.emin) != 0 || mpfr_set_emax(format.emax) != 0) {
    fail("MPFR rejected the exponent range", NULL);
  }
  mpfr_t result;
  mpfr_init2(result, (mpfr_prec_t)(format.fraction_width + 1));
  mpfr_clear_flags();
  int ternary = evaluate(result, operation->operation, arguments, mode);
  ternary = mpfr_check_range(result, ternary, mode);
  ternary = mpfr_subnormalize(result, ternary, mode);
  encode(bits, result, &format);
  restore_range();

  fputs(line, stdout);
  fputs(" mpfr ", stdout);
  print_hex(bits);
  printf(" %d\n", mpfr_nan_p(result) ? 0 : sign_of(ternary));

  mpfr_clear(result);
  for (size_t i = 0; i < count; ++i) mpfr_clear(arguments[i]);
  mpz_clears(bits, format.bias, NULL);
}

static void parse_endpoint(struct cursor *cursor, const char *keyword,
                           mpfr_t endpoint) {
  expect_keyword(cursor, keyword);
  mpz_t mantissa;
  mpz_t exponent;
  mpz_inits(mantissa, exponent, NULL);
  parse_integer(mantissa, take(cursor, "endpoint mantissa"), keyword);
  parse_integer(exponent, take(cursor, "endpoint exponent"), keyword);
  if (!mpz_fits_slong_p(exponent)) fail("endpoint exponent too large", keyword);
  const size_t width = mpz_sizeinbase(mantissa, 2);
  mpfr_init2(endpoint, (mpfr_prec_t)(width < 2 ? 2 : width));
  if (mpfr_set_z_2exp(endpoint, mantissa, (mpfr_exp_t)mpz_get_si(exponent),
                      MPFR_RNDN) != 0) {
    fail("endpoint is outside MPFR's exponent range", keyword);
  }
  mpz_clears(mantissa, exponent, NULL);
}

/*
 * Decide whether f(args) lies in [lower, upper]. At each precision the value
 * is rounded down and up: an exact rounding gives the value itself, and an
 * inexact pair brackets it strictly. Overflow or underflow of MPFR's own
 * exponent range makes the bracket meaningless and reports `range`.
 */
static void process_contain(struct cursor *cursor, const char *line) {
  (void)take(cursor, "case id");
  expect_keyword(cursor, "op");
  const struct operation_name *operation = parse_operation(take(cursor, "op"));
  expect_keyword(cursor, "format");
  struct format format;
  mpz_init(format.bias);
  parse_format(cursor, &format);
  restore_range();
  mpfr_t arguments[MAX_ARGUMENTS];
  const size_t count = parse_arguments(cursor, operation, &format, arguments);
  mpfr_t lower;
  mpfr_t upper;
  parse_endpoint(cursor, "lower", lower);
  parse_endpoint(cursor, "upper", upper);
  if (cursor->index != cursor->count) {
    fail("unexpected trailing field", cursor->fields[cursor->index]);
  }
  if (mpfr_cmp(lower, upper) > 0) fail("empty interval", NULL);

  const char *verdict = "undecided";
  mpfr_prec_t precision = CONTAIN_START_PRECISION;
  if (precision < (mpfr_prec_t)(2 * (format.fraction_width + 1))) {
    precision = (mpfr_prec_t)(2 * (format.fraction_width + 1));
  }
  if (precision > CONTAIN_MAX_PRECISION) precision = CONTAIN_MAX_PRECISION;
  mpfr_t down;
  mpfr_t up;
  mpfr_inits2(precision, down, up, (mpfr_ptr)0);
  for (;;) {
    mpfr_set_prec(down, precision);
    mpfr_set_prec(up, precision);
    mpfr_clear_flags();
    const int below = evaluate(down, operation->operation, arguments, MPFR_RNDD);
    (void)evaluate(up, operation->operation, arguments, MPFR_RNDU);
    if (mpfr_nan_p(down) || mpfr_nan_p(up)) {
      verdict = "nan";
      break;
    }
    if (mpfr_overflow_p() || mpfr_underflow_p()) {
      verdict = "range";
      break;
    }
    if (below == 0) {
      verdict = mpfr_cmp(lower, down) <= 0 && mpfr_cmp(down, upper) <= 0
                    ? "inside"
                    : "outside";
      break;
    }
    if (mpfr_cmp(lower, down) <= 0 && mpfr_cmp(up, upper) <= 0) {
      verdict = "inside";
      break;
    }
    if (mpfr_cmp(up, lower) <= 0 || mpfr_cmp(down, upper) >= 0) {
      verdict = "outside";
      break;
    }
    if (precision >= CONTAIN_MAX_PRECISION) break;
    precision = precision > CONTAIN_MAX_PRECISION / 2 ? CONTAIN_MAX_PRECISION : 2 * precision;
  }
  printf("%s result %s precision %ld\n", line, verdict, (long)precision);
  mpfr_clears(down, up, lower, upper, (mpfr_ptr)0);
  for (size_t i = 0; i < count; ++i) mpfr_clear(arguments[i]);
  mpz_clear(format.bias);
}

int main(void) {
  const mpfr_exp_t original_emin = mpfr_get_emin();
  const mpfr_exp_t original_emax = mpfr_get_emax();
  char *line = NULL;
  size_t capacity = 0;
  size_t cases = 0;
  size_t queries = 0;
  ssize_t length;
  char **fields = NULL;
  size_t field_capacity = 0;

  while ((length = getline(&line, &capacity, stdin)) >= 0) {
    ++current_line;
    /* Parsing and echoing stop at a NUL, which would hide the rest of the line. */
    if (memchr(line, '\0', (size_t)length) != NULL) {
      fail("NUL byte in request", NULL);
    }
    while (length > 0 && (line[length - 1] == '\n' || line[length - 1] == '\r')) {
      line[--length] = '\0';
    }
    if (line[0] == '#') {
      puts(line);
      continue;
    }
    if (length == 0) continue;
    char *copy = strdup(line);
    if (copy == NULL) {
      perror("transcendental MPFR");
      return EXIT_FAILURE;
    }
    if (field_capacity < (size_t)length + 1) {
      field_capacity = (size_t)length + 1;
      fields = realloc(fields, field_capacity * sizeof *fields);
      if (fields == NULL) {
        perror("transcendental MPFR");
        return EXIT_FAILURE;
      }
    }
    struct cursor cursor = {fields, split_fields(copy, fields, field_capacity), 0};
    const char *kind = take(&cursor, "request kind");
    if (strcmp(kind, "case") == 0) {
      process_case(&cursor, line);
      ++cases;
    } else if (strcmp(kind, "contain") == 0) {
      process_contain(&cursor, line);
      ++queries;
    } else {
      fail("unknown request", kind);
    }
    free(copy);
  }
  free(fields);
  free(line);
  (void)mpfr_set_emin(original_emin);
  (void)mpfr_set_emax(original_emax);
  mpfr_free_cache();
  if (ferror(stdin)) {
    perror("reading transcendental vectors");
    return EXIT_FAILURE;
  }
  if (fflush(stdout) != 0) {
    perror("writing transcendental references");
    return EXIT_FAILURE;
  }
  fprintf(stderr,
          "MPFR transcendental references generated: %zu cases, %zu "
          "containment queries\n",
          cases, queries);
  return EXIT_SUCCESS;
}
