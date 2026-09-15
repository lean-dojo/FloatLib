/*
 * Copyright (c) 2026 FloatLib
 * Released under MIT license as described in the file LICENSE.
 * Independent MPFR oracle for sharded binary16 differential checks.
 */

#include <errno.h>
#include <inttypes.h>
#include <mpfr.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum operation {
  OP_ADD,
  OP_MUL,
};

static uint64_t parse_u64(const char *name, const char *text) {
  char *end = NULL;
  errno = 0;
  unsigned long long value = strtoull(text, &end, 10);
  if (errno != 0 || end == text || *end != '\0') {
    fprintf(stderr, "invalid %s: %s\n", name, text);
    exit(2);
  }
  return (uint64_t)value;
}

static int half_is_nan(uint16_t bits) {
  return (bits & UINT16_C(0x7c00)) == UINT16_C(0x7c00) &&
         (bits & UINT16_C(0x03ff)) != 0;
}

static int half_is_signaling_nan(uint16_t bits) {
  return half_is_nan(bits) && (bits & UINT16_C(0x0200)) == 0;
}

static int half_is_inf(uint16_t bits) {
  return (bits & UINT16_C(0x7fff)) == UINT16_C(0x7c00);
}

static int half_is_zero(uint16_t bits) {
  return (bits & UINT16_C(0x7fff)) == 0;
}

static uint16_t quiet_nan(uint16_t bits) {
  return (uint16_t)(bits | UINT16_C(0x0200));
}

static int choose_nan(uint16_t left, uint16_t right, uint16_t *result) {
  if (half_is_signaling_nan(left)) {
    *result = quiet_nan(left);
  } else if (half_is_signaling_nan(right)) {
    *result = quiet_nan(right);
  } else if (half_is_nan(left)) {
    *result = quiet_nan(left);
  } else if (half_is_nan(right)) {
    *result = quiet_nan(right);
  } else {
    return 0;
  }
  return 1;
}

static void decode_finite_half(mpfr_t result, uint16_t bits) {
  const unsigned exponent = (bits >> 10) & 0x1f;
  const unsigned fraction = bits & 0x03ff;
  if (exponent == 0) {
    mpfr_set_ui_2exp(result, fraction, -24, MPFR_RNDN);
  } else {
    mpfr_set_ui_2exp(result, 1024U + fraction, (long)exponent - 25, MPFR_RNDN);
  }
  if ((bits & UINT16_C(0x8000)) != 0) {
    mpfr_neg(result, result, MPFR_RNDN);
  }
}

static uint16_t encode_half(const mpfr_t value) {
  const uint16_t sign = mpfr_signbit(value) ? UINT16_C(0x8000) : 0;
  if (mpfr_nan_p(value)) {
    return UINT16_C(0x7e00);
  }
  if (mpfr_inf_p(value)) {
    return (uint16_t)(sign | UINT16_C(0x7c00));
  }
  if (mpfr_zero_p(value)) {
    return sign;
  }

  mpfr_t magnitude;
  mpfr_init2(magnitude, 11);
  mpfr_abs(magnitude, value, MPFR_RNDN);
  const mpfr_exp_t exponent = mpfr_get_exp(magnitude);
  uint16_t encoded;
  if (exponent >= -13) {
    mpfr_mul_2si(magnitude, magnitude, 11 - exponent, MPFR_RNDN);
    const unsigned long mantissa = mpfr_get_ui(magnitude, MPFR_RNDN);
    const uint16_t exponent_field = (uint16_t)(exponent + 14);
    encoded = (uint16_t)(sign | (uint16_t)(exponent_field << 10) |
                         (uint16_t)(mantissa - 1024));
  } else {
    mpfr_mul_2si(magnitude, magnitude, 24, MPFR_RNDN);
    encoded = (uint16_t)(sign | (uint16_t)mpfr_get_ui(magnitude, MPFR_RNDN));
  }
  mpfr_clear(magnitude);
  return encoded;
}

static uint16_t finite_result(enum operation operation, uint16_t left_bits,
                              uint16_t right_bits, mpfr_t left, mpfr_t right,
                              mpfr_t result) {
  decode_finite_half(left, left_bits);
  decode_finite_half(right, right_bits);
  mpfr_clear_flags();
  int ternary;
  if (operation == OP_ADD) {
    ternary = mpfr_add(result, left, right, MPFR_RNDN);
  } else {
    ternary = mpfr_mul(result, left, right, MPFR_RNDN);
  }
  (void)mpfr_subnormalize(result, ternary, MPFR_RNDN);
  return encode_half(result);
}

static uint16_t expected_result(enum operation operation, uint16_t left,
                                uint16_t right, mpfr_t left_value,
                                mpfr_t right_value, mpfr_t result) {
  uint16_t nan;
  if (choose_nan(left, right, &nan)) {
    return nan;
  }

  const int left_inf = half_is_inf(left);
  const int right_inf = half_is_inf(right);
  if (operation == OP_ADD) {
    if (left_inf && right_inf) {
      return ((left ^ right) & UINT16_C(0x8000)) == 0 ? left
                                                       : UINT16_C(0x7e00);
    }
    if (left_inf) {
      return left;
    }
    if (right_inf) {
      return right;
    }
  } else {
    if ((left_inf && half_is_zero(right)) ||
        (right_inf && half_is_zero(left))) {
      return UINT16_C(0x7e00);
    }
    if (left_inf || right_inf) {
      return (uint16_t)(((left ^ right) & UINT16_C(0x8000)) |
                        UINT16_C(0x7c00));
    }
  }
  return finite_result(operation, left, right, left_value, right_value, result);
}

static uint16_t read_word(void) {
  unsigned char bytes[2];
  if (fread(bytes, 1, sizeof(bytes), stdin) != sizeof(bytes)) {
    if (ferror(stdin)) {
      perror("reading Lean result stream");
    } else {
      fprintf(stderr, "unexpected end of Lean result stream\n");
    }
    exit(1);
  }
  return (uint16_t)(bytes[0] | ((uint16_t)bytes[1] << 8));
}

int main(int argc, char **argv) {
  if (argc != 4) {
    fprintf(stderr,
            "usage: binary16_mpfr_oracle {add|mul} SHARD_INDEX SHARD_COUNT\n");
    return 2;
  }

  enum operation operation;
  if (strcmp(argv[1], "add") == 0) {
    operation = OP_ADD;
  } else if (strcmp(argv[1], "mul") == 0) {
    operation = OP_MUL;
  } else {
    fprintf(stderr, "unknown operation: %s\n", argv[1]);
    return 2;
  }

  const uint64_t shard_index = parse_u64("shard index", argv[2]);
  const uint64_t shard_count = parse_u64("shard count", argv[3]);
  const uint64_t total_pairs = UINT64_C(1) << 32;
  if (shard_count == 0 || shard_count > total_pairs ||
      shard_index >= shard_count) {
    fprintf(stderr, "invalid shard %" PRIu64 "/%" PRIu64 "\n", shard_index,
            shard_count);
    return 2;
  }
  const uint64_t start =
      (uint64_t)(((__uint128_t)total_pairs * shard_index) / shard_count);
  const uint64_t stop =
      (uint64_t)(((__uint128_t)total_pairs * (shard_index + 1)) / shard_count);

  if (mpfr_set_emin(-23) != 0 || mpfr_set_emax(16) != 0) {
    fprintf(stderr, "MPFR cannot represent the binary16 exponent range\n");
    return 2;
  }

  mpfr_t left_value;
  mpfr_t right_value;
  mpfr_t result;
  mpfr_inits2(11, left_value, right_value, result, (mpfr_ptr)0);
  static unsigned char input_buffer[1 << 20];
  setvbuf(stdin, (char *)input_buffer, _IOFBF, sizeof(input_buffer));

  for (uint64_t pair = start; pair < stop; ++pair) {
    const uint16_t left = (uint16_t)(pair >> 16);
    const uint16_t right = (uint16_t)pair;
    const uint16_t actual = read_word();
    const uint16_t expected =
        expected_result(operation, left, right, left_value, right_value, result);
    if (actual != expected) {
      fprintf(stderr,
              "binary16 %s mismatch at pair %" PRIu64
              ": left=0x%04" PRIx16 " right=0x%04" PRIx16
              " expected=0x%04" PRIx16 " actual=0x%04" PRIx16 "\n",
              argv[1], pair, left, right, expected, actual);
      mpfr_clears(left_value, right_value, result, (mpfr_ptr)0);
      return 1;
    }
  }

  if (fgetc(stdin) != EOF) {
    fprintf(stderr, "Lean result stream contains trailing bytes\n");
    mpfr_clears(left_value, right_value, result, (mpfr_ptr)0);
    return 1;
  }

  mpfr_clears(left_value, right_value, result, (mpfr_ptr)0);
  fprintf(stderr,
          "binary16 %s shard %" PRIu64 "/%" PRIu64
          " passed: %" PRIu64 " ordered pairs\n",
          argv[1], shard_index, shard_count, stop - start);
  return 0;
}
