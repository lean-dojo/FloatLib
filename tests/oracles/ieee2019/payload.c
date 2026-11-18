/* Reference results for the NaN payload operations of IEEE 754-2019 9.7 from the C library.
 *
 * glibc provides getpayload, setpayload and setpayloadsig (ISO/IEC 9899:2024 F.10.13.2 to
 * F.10.13.4). The program prints one case per line for `oracle ieee2019`:
 *
 *   pay OP WIDTH X R        OP get|set|setsig, WIDTH 32|64, words in hexadecimal
 *
 * usage: payload COUNT SEED
 */
#define _GNU_SOURCE
#define __STDC_WANT_IEC_60559_BFP_EXT__ 1
#define __STDC_WANT_IEC_60559_EXT__ 1
#include <inttypes.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static uint64_t state;

static uint64_t next(void) {
  state ^= state << 13;
  state ^= state >> 7;
  state ^= state << 17;
  return state;
}

static uint64_t bits64(double value) {
  uint64_t word;
  memcpy(&word, &value, sizeof word);
  return word;
}

static double from64(uint64_t word) {
  double value;
  memcpy(&value, &word, sizeof value);
  return value;
}

static uint32_t bits32(float value) {
  uint32_t word;
  memcpy(&word, &value, sizeof word);
  return word;
}

static float from32(uint32_t word) {
  float value;
  memcpy(&value, &word, sizeof value);
  return value;
}

/* A payload operand: an integer in or near the admissible range, a fraction, a negative or a
   special value. */
static double operand(int fractionBits) {
  uint64_t r = next();
  double integer = (double)(next() >> (64 - (int)(r % (uint64_t)(fractionBits + 2))));
  switch (r >> 60) {
    case 0: return integer + 0.5;
    case 1: return -integer;
    case 2: return ldexp(1.0, fractionBits - 1) + (double)(next() % 3) - 1.0;
    case 3: return from64(next());
    case 4: return 0.0;
    case 5: return -0.0;
    case 6: return (double)(next() % 5);
    default: return integer;
  }
}

int main(int argc, char **argv) {
  if (argc != 3) {
    fprintf(stderr, "usage: payload COUNT SEED\n");
    return 2;
  }
  long count = strtol(argv[1], NULL, 10);
  state = strtoull(argv[2], NULL, 10) * 0x9E3779B97F4A7C15ull + 1;
  for (long i = 0; i < count; i++) {
    uint64_t word = next();
    if (i % 4 != 3) word |= 0x7FF0000000000000ull;          /* mostly NaNs and infinities */
    double x = from64(word);
    printf("pay get 64 %016" PRIx64 " %016" PRIx64 "\n", word, bits64(getpayload(&x)));
    uint32_t narrow = (uint32_t)next();
    if (i % 4 != 3) narrow |= 0x7F800000u;
    float y = from32(narrow);
    printf("pay get 32 %08" PRIx32 " %08" PRIx32 "\n", narrow, bits32(getpayloadf(&y)));

    double pl = operand(52), result;
    setpayload(&result, pl);
    printf("pay set 64 %016" PRIx64 " %016" PRIx64 "\n", bits64(pl), bits64(result));
    setpayloadsig(&result, pl);
    printf("pay setsig 64 %016" PRIx64 " %016" PRIx64 "\n", bits64(pl), bits64(result));
    float plf = (float)operand(23), resultf;
    setpayloadf(&resultf, plf);
    printf("pay set 32 %08" PRIx32 " %08" PRIx32 "\n", bits32(plf), bits32(resultf));
    setpayloadsigf(&resultf, plf);
    printf("pay setsig 32 %08" PRIx32 " %08" PRIx32 "\n", bits32(plf), bits32(resultf));
  }
  return 0;
}
