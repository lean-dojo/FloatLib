/*
 * Independent Clang Embedded C observations. Compile as C with -ffixed-point.
 * Saturating arithmetic avoids undefined overflow; zero divisors are not evaluated.
 * memcpy observes object representations without pointer aliasing assumptions.
 */
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#define LAYOUT(label, type) do { \
    type half = (type)0.5; \
    uint64_t word = 0; \
    if (sizeof(half) > sizeof(word)) return 2; \
    memcpy(&word, &half, sizeof(half)); \
    fprintf(stderr, "layout,%s,%zu,%llu\n", label, sizeof(half), (unsigned long long)word); \
} while (0)

#define RUN(sign, type) do { \
    if (sizeof(type) != 1 || CHAR_BIT != 8) return 3; \
    for (unsigned i = 0; i < 256; ++i) { \
        uint8_t ai = (uint8_t)i; \
        type a; memcpy(&a, &ai, 1); \
        for (unsigned j = 0; j < 256; ++j) { \
            uint8_t bj = (uint8_t)j; \
            type b; memcpy(&b, &bj, 1); \
            type results[4] = {a + b, a - b, a * b, (type)0}; \
            if (b != (type)0) results[3] = a / b; \
            printf("%d,%u,%u", sign, i, j); \
            for (unsigned k = 0; k < 4; ++k) { \
                uint8_t word; memcpy(&word, &results[k], 1); \
                if (k == 3 && b == (type)0) printf(",NA"); \
                else printf(",%u", word); \
            } \
            printf(",%d,%d,%d,%d,%d,%d\n", a == b, a != b, a < b, a <= b, a > b, a >= b); \
        } \
    } \
} while (0)

int main(void) {
    const uint16_t endian = 1;
    if (*(const unsigned char *)&endian != 1) return 4;
    LAYOUT("short _Fract", short _Fract);
    LAYOUT("_Fract", _Fract);
    LAYOUT("long _Fract", long _Fract);
    LAYOUT("unsigned short _Fract", unsigned short _Fract);
    LAYOUT("unsigned _Fract", unsigned _Fract);
    LAYOUT("unsigned long _Fract", unsigned long _Fract);
    LAYOUT("short _Accum", short _Accum);
    LAYOUT("_Accum", _Accum);
    LAYOUT("long _Accum", long _Accum);
    LAYOUT("unsigned short _Accum", unsigned short _Accum);
    LAYOUT("unsigned _Accum", unsigned _Accum);
    LAYOUT("unsigned long _Accum", unsigned long _Accum);
    RUN(1, _Sat short _Fract);
    RUN(0, _Sat unsigned short _Fract);
    return 0;
}
