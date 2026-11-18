/* MIT license, as in the repository LICENSE.
 * Independent unary reference using MPFR's documented IEEE emulation:
 * target precision, bounded exponents, and ternary-aware subnormal rounding.
 * Input: ID WIDTH OP INPUT_BITS_HEX. Output: ID OUTPUT_BITS_HEX NANOSECONDS.
 */
#define _POSIX_C_SOURCE 200809L
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <float.h>
#include <mpfr.h>

#ifdef CORE_REFERENCE
extern double cr_exp(double), cr_log(double), cr_expm1(double), cr_log1p(double);
extern float cr_expf(float), cr_logf(float), cr_expm1f(float), cr_log1pf(float);
static uint64_t core_result(unsigned width, const char *op, uint64_t bits) {
    if (width == 32) {
        uint32_t raw = (uint32_t)bits;
        float x, y;
        memcpy(&x, &raw, sizeof x);
        if (!strcmp(op, "exp")) y = cr_expf(x);
        else if (!strcmp(op, "log")) y = cr_logf(x);
        else if (!strcmp(op, "expm1")) y = cr_expm1f(x);
        else y = cr_log1pf(x);
        memcpy(&raw, &y, sizeof raw);
        return raw;
    }
    double x, y;
    memcpy(&x, &bits, sizeof x);
    if (!strcmp(op, "exp")) y = cr_exp(x);
    else if (!strcmp(op, "log")) y = cr_log(x);
    else if (!strcmp(op, "expm1")) y = cr_expm1(x);
    else y = cr_log1p(x);
    memcpy(&bits, &y, sizeof bits);
    return bits;
}
#endif

static uint64_t nanos(void) {
    struct timespec t;
    if (clock_gettime(CLOCK_MONOTONIC, &t)) abort();
    return (uint64_t)t.tv_sec * 1000000000 + t.tv_nsec;
}

int main(int argc, char **argv) {
    if (argc == 2 && !strcmp(argv[1], "--version")) {
        printf("MPFR %s; headers %s; GMP %s\n",
               mpfr_get_version(), MPFR_VERSION_STRING, gmp_version);
        return 0;
    }
    if (FLT_RADIX != 2 || FLT_MANT_DIG != 24 || DBL_MANT_DIG != 53 ||
        sizeof(float) != 4 || sizeof(double) != 8) {
        fputs("Native IEEE binary32/binary64 representations required\n", stderr);
        return 2;
    }
    char id[256], operation[32];
    unsigned width;
    uint64_t bits;
    while (scanf("%255s %u %31s %" SCNx64, id, &width, operation, &bits) == 4) {
        if (width != 32 && width != 64) return 2;
        unsigned p = width == 32 ? 24 : 53;
        if (mpfr_set_emin(width == 32 ? -148 : -1073) ||
            mpfr_set_emax(width == 32 ? 128 : 1024)) return 2;
        mpfr_t x, y;
        mpfr_init2(x, p);
        mpfr_init2(y, p);
        if (width == 32) {
            if (bits > UINT32_MAX) return 2;
            uint32_t raw = (uint32_t)bits;
            float value;
            memcpy(&value, &raw, sizeof value);
            mpfr_set_flt(x, value, MPFR_RNDN);
        } else {
            double value;
            memcpy(&value, &bits, sizeof value);
            mpfr_set_d(x, value, MPFR_RNDN);
        }
        mpfr_clear_flags();
        int ternary;
        uint64_t start = nanos();
        if (!strcmp(operation, "exp")) ternary = mpfr_exp(y, x, MPFR_RNDN);
        else if (!strcmp(operation, "log")) ternary = mpfr_log(y, x, MPFR_RNDN);
        else if (!strcmp(operation, "expm1")) ternary = mpfr_expm1(y, x, MPFR_RNDN);
        else if (!strcmp(operation, "log1p")) ternary = mpfr_log1p(y, x, MPFR_RNDN);
        else {
            fprintf(stderr, "Unsupported unary function: %s\n", operation);
            return 2;
        }
        mpfr_subnormalize(y, ternary, MPFR_RNDN);
        uint64_t result;
        if (width == 32) {
            float value = mpfr_get_flt(y, MPFR_RNDN);
            uint32_t raw;
            memcpy(&raw, &value, sizeof raw);
            result = raw;
        } else {
            double value = mpfr_get_d(y, MPFR_RNDN);
            memcpy(&result, &value, sizeof result);
        }
        uint64_t elapsed = nanos() - start;
        printf("%s %016" PRIx64 " %" PRIu64, id, result, elapsed);
#ifdef CORE_REFERENCE
        uint64_t core_start = nanos();
        uint64_t core = core_result(width, operation, bits);
        uint64_t core_elapsed = nanos() - core_start;
        printf(" %016" PRIx64 " %" PRIu64, core, core_elapsed);
#endif
        putchar('\n');
        fflush(stdout);
        mpfr_clear(x);
        mpfr_clear(y);
    }
    mpfr_free_cache();
    return ferror(stdin) ? 2 : 0;
}
