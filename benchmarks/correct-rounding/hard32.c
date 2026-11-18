/*
 * Rank candidates from CORE-MATH's exhaustive binary32 input space.
 * The ranking is a numerical screen, not a certificate of global hardness.
 */
#include <float.h>
#include <inttypes.h>
#include <math.h>
#include <mpfr.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern double cr_exp(double);
extern double cr_log(double);
extern double cr_expm1(double);
extern double cr_log1p(double);
typedef union { float value; uint32_t bits; } binary32;
typedef union { double value; uint64_t bits; } binary64;
typedef struct { uint32_t bits, distance; } candidate;

static int compare(const void *left, const void *right) {
    const candidate *a = left, *b = right;
    if (a->distance != b->distance) return a->distance < b->distance ? -1 : 1;
    return a->bits < b->bits ? -1 : a->bits > b->bits;
}

static double difficulty(uint32_t bits, int precision,
                         int (*function)(mpfr_ptr, mpfr_srcptr, mpfr_rnd_t)) {
    binary32 input = {.bits = bits};
    mpfr_t x, y, scaled;
    mpfr_inits2(precision, x, y, scaled, (mpfr_ptr) 0);
    mpfr_set_d(x, input.value, MPFR_RNDN);
    function(y, x, MPFR_RNDN);
    mpfr_abs(y, y, MPFR_RNDN);
    mpfr_mul_2si(scaled, y, 24 - mpfr_get_exp(y), MPFR_RNDN);
    mpfr_frac(scaled, scaled, MPFR_RNDN);
    mpfr_sub_d(scaled, scaled, 0.5, MPFR_RNDN);
    mpfr_abs(scaled, scaled, MPFR_RNDN);
    double result = -log2(mpfr_get_d(scaled, MPFR_RNDN));
    mpfr_clears(x, y, scaled, (mpfr_ptr) 0);
    return result;
}

int main(int argc, char **argv) {
    if (argc != 5) {
        fprintf(stderr, "usage: hard32 {exp|log|expm1|log1p} START END KEEP\n");
        return 2;
    }
    double (*function)(double) = NULL;
    int (*reference)(mpfr_ptr, mpfr_srcptr, mpfr_rnd_t) = NULL;
    if (!strcmp(argv[1], "exp")) { function = cr_exp; reference = mpfr_exp; }
    if (!strcmp(argv[1], "log")) { function = cr_log; reference = mpfr_log; }
    if (!strcmp(argv[1], "expm1")) { function = cr_expm1; reference = mpfr_expm1; }
    if (!strcmp(argv[1], "log1p")) { function = cr_log1p; reference = mpfr_log1p; }
    uint64_t start = strtoull(argv[2], NULL, 0), end = strtoull(argv[3], NULL, 0);
    size_t keep = strtoul(argv[4], NULL, 0);
    if (!function || start >= end || end > (UINT64_C(1) << 32) || !keep || keep > 1024)
        return 2;
    candidate *best = calloc(keep, sizeof(*best));
    if (!best) return 2;
    size_t count = 0, worst = 0;
    uint64_t finite_inputs = 0, normal_outputs = 0;
    for (uint64_t index = start; index < end; ++index) {
        binary32 input = {.bits = (uint32_t) index};
        if (!isfinite(input.value)) continue;
        ++finite_inputs;
        binary64 result = {.value = function((double) input.value)};
        double magnitude = fabs(result.value);
        if (!(magnitude >= FLT_MIN && magnitude <= FLT_MAX)) continue;
        ++normal_outputs;
        uint32_t low = (uint32_t) (result.bits & ((UINT64_C(1) << 29) - 1));
        uint32_t midpoint = UINT32_C(1) << 28;
        candidate next = {.bits = input.bits,
                          .distance = low > midpoint ? low - midpoint : midpoint - low};
        if (count == keep && compare(&next, &best[worst]) >= 0) continue;
        if (count < keep) best[count++] = next;
        else best[worst] = next;
        worst = 0;
        for (size_t i = 1; i < count; ++i)
            if (compare(&best[worst], &best[i]) < 0) worst = i;
    }
    qsort(best, count, sizeof(*best), compare);
    printf("{\"kind\":\"coverage\",\"operation\":\"%s\",\"start\":%" PRIu64
           ",\"end\":%" PRIu64 ",\"visited\":%" PRIu64 ",\"finite_inputs\":%" PRIu64
           ",\"normal_outputs\":%" PRIu64 ",\"selected\":%zu}\n",
           argv[1], start, end, end-start, finite_inputs, normal_outputs, count);
    for (size_t i = 0; i < count; ++i) {
        double first = difficulty(best[i].bits, 256, reference);
        double second = difficulty(best[i].bits, 512, reference);
        if (!isfinite(first) || !isfinite(second) || fabs(first-second) > 1e-9) {
            fprintf(stderr, "MPFR difficulty did not stabilize: %08" PRIx32 "\n", best[i].bits);
            free(best);
            return 1;
        }
        printf("{\"kind\":\"candidate\",\"operation\":\"%s\",\"bits\":%" PRIu32
               ",\"screen_distance_units_2pow_minus29\":%" PRIu32
               ",\"hardness_bits_256\":%.17g,\"hardness_bits_512\":%.17g}\n",
               argv[1], best[i].bits, best[i].distance, first, second);
    }
    free(best);
    return 0;
}
