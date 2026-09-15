/*
 * Stream SoftPosit pX2 reference results to FloatLib's independent checker.
 *
 * SoftPosit stores an n-bit pX2 word in the high bits of a uint32_t. This
 * program accepts and emits compact words, and treats nonzero result padding
 * as a protocol failure instead of silently discarding it.
 */

#include <errno.h>
#include <ctype.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "softposit.h"

enum operation {
    OP_NONE = 0,
    OP_ADD = 1,
    OP_SUB = 2,
    OP_MUL = 3,
    OP_DIV = 4,
    OP_FMA = 5,
    OP_SQRT = 6,
    OP_RINT = 7,
    OP_EQ = 8,
    OP_LE = 9,
    OP_LT = 10
};

enum family {
    FAMILY_PX2 = 0,
    FAMILY_P32 = 1
};

enum generation_mode {
    MODE_EXHAUSTIVE = 0,
    MODE_SAMPLED = 1
};

struct options {
    unsigned bits;
    enum operation operation;
    enum family family;
    bool exhaustive;
    uint64_t cases;
    uint64_t seed;
    uint64_t shard_index;
    uint64_t shard_count;
    uint8_t source_revision[20];
    char source_revision_hex[41];
    bool source_revision_seen;
};

static void fail_invalid_operation(enum operation operation)
{
    fprintf(stderr, "internal error: invalid operation id %d\n", (int)operation);
    exit(2);
}

static const char *operation_name(enum operation operation)
{
    switch (operation) {
    case OP_ADD: return "add";
    case OP_SUB: return "sub";
    case OP_MUL: return "mul";
    case OP_DIV: return "div";
    case OP_FMA: return "fma";
    case OP_SQRT: return "sqrt";
    case OP_RINT: return "rint";
    case OP_EQ: return "eq";
    case OP_LE: return "le";
    case OP_LT: return "lt";
    case OP_NONE: break;
    }
    fail_invalid_operation(operation);
    return NULL;
}

static unsigned operation_arity(enum operation operation)
{
    switch (operation) {
    case OP_SQRT:
    case OP_RINT:
        return 1;
    case OP_FMA:
        return 3;
    case OP_ADD:
    case OP_SUB:
    case OP_MUL:
    case OP_DIV:
    case OP_EQ:
    case OP_LE:
    case OP_LT:
        return 2;
    case OP_NONE:
        break;
    }
    fail_invalid_operation(operation);
    return 0;
}

static enum operation parse_operation(const char *text)
{
    if (strcmp(text, "add") == 0) return OP_ADD;
    if (strcmp(text, "sub") == 0) return OP_SUB;
    if (strcmp(text, "mul") == 0) return OP_MUL;
    if (strcmp(text, "div") == 0) return OP_DIV;
    if (strcmp(text, "fma") == 0) return OP_FMA;
    if (strcmp(text, "sqrt") == 0) return OP_SQRT;
    if (strcmp(text, "rint") == 0) return OP_RINT;
    if (strcmp(text, "eq") == 0) return OP_EQ;
    if (strcmp(text, "le") == 0) return OP_LE;
    if (strcmp(text, "lt") == 0) return OP_LT;
    fprintf(stderr, "unknown operation: %s\n", text);
    exit(2);
}

static uint64_t parse_u64(const char *name, const char *text)
{
    char *end = NULL;
    if (text[0] == '\0' || text[0] == '-' || text[0] == '+' ||
        isspace((unsigned char)text[0])) {
        fprintf(stderr, "invalid %s: %s\n", name, text);
        exit(2);
    }
    errno = 0;
    uint64_t value = strtoull(text, &end, 0);
    if (errno != 0 || end == text || *end != '\0') {
        fprintf(stderr, "invalid %s: %s\n", name, text);
        exit(2);
    }
    return value;
}

static void parse_shard(const char *text, uint64_t *index, uint64_t *count)
{
    char *end = NULL;
    if (text[0] == '\0' || text[0] == '-' || text[0] == '+' ||
        isspace((unsigned char)text[0])) {
        fprintf(stderr, "invalid shard (expected INDEX/COUNT): %s\n", text);
        exit(2);
    }
    errno = 0;
    uint64_t parsed_index = strtoull(text, &end, 0);
    if (errno != 0 || end == text || *end != '/') {
        fprintf(stderr, "invalid shard (expected INDEX/COUNT): %s\n", text);
        exit(2);
    }
    const char *count_text = end + 1;
    if (count_text[0] == '\0' || count_text[0] == '-' ||
        count_text[0] == '+' || isspace((unsigned char)count_text[0])) {
        fprintf(stderr, "invalid shard (expected INDEX/COUNT): %s\n", text);
        exit(2);
    }
    errno = 0;
    uint64_t parsed_count = strtoull(count_text, &end, 0);
    if (errno != 0 || end == count_text || *end != '\0' ||
        parsed_count == 0 || parsed_index >= parsed_count) {
        fprintf(stderr, "invalid shard (expected 0 <= INDEX < COUNT): %s\n", text);
        exit(2);
    }
    *index = parsed_index;
    *count = parsed_count;
}

static uint8_t parse_hex_nibble(char value)
{
    if (value >= '0' && value <= '9') return (uint8_t)(value - '0');
    if (value >= 'a' && value <= 'f') return (uint8_t)(value - 'a' + 10);
    if (value >= 'A' && value <= 'F') return (uint8_t)(value - 'A' + 10);
    fprintf(stderr, "invalid source revision: expected exactly 40 hexadecimal digits\n");
    exit(2);
}

static void parse_source_revision(const char *text, struct options *options)
{
    static const char digits[] = "0123456789abcdef";
    if (options->source_revision_seen) {
        fprintf(stderr, "--source-revision may be specified only once\n");
        exit(2);
    }
    if (strlen(text) != 40) {
        fprintf(stderr, "invalid source revision: expected exactly 40 hexadecimal digits\n");
        exit(2);
    }
    for (unsigned index = 0; index < 20; ++index) {
        uint8_t high = parse_hex_nibble(text[2 * index]);
        uint8_t low = parse_hex_nibble(text[2 * index + 1]);
        uint8_t byte = (uint8_t)((high << 4) | low);
        options->source_revision[index] = byte;
        options->source_revision_hex[2 * index] = digits[byte >> 4];
        options->source_revision_hex[2 * index + 1] = digits[byte & 0xf];
    }
    options->source_revision_hex[40] = '\0';
    options->source_revision_seen = true;
}

static void usage(const char *program)
{
    fprintf(stderr,
        "usage: %s --bits N --op OP [--family px2|p32]\n"
        "          (--exhaustive | --sampled COUNT) --source-revision SHA40\n"
        "          [--seed N] [--shard I/N]\n"
        "operations: add sub mul div fma sqrt rint eq le lt\n",
        program);
}

static struct options parse_options(int argc, char **argv)
{
    struct options options = {
        .bits = 0,
        .operation = OP_NONE,
        .family = FAMILY_PX2,
        .exhaustive = false,
        .cases = 0,
        .seed = UINT64_C(0x4f1bbcdc676f5f39),
        .shard_index = 0,
        .shard_count = 1,
        .source_revision = { 0 },
        .source_revision_hex = { 0 },
        .source_revision_seen = false
    };
    bool mode_seen = false;

    for (int index = 1; index < argc; ++index) {
        if (strcmp(argv[index], "--bits") == 0 && index + 1 < argc) {
            options.bits = (unsigned)parse_u64("width", argv[++index]);
        } else if (strcmp(argv[index], "--op") == 0 && index + 1 < argc) {
            options.operation = parse_operation(argv[++index]);
        } else if (strcmp(argv[index], "--family") == 0 && index + 1 < argc) {
            const char *family = argv[++index];
            if (strcmp(family, "px2") == 0) {
                options.family = FAMILY_PX2;
            } else if (strcmp(family, "p32") == 0) {
                options.family = FAMILY_P32;
            } else {
                fprintf(stderr, "unknown family: %s\n", family);
                exit(2);
            }
        } else if (strcmp(argv[index], "--exhaustive") == 0) {
            if (mode_seen) {
                fprintf(stderr, "choose exactly one generation mode\n");
                exit(2);
            }
            options.exhaustive = true;
            mode_seen = true;
        } else if (strcmp(argv[index], "--sampled") == 0 && index + 1 < argc) {
            if (mode_seen) {
                fprintf(stderr, "choose exactly one generation mode\n");
                exit(2);
            }
            options.cases = parse_u64("sample count", argv[++index]);
            mode_seen = true;
        } else if (strcmp(argv[index], "--seed") == 0 && index + 1 < argc) {
            options.seed = parse_u64("seed", argv[++index]);
        } else if (strcmp(argv[index], "--shard") == 0 && index + 1 < argc) {
            parse_shard(argv[++index], &options.shard_index, &options.shard_count);
        } else if (strcmp(argv[index], "--source-revision") == 0 &&
            index + 1 < argc) {
            parse_source_revision(argv[++index], &options);
        } else {
            usage(argv[0]);
            exit(2);
        }
    }

    if (options.bits < 2 || options.bits > 32 || options.operation == OP_NONE ||
        !mode_seen || !options.source_revision_seen ||
        (!options.exhaustive && options.cases == 0)) {
        usage(argv[0]);
        exit(2);
    }
    if (options.family == FAMILY_P32 && options.bits != 32) {
        fprintf(stderr, "the named p32 family requires --bits 32\n");
        exit(2);
    }
    if (options.exhaustive &&
        options.bits * operation_arity(options.operation) >= 64) {
        fprintf(stderr,
            "the exhaustive index space does not fit in 64 bits; use sampled mode\n");
        exit(2);
    }
    return options;
}

static enum generation_mode generation_mode(const struct options *options)
{
    return options->exhaustive ? MODE_EXHAUSTIVE : MODE_SAMPLED;
}

static const char *generation_mode_name(const struct options *options)
{
    return options->exhaustive ? "exhaustive" : "sampled";
}

static uint64_t source_case_count(const struct options *options)
{
    if (!options->exhaustive) return options->cases;
    unsigned index_bits = options->bits * operation_arity(options->operation);
    return UINT64_C(1) << index_bits;
}

static uint64_t expected_case_count(
    uint64_t source_cases, uint64_t first_case, uint64_t stride)
{
    if (first_case >= source_cases) return 0;
    return UINT64_C(1) + (source_cases - UINT64_C(1) - first_case) / stride;
}

static uint32_t compact_mask(unsigned bits)
{
    return bits == 32 ? UINT32_MAX : (UINT32_C(1) << bits) - UINT32_C(1);
}

static uint32_t to_carrier(uint32_t compact, unsigned bits)
{
    return bits == 32 ? compact : compact << (32 - bits);
}

static bool from_carrier(uint32_t carrier, unsigned bits, uint32_t *compact)
{
    if (bits == 32) {
        *compact = carrier;
        return true;
    }
    unsigned shift = 32 - bits;
    uint32_t padding_mask = (UINT32_C(1) << shift) - UINT32_C(1);
    if ((carrier & padding_mask) != 0) {
        return false;
    }
    *compact = carrier >> shift;
    return true;
}

static posit_2_t px2(uint32_t compact, unsigned bits)
{
    posit_2_t value;
    value.v = to_carrier(compact, bits);
    return value;
}

static posit32_t p32(uint32_t compact)
{
    posit32_t value;
    value.v = compact;
    return value;
}

static uint32_t apply_px2(const struct options *options, const uint32_t *operands,
    bool *padding_ok)
{
    const unsigned bits = options->bits;
    posit_2_t a = px2(operands[0], bits);
    posit_2_t b = px2(operands[1], bits);
    posit_2_t c = px2(operands[2], bits);
    posit_2_t result;
    result.v = 0;

    switch (options->operation) {
    case OP_ADD: result = pX2_add(a, b, (int)bits); break;
    case OP_SUB: result = pX2_sub(a, b, (int)bits); break;
    case OP_MUL: result = pX2_mul(a, b, (int)bits); break;
    case OP_DIV: result = pX2_div(a, b, (int)bits); break;
    case OP_FMA: result = pX2_mulAdd(a, b, c, (int)bits); break;
    case OP_SQRT: result = pX2_sqrt(a, (int)bits); break;
    case OP_RINT: result = pX2_roundToInt(a, (int)bits); break;
    case OP_EQ: return pX2_eq(a, b) ? 1 : 0;
    case OP_LE: return pX2_le(a, b) ? 1 : 0;
    case OP_LT: return pX2_lt(a, b) ? 1 : 0;
    case OP_NONE:
        fail_invalid_operation(options->operation);
    }

    uint32_t compact = 0;
    *padding_ok = from_carrier(result.v, bits, &compact);
    return compact;
}

static uint32_t apply_p32(const struct options *options, const uint32_t *operands)
{
    posit32_t a = p32(operands[0]);
    posit32_t b = p32(operands[1]);
    posit32_t c = p32(operands[2]);

    switch (options->operation) {
    case OP_ADD: return p32_add(a, b).v;
    case OP_SUB: return p32_sub(a, b).v;
    case OP_MUL: return p32_mul(a, b).v;
    case OP_DIV: return p32_div(a, b).v;
    case OP_FMA: return p32_mulAdd(a, b, c).v;
    case OP_SQRT: return p32_sqrt(a).v;
    case OP_RINT: return p32_roundToInt(a).v;
    case OP_EQ: return p32_eq(a, b) ? 1 : 0;
    case OP_LE: return p32_le(a, b) ? 1 : 0;
    case OP_LT: return p32_lt(a, b) ? 1 : 0;
    case OP_NONE:
        fail_invalid_operation(options->operation);
    }
    fail_invalid_operation(options->operation);
    return 0;
}

static uint64_t splitmix64(uint64_t value)
{
    value += UINT64_C(0x9e3779b97f4a7c15);
    value = (value ^ (value >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
    value = (value ^ (value >> 27)) * UINT64_C(0x94d049bb133111eb);
    return value ^ (value >> 31);
}

static uint32_t edge_word(unsigned bits, uint64_t selector)
{
    const uint32_t mask = compact_mask(bits);
    const uint32_t nar = UINT32_C(1) << (bits - 1);
    const uint32_t one = UINT32_C(1) << (bits - 2);
    const uint32_t edges[] = {
        0, 1, 2, one - 1, one, one + 1, nar - 1, nar,
        nar + 1, mask - one, mask - 2, mask - 1, mask
    };
    return edges[selector % (sizeof(edges) / sizeof(edges[0]))] & mask;
}

static uint32_t sampled_word(const struct options *options, uint64_t case_id,
    unsigned lane)
{
    const uint32_t mask = compact_mask(options->bits);
    uint64_t source = splitmix64(options->seed ^ case_id ^
        (UINT64_C(0xd1b54a32d192ed03) * (lane + 1)));
    switch (case_id & 3) {
    case 0:
        return edge_word(options->bits, case_id / 4 + lane);
    case 1:
        if (lane == 0) return (uint32_t)source & mask;
        if (lane == 1) return (-(uint32_t)source) & mask;
        return edge_word(options->bits, source);
    case 2:
        if (lane == 1) return ((uint32_t)source + 1) & mask;
        return (uint32_t)source & mask;
    default:
        return (uint32_t)source & mask;
    }
}

static void exhaustive_operands(const struct options *options, uint64_t case_id,
    uint32_t *operands)
{
    uint64_t remaining = case_id;
    uint32_t mask = compact_mask(options->bits);
    for (unsigned lane = 0; lane < operation_arity(options->operation); ++lane) {
        operands[lane] = (uint32_t)remaining & mask;
        remaining >>= options->bits;
    }
}

static void sampled_operands(const struct options *options, uint64_t case_id,
    uint32_t *operands)
{
    for (unsigned lane = 0; lane < operation_arity(options->operation); ++lane) {
        operands[lane] = sampled_word(options, case_id, lane);
    }
}

static void write_u8(uint8_t value)
{
    if (fputc(value, stdout) == EOF) {
        perror("writing SoftPosit stream");
        exit(1);
    }
}

static void write_u32(uint32_t value)
{
    for (unsigned byte = 0; byte < 4; ++byte) {
        write_u8((uint8_t)(value >> (8 * byte)));
    }
}

static void write_u64(uint64_t value)
{
    for (unsigned byte = 0; byte < 8; ++byte) {
        write_u8((uint8_t)(value >> (8 * byte)));
    }
}

static void write_header(const struct options *options, uint64_t source_cases,
    uint64_t expected_cases)
{
    const uint8_t magic[] = { 0x53, 0x50, 0x58, 0x32 };
    if (fwrite(magic, sizeof(magic), 1, stdout) != 1) {
        perror("writing SoftPosit header");
        exit(1);
    }
    write_u8(2);
    write_u8(80);
    write_u8((uint8_t)options->bits);
    write_u8((uint8_t)options->operation);
    write_u8((uint8_t)options->family);
    write_u8((uint8_t)operation_arity(options->operation));
    write_u8((uint8_t)generation_mode(options));
    for (unsigned index = 0; index < 5; ++index) {
        write_u8(0);
    }
    write_u64(expected_cases);
    write_u64(options->shard_index);
    write_u64(options->shard_count);
    write_u64(source_cases);
    write_u64(options->seed);
    for (unsigned index = 0; index < 20; ++index) {
        write_u8(options->source_revision[index]);
    }
    for (unsigned index = 0; index < 4; ++index) {
        write_u8(0);
    }
}

static void emit_case(const struct options *options, uint64_t case_id,
    uint64_t *padding_errors)
{
    uint32_t operands[3] = { 0, 0, 0 };
    if (options->exhaustive) {
        exhaustive_operands(options, case_id, operands);
    } else {
        sampled_operands(options, case_id, operands);
    }

    bool padding_ok = true;
    uint32_t expected = options->family == FAMILY_P32
        ? apply_p32(options, operands)
        : apply_px2(options, operands, &padding_ok);
    if (!padding_ok) {
        ++*padding_errors;
        fprintf(stderr,
            "noncanonical SoftPosit padding: case=%" PRIu64
            " bits=%u operation=%s carrier result rejected\n",
            case_id, options->bits, operation_name(options->operation));
        exit(1);
    }

    write_u64(case_id);
    for (unsigned lane = 0; lane < operation_arity(options->operation); ++lane) {
        write_u32(operands[lane]);
    }
    write_u32(expected);
}

int main(int argc, char **argv)
{
    struct options options = parse_options(argc, argv);
    uint64_t source_cases = source_case_count(&options);
    uint64_t expected_cases = expected_case_count(
        source_cases, options.shard_index, options.shard_count);
    uint64_t emitted = 0;
    uint64_t padding_errors = 0;

    if (expected_cases == 0) {
        fprintf(stderr,
            "the selected shard contains no cases: first=%" PRIu64
            " stride=%" PRIu64 " source_cases=%" PRIu64 "\n",
            options.shard_index, options.shard_count, source_cases);
        return 2;
    }

    write_header(&options, source_cases, expected_cases);
    for (uint64_t case_id = options.shard_index; case_id < source_cases;) {
        emit_case(&options, case_id, &padding_errors);
        ++emitted;
        if (UINT64_MAX - case_id < options.shard_count) break;
        case_id += options.shard_count;
    }

    if (emitted != expected_cases) {
        fprintf(stderr,
            "internal case-count mismatch: emitted=%" PRIu64
            " expected=%" PRIu64 "\n",
            emitted, expected_cases);
        return 1;
    }

    if (fflush(stdout) != 0) {
        perror("flushing SoftPosit stream");
        return 1;
    }
    fprintf(stderr,
        "RESULT emitter=softposit family=%s bits=%u operation=%s mode=%s"
        " source_cases=%" PRIu64 " expected_cases=%" PRIu64
        " first_case=%" PRIu64 " stride=%" PRIu64 " seed=%" PRIu64
        " revision=%s cases=%" PRIu64 " padding_errors=%" PRIu64 "\n",
        options.family == FAMILY_P32 ? "p32" : "px2",
        options.bits, operation_name(options.operation),
        generation_mode_name(&options), source_cases, expected_cases,
        options.shard_index, options.shard_count, options.seed,
        options.source_revision_hex, emitted, padding_errors);
    return 0;
}
