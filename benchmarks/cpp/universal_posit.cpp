/*
 * Copyright (c) 2026 FloatLib
 * Released under MIT license as described in the file LICENSE.
 *
 * We use Stillwater Universal as the independent posit implementation because
 * it supports the wide static posit types used in this comparison. The runner
 * pins the exact source revision instead of benchmarking whatever happens to
 * be on the machine:
 * https://github.com/stillwater-sc/universal
 */

#include <array>
#include <cerrno>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <string_view>
#include <vector>

#include <universal/number/posit/posit.hpp>

#ifndef FLOATLIB_POSIT_WIDTH
#error "Compile with -DFLOATLIB_POSIT_WIDTH=<static width>."
#endif

#ifndef FLOATLIB_UNIVERSAL_REVISION
#define FLOATLIB_UNIVERSAL_REVISION "unknown"
#endif

namespace {

constexpr unsigned kWidth = FLOATLIB_POSIT_WIDTH;
constexpr std::size_t kInputCount = 16;
using Posit = sw::universal::posit<kWidth, 2, std::uint64_t>;

#if defined(__GNUC__) || defined(__clang__)
#define FLOATLIB_NOINLINE __attribute__((noinline))
#else
#define FLOATLIB_NOINLINE
#endif

struct Vector {
  Posit x;
  Posit y;
  Posit z;
  Posit sqrt_input;
  std::array<std::string, 6> expected;
};

volatile std::uint64_t warmup_sink = 0;

std::vector<std::string> split_csv(const std::string& line) {
  std::vector<std::string> fields;
  std::size_t begin = 0;
  while (true) {
    const std::size_t comma = line.find(',', begin);
    fields.emplace_back(line.substr(begin, comma - begin));
    if (comma == std::string::npos) {
      return fields;
    }
    begin = comma + 1;
  }
}

std::size_t positive_size(const char* name, const char* text) {
  if (text == nullptr || *text == '\0') {
    throw std::runtime_error(std::string(name) + " is required");
  }
  char* end = nullptr;
  errno = 0;
  const unsigned long long value = std::strtoull(text, &end, 10);
  if (errno != 0 || end == text || *end != '\0' || value == 0) {
    throw std::runtime_error(
        std::string(name) + " must be a positive integer: " + text);
  }
  return static_cast<std::size_t>(value);
}

std::size_t positive_size_env(const char* name, std::size_t fallback) {
  const char* text = std::getenv(name);
  return text == nullptr || *text == '\0'
             ? fallback
             : positive_size(name, text);
}

Posit from_binary(std::string_view code) {
  if (code.size() != kWidth) {
    throw std::runtime_error(
        "expected " + std::to_string(kWidth) +
        " encoded bits, received " + std::to_string(code.size()));
  }
  Posit result;
  result.setzero();
  for (std::size_t index = 0; index < code.size(); ++index) {
    const char digit = code[code.size() - 1 - index];
    if (digit == '1') {
      result.setbit(static_cast<unsigned>(index));
    } else if (digit != '0') {
      throw std::runtime_error("non-binary digit in interoperability vector");
    }
  }
  return result;
}

std::string to_binary(const Posit& value) {
  const auto raw = value.bits();
  std::string result(kWidth, '0');
  for (unsigned index = 0; index < kWidth; ++index) {
    if (raw.at(index)) {
      result[kWidth - 1 - index] = '1';
    }
  }
  return result;
}

std::array<Vector, kInputCount> read_vectors(const char* path) {
  if (path == nullptr || *path == '\0') {
    throw std::runtime_error("POSIT_VECTOR_FILE is required");
  }
  std::ifstream stream(path);
  if (!stream) {
    throw std::runtime_error(std::string("cannot open vector file: ") + path);
  }
  std::string line;
  if (!std::getline(stream, line)) {
    throw std::runtime_error("interoperability vector file is empty");
  }
  std::array<Vector, kInputCount> vectors;
  std::array<bool, kInputCount> seen{};
  while (std::getline(stream, line)) {
    const auto fields = split_csv(line);
    if (fields.size() != 12) {
      throw std::runtime_error("interoperability vector row must have 12 fields");
    }
    if (positive_size("totalBits", fields[0].c_str()) != kWidth) {
      throw std::runtime_error("interoperability vector width mismatch");
    }
    char* end = nullptr;
    errno = 0;
    const unsigned long parsed_index =
        std::strtoul(fields[1].c_str(), &end, 10);
    if (errno != 0 || end == fields[1].c_str() || *end != '\0' ||
        parsed_index >= kInputCount) {
      throw std::runtime_error("invalid interoperability vector index");
    }
    if (seen[parsed_index]) {
      throw std::runtime_error("duplicate interoperability vector index");
    }
    seen[parsed_index] = true;
    Vector& vector = vectors[parsed_index];
    vector.x = from_binary(fields[2]);
    vector.y = from_binary(fields[3]);
    vector.z = from_binary(fields[4]);
    vector.sqrt_input = from_binary(fields[5]);
    for (std::size_t operation = 0; operation < vector.expected.size();
         ++operation) {
      vector.expected[operation] = fields[6 + operation];
    }
  }
  for (bool present : seen) {
    if (!present) {
      throw std::runtime_error("interoperability vector set is incomplete");
    }
  }
  return vectors;
}

enum class Operation {
  add,
  sub,
  mul,
  div,
  sqrt,
  fma,
};

Operation parse_operation(const char* text) {
  if (text == nullptr) {
    throw std::runtime_error("FORMAT_COMPARE_OPERATION is required");
  }
  if (std::string_view(text) == "add") return Operation::add;
  if (std::string_view(text) == "sub") return Operation::sub;
  if (std::string_view(text) == "mul") return Operation::mul;
  if (std::string_view(text) == "div") return Operation::div;
  if (std::string_view(text) == "sqrt") return Operation::sqrt;
  if (std::string_view(text) == "fma") return Operation::fma;
  throw std::runtime_error(
      std::string("unsupported FORMAT_COMPARE_OPERATION: ") + text);
}

std::string_view operation_name(Operation operation) {
  switch (operation) {
    case Operation::add: return "add";
    case Operation::sub: return "sub";
    case Operation::mul: return "mul";
    case Operation::div: return "div";
    case Operation::sqrt: return "sqrt";
    case Operation::fma: return "fma";
  }
  throw std::runtime_error("invalid operation");
}

std::string backend_name(Operation operation) {
  if (operation == Operation::sqrt) {
#if POSIT_NATIVE_SQRT
    return "Universal " FLOATLIB_UNIVERSAL_REVISION
           " native posit square root";
#else
    /*
     * We label this path honestly. At the pinned revision, Universal's default
     * generic square root converts through binary64 and calls std::sqrt. It is
     * still a useful external result. We report it as hardware-assisted rather
     * than comparing it with FloatLib's certified software square root.
     */
    return "Universal " FLOATLIB_UNIVERSAL_REVISION
           " posit-to-binary64 hardware sqrt";
#endif
  }
  return "Universal " FLOATLIB_UNIVERSAL_REVISION " generic posit<" +
         std::to_string(kWidth) + "; es=2>";
}

std::string_view execution_class(Operation operation) {
  return operation == Operation::sqrt
             ? "hardware-assisted-external"
             : "external-software";
}

std::size_t operation_index(Operation operation) {
  return static_cast<std::size_t>(operation);
}

Posit evaluate(Operation operation, const Vector& vector) {
  switch (operation) {
    case Operation::add: return vector.x + vector.y;
    case Operation::sub: return vector.x - vector.y;
    case Operation::mul: return vector.x * vector.y;
    case Operation::div: return vector.x / vector.y;
    case Operation::sqrt: return sw::universal::sqrt(vector.sqrt_input);
    case Operation::fma:
      return sw::universal::fma(vector.x, vector.y, vector.z);
  }
  throw std::runtime_error("invalid operation");
}

void validate(
    Operation operation, const std::array<Vector, kInputCount>& vectors) {
  for (std::size_t index = 0; index < vectors.size(); ++index) {
    const std::string actual = to_binary(evaluate(operation, vectors[index]));
    const std::string& expected =
        vectors[index].expected[operation_index(operation)];
    if (actual != expected) {
      throw std::runtime_error(
          "Stillwater Universal disagrees with FloatLib for posit" +
          std::to_string(kWidth) + " " +
          std::string(operation_name(operation)) + " at vector " +
          std::to_string(index) + ": expected " + expected +
          ", received " + actual);
    }
  }
}

inline std::uint64_t mix_sink(std::uint64_t sink, const Posit& value) {
  return (sink ^ value.encoding()) * UINT64_C(1099511628211);
}

inline std::uint64_t mix_fixture_trace(
    std::uint64_t trace, std::size_t index) {
  return (trace ^ static_cast<std::uint64_t>(index)) *
      UINT64_C(1099511628211);
}

struct RunResult {
  std::uint64_t sink;
  std::uint64_t fixture_trace;
};

inline std::size_t dependent_index(std::uint64_t sink) {
  std::uint64_t folded = sink ^ (sink >> 32);
  folded ^= folded >> 16;
  return static_cast<std::size_t>(folded) & (kInputCount - 1);
}

FLOATLIB_NOINLINE RunResult run_add(
    std::size_t count, const std::array<Vector, kInputCount>& vectors) {
  std::uint64_t sink = UINT64_C(14695981039346656037);
  std::uint64_t fixture_trace = UINT64_C(14695981039346656037);
  while (count != 0) {
    --count;
    const std::size_t index = dependent_index(sink);
    fixture_trace = mix_fixture_trace(fixture_trace, index);
    sink = mix_sink(sink, vectors[index].x + vectors[index].y);
  }
  return {sink, fixture_trace};
}

FLOATLIB_NOINLINE RunResult run_sub(
    std::size_t count, const std::array<Vector, kInputCount>& vectors) {
  std::uint64_t sink = UINT64_C(14695981039346656037);
  std::uint64_t fixture_trace = UINT64_C(14695981039346656037);
  while (count != 0) {
    --count;
    const std::size_t index = dependent_index(sink);
    fixture_trace = mix_fixture_trace(fixture_trace, index);
    sink = mix_sink(sink, vectors[index].x - vectors[index].y);
  }
  return {sink, fixture_trace};
}

FLOATLIB_NOINLINE RunResult run_mul(
    std::size_t count, const std::array<Vector, kInputCount>& vectors) {
  std::uint64_t sink = UINT64_C(14695981039346656037);
  std::uint64_t fixture_trace = UINT64_C(14695981039346656037);
  while (count != 0) {
    --count;
    const std::size_t index = dependent_index(sink);
    fixture_trace = mix_fixture_trace(fixture_trace, index);
    sink = mix_sink(sink, vectors[index].x * vectors[index].y);
  }
  return {sink, fixture_trace};
}

FLOATLIB_NOINLINE RunResult run_div(
    std::size_t count, const std::array<Vector, kInputCount>& vectors) {
  std::uint64_t sink = UINT64_C(14695981039346656037);
  std::uint64_t fixture_trace = UINT64_C(14695981039346656037);
  while (count != 0) {
    --count;
    const std::size_t index = dependent_index(sink);
    fixture_trace = mix_fixture_trace(fixture_trace, index);
    sink = mix_sink(sink, vectors[index].x / vectors[index].y);
  }
  return {sink, fixture_trace};
}

FLOATLIB_NOINLINE RunResult run_sqrt(
    std::size_t count, const std::array<Vector, kInputCount>& vectors) {
  std::uint64_t sink = UINT64_C(14695981039346656037);
  std::uint64_t fixture_trace = UINT64_C(14695981039346656037);
  while (count != 0) {
    --count;
    const std::size_t index = dependent_index(sink);
    fixture_trace = mix_fixture_trace(fixture_trace, index);
    sink = mix_sink(sink, sw::universal::sqrt(vectors[index].sqrt_input));
  }
  return {sink, fixture_trace};
}

FLOATLIB_NOINLINE RunResult run_fma(
    std::size_t count, const std::array<Vector, kInputCount>& vectors) {
  std::uint64_t sink = UINT64_C(14695981039346656037);
  std::uint64_t fixture_trace = UINT64_C(14695981039346656037);
  while (count != 0) {
    --count;
    const std::size_t index = dependent_index(sink);
    fixture_trace = mix_fixture_trace(fixture_trace, index);
    sink = mix_sink(
        sink,
        sw::universal::fma(
            vectors[index].x, vectors[index].y, vectors[index].z));
  }
  return {sink, fixture_trace};
}

RunResult run(
    Operation operation, std::size_t count,
    const std::array<Vector, kInputCount>& vectors) {
  switch (operation) {
    case Operation::add: return run_add(count, vectors);
    case Operation::sub: return run_sub(count, vectors);
    case Operation::mul: return run_mul(count, vectors);
    case Operation::div: return run_div(count, vectors);
    case Operation::sqrt: return run_sqrt(count, vectors);
    case Operation::fma: return run_fma(count, vectors);
  }
  throw std::runtime_error("invalid operation");
}

}  // namespace

int main() {
  try {
    const char* selected_width = std::getenv("FORMAT_COMPARE_WIDTH");
    if (selected_width != nullptr &&
        positive_size("FORMAT_COMPARE_WIDTH", selected_width) != kWidth) {
      throw std::runtime_error("runner width does not match FORMAT_COMPARE_WIDTH");
    }
    const Operation operation =
        parse_operation(std::getenv("FORMAT_COMPARE_OPERATION"));
    const auto vectors = read_vectors(std::getenv("POSIT_VECTOR_FILE"));
    validate(operation, vectors);
    const std::size_t warmup =
        positive_size_env("FORMAT_COMPARE_WARMUP_ITERATIONS", 64);
    const std::size_t iterations =
        positive_size_env("FORMAT_COMPARE_ITERATIONS", 1000);
    warmup_sink = run(operation, warmup, vectors).sink;
    const auto start = std::chrono::steady_clock::now();
    const RunResult result = run(operation, iterations, vectors);
    const auto stop = std::chrono::steady_clock::now();
    const auto elapsed =
        std::chrono::duration_cast<std::chrono::nanoseconds>(stop - start)
            .count();
    std::cout
        << "implementation,family,format,totalBits,operation,executionClass,"
           "backend,measurementMethod,iterations,totalNanos,sink,"
           "fixtureTraceDigest,agreementIterations,agreementSink,"
           "agreementFixtureTraceDigest\n"
        << "Stillwater Universal,posit-external,posit" << kWidth
        << "-es2," << kWidth << ',' << operation_name(operation)
        << ',' << execution_class(operation) << ',' << backend_name(operation)
        << ','
        << "result-dependent-fixture-chain,"
        << iterations << ','
        << elapsed << ',' << result.sink << ',' << result.fixture_trace
        << ",0,0,0\n";
    return EXIT_SUCCESS;
  } catch (const std::exception& error) {
    std::cerr << error.what() << '\n';
    return EXIT_FAILURE;
  }
}
