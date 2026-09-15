#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
cd "$ROOT"

# shellcheck source=tests/lib/lake.sh
source "$ROOT/tests/lib/lake.sh"

floatlib_benchmark_lake build \
  FloatLibBenchmarks.Codegen.StaticLowBit:c \
  FloatLib.Floats.ExecFloat.Backends.TinyTable.Generic.Construction:c \
  FloatLib.Floats.Formats.OCP.MX.E2M1:c \
  FloatLib.Floats.Formats.OCP.MX.E2M3:c \
  FloatLib.Floats.Formats.OCP.MX.E3M2:c \
  FloatLib.Floats.Formats.OCP.FP8.E4M3FN:c \
  FloatLib.Floats.Formats.OCP.FP8.E5M2:c \
  FloatLib.Floats.Formats.FiniteOnly.E4M3FNUZ:c \
  FloatLib.Floats.Formats.FiniteOnly.E5M2FNUZ:c

generated_c="$(
  floatlib_build_path ir/FloatLibBenchmarks/Codegen/StaticLowBit.c
)"
if [[ ! -f "$generated_c" ]]; then
  printf 'missing generated C file: %s\n' "$generated_c" >&2
  exit 1
fi

prefix="lp_floatlibBenchmarks_FloatLibBenchmarks_Codegen_StaticLowBit"
tiny_table_c="$(
  floatlib_build_path \
    ir/FloatLib/Floats/ExecFloat/Backends/TinyTable/Generic/Construction.c
)"
tiny_table_prefix="lp_floatlib_FloatLib_Floats_ExecFloat_Backend_TinyTable"

extract_c_body() {
  local file="$1"
  local signature="$2"

  awk -v signature="$signature" '
    index($0, signature) == 1 && index($0, "{") > 0 {
      selected = 1
    }
    selected {
      print
      opens = $0
      closes = $0
      open_count = gsub(/\{/, "{", opens)
      close_count = gsub(/\}/, "}", closes)
      depth += open_count - close_count
      if (open_count > 0) {
        entered = 1
      }
      if (entered && depth == 0) {
        exit
      }
    }
  ' "$file"
}

extract_body() {
  local function_name="$1"

  extract_c_body "$generated_c" \
    "LEAN_EXPORT uint8_t ${prefix}_${function_name}("
}

count_fixed() {
  local text="$1"
  local needle="$2"

  awk -v needle="$needle" '
    {
      rest = $0
      while ((position = index(rest, needle)) > 0) {
        count += 1
        rest = substr(rest, position + length(needle))
      }
    }
    END {
      print count + 0
    }
  ' <<< "$text"
}

require_signature() {
  local function_name="$1"
  local parameters="$2"
  local expected="LEAN_EXPORT uint8_t ${prefix}_${function_name}(${parameters});"

  if ! grep -Fq "$expected" "$generated_c"; then
    printf 'missing native low-bit signature:\n%s\n' "$expected" >&2
    exit 1
  fi
}

check_direct_table() {
  local function_name="$1"
  local parameters="$2"
  local body

  require_signature "$function_name" "$parameters"
  body="$(extract_body "$function_name")"
  if [[ -z "$body" ]]; then
    printf 'missing generated body for %s\n' "$function_name" >&2
    exit 1
  fi
  if [[ "$(count_fixed "$body" 'lean_thunk_get_own')" -ne 1 ]]; then
    printf '%s did not compile to exactly one memoized-table read:\n%s\n' \
      "$function_name" "$body" >&2
    exit 1
  fi
  if [[ "$(count_fixed "$body" 'lean_byte_array_uget')" -ne 1 ]]; then
    printf '%s did not compile to exactly one direct byte-table lookup:\n%s\n' \
      "$function_name" "$body" >&2
    exit 1
  fi
  if grep -Eq \
      '\blean_apply_[0-9]+\b|\blean_uint8_(to_nat|of_nat)\b|\blean_(box|unbox)\b' \
      <<< "$body"; then
    printf '%s retained boxed or dynamically dispatched work:\n%s\n' \
      "$function_name" "$body" >&2
    exit 1
  fi
}

check_model_fma() {
  local function_name="$1"
  local body

  require_signature "$function_name" 'uint8_t, uint8_t, uint8_t'
  body="$(extract_body "$function_name")"
  if [[ -z "$body" ]]; then
    printf 'missing generated body for %s\n' "$function_name" >&2
    exit 1
  fi
  if grep -Eq '\blean_apply_[0-9]+\b|\blean_(box|unbox)\b' <<< "$body"; then
    printf '%s retained a runtime capability closure or boxed dictionary:\n%s\n' \
      "$function_name" "$body" >&2
    exit 1
  fi
}

check_lazy_constructor() {
  local arity_name="$1"
  local eager_name="$2"
  local function_name="${tiny_table_prefix}_lazy${arity_name}Total___redArg"
  local body

  body="$(extract_c_body "$tiny_table_c" \
    "LEAN_EXPORT lean_object* ${function_name}(")"
  if [[ -z "$body" ]]; then
    printf 'missing generated lazy-table constructor: %s\n' "$function_name" >&2
    exit 1
  fi
  if [[ "$(count_fixed "$body" 'lean_mk_thunk')" -ne 1 ]]; then
    printf '%s did not compile to exactly one runtime thunk:\n%s\n' \
      "$function_name" "$body" >&2
    exit 1
  fi
  if grep -Fq "${tiny_table_prefix}_${eager_name}Total(" <<< "$body"; then
    printf '%s eagerly generated its table instead of delaying it:\n%s\n' \
      "$function_name" "$body" >&2
    exit 1
  fi
}

check_lazy_format_initialization() {
  local module_name="$1"
  local expected_tables="$2"
  local module_path="${module_name//./\/}"
  local c_file
  c_file="$(
    floatlib_build_path "ir/${module_path}.c"
  )"
  local init_name
  local body
  local table_count

  init_name="runtime_initialize_floatlib_${module_name//./_}"
  if [[ ! -f "$c_file" ]]; then
    printf 'missing generated low-bit format C file: %s\n' "$c_file" >&2
    exit 1
  fi
  body="$(extract_c_body "$c_file" "LEAN_EXPORT lean_object* ${init_name}(")"
  if [[ -z "$body" ]]; then
    printf 'missing generated runtime initializer: %s\n' "$init_name" >&2
    exit 1
  fi
  if grep -Eq \
      'lean_thunk_get(_own)?|TinyTable_(binaryTotal|unaryTotal|ternaryTotal)(___redArg)?\(' \
      <<< "$body"; then
    printf '%s forced or generated a table during module initialization:\n%s\n' \
      "$module_name" "$body" >&2
    exit 1
  fi
  table_count="$(
    grep -Ec 'Table = _init_.*Table\(\);' <<< "$body" || true
  )"
  if [[ "$table_count" -ne "$expected_tables" ]]; then
    printf '%s initialized %s table handles; expected %s:\n%s\n' \
      "$module_name" "$table_count" "$expected_tables" "$body" >&2
    exit 1
  fi
  if grep -Eq \
      'TinyTable_(binaryTotal|unaryTotal|ternaryTotal)(___redArg)?\(' \
      "$c_file"; then
    printf '%s retained an eager table generator outside a delayed thunk\n' \
      "$module_name" >&2
    exit 1
  fi
}

for family in e2m1; do
  for operation in Add Sub Mul Div; do
    check_direct_table "${family}${operation}" 'uint8_t, uint8_t'
  done
  check_direct_table "${family}Sqrt" 'uint8_t'
  check_direct_table "${family}Fma" 'uint8_t, uint8_t, uint8_t'
done

for family in e2m3 e3m2; do
  for operation in Add Sub Mul Div; do
    check_direct_table "${family}${operation}" 'uint8_t, uint8_t'
  done
  check_direct_table "${family}Sqrt" 'uint8_t'
  check_model_fma "${family}Fma"
  check_direct_table "ThroughputPlan_${family}Fma" 'uint8_t, uint8_t, uint8_t'
done

for family in e4m3fn e5m2 e4m3fnuz e5m2fnuz; do
  for operation in Add Sub Mul Div; do
    check_direct_table "${family}${operation}" 'uint8_t, uint8_t'
  done
  check_direct_table "${family}Sqrt" 'uint8_t'
  check_model_fma "${family}Fma"
done

if [[ ! -f "$tiny_table_c" ]]; then
  printf 'missing generated tiny-table C file: %s\n' "$tiny_table_c" >&2
  exit 1
fi

check_lazy_constructor Binary binary
check_lazy_constructor Unary unary
check_lazy_constructor Ternary ternary

check_lazy_format_initialization FloatLib.Floats.Formats.OCP.MX.E2M1 6
check_lazy_format_initialization FloatLib.Floats.Formats.OCP.MX.E2M3 6
check_lazy_format_initialization FloatLib.Floats.Formats.OCP.MX.E3M2 6
check_lazy_format_initialization FloatLib.Floats.Formats.OCP.FP8.E4M3FN 5
check_lazy_format_initialization FloatLib.Floats.Formats.OCP.FP8.E5M2 5
check_lazy_format_initialization FloatLib.Floats.Formats.FiniteOnly.E4M3FNUZ 5
check_lazy_format_initialization FloatLib.Floats.Formats.FiniteOnly.E5M2FNUZ 5

printf '%s\n' \
  'Static low-bit code generation passed: generic lazy tables, native bytes, no eager format initialization, and no capability closures.'
