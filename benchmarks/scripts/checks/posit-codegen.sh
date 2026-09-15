#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
cd "$ROOT"

# shellcheck source=tests/lib/lake.sh
source "$ROOT/tests/lib/lake.sh"

floatlib_benchmark_lake build FloatLibBenchmarks.Codegen.Posit

generated_c="$(floatlib_build_path ir/FloatLibBenchmarks/Codegen/Posit.c)"
if [[ ! -f "$generated_c" ]]; then
  printf 'missing generated Posit benchmark C file: %s\n' "$generated_c" >&2
  exit 1
fi

# The public probes can look direct while an out-of-line raw kernel still loads conversion
# closures from a carrier record. Inspect every fixed-word implementation boundary as well.
raw_carriers=(Byte Word16 Word32 Word64)
for raw_carrier in "${raw_carriers[@]}"; do
  raw_c="$(floatlib_build_path \
    "ir/FloatLib/Floats/Formats/Posit/Configured/Backend/FixedWords/${raw_carrier}/Raw.c")"
  if [[ ! -f "$raw_c" ]]; then
    printf 'missing generated fixed-word Posit C file: %s\n' "$raw_c" >&2
    exit 1
  fi
  if grep -Eq 'FixedWords_uint(8|16|32|64)Carrier|lean_apply_[0-9]+' "$raw_c"; then
    printf '%s contains a runtime carrier or indirect conversion call\n' "$raw_c" >&2
    exit 1
  fi
done

prefix="lp_floatlibBenchmarks_FloatLibBenchmarks_Codegen_Posit"

# These widths cover every public storage tier, both sides of the two-limb
# boundary, and both ends of the arbitrary-width path.
widths=(2 8 16 32 36 37 38 64 65 128 129 256 4096)
operations=(Add Sub Mul Div Sqrt Fma)

expected_functions=()
for width in "${widths[@]}"; do
  for operation in "${operations[@]}"; do
    expected_functions+=("p${width}${operation}")
  done
done

awk_program="$(
  printf '%s\n' '
    BEGIN {
      expected_count = split(expected_names, names, " ")
      for (i = 1; i <= expected_count; i++) {
        expected[names[i]] = 1
      }
      planning_forbidden = "List_foldl|considerCertified|selectCertified|lean_mk_thunk|" \
        "lean_thunk_get(_own)?"
    }

    index($0, "LEAN_EXPORT ") == 1 &&
        index($0, "'"$prefix"'_p") > 0 &&
        index($0, "{") > 0 {
      name = $0
      sub(/^.*_Posit_/, "", name)
      sub(/\(.*/, "", name)

      if (name in expected) {
        selected = 1
        seen[name] = 1
        body_lines = 0
        saw_static_tag = 0
        saw_static_resource = 0
        depth = 0
        entered = 0
      }
    }

    selected {
      body_lines += 1
      if ($0 ~ planning_forbidden) {
        printf "%s contains planning or thunk work in its hot body:\n%s\n",
          name, $0 > "/dev/stderr"
        failed = 1
      }
      if ($0 ~ /lean_apply_[123]/) {
          printf "%s contains an indirect capability call:\n%s\n",
          name, $0 > "/dev/stderr"
        failed = 1
      }
      if (name ~ /^p(2|8|16|32|36|37|38|64)/ &&
          $0 ~ /lean_(box|unbox)/) {
        printf "%s boxes a fixed-word operand or result:\n%s\n",
          name, $0 > "/dev/stderr"
        failed = 1
      }
      if ($0 ~ /lean_uint8_once/) {
        saw_static_tag = 1
      }
      if ($0 ~ /lean_obj_once/) {
        saw_static_resource = 1
      }

      opens = $0
      closes = $0
      open_count = gsub(/\{/, "{", opens)
      close_count = gsub(/\}/, "}", closes)
      depth += open_count - close_count
      if (open_count > 0) {
        entered = 1
      }
      if (entered && depth == 0) {
        if (name ~ /^p(2|8)(Add|Sub|Mul|Div|Sqrt|Fma)$/ &&
            body_lines > 40) {
          printf "%s expands byte planning into its hot body (%d lines)\n",
            name, body_lines > "/dev/stderr"
          failed = 1
        }
        if (name ~ /^p(2|8)(Add|Sub|Mul|Div|Sqrt|Fma)$/ &&
            !saw_static_tag) {
          printf "%s does not use a static byte-kernel tag\n",
            name > "/dev/stderr"
          failed = 1
        }
        if (name ~ /^p(2|8)(Add|Sub|Mul|Div|Sqrt|Fma)$/ &&
            !saw_static_resource) {
          printf "%s does not use a static certified table resource\n",
            name > "/dev/stderr"
          failed = 1
        }
        selected = 0
      }
    }

    END {
      for (name in expected) {
        if (!(name in seen)) {
          printf "missing generated Posit hot-loop body: %s\n", name > "/dev/stderr"
          failed = 1
        }
      }
      exit failed
    }
  '
)"

awk -v expected_names="${expected_functions[*]}" "$awk_program" "$generated_c"

# A fresh lazy table object in the dispatcher gives every call a fresh thunk, defeating
# memoization even though the visible hot body remains compact. Require the closed p2/p8 probes
# to construct each operation's certified table object in a static initializer.
for width in 2 8; do
  for operation in "${operations[@]}"; do
    lower_operation="${operation,,}"
    initializer_prefix="_init_${prefix}_p${width}${operation}___closed__"
    constructor="ByteTable_${lower_operation}Table___redArg"
    if ! awk -v initializer_prefix="$initializer_prefix" \
        -v constructor="$constructor" '
      index($0, "static lean_object* " initializer_prefix) == 1 {
        selected = 1
        depth = 0
        entered = 0
      }
      selected {
        if (index($0, constructor) > 0) {
          matched = 1
        }
        opens = $0
        closes = $0
        open_count = gsub(/\{/, "{", opens)
        close_count = gsub(/\}/, "}", closes)
        depth += open_count - close_count
        if (open_count > 0) {
          entered = 1
        }
        if (entered && depth == 0) {
          selected = 0
        }
      }
      END {
        exit !matched
      }
    ' "$generated_c"; then
      printf 'Posit%s %s does not hoist its certified table resource\n' \
        "$width" "$lower_operation" >&2
      exit 1
    fi
  done
done

if grep -q 'lean_apply_[123]' "$generated_c"; then
  printf '%s\n' 'generated Posit probes contain an indirect closure invocation' >&2
  exit 1
fi

byte_operations=(add sub mul div sqrt fma)
for operation in "${byte_operations[@]}"; do
  if ! grep -q "ByteDispatch_${operation}Selected___redArg" "$generated_c"; then
    printf 'missing first-order byte tag dispatcher for %s\n' "$operation" >&2
    exit 1
  fi
done

fixed_words=(16 32)
fixed_word_operations=(add sub mul div sqrt fma)
for width in "${fixed_words[@]}"; do
  for operation in "${fixed_word_operations[@]}"; do
    if ! grep -q "Backend_Word${width}_${operation}Raw___redArg" "$generated_c"; then
      printf 'missing fixed UInt%s raw backend call for %s\n' "$width" "$operation" >&2
      exit 1
    fi
  done
done

generated_body_contains() {
  local function_name="${1:?generated function name is required}"
  local callee="${2:?generated callee name is required}"
  awk -v function_name="$function_name" -v callee="$callee" '
    index($0, "LEAN_EXPORT ") == 1 &&
        index($0, function_name "(") > 0 &&
        index($0, "{") > 0 {
      selected = 1
      depth = 0
      entered = 0
    }
    selected {
      if (index($0, callee) > 0) {
        matched = 1
      }
      opens = $0
      closes = $0
      open_count = gsub(/\{/, "{", opens)
      close_count = gsub(/\}/, "}", closes)
      depth += open_count - close_count
      if (open_count > 0) {
        entered = 1
      }
      if (entered && depth == 0) {
        selected = 0
      }
    }
    END {
      exit !matched
    }
  ' "$generated_c"
}

native_limb_prefix="Backend_storedNativeLimb"
for width in 65 128; do
  for operation in Add Sub; do
    if ! generated_body_contains \
        "${prefix}_p${width}${operation}" \
        "${native_limb_prefix}${operation}___redArg"; then
      printf 'Posit%s %s does not call the native two-limb backend directly\n' \
        "$width" "${operation,,}" >&2
      exit 1
    fi
  done
done

dyadic_prefix="Backend_dyadic"
for width in 129 256 4096; do
  for operation in Add Sub; do
    if ! generated_body_contains \
        "${prefix}_p${width}${operation}" \
        "${dyadic_prefix}${operation}___redArg"; then
      printf 'Posit%s %s does not call the arbitrary-width backend directly\n' \
        "$width" "${operation,,}" >&2
      exit 1
    fi
  done
done

word64_prefix="Backend_Word64"
for width in 36 37 38 64; do
  for operation in Add Sub Mul Div Sqrt Fma; do
    lower_operation="${operation,,}"
    if ! generated_body_contains \
        "${prefix}_p${width}${operation}" \
        "${word64_prefix}_${lower_operation}Raw___redArg"; then
      printf 'Posit%s %s does not call the unified UInt64 backend directly\n' \
        "$width" "$lower_operation" >&2
      exit 1
    fi
  done
done

for width in 16 32 36 37 38 64; do
  case "$width" in
    16) expected_return="uint16_t" ;;
    32) expected_return="uint32_t" ;;
    *) expected_return="uint64_t" ;;
  esac
  for operation in Add Sub Mul Div Sqrt Fma; do
    if ! grep -q "LEAN_EXPORT ${expected_return} ${prefix}_p${width}${operation}(" \
        "$generated_c"; then
      printf 'public Posit%s %s does not expose the native %s ABI\n' \
        "$width" "$operation" "$expected_return" >&2
      exit 1
    fi
  done
done

for width in 2 8; do
  for operation in Add Sub Mul Div Sqrt Fma; do
    if ! grep -q "LEAN_EXPORT uint8_t ${prefix}_p${width}${operation}(" \
        "$generated_c"; then
      printf 'public Posit%s %s does not expose the native uint8_t ABI\n' \
        "$width" "$operation" >&2
      exit 1
    fi
  done
done

printf '%s\n' \
  'Posit code generation passed: byte resources are static and fixed-word calls use direct unified kernels.'
