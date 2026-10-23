#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
cd "$ROOT"

# shellcheck source=tests/lib/lake.sh
source "$ROOT/tests/lib/lake.sh"

floatlib_benchmark_lake build FloatLibBenchmarks.Codegen.ConfiguredBinary

generated_c="$(
  floatlib_build_path ir/FloatLibBenchmarks/Codegen/ConfiguredBinary.c
)"
if [[ ! -f "$generated_c" ]]; then
  printf 'missing generated configured-binary C file: %s\n' "$generated_c" >&2
  exit 1
fi

unchecked_fpu_c="$(
  floatlib_build_path \
    ir/FloatLib/Floats/Formats/BinaryInterchange/Configured/NativeFPU/Unchecked.c
)"
if [[ ! -f "$unchecked_fpu_c" ]]; then
  printf 'missing generated NativeFPU.Unchecked C file: %s\n' "$unchecked_fpu_c" >&2
  exit 1
fi

prefix="lp_floatlibBenchmarks_FloatLibBenchmarks_Codegen_ConfiguredBinary"
operations=(Add Sub Mul Div Sqrt Fma)
unchecked_operations=(Add Sub Mul Div Sqrt)

for width in 32 64; do
  c_type="uint${width}_t"
  for operation in "${operations[@]}"; do
    name="${prefix}_binary${width}${operation}"
    case "$operation" in
      Sqrt)
        signature="LEAN_EXPORT ${c_type} ${name}(${c_type});"
        ;;
      Fma)
        signature="LEAN_EXPORT ${c_type} ${name}(${c_type}, ${c_type}, ${c_type});"
        ;;
      *)
        signature="LEAN_EXPORT ${c_type} ${name}(${c_type}, ${c_type});"
        ;;
    esac
    if ! grep -Fq "$signature" "$generated_c"; then
      printf 'missing native configured-binary signature:\n%s\n' "$signature" >&2
      exit 1
    fi
  done

  for operation in "${unchecked_operations[@]}"; do
    name="${prefix}_unchecked${width}${operation}"
    if [[ "$operation" == "Sqrt" ]]; then
      signature="LEAN_EXPORT ${c_type} ${name}(${c_type});"
    else
      signature="LEAN_EXPORT ${c_type} ${name}(${c_type}, ${c_type});"
    fi
    if ! grep -Fq "$signature" "$generated_c"; then
      printf 'missing explicit unchecked host signature:\n%s\n' "$signature" >&2
      exit 1
    fi
  done
done

# Inspect only the native entry points, not the boxed C-ABI wrappers emitted for Lean callers.
# A planner call, capability projection, closure application, or operand box here would mean that
# the ordinary parameterized user spelling no longer has a first-order hot path.
public_names=()
unchecked_names=()
for width in 32 64; do
  for operation in "${operations[@]}"; do
    public_names+=("binary${width}${operation}")
  done
  for operation in "${unchecked_operations[@]}"; do
    unchecked_names+=("unchecked${width}${operation}")
  done
done
expected_names=("${public_names[@]}" "${unchecked_names[@]}")

awk -v expected_names="${expected_names[*]}" -v public_names="${public_names[*]}" \
    -v prefix="$prefix" '
  BEGIN {
    expected_count = split(expected_names, names, " ")
    for (i = 1; i <= expected_count; i++) {
      expected[names[i]] = 1
    }
    public_count = split(public_names, names, " ")
    for (i = 1; i <= public_count; i++) {
      public_entry[names[i]] = 1
    }
    forbidden = "lean_apply_[0-9]+|lean_(box|unbox)|selectCertified|" \
      "considerCertified|lean_mk_thunk|lean_thunk_get(_own)?"
    host = "lean_float32_(add|sub|mul|div)|sqrtf\\(|" \
      "lean_float_(add|sub|mul|div)|(^|[^A-Za-z0-9_])sqrt\\(|NativeFPU.*Unchecked"
  }

  index($0, "LEAN_EXPORT ") == 1 && index($0, prefix "_") > 0 &&
      index($0, "___boxed") == 0 && index($0, "{") > 0 {
    name = $0
    sub(/^.*_ConfiguredBinary_/, "", name)
    sub(/\(.*/, "", name)
    if (name in expected) {
      selected = 1
      seen[name] = 1
      depth = 0
      entered = 0
    }
  }

  selected {
    if ($0 ~ forbidden) {
      printf "%s retained generic dispatch or boxing in its native body:\n%s\n",
        name, $0 > "/dev/stderr"
      failed = 1
    }
    if ((name in public_entry) && $0 ~ host) {
      printf "%s reached an unchecked host primitive from certified dispatch:\n%s\n",
        name, $0 > "/dev/stderr"
      failed = 1
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
    for (name in expected) {
      if (!(name in seen)) {
        printf "missing generated configured-binary body: %s\n", name > "/dev/stderr"
        failed = 1
      }
    }
    exit failed
  }
' "$generated_c"

# The explicit opt-in surface must retain Lean's five host primitives for each width. Search both
# the probe and imported runtime C because `@[always_inline]` may place a body in either unit.
required_callees=(
  lean_float32_add
  lean_float32_sub
  lean_float32_mul
  lean_float32_div
  sqrtf
  lean_float_add
  lean_float_sub
  lean_float_mul
  lean_float_div
  'sqrt('
)
for callee in "${required_callees[@]}"; do
  if ! grep -Fq "$callee" "$generated_c" "$unchecked_fpu_c"; then
    printf 'explicit NativeFPU.Unchecked probe lost expected host primitive: %s\n' \
      "$callee" >&2
    exit 1
  fi
done

# The configured selectors: every default spelling compiles to exactly the generic operation's
# code (after renaming the probe and its local variables), and the directed and status forms reach
# the descriptor-model kernels without planner or thunk calls.
python3 - "$generated_c" "$prefix" <<'PY'
import re
import sys

path, prefix = sys.argv[1], sys.argv[2]
text = open(path, encoding="utf-8").read()
functions = {}
for match in re.finditer(r"^(?:LEAN_EXPORT |static )[^\n;{]*? (\w+)\([^;{]*\)\{$", text, re.M):
    depth, index = 1, match.end()
    while depth:
        index = min(i for i in (text.find("{", index), text.find("}", index)) if i >= 0)
        depth += 1 if text[index] == "{" else -1
        index += 1
    functions[match.group(1)] = text[match.end():index]


def name_pattern(probe):
    return re.compile(re.escape("ConfiguredBinary_" + probe) + r"(?![A-Za-z0-9])")


def normal(body, *probes):
    for probe in probes:
        body = name_pattern(probe).sub("ConfiguredBinary_PROBE", body)
    seen = {}
    return re.sub(r"\bv_\w*?_[0-9]+_\b",
                  lambda m: seen.setdefault(m.group(0), "v%d" % len(seen)), body)


def entry(probe):
    name = prefix + "_" + probe
    if name not in functions:
        print("missing generated configured-selector body:", probe, file=sys.stderr)
        sys.exit(1)
    return functions[name]


def helpers(probe):
    """Specializations and constants named after the probe, apart from its entry points."""
    own = {prefix + "_" + probe, prefix + "_" + probe + "___boxed"}
    return {name: body for name, body in functions.items()
            if name_pattern(probe).search(name) and name not in own}


planner = re.compile(r"selectCertified|considerCertified|lean_mk_thunk|lean_thunk_get")
same = kernels = 0
for width in ("32", "64"):
    for operation in ("Add", "Sub", "Mul", "Div", "Sqrt", "Fma"):
        reference = "binary%s%s" % (width, operation)
        forms = ["Binary", "Nearest", "Field"]
        forms += ["Operator"] if operation in ("Add", "Sub", "Mul", "Div") else []
        forms += ["NearestAway"] if operation == "Sqrt" else []
        reference_helpers = sorted(normal(body, reference) for body in helpers(reference).values())
        for form in forms:
            probe = reference + form
            # The entry point must make the reference's call; any specialization of its own must
            # repeat one of the reference's.
            matches = normal(entry(probe), probe, reference) == normal(entry(reference), reference)
            own = sorted(normal(body, probe) for body in helpers(probe).values())
            if not matches or any(body not in reference_helpers for body in own):
                print("%s does not compile to the code of %s" % (probe, reference),
                      file=sys.stderr)
                sys.exit(1)
            same += 1
        for form, kernel in (("Up", "Model_Internal_Directed_"),
                             ("Status", "Model_Internal_Status_")):
            probe = reference + form
            body = entry(probe) + "".join(helpers(probe).values())
            if kernel not in body or planner.search(body):
                print("%s does not call its %s kernel directly" % (probe, kernel),
                      file=sys.stderr)
                sys.exit(1)
            kernels += 1
print("Configured selectors: %d default spellings compile to the generic kernels, %d directed "
      "and status forms reach the model kernels." % (same, kernels))
PY

if [[ "$(grep -Fc 'Model_FmaBackend_word' "$generated_c")" -lt 2 ]]; then
  printf '%s\n' 'configured binary32/binary64 FMA lost the proved word kernel' >&2
  exit 1
fi

printf '%s\n' \
  'Configured binary code generation passed: 12 certified software operations and 10 explicit unchecked host operations are native and first-order.'
