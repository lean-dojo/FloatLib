#!/usr/bin/env bash

# Check the repository boundaries that Lean's type system cannot express on its own.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

# shellcheck source=tests/lib/sources.sh
source "$ROOT/tests/lib/sources.sh"

if ! command -v rg >/dev/null 2>&1; then
  printf 'architecture check failed: ripgrep (rg) is required\n' >&2
  exit 1
fi

fail() {
  printf 'architecture check failed: %s\n' "$1" >&2
  exit 1
}

mapfile -t floatlib_sources < <(floatlib_source_files)

mapfile -t numerics_sources < <(
  printf '%s\n' "${floatlib_sources[@]}" |
    awk '/^FloatLib\/Numerics(\.lean|\/)/'
)
mapfile -t kernel_sources < <(
  printf '%s\n' "${floatlib_sources[@]}" |
    awk '/^FloatLib\/Kernels(\.lean|\/)/'
)
mapfile -t production_sources < <(
  printf '%s\n' "${floatlib_sources[@]}" |
    awk '$0 == "FloatLib.lean" || /^FloatLib\/(Numerics|Kernels|Floats)(\.lean|\/)/'
)

# Public modules follow the same predictable UpperCamelCase path convention as mathlib. Keeping
# this check at the source boundary prevents ad hoc lowercase or punctuation-heavy module names
# from becoming part of the import API.
invalid_floatlib_paths="$(
  for source in "${floatlib_sources[@]}"; do
    module_path="${source#tests/}"
    module_path="${module_path%.lean}"
    IFS=/ read -r -a components <<< "$module_path"
    for component in "${components[@]}"; do
      if [[ ! "$component" =~ ^[A-Z][A-Za-z0-9]*$ ]]; then
        printf '%s: %s\n' "$source" "$component"
      fi
    done
  done
)"
if [[ -n "$invalid_floatlib_paths" ]]; then
  printf '%s\n' "$invalid_floatlib_paths" >&2
  fail "FloatLib module paths must use UpperCamelCase components"
fi

# Plain grep here: one short-lived process per file, with no thread pool to exhaust on a loaded
# machine, where ripgrep has reported spurious misses.
missing_module_declarations="$(
  for source in "${floatlib_sources[@]}"; do
    grep -qE '^module( -- shake: [a-z-]+)?$' "$source" ||
      printf '%s\n' "$source"
  done
)"
if [[ -n "$missing_module_declarations" ]]; then
  printf '%s\n' "$missing_module_declarations" >&2
  fail "FloatLib modules must declare their module boundary"
fi

missing_module_docs="$(
  for source in "${floatlib_sources[@]}"; do
    rg --quiet '^[[:space:]]*/-!' "$source" ||
      printf '%s\n' "$source"
  done
)"
if [[ -n "$missing_module_docs" ]]; then
  printf '%s\n' "$missing_module_docs" >&2
  fail "FloatLib modules must have a module docstring"
fi

# Keep source modules readable as units. Split at a mathematical or execution boundary, rather
# than creating a separate file for each declaration merely to satisfy this bound.
oversized_modules="$(
  awk '
    FNR == 1 {
      if (NR > 1 && lines > 1500)
        print source ": " lines " lines"
      source = FILENAME
    }
    { lines = FNR }
    END {
      if (lines > 1500)
        print source ": " lines " lines"
    }
  ' "${floatlib_sources[@]}"
)"
if [[ -n "$oversized_modules" ]]; then
  printf '%s\n' "$oversized_modules" >&2
  fail "FloatLib modules must stay within 1500 lines and have coherent topic boundaries"
fi

# The dependency graph is intentionally one-way:
#
#   Numerics -> Kernels -> Floats
#
# Validation and examples may depend on production code, but production code must never import
# them. These checks preserve the ownership boundary that lets the exact semantics and verified
# kernels remain independently reusable.
layer_violations="$(
  while IFS= read -r source; do
    while IFS= read -r imported_module; do
      case "$imported_module" in
        FloatLib.Kernels*|FloatLib.Floats*)
          printf '%s: %s\n' "$source" "$imported_module"
          ;;
      esac
    done < <(floatlib_header_imports "$source")
  done < <(printf '%s\n' "${numerics_sources[@]}")

  while IFS= read -r source; do
    while IFS= read -r imported_module; do
      case "$imported_module" in
        FloatLib.Floats*)
          printf '%s: %s\n' "$source" "$imported_module"
          ;;
      esac
    done < <(floatlib_header_imports "$source")
  done < <(printf '%s\n' "${kernel_sources[@]}")

  while IFS= read -r source; do
    while IFS= read -r imported_module; do
      case "$imported_module" in
        FloatLibTests*|FloatLib.Examples*)
          printf '%s: %s\n' "$source" "$imported_module"
          ;;
      esac
    done < <(floatlib_header_imports "$source")
  done < <(printf '%s\n' "${production_sources[@]}")
)"
if [[ -n "$layer_violations" ]]; then
  printf '%s\n' "$layer_violations" >&2
  fail "FloatLib dependency layers point in the wrong direction"
fi

# Host-FPU operations are an explicit unchecked API for tests, benchmarks, and applications.
# Keeping that module out of every production import header prevents an aggregate or certified
# implementation from exposing the trust boundary transitively. Elementary-function barrels are a
# separate import fence: Configured.Transcendentals must not ride in on import FloatLib, and the
# model barrel may be imported only by that configured module. Kernel files and Contract stay
# reachable as named modules.
opt_in_ok_importer() {
  local source="$1" module="$2"
  case "$module" in
    FloatLib.Floats.Formats.BinaryInterchange.Configured.NativeFPU.Unchecked) return 1 ;;
    FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals) return 1 ;;
    FloatLib.Floats.Formats.BinaryInterchange.Transcendentals)
      [[ "$source" == "FloatLib/Floats/Formats/BinaryInterchange/Configured/Transcendentals.lean" ]]
      ;;
    *) return 1 ;;
  esac
}

opt_in_production_ban=(
  FloatLib.Floats.Formats.BinaryInterchange.Configured.NativeFPU.Unchecked
  FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals
  FloatLib.Floats.Formats.BinaryInterchange.Transcendentals
  FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Certified.Proof
)
for banned_module in "${opt_in_production_ban[@]}"; do
  banned_imports="$(
    while IFS= read -r source; do
      while IFS= read -r imported_module; do
        if [[ "$imported_module" == "$banned_module" ]] &&
            ! opt_in_ok_importer "$source" "$imported_module"; then
          printf '%s\n' "$source"
        fi
      done < <(floatlib_header_imports "$source")
    done < <(printf '%s\n' "${production_sources[@]}")
  )"
  if [[ -n "$banned_imports" ]]; then
    printf '%s\n' "$banned_imports" >&2
    fail "certified production modules must not import ${banned_module}"
  fi
done

unresolved_imports="$(
  while IFS= read -r source; do
    while IFS= read -r imported_module; do
      case "$imported_module" in
        FloatLib|FloatLib.*|FloatLibTests|FloatLibTests.*) ;;
        *) continue ;;
      esac
      imported_path="$(floatlib_module_source "$imported_module")"
      [[ -f "$imported_path" ]] ||
        printf '%s: %s\n' "$source" "$imported_module"
    done < <(floatlib_header_imports "$source")
  done < <(printf '%s\n' "${floatlib_sources[@]}")
)"
if [[ -n "$unresolved_imports" ]]; then
  printf '%s\n' "$unresolved_imports" >&2
  fail "FloatLib imports do not resolve to source modules"
fi

duplicate_imports="$(
  while IFS= read -r source; do
    duplicates="$(
      floatlib_header_import_edges "$source" |
        sort |
        uniq -d
    )"
    if [[ -n "$duplicates" ]]; then
      while IFS=$'\t' read -r import_channel imported_module; do
        printf '%s: %s (%s import)\n' "$source" "$imported_module" "$import_channel"
      done <<< "$duplicates"
    fi
  done < <(printf '%s\n' "${floatlib_sources[@]}")
)"
if [[ -n "$duplicate_imports" ]]; then
  printf '%s\n' "$duplicate_imports" >&2
  fail "duplicate imports remain"
fi


mapfile -t format_sources < <(
  printf '%s\n' "${floatlib_sources[@]}" |
    awk '/^FloatLib\/Floats\/Formats\//'
)
mapfile -t posit_sources < <(
  printf '%s\n' "${format_sources[@]}" |
    awk '/^FloatLib\/Floats\/Formats\/Posit\//'
)
mapfile -t flocq_sources < <(
  printf '%s\n' "${format_sources[@]}" |
    awk '/^FloatLib\/Floats\/Formats\/Flocq\//'
)
mapfile -t backend_sources < <(
  printf '%s\n' "${floatlib_sources[@]}" |
    awk '/^FloatLib\/Floats\/ExecFloat\/Backends\//'
)
mapfile -t example_sources < <(
  printf '%s\n' "${floatlib_sources[@]}" |
    awk '/^FloatLib\/Examples\//'
)

required_entrypoints=(
  FloatLib.lean
  tests/FloatLibTests.lean
  FloatLib/Numerics.lean
  FloatLib/Kernels.lean
  FloatLib/Floats.lean
  FloatLib/Examples.lean
  tests/FloatLibTests/Conformance.lean
  FloatLib/Floats/ExecFloat.lean
  FloatLib/Floats/Formats.lean
  FloatLib/Floats/Interval.lean
)

for path in "${required_entrypoints[@]}"; do
  [[ -f "$path" ]] || fail "missing entry point $path"
done

# A format becomes public by adding its top-level module to Formats.lean. Derive the expected set
# from the tree so adding or moving a family does not require editing this script.
mapfile -t expected_format_modules < <(
  printf '%s\n' "${format_sources[@]}" |
    awk -F/ 'NF == 4 {
      sub(/\.lean$/, "")
      gsub(/\//, ".")
      print
    }' |
    sort
)
mapfile -t registered_format_modules < <(
  sed -nE \
    's/^public import (FloatLib\.Floats\.Formats\.[^.[:space:]]+)$/\1/p' \
    FloatLib/Floats/Formats.lean |
    sort
)

format_registration_diff="$(
  comm -3 \
    <(printf '%s\n' "${expected_format_modules[@]}") \
    <(printf '%s\n' "${registered_format_modules[@]}")
)"
if [[ -n "$format_registration_diff" ]]; then
  printf '%s\n' "$format_registration_diff" >&2
  fail "FloatLib.Floats.Formats does not match the top-level format families"
fi

duplicate_format_imports="$(
  printf '%s\n' "${registered_format_modules[@]}" |
    uniq -d
)"
if [[ -n "$duplicate_format_imports" ]]; then
  printf '%s\n' "$duplicate_format_imports" >&2
  fail "FloatLib.Floats.Formats imports a family more than once"
fi

if unscoped_resource_options="$(
  rg -n \
    '^[[:space:]]*set_option[[:space:]]+(maxHeartbeats|maxRecDepth)[[:space:]]+[^[:space:]]+[[:space:]]*$' \
    "${floatlib_sources[@]}"
)"; then
  printf '%s\n' "$unscoped_resource_options" >&2
  fail "proof resource overrides must be scoped with 'in'"
fi

# The root package stays library-only; developer executables belong to their own workspaces.
if rg -q '^lean_exe\b|^[[:space:]]*testDriver[[:space:]]*:=' lakefile.lean; then
  fail "root Lake configuration must not register test or benchmark runners"
fi

# Resolve every tooling executable back to its source module.
mapfile -t executable_specs < <(
  awk '
    function emit() {
      if (in_executable && root != "")
        printf "%s\t%s\n", src_dir, root
      in_executable = 0
    }

    FNR == 1 {
      emit()
      package_dir = FILENAME
      sub(/\/lakefile\.lean$/, "", package_dir)
      default_src_dir = package_dir
      in_package = 0
    }

    /^package[[:space:]]/ { in_package = 1; next }
    /^[^[:space:]]/ { in_package = 0 }
    in_package && /^[[:space:]]+srcDir[[:space:]]*:=/ {
      directory = $0
      sub(/^[[:space:]]+srcDir[[:space:]]*:=[[:space:]]*"/, "", directory)
      sub(/".*$/, "", directory)
      default_src_dir = package_dir "/" directory
    }

    /^[[:space:]]*lean_exe[[:space:]]+/ {
      emit()
      in_executable = 1
      src_dir = default_src_dir
      root = ""
      next
    }

    in_executable && /^[^[:space:]]/ {
      emit()
    }

    in_executable && /^[[:space:]]+srcDir[[:space:]]*:=/ {
      src_dir = $0
      sub(/^[[:space:]]+srcDir[[:space:]]*:=[[:space:]]*"/, "", src_dir)
      sub(/".*$/, "", src_dir)
    }

    in_executable && /^[[:space:]]+root[[:space:]]*:=/ {
      root = $0
      sub(/^[[:space:]]+root[[:space:]]*:=[[:space:]]*`/, "", root)
      sub(/[[:space:]].*$/, "", root)
    }

    END { emit() }
  ' tests/lakefile.lean benchmarks/lakefile.lean
)

for spec in "${executable_specs[@]}"; do
  IFS=$'\t' read -r src_dir module <<< "$spec"
  source_path="${src_dir%/}/${module//.//}.lean"
  source_path="${source_path#./}"

  [[ -f "$source_path" ]] ||
    fail "Lake executable root does not exist: $source_path"
  rg -q '^public def main\b' "$source_path" ||
    fail "Lake executable root must export public main: $source_path"
done

# Every project module should be reachable from a public root, the test root, the examples root,
# or a declared executable. Traverse imports from those roots: disconnected chains and cycles
# must not keep one another alive merely by having incoming edges.
# Two native-only oracle runners intentionally live in small helper workspaces. Importing either
# one through FloatLibTests would make every ordinary test build carry its solver or
# transcendental dependencies, so we keep the executable roots explicit here and check that their
# Lake files remain present below.
standalone_oracle_specs=(
  'tests/oracles/SMTFP/lakefile.lean|FloatLibTests.Oracle.SMT|FloatLibTests.Oracle.SMT'
  'tests/oracles/Transcendental/lakefile.lean|Transcendentals|FloatLibTests.Oracle.Transcendentals'
)
standalone_oracle_entrypoints=()
for spec in "${standalone_oracle_specs[@]}"; do
  IFS='|' read -r path lake_root module <<< "$spec"
  [[ -f "$path" ]] || fail "missing standalone oracle workspace $path"
  rg -q -F "root := \`$lake_root" "$path" ||
    fail "standalone oracle workspace has the wrong executable root: $path"
  standalone_oracle_entrypoints+=("$module")
done

maintained_roots=(
  FloatLib
  FloatLib.Examples
  FloatLibTests
  "${standalone_oracle_entrypoints[@]}"
)
# These named public imports are deliberately absent from FloatLib. They remain supported entry
# points even if no current test or executable happens to import them.
for module in "${opt_in_production_ban[@]}"; do
  [[ -f "$(floatlib_module_source "$module")" ]] ||
    fail "missing optional public entry point $module"
  maintained_roots+=("$module")
done
for spec in "${executable_specs[@]}"; do
  IFS=$'\t' read -r src_dir module <<< "$spec"
  maintained_roots+=("$module")
done

unreachable_modules="$(
  comm -23 \
    <(
      for source in "${floatlib_sources[@]}"; do
        floatlib_source_module "$source"
      done |
        LC_ALL=C sort -u
    ) \
    <(
      {
        printf '%s\n' "${floatlib_sources[@]}"
        floatlib_lean_files benchmarks/lean
      } | floatlib_reachable_modules "${maintained_roots[@]}"
    )
)"
if [[ -n "$unreachable_modules" ]]; then
  printf '%s\n' "$unreachable_modules" >&2
  fail "FloatLib modules are not reachable from a maintained root"
fi

mapfile -t expected_example_modules < <(
  for source in "${example_sources[@]}"; do
    module="${source%.lean}"
    printf '%s\n' "${module//\//.}"
  done
)
mapfile -t registered_example_modules < <(
  sed -nE \
    's/^public import (FloatLib\.Examples\.[^[:space:]]+)$/\1/p' \
    FloatLib/Examples.lean |
    sort
)

example_registration_diff="$(
  comm -3 \
    <(printf '%s\n' "${expected_example_modules[@]}") \
    <(printf '%s\n' "${registered_example_modules[@]}")
)"
if [[ -n "$example_registration_diff" ]]; then
  printf '%s\n' "$example_registration_diff" >&2
  fail "FloatLib.Examples does not match the teaching modules"
fi

if test_paths="$(
  printf '%s\n' "${floatlib_sources[@]}" |
    rg '(^|/)Tests(\.lean|/)'
)"; then
  printf '%s\n' "$test_paths" >&2
  fail "tests belong under tests/FloatLibTests, not beside production modules"
fi

if posit_binary_coupling="$(
  rg -n \
    'FloatLib\.Floats\.Formats\.BinaryInterchange' \
    "${posit_sources[@]}"
)"; then
  printf '%s\n' "$posit_binary_coupling" >&2
  fail "Posit must share arithmetic through Numerics or Kernels"
fi

if execfloat_core_aggregate_imports="$(
  rg -n --glob '!**/ExecFloat/Core.lean' \
    '^(public[[:space:]]+)?(meta[[:space:]]+)?import FloatLib\.Floats\.ExecFloat\.Core$' \
    "${floatlib_sources[@]}"
)"; then
  printf '%s\n' "$execfloat_core_aggregate_imports" >&2
  fail "internal modules must import the required ExecFloat.Core facet directly"
fi

if posit_model_aggregate_imports="$(
  rg -n --glob '!**/Formats/Posit/Model.lean' \
    '^(public[[:space:]]+)?(meta[[:space:]]+)?import FloatLib\.Floats\.Formats\.Posit\.Model$' \
    "${floatlib_sources[@]}"
)"; then
  printf '%s\n' "$posit_model_aggregate_imports" >&2
  fail "internal modules must import the required Posit.Model facet directly"
fi

if precision_paths="$(
  printf '%s\n' "${backend_sources[@]}" |
    rg '/(FP|BF|TF|Binary)[0-9]+(/|$)'
)"; then
  printf '%s\n' "$precision_paths" >&2
  fail "backend ownership must describe an algorithm, not one precision"
fi

if stale_flocq_namespaces="$(
  rg -n '^namespace FloatLib\.Floats\.' \
    "${flocq_sources[@]}" |
    rg -v ':namespace FloatLib\.Floats\.Formats\.Flocq($|\.)'
)"; then
  printf '%s\n' "$stale_flocq_namespaces" >&2
  fail "a Flocq module escaped the Formats.Flocq namespace"
fi

carrier_count="$(
  rg -n '^abbrev ExecFloat \(F : Type' "${floatlib_sources[@]}" |
    wc -l
)"
[[ "$carrier_count" -eq 1 ]] ||
  fail "expected one public ExecFloat carrier, found $carrier_count"

posit_constructor_count="$(
  rg -n '^abbrev Posit$' "${floatlib_sources[@]}" |
    wc -l
)"
[[ "$posit_constructor_count" -eq 1 ]] ||
  fail "expected one public ExecFloat.Posit constructor, found $posit_constructor_count"

mapfile -t runtime_files < <(
  printf '%s\n' "${floatlib_sources[@]}" |
    awk '/\/Runtime\.lean$/'
)

# A runtime module that must construct validity-carrying kernels can declare
# `-- architecture: allow-proof-imports` in its module preamble, with a comment explaining why.
# Such modules are exempt from the two proof-facet rules below and are counted so additions stay
# visible.
mapfile -t exempt_runtime_files < <(
  rg -l '^-- architecture: allow-proof-imports$' "${runtime_files[@]}" || true
)
if [[ "${#exempt_runtime_files[@]}" -gt 0 ]]; then
  printf 'runtime modules exempt from the proof-facet rule: %d\n' "${#exempt_runtime_files[@]}"
  mapfile -t runtime_files < <(
    printf '%s\n' "${runtime_files[@]}" |
      grep -v -x -F -f <(printf '%s\n' "${exempt_runtime_files[@]}")
  )
fi

if runtime_proof_imports="$(
  rg -n '^public import .*\.Proof$' "${runtime_files[@]}"
)"; then
  printf '%s\n' "$runtime_proof_imports" >&2
  fail "runtime modules must not import proof facets"
fi

if runtime_meta_imports="$(
  rg -n \
    '^(public[[:space:]]+)?(meta[[:space:]]+)?import (Lean\.Elab|FloatLib\.Floats\.(ExecFloat\.Info|Formats\..*\.Info))|^[[:space:]]*#float_info\b' \
    "${runtime_files[@]}"
)"; then
  printf '%s\n' "$runtime_meta_imports" >&2
  fail "runtime modules must not import inspection or elaborator support"
fi

# An aggregate can hide a Proof import even when Runtime.lean does not mention Proof directly.
runtime_aggregate_imports="$(
  while IFS=: read -r source line import_line; do
    imported_module="${import_line#*import }"
    imported_module="${imported_module%% *}"
    imported_path="${imported_module//.//}.lean"
    if [[ -f "$imported_path" ]] &&
        rg -q -F -x "public import ${imported_module}.Proof" "$imported_path"; then
      printf '%s:%s:%s\n' "$source" "$line" "$imported_module"
    fi
  done < <(
    rg -n '^(public )?import FloatLib\.' "${runtime_files[@]}"
  )
)"
if [[ -n "$runtime_aggregate_imports" ]]; then
  printf '%s\n' "$runtime_aggregate_imports" >&2
  fail "runtime modules import aggregates that re-export proof facets"
fi

mapfile -t configured_conversion_files < <(
  printf '%s\n' "${format_sources[@]}" |
    rg '/Configured/Conversion/(Runtime|Proof|Instances)\.lean$' |
    LC_ALL=C sort
)

configured_conversion_aggregate_imports="$(
  while IFS=: read -r source line import_line; do
    imported_module="${import_line#*import }"
    imported_module="${imported_module%% *}"
    imported_path="${imported_module//.//}.lean"
    configured_entry="${source%/Conversion/*}.lean"
    family_entry="${source%%/Configured/Conversion/*}.lean"
    if [[ "$imported_path" == "$configured_entry" || "$imported_path" == "$family_entry" ]]; then
      printf '%s:%s:%s\n' "$source" "$line" "$imported_module"
    fi
  done < <(
    rg -n \
      '^(public[[:space:]]+)?(meta[[:space:]]+)?import FloatLib\.' \
      "${configured_conversion_files[@]}"
  )
)"
if [[ -n "$configured_conversion_aggregate_imports" ]]; then
  printf '%s\n' "$configured_conversion_aggregate_imports" >&2
  fail "configured conversion adapters import an ancestor aggregate"
fi

mapfile -t format_family_files < <(
  printf '%s\n' "${format_sources[@]}" |
    awk -F/ 'NF == 4' |
    LC_ALL=C sort
)
if runtime_info_imports="$(
  rg -n \
    '^public import FloatLib\.Floats\.(ExecFloat\.Info|Formats\..*\.Info)$' \
    "${format_family_files[@]}"
)"; then
  printf '%s\n' "$runtime_info_imports" >&2
  fail "format-family modules must not pull inspection support into runtime imports"
fi

if eager_examples="$(
  rg -n '^#(eval|reduce|print|check)\b' "${example_sources[@]}"
)"; then
  printf '%s\n' "$eager_examples" >&2
  fail "teaching modules stay quiet; output belongs in an explicit executable"
fi

printf '%s\n' 'FloatLib architecture check passed.'
