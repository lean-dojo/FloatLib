#!/usr/bin/env bash
# Time the proof checkers that ship with the Lean toolchain on FloatLib's proofs by kernel
# evaluation, and record whether each one accepts them.
#
# usage: benchmarks/kernel/checkers.sh [FAMILY...]
#
# Families (default: all, in this order):
#   exact-layer   every declaration of the definition modules of `FloatLib.Numerics.Kernel`, which
#                 import no mathematics from Mathlib: Bits, Strict, Z, Signed, Q, Frac, Dyad, Ball,
#                 CBall, CFix, Seq, Multiplicative, Mod and Root
#   exact-checks  the checks of `tests/FloatLibTests/Conformance/Numerics/KernelExact.lean`, with
#                 each `example` turned into a named theorem
#   loops-kernel  the three theorems of `loops.sh` about loops of 1,000 steps, by `float_decide`
#   loops-public  the same three theorems by `decide +kernel` on the public operations
#   exhaustive    the two theorems of `Exhaustive.lean` about all 65,536 pairs of E4M3 encodings
#
# Checkers:
#   leanchecker, leanchecker-paranoid   replay the family's modules from their `.olean` files
#   nanoda, con-ron                     check an export written by `leanexport`
#   lean-export                         `leanchecker --from-export`: Lean's kernel on that export
#
# Each run is paired with a baseline, so that the difference is the cost of the family's own
# declarations. For the two replaying checkers the baseline is a module with the family's imports
# and nothing else. For an export it is the export of the constants that the family's declarations
# use from other modules (`Closure.lean` lists them), with everything those depend on.
# The replaying checkers run once per module, one process after the other. They take module
# prefixes, so the modules of `exact-layer` are replayed from a directory that holds only them and
# the library modules they import; otherwise `Bits` and `CBall` would bring their proof modules
# along. The baseline of a family of several modules is one baseline run times the number of
# modules.
#
# Output: one row per family and checker in `benchmarks/kernel/checkers.csv`, or in the file named
# by KERNEL_CHECKERS_CSV. Times are wall-clock seconds of one run. `status` is `accepted`,
# `rejected` (the checker's exit code is in `exit`) or `no verdict` (the run reached its time
# limit or ended on a signal, exit above 128). KERNEL_CHECKERS_TIMEOUT bounds
# each run (seconds, default 1800), KERNEL_CHECKERS_JOBS sets the workers of `con-ron` (default
# 8), and KERNEL_CHECKERS_KEEP names a directory that keeps the generated modules, the exports and
# every checker's output.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
root="$(cd "$here/../.." && pwd)"
source "$root/tests/lib/lake.sh"

families=("$@")
if [[ ${#families[@]} -eq 0 ]]; then
  families=(exact-layer exact-checks loops-kernel loops-public exhaustive)
fi
csv="${KERNEL_CHECKERS_CSV:-$here/checkers.csv}"
limit="${KERNEL_CHECKERS_TIMEOUT:-1800}"
jobs="${KERNEL_CHECKERS_JOBS:-8}"
if [[ -n "${KERNEL_CHECKERS_KEEP:-}" ]]; then
  work="$KERNEL_CHECKERS_KEEP"
  mkdir -p "$work"
else
  work="$(mktemp -d "${TMPDIR:-/tmp}/kernel-checkers.XXXXXX")"
  trap 'rm -rf "$work"' EXIT
fi

cd "$root"
search="$(floatlib_lake env printenv LEAN_PATH)"
bin="$(floatlib_lake env lean --print-prefix)/bin"
libdir="$("$bin/lean" --print-libdir)"
export LEAN_PATH="$work:$search:$libdir"
# The search path without the library's own build directory.
outside="$(printf '%s' "$search" | tr ':' '\n' | grep -vxF "$FLOATLIB_BUILD_DIR/lib/lean" | paste -sd: -)"
toolchain="$("$bin/lean" --version | sed -E 's/.*version ([^ ,]+).*/\1/')"

# Compile one generated module into the work directory.
compile() {
  "$bin/lean" --root="$work" -o "$work/$1.olean" "$work/$1.lean" > "$work/$1.build" 2>&1 || {
    cat "$work/$1.build" >&2
    echo "checkers.sh: $1.lean does not compile" >&2
    exit 1
  }
}

# The import lines of a Lean file, with `module` when the file has it.
header() {
  awk '/^module/ { print; next } /^(public |private )?(meta )?import / { print; next }
    /^(theorem|def|namespace|open|@\[|set_option|\/-!)/ { exit }' "$1"
}

# The library modules that the modules named import, with those modules, one per line.
library_closure() {
  local todo=("$@") seen=" " module name
  while [[ ${#todo[@]} -gt 0 ]]; do
    module="${todo[0]}"
    todo=("${todo[@]:1}")
    [[ "$seen" == *" $module "* ]] && continue
    seen+="$module "
    echo "$module"
    while read -r name; do
      todo+=("$name")
    done < <(awk '/^(public |private )?(meta )?import / {
      for (i = 1; i <= NF; i++) if ($i ~ /^FloatLib(\.|$)/) { print $i; break } }' \
      "$root/${module//.//}.lean")
  done
}

# Prepare a family: set `modules` (to replay), `base` (baseline module), `closure` (the modules
# whose constants are exported) and `replay_path` (the search path of the replaying checkers).
prepare() {
  replay_path="$LEAN_PATH"
  case "$1" in
    exact-layer)
      modules=()
      for name in Bits Strict Z Signed Q Frac Dyad Ball CBall CFix Seq Multiplicative Mod Root; do
        modules+=("FloatLib.Numerics.Kernel.$name")
      done
      printf 'module\npublic import FloatLib.Tactic.CompiledAs\npublic import Mathlib.Init\n' \
        > "$work/ExactLayerBase.lean"
      base=ExactLayerBase
      # A directory with the compiled files of these modules and of the library modules they import
      # (copies: the checkers do not follow symbolic links when they look for modules).
      local module path part
      while read -r module; do
        path="${module//.//}"
        mkdir -p "$work/layer/$(dirname "$path")"
        for part in olean olean.server olean.private; do
          if [[ -f "$FLOATLIB_BUILD_DIR/lib/lean/$path.$part" ]]; then
            cp -f "$FLOATLIB_BUILD_DIR/lib/lean/$path.$part" "$work/layer/$path.$part"
          fi
        done
      done < <(library_closure "${modules[@]}")
      replay_path="$work/layer:$work:$outside:$libdir"
      ;;
    exact-checks)
      awk '/^example/ { count += 1; sub(/^example/, sprintf("theorem exact_%03d", count)) } { print }' \
        "$root/tests/FloatLibTests/Conformance/Numerics/KernelExact.lean" > "$work/ExactChecks.lean"
      header "$work/ExactChecks.lean" > "$work/ExactChecksBase.lean"
      compile ExactChecks
      modules=(ExactChecks)
      base=ExactChecksBase
      ;;
    loops-kernel | loops-public)
      [[ -f "$work/Loops.olean" ]] || { cp "$here/Loops.lean" "$work/Loops.lean"; compile Loops; }
      local module=LoopsKernel
      [[ "$1" == loops-public ]] && module=LoopsPublic
      {
        echo "import Loops"
        echo "open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange"
        echo "open FloatLibBenchmarks.KernelLoops"
        echo "set_option maxRecDepth 1000000"
        while IFS='|' read -r name statement; do
          echo "theorem ${name}_encoding : $statement := by"
          if [[ "$1" == loops-kernel ]]; then
            echo "  float_decide [$name]"
          else
            echo "  unfold $name; decide +kernel"
          fi
        done <<'CASES'
sumTenth|KernelPath.toNat (sumTenth 1000) = 1120403331
sum64|KernelPath.toNat (sum64 1000) = 13851123079082828159
dot64|KernelPath.toNat (dot64 1000) = 4676214714831268436
CASES
      } > "$work/$module.lean"
      printf 'import Loops\n' > "$work/LoopsBase.lean"
      compile "$module"
      modules=("$module")
      base=LoopsBase
      ;;
    exhaustive)
      cp "$here/Exhaustive.lean" "$work/Exhaustive.lean"
      header "$work/Exhaustive.lean" > "$work/ExhaustiveBase.lean"
      compile Exhaustive
      modules=(Exhaustive)
      base=ExhaustiveBase
      ;;
    *)
      echo "checkers.sh: unknown family $1" >&2
      exit 2
      ;;
  esac
  compile "$base"
  closure=("${modules[@]}")
}

# No core files: writing one can take minutes.
ulimit -c 0

# Run one command with the time limit; print `seconds exit` and keep its output in FILE.
timed() {
  local file="$1" start end code
  shift
  start="$(date +%s.%N)"
  set +e
  timeout --kill-after=20 "$limit" "$@" > "$file" 2>&1
  code=$?
  set -e
  end="$(date +%s.%N)"
  awk -v s="$start" -v e="$end" -v c="$code" 'BEGIN { printf "%.2f %d\n", e - s, c }'
}

# Write the configuration of `nanoda_bin` for one export.
nanoda_config() {
  printf '{"export_file_path":"%s","use_stdin":false,"permitted_axioms":["propext","Classical.choice","Quot.sound"],"unpermitted_axiom_hard_error":true,"nat_extension":true,"string_extension":true,"print_success_message":true}\n' \
    "$1" > "$2"
}

# One CSV row from a family, a checker, the number of declarations checked and the two runs.
row() {
  local family="$1" checker="$2" declarations="$3" seconds="$4" code="$5" base_seconds="$6" base_code="$7"
  local status=accepted
  if [[ "$code" -eq 124 || "$code" -gt 128 ]]; then
    status="no verdict"
  elif [[ "$code" -ne 0 ]]; then
    status=rejected
  fi
  awk -v f="$family" -v k="$checker" -v d="$declarations" -v s="$seconds" -v c="$code" \
    -v bs="$base_seconds" -v bc="$base_code" -v st="$status" -v t="$toolchain" \
    'BEGIN { printf "%s,%s,%s,%s,%d,%s,%s,%d,%.2f,%s\n", f, k, d, st, c, s, bs, bc, s - bs, t }' >> "$csv"
}

echo "family,checker,declarations,status,exit,seconds,baseline_seconds,baseline_exit,net_seconds,lean" > "$csv"

for family in "${families[@]}"; do
  prepare "$family"
  out="$work/$family"
  mkdir -p "$out"

  # The family's constants and the constants they use from other modules.
  "$bin/lean" --run "$here/Closure.lean" "${closure[@]}" | sort > "$out/closure.txt"
  mapfile -t roots < <(awk '$1 == "root" { print $2 }' "$out/closure.txt")
  mapfile -t uses < <(awk '$1 == "uses" { print $2 }' "$out/closure.txt")
  declared="$(grep -cE '^(root|hidden) ' "$out/closure.txt")"
  echo "$family: ${#roots[@]} constants exported by name of $declared declared," \
    "$(grep -c '^unreachable ' "$out/closure.txt" || true) used constants that cannot be named"

  for checker in leanchecker leanchecker-paranoid; do
    seconds=0
    code=0
    for module in "${modules[@]}"; do
      read -r one one_code < <(LEAN_PATH="$replay_path" timed "$out/$checker-$module.txt" "$bin/$checker" "$module")
      seconds="$(awk -v a="$seconds" -v b="$one" 'BEGIN { printf "%.2f", a + b }')"
      [[ "$code" -eq 0 ]] && code="$one_code"
    done
    read -r one base_code < <(LEAN_PATH="$replay_path" timed "$out/$checker-base.txt" "$bin/$checker" "$base")
    base_seconds="$(awk -v b="$one" -v n="${#modules[@]}" 'BEGIN { printf "%.2f", b * n }')"
    row "$family" "$checker" "$declared" "$seconds" "$code" "$base_seconds" "$base_code"
  done

  "$bin/leanexport" "${closure[@]}" -- "${roots[@]}" > "$out/family.ndjson"
  "$bin/leanexport" "${closure[@]}" -- "${uses[@]}" > "$out/base.ndjson"
  exported="$(grep -cE '"(thm|def|axiom|opaque|inductive|quot)":' "$out/family.ndjson" || true)"
  nanoda_config "$out/family.ndjson" "$out/nanoda.json"
  nanoda_config "$out/base.ndjson" "$out/nanoda-base.json"

  read -r seconds code < <(timed "$out/nanoda.txt" "$bin/nanoda_bin" "$out/nanoda.json")
  read -r base_seconds base_code < <(timed "$out/nanoda-base.txt" "$bin/nanoda_bin" "$out/nanoda-base.json")
  row "$family" nanoda "$exported" "$seconds" "$code" "$base_seconds" "$base_code"

  read -r seconds code < <(timed "$out/con-ron.txt" "$bin/con-ron" "--jobs=$jobs" "$out/family.ndjson")
  read -r base_seconds base_code < <(timed "$out/con-ron-base.txt" "$bin/con-ron" "--jobs=$jobs" "$out/base.ndjson")
  row "$family" con-ron "$exported" "$seconds" "$code" "$base_seconds" "$base_code"

  read -r seconds code < <(timed "$out/lean-export.txt" "$bin/leanchecker" --from-export "$out/family.ndjson")
  read -r base_seconds base_code < <(timed "$out/lean-export-base.txt" "$bin/leanchecker" --from-export "$out/base.ndjson")
  row "$family" lean-export "$exported" "$seconds" "$code" "$base_seconds" "$base_code"

  # The exports are large; the checkers' output is what is kept.
  rm -f "$out/family.ndjson" "$out/base.ndjson"
done

column -s, -t "$csv"
