#!/usr/bin/env bash
# The exact-arithmetic suite: kernel cost of exact operations, of other projects' checks and of
# FloatLib's own exact layer, against `native_decide`, compiled code and Coq.
#
# usage: benchmarks/exact/run.sh [PART...]
#
#   operations  one operation per type and size (`Operations.lean`)
#   workloads   the kernel checks of PrimeCert, EllipticCurveRank and HighlyAbundant, as written
#               and on `FloatLib.Numerics.Kernel`, and packed rows (`Workloads.lean`)
#   baseline    FloatLib's own exact layer (`Baseline.lean`)
#   tactic      the `interval` tactic (`Tactic.lean`)
#   native      `decide +kernel` against `native_decide` on generated statements (`native.py`)
#   compiled    the compiled program `exactCompiled` against the kernel times of `operations`
#   coq         Coq 8.20.1 `Z`, `Q` and `bignums` under `vm_compute` (`coq/gen.py`), in Docker
#   load        time and memory to load a check module with core-only and with Mathlib imports
#   tables      write the Markdown tables from the logs (done after every run)
#
# With no PART, all parts run. Logs and tables go to `benchmarks/results/exact/` unless
# EXACT_BENCH_OUT names another directory. A run that measures also copies `lean-toolchain` to
# `toolchain.log` there, and the tables name that release: rerun every part after a toolchain
# change, so that no table cites a release other than the one that produced its log.
#
#   EXACT_BENCH_RUNS     how often each Lean file runs; the tables keep the fastest time of
#                        each row (default 1; the recorded results use 3)
#   EXACT_BENCH_TIMEOUT  seconds for one Lean file (default 900)
#   EXACT_BENCH_IMAGE    the Docker image for `coq` (default `leanfloat-flocq-bench:4.2.2`)
#
# Every time in the tables is printed by Lean (`Lean.Kernel.whnf` in `Harness.lean`,
# `IO.monoNanosNow` in `exactCompiled`), by Coq (`Finished transaction`) or by `/usr/bin/time`;
# `tables.py` only divides totals by counts and formats.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
root="$(cd "$here/../.." && pwd)"
source "$root/tests/lib/lake.sh"

parts=("$@")
if [[ ${#parts[@]} -eq 0 ]]; then
  parts=(operations workloads baseline tactic native compiled coq load)
fi
out="${EXACT_BENCH_OUT:-$root/benchmarks/results/exact}"
limit="${EXACT_BENCH_TIMEOUT:-900}"
runs="${EXACT_BENCH_RUNS:-1}"
work="$(mktemp -d "${TMPDIR:-/tmp}/exact-bench.XXXXXX")"
trap 'rm -rf "$work"' EXIT
mkdir -p "$out"
cd "$root"

for part in "${parts[@]}"; do
  if [[ "$part" != tables ]]; then
    cp "$root/lean-toolchain" "$out/toolchain.log"
    break
  fi
done

floatlib_lake env lean -o "$work/Harness.olean" "$here/Harness.lean"

# Keep the result lines and the error lines of a Lean run, with file names relative to the
# checkout: an absolute path of this machine does not belong in a published log.
result_lines() {
  grep -E '^(KOP|KTERM|KCMD) |error' | sed -E 's#(^|[ :(])/[^ :]*/([A-Za-z0-9_.-]+\.lean)#\1\2#g'
}

# Run a Lean file on this checkout; keep the result lines.
run_here() {
  local file="$1" log="$2" status
  : > "$log"
  for _ in $(seq 1 "$runs"); do
    if floatlib_lake env bash -c \
        "LEAN_PATH=\"$work:\$LEAN_PATH\" timeout --kill-after=10 $limit lean \"$file\"" 2>&1 |
        result_lines >> "$log"; then
      :
    else
      status=$?
      cat "$log" >&2
      return "$status"
    fi
  done
  echo "$(grep -c '^K' "$log" || true) rows in $log"
}

for part in "${parts[@]}"; do
  echo "== $part"
  case "$part" in
    operations) run_here "$here/Operations.lean" "$out/operations.log" ;;
    workloads) run_here "$here/Workloads.lean" "$out/workloads.log" ;;
    baseline) run_here "$here/Baseline.lean" "$out/baseline.log" ;;
    tactic) run_here "$here/Tactic.lean" "$out/tactic.log" ;;
    native)
      python3 "$here/native.py" "$work/Native.lean" "$here/Workloads.lean"
      run_here "$work/Native.lean" "$out/native.log" ;;
    compiled)
      floatlib_benchmark_lake build exactCompiled
      "$(floatlib_build_path bin/exactCompiled)" | grep '^COMPILED ' > "$out/compiled.log" ;;
    coq)
      python3 "$here/coq/gen.py" "$work/Exact.v" 64 1024 4096 16384
      docker run --rm --memory=8g --cpus=2 -v "$work:/work:ro" \
        "${EXACT_BENCH_IMAGE:-leanfloat-flocq-bench:4.2.2}" \
        bash -c 'cp /work/Exact.v /tmp/ && cd /tmp && coqc Exact.v' 2>&1 |
        grep -E '^(ROW |Finished transaction)|rror' > "$out/coq.log" ;;
    load)
      statement='open FloatLib.Numerics.Kernel
example : Frac.le (Frac.add ⟨1, 0, 3, by decide⟩ ⟨1, 0, 6, by decide⟩) ⟨1, 0, 2, by decide⟩ = true := by
  decide +kernel'
      : > "$out/load.log"
      load_row() {
        local label="$1" imports="$2" file="$work/Load_$3.lean" modules timing best="" memory=""
        printf '%s\n%s\n' "$imports" "$statement" > "$file"
        modules="$(floatlib_lake env lean --stats "$file" 2>&1 |
          awk '/number of imported modules/ {print $NF}')"
        for _ in 1 2 3; do
          timing="$(floatlib_lake env /usr/bin/time -f '%e %M' lean "$file" 2>&1)"
          read -r wall rss <<< "$(tail -1 <<< "$timing")"
          if [[ -z "$best" ]] || awk -v a="$wall" -v b="$best" 'BEGIN {exit !(a < b)}'; then
            best="$wall"; memory="$rss"
          fi
        done
        printf 'ROW\t%s\t%s\t%s s\t%s MB\n' "$label" "$modules" "$best" "$((memory / 1024))" |
          tee -a "$out/load.log"
      }
      load_row 'core only: `FloatLib.Numerics.Kernel.Frac`' \
        'import FloatLib.Numerics.Kernel.Frac' core
      load_row 'the proof module: `FloatLib.Numerics.Kernel.FracProof`' \
        'import FloatLib.Numerics.Kernel.FracProof' proof
      load_row '`Frac` and one analysis module of Mathlib (`Mathlib.Analysis.SpecialFunctions.Log.Basic`)' \
        'import FloatLib.Numerics.Kernel.Frac
import Mathlib.Analysis.SpecialFunctions.Log.Basic' analysis
      load_row 'all of FloatLib: `FloatLib`' 'import FloatLib' floatlib
      load_row 'all of Mathlib: `Mathlib`' 'import Mathlib
import FloatLib.Numerics.Kernel.Frac' mathlib ;;
    tables) ;;
    *) echo "unknown part $part" >&2; exit 2 ;;
  esac
done

python3 "$here/tables.py" "$out"
echo "tables in $out"
