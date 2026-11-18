#!/usr/bin/env bash
# One benchmark suite for both modes: Lean's kernel (proofs) and compiled code.
#
# usage: benchmarks/suite/run.sh OUT [SECTION...]
#
# OUT is a directory for logs, tables and figures (created if missing, outside the checkout).
# Sections, in the order of `all` (the default):
#
#   kernel-binary   microseconds of kernel time per operation in the binary formats of 8 to
#                   4,096 bits and two custom layouts (benchmarks/kernel/run.sh kernel)
#   matched         five loops of 100 or 10 operations per binary format in Lean's kernel, as
#                   `float_decide` rewrites them (matched.py, `#kernel_cost rewritten`)
#   flocq           the same loops in Coq 8.20.1 with Flocq 4.2.2, with `vm_compute` and with
#                   `lazy`, in the Docker image SUITE_FLOCQ_IMAGE (default
#                   leanfloat-flocq-bench:4.2.2), one container at a time with
#                   `--memory=8g --cpus=2`. The section refuses to start while another
#                   container is running.
#   families        kernel time of one operation in fixed point, logarithmic, P3109, posit,
#                   decimal and MX element formats, as written and with the tagged kernel
#                   rules (Families.lean)
#   exhaustive      statements about all 65,536 pairs of encodings: the loop of `float_decide`
#                   (benchmarks/kernel/Exhaustive.lean) and one run on all lanes
#                   (`lane_decide`, Lanes.lean), and the build of one packed table
#   compiled        nanoseconds per compiled operation at 17 significand precisions from 2 to
#                   4,096 bits (execFloatSweep), FP8 and posit kernels (execFloatFP8Bench,
#                   benchmarks/scripts/posit.sh), and FloatLib next to MPFR and Berkeley SoftFloat
#                   (benchmarks/scripts/format-comparison.sh, one development trial; set
#                   SUITE_COMPARISON=0 to skip it)
#   tables          README.md in OUT with every table, from the logs that are present
#
# The figures are drawn by benchmarks/plots/figures.py, whose timing mode starts these sections.
#
# SUITE_FORMATS selects the binary formats of `kernel-binary`, SUITE_MATCHED those of `matched`
# and `flocq`. Every number is a time on this machine at this commit: read the tables as ratios.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
root="$(cd "$here/../.." && pwd)"
source "$root/tests/lib/lake.sh"

out="${1:?output directory}"
shift
sections=("$@")
if [[ ${#sections[@]} -eq 0 || "${sections[0]}" == all ]]; then
  sections=(kernel-binary matched flocq families exhaustive compiled tables)
fi
mkdir -p "$out"
out="$(cd "$out" && pwd)"
cd "$root"

binary_formats="${SUITE_FORMATS:-e4m3 e5m2 binary16 e8f15 binary32 binary64 e15f64 binary128 binary256 binary512 binary1024 binary4096}"
matched_formats="${SUITE_MATCHED:-binary32 binary64 binary128 binary256 binary512 binary1024 binary4096}"
flocq_image="${SUITE_FLOCQ_IMAGE:-leanfloat-flocq-bench:4.2.2}"

lean_file() { # FILE LOG [SECONDS]: run lean on a file inside the library's environment
  floatlib_lake env timeout --kill-after=10 "${3:-1800}" lean "$1" > "$2" 2>&1 || true
}

for section in "${sections[@]}"; do
  echo "== $section"
  case "$section" in
    kernel-binary)
      # shellcheck disable=SC2086
      KERNEL_BENCH_OUT="$out/kernel-binary" benchmarks/kernel/run.sh kernel 8 3 $binary_formats \
        > "$out/kernel-binary.out" 2>&1
      tail -n 3 "$out/kernel-binary.out" ;;
    matched)
      # shellcheck disable=SC2086
      python3 -I "$here/matched.py" gen "$out/matched" $matched_formats
      for format in $matched_formats; do
        lean_file "$out/matched/lean/Matched_$format.lean" "$out/matched/lean/Matched_$format.log"
      done ;;
    flocq)
      # shellcheck disable=SC2086
      [[ -d "$out/matched/flocq" ]] || python3 -I "$here/matched.py" gen "$out/matched" $matched_formats
      if [[ -n "$(docker ps -q)" ]]; then
        echo "another container is running: the flocq section is skipped" >&2
        continue
      fi
      for format in $matched_formats; do
        for strategy in vm lazy; do
          # The sources are mounted read-only and compiled in the container's own directory.
          timeout 1800 docker run --rm --memory=8g --memory-swap=8g --cpus=2 \
            -v "$out/matched/flocq:/work:ro" "$flocq_image" \
            bash -lc "cp /work/${format}_$strategy.v /tmp/ && cd /tmp && coqc ${format}_$strategy.v" \
            > "$out/matched/flocq/${format}_$strategy.log" 2>&1 ||
            echo "$format $strategy: exit $?" >> "$out/matched/flocq/status"
        done
      done ;;
    families)
      lean_file "$here/Families.lean" "$out/families.log" ;;
    exhaustive)
      floatlib_lake env timeout --kill-after=10 1800 lean -Dprofiler=true \
        -Dprofiler.threshold=100 "$root/benchmarks/kernel/Exhaustive.lean" \
        > "$out/exhaustive-loop.log" 2>&1 || true
      floatlib_lake env timeout --kill-after=10 1800 lean -Dprofiler=true \
        -Dprofiler.threshold=100 "$here/Lanes.lean" > "$out/exhaustive-lanes.log" 2>&1 || true ;;
    compiled)
      mkdir -p "$out/compiled"
      BENCH_ITERATIONS="${SUITE_ITERATIONS:-2000}" floatlib_benchmark_lake exe execFloatSweep all \
        > "$out/compiled/sweep.log" 2>&1 || true
      floatlib_benchmark_lake exe execFloatFP8Bench > "$out/compiled/fp8.log" 2>&1 || true
      rm -rf "$out/compiled/posit"
      benchmarks/scripts/posit.sh "${SUITE_POSIT_RUNS:-9}" "$out/compiled/posit" \
        > "$out/compiled/posit.log" 2>&1 || true
      if [[ "${SUITE_COMPARISON:-1}" == 1 ]]; then
        rm -rf "$out/compiled/comparison"
        FORMAT_COMPARE_DEVELOPMENT_ONLY=1 FORMAT_COMPARE_INCLUDE_UNIVERSAL=0 \
          FORMAT_COMPARE_INCLUDE_PYTHON=0 \
          benchmarks/scripts/format-comparison.sh 1 "$out/compiled/comparison" \
          > "$out/compiled/comparison.log" 2>&1 || true
      fi ;;
    tables)
      python3 -I "$here/tables.py" "$out" ;;
    *) echo "unknown section $section" >&2; exit 2 ;;
  esac
done
