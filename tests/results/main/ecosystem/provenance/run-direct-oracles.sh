#!/usr/bin/env bash

set -euo pipefail

campaign=/efs/robert/floatlean-results/332491fd0acb7702b5730aa96bf5927063583d92/20260910T150728Z/ecosystem
result_name=${RESULT_NAME:-direct-oracles-rerun1}
work_name=${WORK_NAME:-floatlean-direct-oracles}
attempt=${ATTEMPT:-1}
result_dir="$campaign/results/$result_name"
work_dir="/work/$work_name"
source_repo=/efs/robert/pde/FloatLibrary
floatlean_revision=332491fd0acb7702b5730aa96bf5927063583d92
softposit_revision=17d5628185b31828b10c1f910c9bf65737e83640
ibm_revision=12e883a0c7b826976a8f1243318ac4b7626a0ffc
jobs=${JOBS:-180}
parallel_jobs=${PARALLEL_JOBS:-80}

mkdir -p "$result_dir" "$work_dir"
exec > >(tee "$result_dir/run.log") 2>&1

started=$(date -u +%Y-%m-%dT%H:%M:%SZ)
printf 'suite=direct-oracles\nattempt=%s\nstarted=%s\nnode=%s\njobs=%s\nparallel_jobs=%s\nfloatlean_revision=%s\nsoftposit_revision=%s\nibm_revision=%s\n' \
  "$attempt" "$started" "${NODE_NAME:-unknown}" "$jobs" "$parallel_jobs" \
  "$floatlean_revision" "$softposit_revision" "$ibm_revision" \
  >"$result_dir/metadata.env"

finish() {
  status=$?
  finished=$(date -u +%Y-%m-%dT%H:%M:%SZ)
  printf 'status=%s\nfinished=%s\n' "$status" "$finished" \
    | tee "$result_dir/status.env"
  exit "$status"
}
trap finish EXIT

export DEBIAN_FRONTEND=noninteractive
apt-get update
apt-get install -y --no-install-recommends \
  bash build-essential ca-certificates curl git libgmp-dev parallel python3

curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
  | sh -s -- -y --default-toolchain none
export PATH="/root/.elan/bin:$PATH"

repo="$work_dir/FloatLibrary"
# The EFS checkout is owned by the host user, while benchmark containers run
# as root. Git requires this explicit acknowledgement before using it as a
# local clone source.
git config --global --add safe.directory "$source_repo"
git config --global --add safe.directory "$source_repo/.git"
git clone --no-hardlinks "$source_repo" "$repo"
git -C "$repo" checkout --detach "$floatlean_revision"
test "$(git -C "$repo" rev-parse HEAD)" = "$floatlean_revision"

# Overlay only the reviewed oracle work from the shared checkout. This keeps
# paper/site edits and unrelated worktree state out of the benchmark snapshot.
overlay_files=(
  tests/Oracle.lean
  tests/LeanFloatTests/Oracle/Posit.lean
  tests/LeanFloatTests/Oracle/TestFloat.lean
  tests/oracles/ibm_fpgen.py
  tests/oracles/ibm_fpgen.sh
  tests/oracles/ibm_fpgen_test.py
  tests/oracles/softposit.sh
  tests/oracles/softposit_emitter.c
)
for relative in "${overlay_files[@]}"; do
  test -f "$source_repo/$relative"
  mkdir -p "$(dirname "$repo/$relative")"
  cp "$source_repo/$relative" "$repo/$relative"
done
(
  cd "$source_repo"
  sha256sum "${overlay_files[@]}"
) >"$result_dir/overlay-sha256.txt"
git -C "$repo" diff -- tests/Oracle.lean tests/LeanFloatTests/Oracle/TestFloat.lean \
  >"$result_dir/tracked-overlay.patch"

python3 -m unittest "$repo/tests/oracles/ibm_fpgen_test.py" \
  |& tee "$result_dir/ibm-adapter-unit.log"
bash -n "$repo/tests/oracles/ibm_fpgen.sh"
bash -n "$repo/tests/oracles/softposit.sh"

export LEANFLOAT_BUILD_DIR="$work_dir/lean-build"
# shellcheck source=tests/lib/lake.sh
source "$repo/tests/lib/lake.sh"
leanfloat_test_lake -KmaxJobs="$jobs" build oracle \
  |& tee "$result_dir/lean-build.log"
checker="$(leanfloat_build_path bin/oracle)"
test -x "$checker"

ibm_source="$work_dir/ieee754-test-suite"
git clone --no-tags https://github.com/sergev/ieee754-test-suite.git "$ibm_source"
git -C "$ibm_source" checkout --detach "$ibm_revision"
test "$(git -C "$ibm_source" rev-parse HEAD)" = "$ibm_revision"

softposit_source="$work_dir/SoftPosit"
git clone --no-tags https://gitlab.com/cerlane/SoftPosit.git "$softposit_source"
git -C "$softposit_source" checkout --detach "$softposit_revision"
test "$(git -C "$softposit_source" rev-parse HEAD)" = "$softposit_revision"

softposit_build="$softposit_source/build/Linux-x86_64-GCC"
softposit_objects=(
  s_addMagsPX2.o s_subMagsPX2.o s_mulAddPX2.o
  pX2_add.o pX2_sub.o pX2_mul.o pX2_div.o pX2_mulAdd.o
  pX2_roundToInt.o pX2_sqrt.o pX2_eq.o pX2_le.o pX2_lt.o
  s_addMagsP32.o s_subMagsP32.o s_mulAddP32.o
  p32_add.o p32_sub.o p32_mul.o p32_div.o p32_mulAdd.o
  p32_roundToInt.o p32_sqrt.o p32_eq.o p32_le.o p32_lt.o
)
make -C "$softposit_build" --no-print-directory \
  -j"$jobs" COMPILER="${CXX:-c++}" "${softposit_objects[@]}" \
  |& tee "$result_dir/softposit-build.log"
"${CC:-cc}" -O2 -DSOFTPOSIT_FAST_INT64 \
  -I"$softposit_build" \
  -I"$softposit_source/source/8086-SSE" \
  -I"$softposit_source/source/include" \
  -c "$softposit_source/source/s_approxRecipSqrt_1Ks.c" \
  -o "$softposit_build/s_approxRecipSqrt_1Ks.o"
softposit_objects+=(s_approxRecipSqrt_1Ks.o)
ar crs "$softposit_build/softposit-oracle.a" \
  "${softposit_objects[@]/#/$softposit_build/}"

emitter="$work_dir/softposit-emitter"
"${CXX:-c++}" -x c++ -O3 -std=c++20 -Wall -Wextra -Werror \
  -I"$softposit_source/source/include" \
  -c "$repo/tests/oracles/softposit_emitter.c" \
  -o "$work_dir/softposit-emitter.o"
"${CXX:-c++}" "$work_dir/softposit-emitter.o" \
  "$softposit_build/softposit-oracle.a" -lm -o "$emitter"

# IBM is small enough to run beside the posit matrix after the shared Lean
# build. Its driver records every generated stream and source map on EFS.
set +e
LEANFLOAT_BUILD_DIR="$LEANFLOAT_BUILD_DIR" \
  "$repo/tests/oracles/ibm_fpgen.sh" \
    --suite "$ibm_source" \
    --results "$result_dir/ibm" \
    --reports 20 \
    >"$result_dir/ibm-driver.log" 2>&1 &
ibm_pid=$!
set -e

operations=(add sub mul div fma sqrt rint eq le lt)
spec_body="$result_dir/softposit-specs.body.tsv"
spec_table="$result_dir/softposit-specs.tsv"
printf 'id\tfamily\tbits\toperation\tmode\trequested\tseed\texpectation\n' >"$spec_table"
: >"$spec_body"

operation_index=0
for operation in "${operations[@]}"; do
  operation_index=$((operation_index + 1))
  for bits in $(seq 2 8); do
    id=$(printf 'px2-b%02d-%s-exhaustive' "$bits" "$operation")
    seed=$((0x4f1b0000 + bits * 32 + operation_index))
    printf '%s\tpx2\t%s\t%s\texhaustive\t0\t%s\tgate\n' \
      "$id" "$bits" "$operation" "$seed" | tee -a "$spec_body" >>"$spec_table"
  done
  for bits in $(seq 9 31); do
    id=$(printf 'px2-b%02d-%s-sampled' "$bits" "$operation")
    seed=$((0x4f1b0000 + bits * 32 + operation_index))
    printf '%s\tpx2\t%s\t%s\tsampled\t100000\t%s\tgate\n' \
      "$id" "$bits" "$operation" "$seed" | tee -a "$spec_body" >>"$spec_table"
  done
  id=$(printf 'p32-b32-%s-sampled' "$operation")
  seed=$((0x4f1b0000 + 32 * 32 + operation_index))
  printf '%s\tp32\t32\t%s\tsampled\t1000000\t%s\tgate\n' \
    "$id" "$operation" "$seed" | tee -a "$spec_body" >>"$spec_table"
  id=$(printf 'px2-b32-%s-diagnostic' "$operation")
  printf '%s\tpx2\t32\t%s\tsampled\t1000000\t%s\tdiagnostic\n' \
    "$id" "$operation" "$seed" | tee -a "$spec_body" >>"$spec_table"
done

mkdir -p "$result_dir/softposit-runs"

run_one() {
  local id=$1
  local family=$2
  local bits=$3
  local operation=$4
  local mode=$5
  local requested=$6
  local seed=$7
  local expectation=$8
  local run_dir="$result_dir/softposit-runs/$id"
  local emitter_status oracle_status result
  local -a arguments=(--bits "$bits" --op "$operation" --family "$family")

  mkdir -p "$run_dir"
  if [[ "$mode" == exhaustive ]]; then
    arguments+=(--exhaustive)
  else
    arguments+=(--sampled "$requested" --seed "$seed")
  fi

  set +e
  "$emitter" "${arguments[@]}" 2>"$run_dir/emitter.log" \
    | "$checker" posit 5 >"$run_dir/oracle.log" 2>&1
  pipeline_status=("${PIPESTATUS[@]}")
  set -e
  emitter_status=${pipeline_status[0]}
  oracle_status=${pipeline_status[1]}
  if [[ "$emitter_status" -eq 0 && "$oracle_status" -eq 0 ]]; then
    result=pass
  else
    result=fail
  fi
  printf 'family=%s\nbits=%s\noperation=%s\nmode=%s\nrequested=%s\nseed=%s\nexpectation=%s\nemitter_status=%s\noracle_status=%s\nresult=%s\n' \
    "$family" "$bits" "$operation" "$mode" "$requested" "$seed" \
    "$expectation" "$emitter_status" "$oracle_status" "$result" \
    >"$run_dir/status.env"
  printf '%-36s %s\n' "$id" "$result"
}
export -f run_one
export checker emitter result_dir
export SHELL=/bin/bash

parallel --jobs "$parallel_jobs" --line-buffer --colsep '\t' \
  'run_one {1} {2} {3} {4} {5} {6} {7} {8}' \
  :::: "$spec_body" | tee "$result_dir/softposit-progress.log"

softposit_summary="$result_dir/softposit-summary.tsv"
printf 'id\tfamily\tbits\toperation\tmode\trequested\texpectation\tresult\temitter_status\toracle_status\tcases\tmismatches\tprotocol_errors\tpadding_errors\n' \
  >"$softposit_summary"
softposit_gate_failed=0
while IFS=$'\t' read -r id family bits operation mode requested seed expectation; do
  # shellcheck disable=SC1090
  source "$result_dir/softposit-runs/$id/status.env"
  oracle_line=$(grep '^RESULT oracle=softposit ' \
    "$result_dir/softposit-runs/$id/oracle.log" | tail -1 || true)
  emitter_line=$(grep '^RESULT emitter=softposit ' \
    "$result_dir/softposit-runs/$id/emitter.log" | tail -1 || true)
  cases=$(sed -n 's/.* cases=\([0-9][0-9]*\).*/\1/p' <<<"$oracle_line")
  mismatches=$(sed -n 's/.* mismatches=\([0-9][0-9]*\).*/\1/p' <<<"$oracle_line")
  protocol_errors=$(sed -n 's/.* protocol_errors=\([0-9][0-9]*\).*/\1/p' <<<"$oracle_line")
  padding_errors=$(sed -n 's/.* padding_errors=\([0-9][0-9]*\).*/\1/p' <<<"$emitter_line")
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$id" "$family" "$bits" "$operation" "$mode" "$requested" \
    "$expectation" "$result" "$emitter_status" "$oracle_status" \
    "${cases:-0}" "${mismatches:-0}" "${protocol_errors:-0}" \
    "${padding_errors:-0}" >>"$softposit_summary"
  if [[ "$expectation" == gate && "$result" != pass ]]; then
    softposit_gate_failed=1
  fi
done <"$spec_body"

set +e
wait "$ibm_pid"
ibm_status=$?
set -e

awk -F '\t' '
  NR > 1 {
    tests += 1
    cases += $11
    mismatches += $12
    protocol += $13
    padding += $14
    if ($7 == "gate") {
      gate_tests += 1
      if ($8 == "pass") gate_pass += 1
    } else {
      diagnostic_tests += 1
      if ($8 == "pass") diagnostic_pass += 1
    }
  }
  END {
    printf "tests=%d\ncases=%d\nmismatches=%d\nprotocol_errors=%d\npadding_errors=%d\n", \
      tests, cases, mismatches, protocol, padding
    printf "gating_tests=%d\ngating_pass=%d\ndiagnostic_tests=%d\ndiagnostic_pass=%d\n", \
      gate_tests, gate_pass, diagnostic_tests, diagnostic_pass
  }
' "$softposit_summary" >"$result_dir/softposit-totals.env"

printf 'ibm_status=%s\nsoftposit_gate_failed=%s\n' \
  "$ibm_status" "$softposit_gate_failed" >"$result_dir/component-status.env"
cat "$result_dir/softposit-totals.env"
printf 'IBM status: %s\n' "$ibm_status"

if [[ "$ibm_status" -ne 0 || "$softposit_gate_failed" -ne 0 ]]; then
  exit 1
fi
