#!/usr/bin/env bash

set -euo pipefail

campaign=/efs/robert/floatlean-results/332491fd0acb7702b5730aa96bf5927063583d92/20260910T150728Z/ecosystem
result_name=${RESULT_NAME:-transcendental-direct-rerun1}
attempt=${ATTEMPT:-1}
result_dir="$campaign/results/$result_name"
work_dir="/work/$result_name"
source_repo=/efs/robert/pde/FloatLibrary
floatlean_revision=332491fd0acb7702b5730aa96bf5927063583d92
core_math_revision=68b034fbe9512781352d28f2dc9795c1686fe8e9
openlibm_revision=5fe399749f9276eaa0b8403e507470da05cbbb3f
rlibm_revision=90431a000071e415abf0f403b6125c385551e346
jobs=${JOBS:-180}

mkdir -p "$result_dir" "$work_dir"
exec > >(tee "$result_dir/run.log") 2>&1

started=$(date -u +%Y-%m-%dT%H:%M:%SZ)
printf 'suite=transcendental-direct\nattempt=%s\nstarted=%s\nnode=%s\njobs=%s\nfloatlean_revision=%s\ncore_math_revision=%s\nopenlibm_revision=%s\nrlibm_revision=%s\n' \
  "$attempt" "$started" "${NODE_NAME:-unknown}" "$jobs" "$floatlean_revision" \
  "$core_math_revision" "$openlibm_revision" "$rlibm_revision" \
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
  bash build-essential ca-certificates curl git libgmp-dev libmpfr-dev \
  make pkg-config python3

curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
  | sh -s -- -y --default-toolchain none
export PATH="/root/.elan/bin:$PATH"

repo="$work_dir/FloatLibrary"
git config --global --add safe.directory "$source_repo"
git config --global --add safe.directory "$source_repo/.git"
git clone --no-hardlinks "$source_repo" "$repo"
git -C "$repo" checkout --detach "$floatlean_revision"
test "$(git -C "$repo" rev-parse HEAD)" = "$floatlean_revision"

overlay_files=(
  tests/LeanFloatTests/Oracle/Transcendentals.lean
  tests/oracles/transcendental_compare.sh
  tests/oracles/transcendental_lakefile.lean
  tests/oracles/transcendental_mpfr.c
  tests/oracles/transcendental_report.py
  tests/oracles/transcendental_test.py
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

core_math="$work_dir/core-math"
openlibm="$work_dir/openlibm"
rlibm="$work_dir/rlibm-all"
git clone --no-tags https://gitlab.inria.fr/core-math/core-math.git "$core_math"
git -C "$core_math" checkout --detach "$core_math_revision"
test "$(git -C "$core_math" rev-parse HEAD)" = "$core_math_revision"
git clone --no-tags https://github.com/JuliaMath/openlibm.git "$openlibm"
git -C "$openlibm" checkout --detach "$openlibm_revision"
test "$(git -C "$openlibm" rev-parse HEAD)" = "$openlibm_revision"
git clone --no-tags https://github.com/rutgers-apl/rlibm-all.git "$rlibm"
git -C "$rlibm" checkout --detach "$rlibm_revision"
test "$(git -C "$rlibm" rev-parse HEAD)" = "$rlibm_revision"

export LEANFLOAT_BUILD_DIR="$work_dir/lean-build"
"$repo/tests/oracles/transcendental_compare.sh" \
  --output-dir "$result_dir/comparison" \
  --random-count 256 \
  --jobs "$jobs" \
  --core-math-root "$core_math" \
  --openlibm-root "$openlibm" \
  --rlibm-root "$rlibm"

test -s "$result_dir/comparison/summary.json"
test -s "$result_dir/comparison/summary.md"
test -s "$result_dir/comparison/details.tsv"
python3 - "$result_dir/comparison/summary.json" <<'PY'
import json
import sys
from pathlib import Path

path = Path(sys.argv[1])
payload = json.loads(path.read_text(encoding="utf-8"))
if payload.get("cases", 0) <= 0:
    raise SystemExit("transcendental comparison produced no cases")
if payload.get("status") != "observational_complete":
    raise SystemExit(f"unexpected comparison status: {payload.get('status')!r}")
if payload.get("conformance") is not False:
    raise SystemExit("transcendental report must explicitly reject a conformance claim")
for provider in payload.get("provider_coverage", []):
    if provider.get("actual_evaluations") != provider.get("expected_evaluations"):
        raise SystemExit(f"incomplete provider coverage: {provider!r}")
print(f"comparison_cases={payload['cases']}")
print("providers=" + ",".join(provider["name"] for provider in payload["providers"]))
PY
