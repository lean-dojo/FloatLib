#!/usr/bin/env bash

set -euo pipefail

campaign=/efs/robert/floatlean-results/332491fd0acb7702b5730aa96bf5927063583d92/20260910T150728Z/ecosystem
result_name=${RESULT_NAME:-smt-qf-fp-rerun1}
attempt=${ATTEMPT:-1}
result_dir="$campaign/results/$result_name"
work_dir="/work/$result_name"
source_repo=/efs/robert/pde/FloatLibrary
floatlean_revision=332491fd0acb7702b5730aa96bf5927063583d92
jobs=${JOBS:-180}
parallel_runs=${PARALLEL_RUNS:-16}

mkdir -p "$result_dir" "$work_dir"
exec > >(tee "$result_dir/run.log") 2>&1

started=$(date -u +%Y-%m-%dT%H:%M:%SZ)
printf 'suite=smt-qf-fp\nattempt=%s\nstarted=%s\nnode=%s\njobs=%s\nparallel_runs=%s\nfloatlean_revision=%s\n' \
  "$attempt" "$started" "${NODE_NAME:-unknown}" "$jobs" "$parallel_runs" \
  "$floatlean_revision" >"$result_dir/metadata.env"

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
  bash build-essential ca-certificates curl git libgmp-dev parallel python3 z3

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
  tests/LeanFloatTests/Oracle/SMT.lean
  tests/oracles/smt_fp.py
  tests/oracles/smt_fp.sh
  tests/oracles/smt_fp_lakefile.lean
  tests/oracles/smt_fp_test.py
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

python3 -m unittest "$repo/tests/oracles/smt_fp_test.py" \
  |& tee "$result_dir/adapter-unit.log"
bash -n "$repo/tests/oracles/smt_fp.sh"

export LEANFLOAT_BUILD_DIR="$work_dir/lean-build"

# The first edge-only run builds the native runner and checks every fixed
# special-value case. Later runs reuse that executable directly.
"$repo/tests/oracles/smt_fp.sh" \
  --random-per-format 0 \
  --timeout 1800 \
  --results "$result_dir/edge-only" \
  >"$result_dir/edge-only.stdout.json" \
  2>"$result_dir/edge-only.stderr.log"

checker="$LEANFLOAT_BUILD_DIR/bin/smtFpRunner"
test -x "$checker"
runner="$work_dir/prebuilt-smt-runner.sh"
printf '%s\n' \
  '#!/usr/bin/env bash' \
  'set -euo pipefail' \
  'if [[ "${1:-}" == "--lean-runner" ]]; then shift; fi' \
  "exec \"$checker\" \"\$@\"" >"$runner"
chmod +x "$runner"

run_seed() {
  local index=$1
  local seed=$((0x5eed5eed + index + 1))
  local name
  name=$(printf 'seed-%02d' "$index")
  python3 "$repo/tests/oracles/smt_fp.py" \
    --solver z3 \
    --lean-runner "$runner" \
    --seed "$seed" \
    --random-per-format 64 \
    --timeout 1800 \
    --results "$result_dir/$name" \
    >"$result_dir/$name.stdout.json" \
    2>"$result_dir/$name.stderr.log"
}
export -f run_seed
export repo runner result_dir
export SHELL=/bin/bash

seq 0 15 | parallel --jobs "$parallel_runs" --halt now,fail=1 run_seed {}

python3 - "$result_dir" <<'PY'
import json
import sys
from pathlib import Path

root = Path(sys.argv[1])
paths = sorted(root.glob("*/summary.json"))
summaries = [json.loads(path.read_text(encoding="utf-8")) for path in paths]
if len(summaries) != 17:
    raise SystemExit(f"expected 17 summaries, found {len(summaries)}")
count_keys = sorted(
    {key for summary in summaries for key in summary.get("counts", {})}
)
counts = {
    key: sum(int(summary.get("counts", {}).get(key, 0)) for summary in summaries)
    for key in count_keys
}
payload = {
    "adapter": "smt_fp_campaign",
    "status": (
        "pass"
        if all(summary.get("status") == "pass" for summary in summaries)
        else "fail"
    ),
    "runs": len(summaries),
    "sampled_runs": 16,
    "random_per_format_per_sampled_run": 64,
    "counts": counts,
    "summaries": [str(path.relative_to(root)) for path in paths],
}
(root / "aggregate-summary.json").write_text(
    json.dumps(payload, indent=2, sort_keys=True) + "\n",
    encoding="utf-8",
)
print(json.dumps(payload, indent=2, sort_keys=True))
if payload["status"] != "pass":
    raise SystemExit(1)
PY
