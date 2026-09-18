#!/usr/bin/env bash

# Rebuild the public benchmark tables and figures from the checked-in raw trials.
#
# The manifests cover the retained measurements and the figures rendered with
# the current project name. The source capture keeps its original hashes.

set -euo pipefail

export LC_ALL=C

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
result="$root/benchmarks/results/main"
release="$result/release"
benchmark="$release/benchmark"
plots="$benchmark/plots"
shared_provenance="$result/provenance"
campaign_provenance="$release/provenance"
generated="$(mktemp -d "${TMPDIR:-/tmp}/floatlib-main-result.XXXXXX")"

cleanup() {
  rm -rf -- "$generated"
}
trap cleanup EXIT

for required in \
  "$result/MANIFEST.tsv" \
  "$release/MANIFEST.tsv" \
  "$benchmark/MANIFEST.tsv" \
  "$benchmark/metadata.txt" \
  "$benchmark/raw" \
  "$plots/summary.csv" \
  "$plots/ratios.csv" \
  "$plots/backend-regimes.csv" \
  "$benchmark/environment/binary-agreement.txt" \
  "$benchmark/environment/backend-selection.csv" \
  "$benchmark/environment/lscpu.txt" \
  "$shared_provenance/SNAPSHOT.txt" \
  "$campaign_provenance/source-snapshot.txt" \
  "$campaign_provenance/source-files.sha256" \
  "$campaign_provenance/worktree-status.txt" \
  "$campaign_provenance/worktree.patch" \
  "$campaign_provenance/cluster-status.txt" \
  "$campaign_provenance/campaign-status.txt" \
  "$campaign_provenance/run-entrypoint.sh" \
  "$campaign_provenance/benchmark-job.yaml"; do
  if [[ ! -e "$required" ]]; then
    printf 'missing benchmark result artifact: %s\n' "$required" >&2
    exit 1
  fi
done

if ! command -v python3 >/dev/null; then
  echo "Python 3 is required to verify the benchmark result" >&2
  exit 1
fi
if ! python3 -c 'import matplotlib' >/dev/null 2>&1; then
  echo "Matplotlib is required to regenerate the benchmark figures" >&2
  exit 1
fi

manifest_verifier="$root/tests/oracles/verify_result_manifest.py"
python3 "$manifest_verifier" "$result"
python3 "$manifest_verifier" "$release"
python3 "$manifest_verifier" "$benchmark"
python3 "$root/tests/oracles/verify_campaign_provenance.py" \
  "$shared_provenance" \
  "$campaign_provenance" \
  --run-mode benchmark

for key in run_exit_code packaging_exit_code final_exit_code; do
  value="$(
    sed -n "s/^${key}=//p" "$campaign_provenance/campaign-status.txt"
  )"
  if [[ "$value" != 0 ]]; then
    printf 'benchmark campaign %s is not zero: %s\n' \
      "$key" "${value:-missing}" >&2
    exit 1
  fi
done
python3 "$root/benchmarks/scripts/verify_release_matrix.py" "$benchmark"

# The matrix verifier checks this too. Keeping the publication gate here makes
# an unpinned result fail before we spend time rebuilding the figures.
benchmark_cpu="$(sed -n 's/^benchmarkCPU=//p' "$benchmark/metadata.txt")"
if [[ ! "$benchmark_cpu" =~ ^[0-9]+$ ]]; then
  printf 'publication benchmark is not pinned to one CPU: %s\n' \
    "${benchmark_cpu:-missing}" >&2
  exit 1
fi

snapshot_commit="$(
  sed -n 's/^head_revision=//p' "$shared_provenance/SNAPSHOT.txt"
)"
benchmark_commit="$(sed -n 's/^gitCommit=//p' "$benchmark/metadata.txt")"
if [[ -z "$snapshot_commit" ||
      "$snapshot_commit" == *$'\n'* ||
      "$benchmark_commit" != "$snapshot_commit" ]]; then
  printf 'benchmark revision does not match its source capture: %s != %s\n' \
    "$benchmark_commit" "$snapshot_commit" >&2
  exit 1
fi

python_has_fma="$(sed -n 's/^pythonHasMathFma=//p' "$benchmark/metadata.txt")"
include_softfloat="$(sed -n 's/^includeSoftFloat=//p' "$benchmark/metadata.txt")"
include_python="$(sed -n 's/^includePython=//p' "$benchmark/metadata.txt")"
agreement_iterations="$(
  sed -n 's/^agreementIterations=//p' "$benchmark/metadata.txt"
)"

# Historical Flocq used unmatched exponent ranges and no agreement prefix.
# Its raw rows and original receipt remain authenticated by the manifests above.
# The matrix verifier requires exactly 84 Flocq rows in each historical trial.
# Exclude it only from this recheck; new campaigns retain the strict Flocq gate.
agreement_raw="$generated/agreement-raw"
python3 - "$benchmark/raw" "$agreement_raw" <<'PY'
import csv
import sys
from pathlib import Path

source, target = map(Path, sys.argv[1:])
target.mkdir()
for trial in sorted(source.glob("trial-*.csv")):
    with trial.open(newline="", encoding="utf-8") as stream:
        reader = csv.DictReader(stream)
        with (target / trial.name).open("w", newline="", encoding="utf-8") as output:
            writer = csv.DictWriter(
                output, fieldnames=reader.fieldnames, lineterminator="\n"
            )
            writer.writeheader()
            for row in reader:
                if row["implementation"] == "Flocq":
                    agreement = tuple(
                        row[field] for field in (
                            "agreementIterations",
                            "agreementSink",
                            "agreementFixtureTraceDigest",
                        )
                    )
                    if agreement != ("0", "0", "0"):
                        raise SystemExit(
                            f"refusing to exclude Flocq row in {trial.name} at "
                            f"{row['totalBits']}/{row['operation']}: expected "
                            f"zero agreement fields, got {agreement!r}"
                        )
                    continue
                writer.writerow(row)
PY

python3 "$root/benchmarks/scripts/verify_binary_agreement.py" \
  "$agreement_raw" \
  "$generated/binary-agreement.txt" \
  --softfloat "$include_softfloat" \
  --python "$include_python" \
  --python-has-fma "$python_has_fma" \
  --flocq 0 \
  --trials 9 \
  --agreement-iterations "$agreement_iterations" \
  --widths 4 5 6 7 8 16 32 64 128 256 512 1024 2048 4096
# The historical receipt describes its old protocol; do not byte-compare that
# text with the current verifier's report.

python3 "$root/benchmarks/plots/format_comparison.py" \
  "$benchmark/raw" "$generated"

for artifact in summary.csv ratios.csv backend-regimes.csv; do
  cmp "$plots/$artifact" "$generated/$artifact"
done

expected_matplotlib="$(
  sed -n 's/^matplotlibVersion=//p' "$benchmark/metadata.txt"
)"
current_matplotlib="$(python3 -c 'import matplotlib; print(matplotlib.__version__)')"
if [[ -z "$expected_matplotlib" || "$expected_matplotlib" == *$'\n'* ]]; then
  echo "benchmark metadata does not name one Matplotlib version" >&2
  exit 1
fi

if [[ "$expected_matplotlib" == "$current_matplotlib" ]]; then
  for artifact in \
    format-comparison.png format-comparison.svg format-comparison.pdf; do
    cmp "$plots/$artifact" "$generated/$artifact"
  done
else
  # The CSV tables are the benchmark result. Matplotlib does not promise
  # byte- or pixel-stable output across releases, even when those tables and
  # plotting instructions are unchanged. The retained manifest authenticates
  # the published figures; with another renderer version we only require that
  # all three figures regenerate successfully from the verified tables.
  for artifact in \
    format-comparison.png format-comparison.svg format-comparison.pdf; do
    if [[ ! -s "$generated/$artifact" ]]; then
      printf 'regenerated benchmark figure is empty: %s\n' \
        "$generated/$artifact" >&2
      exit 1
    fi
  done
  printf \
    'benchmark tables reproduced; figure bytes were not compared across Matplotlib %s and %s\n' \
    "$expected_matplotlib" "$current_matplotlib" >&2
fi

echo "main benchmark result verified for its measured source snapshot"
