#!/usr/bin/env bash

# Verify the checked-in release campaign and the wider external-tool campaign.
#
# The release suites are strict: every conformance row must pass, while the
# transcendental comparison is deliberately observational. The ecosystem
# table is broader. It may retain a qualified or failed upstream experiment,
# but only under an explicit status instead of silently dropping the result.

set -euo pipefail

export LC_ALL=C

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
result="$root/tests/results/main"
release="$result/release"
external="$release/external"
ecosystem="$result/ecosystem"
shared_provenance="$result/provenance"
campaign_provenance="$external/provenance"
manifest_verifier="$root/tests/oracles/verify_result_manifest.py"
generated="$(mktemp -d "${TMPDIR:-/tmp}/floatlib-external-result.XXXXXX")"

cleanup() {
  rm -rf -- "$generated"
}
trap cleanup EXIT

for required in \
  "$result/MANIFEST.tsv" \
  "$release/MANIFEST.tsv" \
  "$external/MANIFEST.tsv" \
  "$external/summary.tsv" \
  "$external/summary.md" \
  "$external/rendering-status.txt" \
  "$external/campaign-duration.png" \
  "$external/campaign-duration.svg" \
  "$external/campaign-duration.pdf" \
  "$shared_provenance/SNAPSHOT.txt" \
  "$campaign_provenance/source-snapshot.txt" \
  "$campaign_provenance/cluster-status.txt" \
  "$campaign_provenance/campaign-status.txt" \
  "$campaign_provenance/run-entrypoint.sh" \
  "$campaign_provenance/conformance-job.yaml" \
  "$ecosystem/MANIFEST.tsv" \
  "$ecosystem/summary.tsv" \
  "$ecosystem/summary.md" \
  "$ecosystem/ecosystem-duration.png" \
  "$ecosystem/ecosystem-duration.svg" \
  "$ecosystem/ecosystem-duration.pdf"; do
  if [[ ! -f "$required" ]]; then
    printf 'missing external result artifact: %s\n' "$required" >&2
    exit 1
  fi
done

packaging_exit_code="$(
  sed -n 's/^packaging_exit_code=//p' \
    "$campaign_provenance/campaign-status.txt"
)"
if [[ ! "$packaging_exit_code" =~ ^[0-9]+$ ]]; then
  printf 'invalid campaign packaging exit code: %s\n' \
    "${packaging_exit_code:-missing}" >&2
  exit 1
fi
if ((packaging_exit_code != 0)) &&
   [[ ! -f "$campaign_provenance/archive-recovery.txt" ]]; then
  printf 'recovered campaign is missing its recovery record: %s\n' \
    "$campaign_provenance/archive-recovery.txt" >&2
  exit 1
fi

python3 "$manifest_verifier" "$result"
python3 "$manifest_verifier" "$release"
python3 "$manifest_verifier" "$external"
python3 "$manifest_verifier" "$ecosystem"
python3 "$root/tests/oracles/verify_campaign_provenance.py" \
  "$shared_provenance" \
  "$campaign_provenance" \
  --run-mode conformance

python3 "$root/tests/oracles/verify_release_evidence.py" \
  "$external" \
  "$ecosystem"

mkdir -p "$generated/release" "$generated/ecosystem"
MPLCONFIGDIR="$generated/matplotlib-release" \
  python3 "$root/tests/oracles/render_release_result.py" \
    "$external/summary.tsv" "$generated/release"
MPLCONFIGDIR="$generated/matplotlib-ecosystem" \
  python3 "$root/tests/oracles/render_ecosystem_result.py" \
    "$ecosystem/summary.tsv" "$generated/ecosystem"

for artifact in \
  summary.md \
  campaign-duration.png \
  campaign-duration.svg \
  campaign-duration.pdf; do
  cmp "$external/$artifact" "$generated/release/$artifact"
done
for artifact in \
  summary.md \
  ecosystem-duration.png \
  ecosystem-duration.svg \
  ecosystem-duration.pdf; do
  cmp "$ecosystem/$artifact" "$generated/ecosystem/$artifact"
done

echo "main external result verified for its measured source snapshots"
