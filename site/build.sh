#!/usr/bin/env bash
# Build the FloatLib site end to end.
#
# Three steps, in the order the data flows: export Lean declarations from the built library
# (site/tooling/export.sh, writes site/data/nodes.json), check that every Lean block in the
# chapters compiles and that the chapter files are well formed (site/tooling/check_chapters.py,
# a failing chapter fails the build), then render the reader on local disk
# (site/reader/build.sh). Every step regenerates its outputs from scratch, so running this
# twice gives the same site; nothing is committed. The export first builds its selected imports,
# including the optional APIs that a default library build does not reach.
#
# Result-derived figures are prebuilt inputs. The preflight regenerates each one in a temporary
# directory and compares the bytes, rather than trusting mtimes copied between machines.
# Result trees are required by default. A developer working only on the reader
# can opt out explicitly with --allow-missing-results.
#
# Usage: site/build.sh [--skip-lean] [--skip-check] [--no-compile]
#                      [--allow-missing-results] [--require-clean]
#   --skip-lean      reuse the local nodes.raw.json instead of rerunning the Lean exporter
#                    (a second instead of a minute; enough after editing prose, titles, or phases
#                    that only rename, not after changing which constants are selected)
#   --skip-check     skip check_chapters.py entirely (only for quick reader iterations)
#   --no-compile     run the chapter checks without compiling the Lean blocks
#   --allow-missing-results
#                    build the reader without checking result-derived figures; development only
#   --require-clean  fail when the exported data was built from a working tree with uncommitted
#                    library files (the site would flag itself as uncommitted on every page and
#                    some GitHub links would be withheld); use this for a build that is published
#
# Environment:
#   FLOATLIB_BUILD_DIR      Lake build directory of the compiled library; when unset, the
#                            default of tests/lib/lake.sh applies (a per-checkout directory
#                            under TMPDIR), the same as every other repository script
#   FLOATLIB_SITE_SCRATCH   where the chapter checker writes its generated Lean files and its
#                            JSON report (default ${FLOATLIB_BUILD_DIR}-site-check)
#   FLOATLIB_SITE_STRICT    check_chapters.py runs with --strict unless this is set to 0, so an
#                            unresolved [[node link]], a nocheck block, or a compiler warning fails
#                            the build the way a failing Lean block does (a result comment that
#                            disagrees with what Lean printed is an error in every mode). Set it
#                            to 0 only while chapters and the node list are being reconciled; the
#                            warnings are always listed in site/data/reader-warnings.md.
#   FLOATLIB_SITE_REQUIRE_CLEAN  set to 1 for the same effect as --require-clean
#   BUILD_DIR, OUT_DIR       forwarded to site/reader/build.sh (local node_modules mirror and
#                            the finished site; defaults: ${FLOATLIB_BUILD_DIR}-site-reader
#                            and ${FLOATLIB_BUILD_DIR}-site)

set -euo pipefail

root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$root"

# tests/lib/lake.sh exports FLOATLIB_BUILD_DIR, honouring a preset value.
source "$root/tests/lib/lake.sh"
export BUILD_DIR="${BUILD_DIR:-${FLOATLIB_BUILD_DIR}-site-reader}"
export PYTHONPYCACHEPREFIX="${PYTHONPYCACHEPREFIX:-${FLOATLIB_BUILD_DIR}-site-pycache}"
scratch="${FLOATLIB_SITE_SCRATCH:-${FLOATLIB_BUILD_DIR}-site-check}"
out_dir="${OUT_DIR:-${FLOATLIB_BUILD_DIR}-site}"

export_args=()
check_args=()
run_check=1
require_clean="${FLOATLIB_SITE_REQUIRE_CLEAN:-0}"
allow_missing_results=0
if [[ "${FLOATLIB_SITE_STRICT:-1}" != "0" ]]; then
  check_args+=("--strict")
fi
for arg in "$@"; do
  case "$arg" in
    --skip-lean) export_args+=("--skip-lean") ;;
    --skip-check) run_check=0 ;;
    --no-compile) check_args+=("--no-compile") ;;
    --allow-missing-results) allow_missing_results=1 ;;
    --require-clean) require_clean=1 ;;
    -h|--help) sed -n '2,34p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "build.sh: unknown option $arg" >&2; exit 2 ;;
  esac
done

if [[ "$require_clean" == "1" && "$allow_missing_results" == "1" ]]; then
  echo "build.sh: --require-clean cannot be combined with --allow-missing-results" >&2
  exit 2
fi

if [[ ! -d "$FLOATLIB_BUILD_DIR/lib" ]]; then
  echo "build.sh: $FLOATLIB_BUILD_DIR has no lib/ directory; build the library first or set FLOATLIB_BUILD_DIR" >&2
  exit 2
fi
for tool in lake python3 node corepack rsync; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    echo "build.sh: $tool is required but not on PATH" >&2
    exit 2
  fi
done

benchmark_result="$root/benchmarks/results/main/release/benchmark"
external_result="$root/tests/results/main/release/external"
ecosystem_result="$root/tests/results/main/ecosystem"
if [[ -d "$benchmark_result" && -d "$external_result" && -d "$ecosystem_result" ]]; then
  result_scratch="$(mktemp -d "${FLOATLIB_BUILD_DIR}-site-results.XXXXXX")"
  cleanup_result_scratch() {
    rm -rf -- "$result_scratch"
  }
  trap cleanup_result_scratch EXIT

  "$root/benchmarks/scripts/verify-main-result.sh"
  "$root/tests/oracles/verify-main-result.sh"

  mkdir -p "$result_scratch/format"
  python3 "$root/site/content/assets/data/plot_format_comparison.py" \
    --out-dir "$result_scratch/format"
  python3 "$root/site/content/assets/figures/ch10_external_ratios.py" \
    --out "$result_scratch/ch10-external-ratios.png"
  python3 "$root/site/content/assets/figures/ch11_universal_preflight.py" \
    --out "$result_scratch/ch11-universal-preflight.png"
  python3 "$root/site/content/assets/figures/ch11_conformance_evidence.py" \
    --out "$result_scratch/ch11-conformance-evidence.png"
  python3 "$root/site/content/assets/figures/ch17_host_vs_software.py" \
    --out "$result_scratch/ch17-host-vs-software.png"

  compare_figure() {
    local retained=$1
    local regenerated=$2
    if ! cmp -s "$retained" "$regenerated"; then
      printf 'build.sh: result-derived figure is stale: %s\n' "$retained" >&2
      return 1
    fi
  }
  compare_figure \
    "$root/site/content/assets/format-comparison-main.png" \
    "$result_scratch/format/format-comparison-main.png"
  compare_figure \
    "$root/site/content/assets/format-comparison-mul-fma.png" \
    "$result_scratch/format/format-comparison-mul-fma.png"
  compare_figure \
    "$root/site/content/assets/format-comparison-div-sqrt.png" \
    "$result_scratch/format/format-comparison-div-sqrt.png"
  compare_figure \
    "$root/site/content/assets/format-comparison-low-width.png" \
    "$result_scratch/format/format-comparison-low-width.png"
  compare_figure \
    "$root/site/content/assets/ch10-external-ratios.png" \
    "$result_scratch/ch10-external-ratios.png"
  compare_figure \
    "$root/site/content/assets/ch11-universal-preflight.png" \
    "$result_scratch/ch11-universal-preflight.png"
  compare_figure \
    "$root/site/content/assets/ch11-conformance-evidence.png" \
    "$result_scratch/ch11-conformance-evidence.png"
  compare_figure \
    "$root/site/content/assets/ch17-host-vs-software.png" \
    "$result_scratch/ch17-host-vs-software.png"
else
  {
    echo "build.sh: retained result trees are not all present:"
    echo "  $benchmark_result"
    echo "  $external_result"
    echo "  $ecosystem_result"
    echo "Figure freshness cannot be checked until those trees exist."
  } >&2
  if [[ "$allow_missing_results" != "1" ]]; then
    echo "build.sh: use --allow-missing-results only for reader development" >&2
    exit 1
  fi
  echo "build.sh: continuing without result checks (--allow-missing-results)" >&2
fi

started=$SECONDS
step() { printf '\n==> %s (%ds elapsed)\n' "$1" "$((SECONDS - started))"; }

step "1/3 export Lean declarations (site/tooling/export.sh ${export_args[*]:-})"
site/tooling/export.sh "${export_args[@]+"${export_args[@]}"}"

if [[ "$require_clean" == "1" ]] && ! python3 -c \
  'import json,sys; sys.exit(json.load(open(sys.argv[1]))["source"]["revision"] is None)' \
  site/data/nodes.json; then
  echo "build.sh: --require-clean set and HEAD has no commit; stopping" >&2
  exit 1
fi

# A build from a dirty tree is fine for iterating and wrong for publishing: every page's footer
# says "plus N uncommitted files" and nodes in changed files lose their exact GitHub links.
dirty_files=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["source"].get("dirtyFiles", 0))' site/data/nodes.json)
if [[ "$dirty_files" != "0" ]]; then
  {
    echo
    echo "WARNING: site/data/nodes.json was exported from a working tree with $dirty_files uncommitted"
    echo "         library files. The site will say so on every page, and declarations in changed"
    echo "         files get a file-level or no GitHub link. Commit the tree and rebuild before"
    echo "         publishing (site/build.sh --require-clean refuses to build in this state)."
    echo
  } >&2
  if [[ "$require_clean" == "1" ]]; then
    echo "build.sh: --require-clean set and the tree is dirty; stopping" >&2
    exit 1
  fi
fi

if (( run_check )); then
  step "2/3 check chapters (site/tooling/check_chapters.py ${check_args[*]:-})"
  mkdir -p "$scratch"
  if ! python3 site/tooling/check_chapters.py --scratch "$scratch" --json "$scratch/report.json" \
       --build-dir "$FLOATLIB_BUILD_DIR" "${check_args[@]+"${check_args[@]}"}"; then
    echo "build.sh: chapter check failed; report in $scratch/report.json" >&2
    exit 1
  fi
else
  step "2/3 check chapters skipped (--skip-check)"
fi

step "3/3 build the reader (site/reader/build.sh)"
OUT_DIR="$out_dir" site/reader/build.sh

step "done"
printf 'site built in %s (%ds)\n' "$out_dir" "$((SECONDS - started))"
if [[ -f "$root/site/data/reader-warnings.md" ]]; then
  printf 'reader warnings: %s\n' "$root/site/data/reader-warnings.md"
fi
if [[ "$dirty_files" != "0" ]]; then
  printf 'note: built from a tree with %s uncommitted library files; not for publishing\n' "$dirty_files"
fi
printf 'serve with:\n  python3 site/serve.py --port 4002 --dir %q\n' "$out_dir"
