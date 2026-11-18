#!/usr/bin/env bash
# Build the FloatLib site end to end.
#
# Three steps, in the order the data flows: export Lean declarations from the built library
# (site/tooling/export.sh, writes site/data/nodes.json), check that every Lean block in the
# chapters compiles and that the chapter files are well formed (site/tooling/check_chapters.py,
# a failing chapter fails the build), then render the reader on local disk
# (site/reader/build.sh). Every step regenerates its outputs from scratch, so running this
# twice gives the same site; nothing is committed. The export first builds its selected imports,
# including the optional APIs that a default library build does not reach, and the chapter check
# builds the modules that the chapters' Lean blocks import.
#
# The figures are prebuilt inputs. The preflight (site/tooling/check_figures.py --fresh)
# regenerates each one in a temporary directory and compares the bytes, rather than trusting
# mtimes copied between machines.
#
# Usage: site/build.sh [--skip-lean] [--skip-check] [--no-compile] [--require-clean]
#   --skip-lean      reuse the local nodes.raw.json instead of rerunning the Lean exporter
#                    (a second instead of a minute; enough after editing prose, titles, or phases
#                    that only rename, not after changing which constants are selected)
#   --skip-check     skip check_chapters.py entirely (only for quick reader iterations)
#   --no-compile     run the chapter checks without compiling the Lean blocks
#   --require-clean  fail when the exported data includes uncommitted library files;
#                    use this for a published build
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
#   FLOATLIB_SITE_JOBS      simultaneous chapter compilers (default: 1)
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
check_args=(--jobs "${FLOATLIB_SITE_JOBS:-1}")
run_check=1
require_clean="${FLOATLIB_SITE_REQUIRE_CLEAN:-0}"
if [[ "${FLOATLIB_SITE_STRICT:-1}" != "0" ]]; then
  check_args+=("--strict")
fi
for arg in "$@"; do
  case "$arg" in
    --skip-lean) export_args+=("--skip-lean") ;;
    --skip-check) run_check=0 ;;
    --no-compile) check_args+=("--no-compile") ;;
    --require-clean) require_clean=1 ;;
    -h|--help) sed -n '2,41p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "build.sh: unknown option $arg" >&2; exit 2 ;;
  esac
done

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

figure_scratch="$(mktemp -d "${FLOATLIB_BUILD_DIR}-site-figures.XXXXXX")"
cleanup_figure_scratch() {
  rm -rf -- "$figure_scratch"
}
trap cleanup_figure_scratch EXIT
python3 "$root/site/tooling/check_figures.py" --fresh --scratch "$figure_scratch"

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

# Published builds require committed sources so GitHub links identify the code used for the export.
dirty_files=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["source"].get("dirtyFiles", 0))' site/data/nodes.json)
if [[ "$dirty_files" != "0" ]]; then
  {
    echo
    echo "WARNING: site/data/nodes.json was exported from a working tree with $dirty_files uncommitted"
    echo "         library files. Exact GitHub links are kept for excerpts that match HEAD."
    echo "         Commit the tree and rebuild before publishing; --require-clean enforces this."
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
