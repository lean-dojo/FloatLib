#!/usr/bin/env bash
# Build the FloatLib reader in a separate build directory.
#
# Mirror site/reader to the build directory, install dependencies and build there, then copy
# the finished static site to the output directory. The data step reads site/data/nodes.json
# and site/content from the source tree through FLOATLIB_SITE_ROOT.
#
# Usage: site/reader/build.sh            (from anywhere)
#   BUILD_DIR   override the build directory (default: ${FLOATLIB_BUILD_DIR}-site-reader)
#   OUT_DIR     override the output directory (default: ${FLOATLIB_BUILD_DIR}-site)
#               FLOATLIB_BUILD_DIR comes from tests/lib/lake.sh when unset.

set -euo pipefail

reader_src=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
site_root=$(cd "$reader_src/.." && pwd)
repo_root=$(cd "$site_root/.." && pwd)
if [[ -z "${BUILD_DIR:-}" || -z "${OUT_DIR:-}" ]]; then
  source "$repo_root/tests/lib/lake.sh"
fi
build_dir="${BUILD_DIR:-${FLOATLIB_BUILD_DIR}-site-reader}"
out_dir="${OUT_DIR:-${FLOATLIB_BUILD_DIR}-site}"

export COREPACK_ENABLE_DOWNLOAD_PROMPT=0
export FLOATLIB_SITE_ROOT=$site_root

echo "reader: mirroring $reader_src to $build_dir"
mkdir -p "$build_dir"
rsync -a --delete --exclude node_modules --exclude dist --exclude public "$reader_src/" "$build_dir/"

cd "$build_dir"
if ! command -v corepack >/dev/null 2>&1; then
  echo "reader: corepack is required; install it before building the reader" >&2
  exit 1
fi
echo "reader: installing dependencies"
if [[ ! -f pnpm-lock.yaml ]]; then
  echo "reader: the committed pnpm-lock.yaml is required" >&2
  exit 1
fi
corepack pnpm install --frozen-lockfile

echo "reader: building"
corepack pnpm build

echo "reader: copying to $out_dir"
mkdir -p "$out_dir"
rsync -a --delete "$build_dir/dist/" "$out_dir/"
if [[ -d "$site_root/content/assets" ]]; then
  mkdir -p "$out_dir/assets"
  # The reader publishes rendered artifacts, not the machinery or private inputs used to
  # produce them. Keep images and hand-written document assets while leaving plotting scripts,
  # Python caches, and retained working data out of the static site.
  rsync -a \
    --exclude '*.py' \
    --exclude '__pycache__/' \
    --exclude 'data/' \
    "$site_root/content/assets/" "$out_dir/assets/"
fi
printf 'reader: done; serve with: python3 %q --port 10000 --dir %q\n' "$site_root/serve.py" "$out_dir"
