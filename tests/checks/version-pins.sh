#!/usr/bin/env bash

# Keep the Lean toolchain, mathlib dependency, and lockfile on one version line.
#
# A mismatched pin can produce plausible local builds with a different theorem or compiler
# surface, so release checks reject inconsistency rather than selecting whichever dependency
# happens to resolve.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

# shellcheck source=tests/lib/lake.sh
source "$ROOT/tests/lib/lake.sh"

source_only=0
for argument in "$@"; do
  case "$argument" in
    --source-only) source_only=1 ;;
    *)
      printf 'usage: %s [--source-only]\n' "$0" >&2
      exit 2
      ;;
  esac
done

toolchain_ref="$(tr -d '[:space:]' < lean-toolchain)"
if [[ "$toolchain_ref" != leanprover/lean4:v* ]]; then
  printf 'unexpected lean-toolchain reference: %s\n' "$toolchain_ref" >&2
  exit 1
fi

expected_lean_version="${toolchain_ref#leanprover/lean4:v}"
if [[ "$source_only" -eq 0 ]]; then
  actual_lean_version="$(
    floatlib_lake env lean --version |
      sed -n 's/^Lean (version \([^,]*\),.*/\1/p'
  )"
  if [[ "$actual_lean_version" != "$expected_lean_version" ]]; then
    printf 'active Lean is %s; lean-toolchain requires %s\n' \
      "${actual_lean_version:-unknown}" "$expected_lean_version" >&2
    exit 1
  fi
fi

python3 - "$expected_lean_version" <<'PY'
import json
import pathlib
import re
import sys

root = pathlib.Path.cwd()
expected_version = sys.argv[1]
expected_mathlib = f"v{expected_version}"


def dependency_pin(path: pathlib.Path, repository: str) -> str:
    source = path.read_text(encoding="utf-8")
    pattern = rf'"[^"]*{re.escape(repository)}[^"]*"\s*@\s*"(v[^"]+)"'
    match = re.search(pattern, source)
    if match is None:
        raise SystemExit(f"missing {repository} version pin in {path}")
    return match.group(1)


def package(manifest: dict, name: str) -> dict:
    for entry in manifest["packages"]:
        if entry["name"] == name:
            return entry
    raise SystemExit(f"manifest has no {name} package")


def check_package_name(workspace: str, lakefile: str, manifest: dict, expected: str) -> None:
    declared = re.search(r"^package\s+(\w+)\s+where\b", lakefile, re.MULTILINE)
    if declared is None or declared.group(1) != expected or manifest.get("name") != expected:
        raise SystemExit(f"{workspace} lakefile and manifest package must be {expected}")


def check_inherited_dependencies(workspace: str, manifest: dict, root_manifest: dict) -> None:
    for dependency in root_manifest["packages"]:
        inherited = package(manifest, dependency["name"])
        for field in ("type", "url", "rev", "inputRev"):
            if inherited.get(field) != dependency.get(field):
                raise SystemExit(f"{workspace} dependency {dependency['name']} has a stale {field}")


root_mathlib_pin = dependency_pin(root / "lakefile.lean", "mathlib4")
if root_mathlib_pin != expected_mathlib:
    raise SystemExit(
        f"root mathlib pin {root_mathlib_pin} does not match Lean {expected_version}"
    )

root_manifest = json.loads((root / "lake-manifest.json").read_text(encoding="utf-8"))
root_mathlib = package(root_manifest, "mathlib")
check_package_name(
    "root", (root / "lakefile.lean").read_text(encoding="utf-8"), root_manifest, "floatlib"
)

if root_mathlib["inputRev"] != expected_mathlib:
    raise SystemExit("root manifest mathlib revision does not match the lakefile pin")

for workspace in ("benchmarks", "tests"):
    lakefile = (root / workspace / "lakefile.lean").read_text(encoding="utf-8")
    manifest = json.loads(
        (root / workspace / "lake-manifest.json").read_text(encoding="utf-8")
    )
    expected_package = "floatlibTests" if workspace == "tests" else "floatlibBenchmarks"
    check_package_name(workspace, lakefile, manifest, expected_package)
    if not re.search(r'^require\s+floatlib\s+from\s+"\.\."\s*$', lakefile, re.MULTILINE):
        raise SystemExit(f"{workspace} lakefile must require floatlib from the repository root")
    toolchain = root / workspace / "lean-toolchain"
    if toolchain.exists() and toolchain.read_text().strip() != f"leanprover/lean4:v{expected_version}":
        raise SystemExit(f"{workspace} toolchain differs from the root toolchain")
    library = package(manifest, "floatlib")
    if library.get("type") != "path" or library.get("dir") != "..":
        raise SystemExit(f"{workspace} must resolve FloatLib from the repository root")
    if manifest.get("packagesDir") != "../.lake/packages":
        raise SystemExit(f"{workspace} must reuse the root dependency directory")
    check_inherited_dependencies(workspace, manifest, root_manifest)
    if workspace == "benchmarks":
        fixtures = package(manifest, "floatlibTests")
        if fixtures.get("type") != "path" or fixtures.get("dir") != "../tests":
            raise SystemExit("benchmarks must use the local test fixtures")

PY

if [[ "$source_only" -eq 1 ]]; then
  printf '%s\n' 'Source pins checked; active Lean version check skipped.'
fi
printf '%s\n' 'FloatLib version-pin check passed.'
