#!/usr/bin/env bash

# Require documentation on the stable API and references for each format family.
#
# Lean generates the declaration inventory. Keeping the source list derived from that inventory
# avoids a second handwritten catalog of public declarations.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

if ! command -v rg >/dev/null 2>&1; then
  printf 'public API documentation check failed: ripgrep (rg) is required\n' >&2
  exit 1
fi

# shellcheck source=tests/lib/sources.sh
source "$ROOT/tests/lib/sources.sh"

# shellcheck source=tests/lib/lake.sh
source "$ROOT/tests/lib/lake.sh"

inventory="$(mktemp "${TMPDIR:-/tmp}/floatlib-public-api.XXXXXX.json")"
trap 'rm -f "$inventory"' EXIT

floatlib_test_lake build FloatLib FloatLibTests.Conformance
if ! floatlib_test_lake env lean "$ROOT/tests/checks/PublicAPIInventory.lean" >"$inventory"; then
  printf '%s\n' 'public API inventory generation failed:' >&2
  sed -n '1,240p' "$inventory" >&2
  exit 1
fi

mapfile -t stable_api_files < <(
  python3 - "$inventory" <<'PY'
import json
import pathlib
import sys

# The inventory is one compressed JSON object on a single line. `lake env lean` may print
# warnings around it, so parse only the JSON line rather than the whole stream.
with pathlib.Path(sys.argv[1]).open(encoding="utf-8") as stream:
    json_lines = [line for line in stream if line.startswith("{")]
if len(json_lines) != 1:
    raise SystemExit("public API inventory did not produce exactly one JSON object")
payload = json.loads(json_lines[0])

if payload.get("schemaVersion") != 1:
    raise SystemExit("unexpected public API inventory schema")

declarations = payload.get("declarations")
if not isinstance(declarations, list) or len(declarations) < 100:
    raise SystemExit("public API inventory is unexpectedly small")

names = [entry.get("name") for entry in declarations]
if len(names) != len(set(names)):
    raise SystemExit("public API inventory contains duplicate declaration names")

expected_groups = {
    "core-numerics",
    "verified-kernels",
    "exec-float",
    "configured-binary",
    "descriptor-model-binary",
    "posit",
    "quire",
    "p3109",
    "specialized-formats",
    "interval",
    "validation-only",
    "internal-backend",
}
expected_stability = {"stable", "experimental", "internal"}
for entry in declarations:
    if entry.get("group") not in expected_groups:
        raise SystemExit(f"unexpected API group: {entry!r}")
    if entry.get("stability") not in expected_stability:
        raise SystemExit(f"unexpected API stability: {entry!r}")

modules = {
    entry["module"]
    for entry in declarations
    if entry["exportedFromRoot"] and entry["stability"] == "stable"
}
for module in sorted(modules):
    print(module.replace(".", "/") + ".lean")
PY
)

[[ "${#stable_api_files[@]}" -gt 0 ]] || {
  printf 'no stable public API modules were discovered\n' >&2
  exit 1
}

for path in "${stable_api_files[@]}"; do
  [[ -f "$path" ]] || {
    printf 'stable public API module has no source file: %s\n' "$path" >&2
    exit 1
  }
done

# Any combination of declaration modifiers is accepted before the keyword. `private` is left out on
# purpose: private names are not part of the public API and the Lean inventory above excludes them.
missing_docs="$(
  awk '
    function declaration(line) {
      return line ~ /^[[:space:]]*(@\[[^]]*\][[:space:]]*)*((public|protected|meta|noncomputable|scoped|unsafe|partial|nonrec)[[:space:]]+)*(def|abbrev|structure|class|inductive|theorem|lemma)[[:space:]]+([A-Za-z0-9_?.]+|\$\(Lean\.mkIdent[[:space:]]+`[A-Za-z0-9_?.]+\))/
    }

    FNR == 1 {
      in_comment = 0
      comment_is_doc = 0
      doc_ready = 0
    }

    {
      line = $0

      if (in_comment) {
        if (line ~ /-\//) {
          in_comment = 0
          if (comment_is_doc)
            doc_ready = 1
          comment_is_doc = 0
        }
        next
      }

      if (line ~ /^[[:space:]]*\/-!/) {
        if (line !~ /-\//)
          in_comment = 1
        comment_is_doc = 0
        next
      }

      if (line ~ /^[[:space:]]*\/--/) {
        if (line ~ /-\//)
          doc_ready = 1
        else {
          in_comment = 1
          comment_is_doc = 1
        }
        next
      }

      if (declaration(line)) {
        if (!doc_ready)
          print FILENAME ":" FNR ": undocumented stable declaration: " line
        doc_ready = 0
        next
      }

      if (line ~ /^[[:space:]]*$/ ||
          line ~ /^[[:space:]]*@\[/ ||
          line ~ /^[[:space:]]*--/)
        next

      doc_ready = 0
    }
  ' "${stable_api_files[@]}"
)"

if [[ -n "$missing_docs" ]]; then
  printf '%s\n' "$missing_docs" >&2
  exit 1
fi

mapfile -t family_reference_modules < <(
  floatlib_source_files |
    awk -F/ '$1 == "FloatLib" && $2 == "Floats" && $3 == "Formats" && NF == 4' |
    LC_ALL=C sort
)

for path in "${family_reference_modules[@]}"; do
  rg -q '^## References?$' "$path" || {
    printf 'missing authoritative reference section: %s\n' "$path" >&2
    exit 1
  }
done

printf 'stable public API documentation and provenance checks passed\n'
