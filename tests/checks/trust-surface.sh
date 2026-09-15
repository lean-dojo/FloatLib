#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"

# shellcheck source=tests/lib/sources.sh
source "$root/tests/lib/sources.sh"

# shellcheck source=tests/lib/lake.sh
source "$root/tests/lib/lake.sh"

source_only=0
case "${1:-}" in
  "") ;;
  --source-only) source_only=1 ;;
  *)
    printf 'usage: %s [--source-only]\n' "$0" >&2
    exit 2
    ;;
esac

# Reuse source discovery for all Lean entry points, including benchmark and site tools.
mapfile -t trust_sources < <(
  floatlib_lean_files FloatLib.lean FloatLib tests benchmarks site
)

python3 - "${trust_sources[@]}" <<'PYTHON'
from bisect import bisect_right
from collections import Counter, defaultdict
from pathlib import Path
import re
import sys

# Native evaluation admits compiler results through axioms. Keep exact per-file counts so that
# adding another use to an approved file still fails. These five entries total 48 sites.
allowed_native = {
    "tests/FloatLibTests/Conformance/Formats/Configured.lean": 2,
    "tests/FloatLibTests/Conformance/Formats/Conversion.lean": 10,
    "tests/FloatLibTests/Conformance/Formats/LowBit.lean": 4,
    "tests/FloatLibTests/Conformance/P3109/Projection.lean": 18,
    "tests/FloatLibTests/Conformance/Posit/ExecutionBoundaries.lean": 14,
}
# Replacements are invisible to collectAxioms. The sole approved implementation replaces
# toDyadic?; its equality theorem follows it in the same file.
allowed_replacements = {"FloatLib/Floats/Formats/Posit/Model/Decode.lean": 1}
# The inspection command evaluates a closed String in MetaM. The site exporter loads a Lean
# environment with initializers enabled. Neither is a numerical implementation or a proof.
allowed_unsafe = {
    "FloatLib/Floats/ExecFloat/Info/Inspection.lean": 1,
    "site/tooling/ExportNodes.lean": 1,
}
# The explicit host boundary is used by native conformance, code generation, and site export.
allowed_imports = {
    "benchmarks/lean/FloatLibBenchmarks/Codegen/ConfiguredBinary.lean": 1,
    "tests/FloatLibTests/Conformance/BinaryInterchange/NativeExecution.lean": 1,
    "site/tooling/ExportNodes.lean": 1,
}
unchecked_module = "FloatLib.Floats.Formats.BinaryInterchange.Configured.NativeFPU.Unchecked"
raw_pattern = re.compile(r'r(#*)"')
char_pattern = re.compile(r"'(?:\\(?:u[0-9a-fA-F]{4}|x[0-9a-fA-F]{2}|.)|[^'\\\n])'")
word_pattern = re.compile(r"[\w'!?]+")


def mask_lean(source):
    """Blank comments/literal text without moving offsets or newlines; retain interpolation holes."""
    masked = list(source)

    def blank(start, end):
        for pos in range(start, end):
            if source[pos] != "\n":
                masked[pos] = " "

    def string(start):
        blank(start, start + 1)
        pos = start + 1
        while pos < len(source):
            if source[pos] == '"':
                blank(pos, pos + 1)
                return pos + 1
            if source[pos] == "\\":
                end = min(pos + 2, len(source))
                blank(pos, end)
                pos = end
            elif source[pos] == "{":
                # Bare strings can be interpolated by Lean syntax (e.g. throwError). Treat all
                # brace holes conservatively as code, including nested strings and comments.
                pos = code(pos + 1, braces=1)
            else:
                blank(pos, pos + 1)
                pos += 1
        raise ValueError(f"unterminated string at offset {start}")

    def code(pos, braces=0):
        while pos < len(source):
            start = pos
            if source.startswith("--", pos):
                end = source.find("\n", pos)
                pos = len(source) if end < 0 else end
                blank(start, pos)
            elif source.startswith("/-", pos):
                depth = 1
                pos += 2
                while pos < len(source) and depth:
                    if source.startswith("/-", pos):
                        depth += 1
                        pos += 2
                    elif source.startswith("-/", pos):
                        depth -= 1
                        pos += 2
                    else:
                        pos += 1
                if depth:
                    raise ValueError(f"unterminated comment at offset {start}")
                blank(start, pos)
            elif source[pos] == "r" and (raw := raw_pattern.match(source, pos)):
                # Raw literals close with the opening number of hashes; escapes do not apply.
                closer = '"' + raw[1]
                end = source.find(closer, raw.end())
                if end < 0:
                    raise ValueError(f"unterminated raw string at offset {start}")
                pos = end + len(closer)
                blank(start, pos)
            elif source[pos] == '"':
                pos = string(pos)
            elif source[pos] == "'" and (char := char_pattern.match(source, pos)):
                pos = char.end()
                blank(start, pos)
            elif source[pos] == "«":
                end = source.find("»", pos + 1)
                if end < 0:
                    raise ValueError(f"unterminated quoted identifier at offset {start}")
                pos = end + 1
            elif word := word_pattern.match(source, pos):
                # Skip whole identifiers, including primes, so an internal r or apostrophe
                # cannot be mistaken for the start of a literal.
                pos = word.end()
            else:
                if braces:
                    if source[pos] == "{":
                        braces += 1
                    elif source[pos] == "}":
                        braces -= 1
                        if not braces:
                            return pos + 1
                pos += 1
        if braces:
            raise ValueError("unterminated interpolation hole")
        return pos

    code(0)
    return "".join(masked)


def decide_native(words, start):
    """Scan only adjacent config items, not Lean terms or tactic elaboration."""
    pos = start + 1
    native = False
    while pos < len(words):
        if words[pos] in {"+", "-"} and pos + 1 < len(words):
            native |= words[pos:pos + 2] == ["+", "native"]
            pos += 2
        elif pos + 2 < len(words) and words[pos] == "(" and words[pos + 2] == ":=":
            name = words[pos + 1]
            end, depth = pos + 3, 1
            while end < len(words) and depth:
                depth += (words[end] == "(") - (words[end] == ")")
                end += 1
            if depth:
                raise ValueError("unterminated decide configuration")
            # Any whole config may compute native=true. Do not try to evaluate it here.
            # Likewise, only the literal false is accepted for an explicit native field.
            native |= name == "config" or (
                name == "native" and words[pos + 3:end - 1] != ["false"])
            pos = end
        else:
            break
    return native


def aesop_rule_safety(words, index):
    """The safety marker in an Aesop attribute controls search, not Lean's trust boundary."""
    return index >= 3 and words[index - 3:index] in (
        ["attribute", "[", "aesop"],
        ["@", "[", "aesop"],
    )


native_sites, replacement_sites, unsafe_sites, import_sites = (
    defaultdict(list) for _ in range(4)
)
errors = []
token_pattern = re.compile(r"«[^»]*»|[\w']+|:=|[^\s]", re.UNICODE)
# Keep the existing ban on unproved declarations, now across multiline attributes/modifiers.
unproved = re.compile(
    r"(?m)^\s*(?:@\[[^]]*\]\s*)*"
    r"(?:(?:private|protected|public|local|scoped|noncomputable|unsafe|partial)\s+)*"
    r"(?:axiom|constant|constants)\b")

for path in sys.argv[1:]:
    source = Path(path).read_text()
    newlines = [-1] + [match.start() for match in re.finditer("\n", source)]

    def location(offset):
        line = bisect_right(newlines, offset - 1)
        return f"{path}:{line}:{offset - newlines[line - 1]}"

    try:
        masked = mask_lean(source)
        tokens = list(token_pattern.finditer(masked))
        # Quoted identifiers can spell the same attribute, module or config field name.
        words = [token[0].removeprefix("«").removesuffix("»") for token in tokens]
        for hit in unproved.finditer(masked):
            errors.append(f"{location(hit.end())}: unproved declaration")
        for index, word in enumerate(words):
            where = location(tokens[index].start())
            if word in {"sorry", "sorryAx", "admit"}:
                errors.append(f"{where}: proof placeholder {word}")
            if word == "unsafe" and not aesop_rule_safety(words, index):
                unsafe_sites[path].append(where)
            if word in {"native_decide", "bv_decide", "bv_check"} or (
                    word == "decide" and decide_native(words, index)):
                native_sites[path].append(where)
            if word in {"implemented_by", "extern"}:
                before = index - 1
                while before >= 1 and words[before] == ".":
                    before -= 2
                if before >= 0 and words[before] in {"local", "scoped"}:
                    before -= 1
                # Attribute entries may start after '[' or a comma, with any whitespace.
                # A similarly shaped ordinary list is deliberately flagged for review too.
                if before >= 0 and words[before] in {"[", ","}:
                    replacement_sites[path].append(where)
            if word == "import":
                after = index + 1
                if after < len(words) and words[after] == "all":
                    after += 1
                end = after + 1
                while end + 1 < len(words) and words[end] == ".":
                    end += 2
                if "".join(words[after:end]) == unchecked_module:
                    import_sites[path].append(where)
    except ValueError as error:
        errors.append(f"{path}: lexical trust scan failed: {error}")


def check_counts(label, actual, allowed):
    counts = Counter({path: len(sites) for path, sites in actual.items()})
    for path in sorted(counts.keys() | allowed.keys()):
        expected = allowed.get(path, 0)
        if counts[path] != expected:
            sites = ", ".join(actual.get(path, [])) or "none"
            errors.append(f"{label} allowlist mismatch: {path} expected {expected}, "
                          f"found {counts[path]}; sites: {sites}")
    return f"{label} allowlist passed ({sum(counts.values())} approved sites)."


summaries = [
    check_counts("native_decide", native_sites, allowed_native),
    check_counts("implemented_by/extern", replacement_sites, allowed_replacements),
    check_counts("unsafe", unsafe_sites, allowed_unsafe),
    check_counts("NativeFPU.Unchecked import", import_sites, allowed_imports),
]
if errors:
    print("\n".join(errors), file=sys.stderr)
    sys.exit(1)
print("\n".join(summaries))
PYTHON

# The compiled audit checks the axioms of loaded FloatLib declarations and verifies that the
# permitted compiler replacement has its unconditional equality proof.
if [[ "$source_only" -eq 1 ]]; then
  printf '%s\n' 'FloatLib source trust-surface audit passed; Lean axiom compilation skipped.'
  exit 0
fi
floatlib_test_lake build FloatLibTests.Conformance.Trust.Axioms

printf '%s\n' 'FloatLib proof trust-surface audit passed.'
