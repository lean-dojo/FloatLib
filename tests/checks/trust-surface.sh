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

# The opt-in host-FPU operations carry no refinement certificate. Every import of their module
# is counted below, and the module stays outside the axiom audit.
export FLOATLIB_UNCHECKED_MODULE=FloatLib.Floats.Formats.BinaryInterchange.Configured.NativeFPU.Unchecked

python3 - "${trust_sources[@]}" <<'PYTHON'
from bisect import bisect_right
from collections import Counter, defaultdict
from pathlib import Path
import os
import re
import sys

# Native evaluation admits compiler results through axioms. Keep exact per-file counts so that
# adding another use to an approved file still fails. These five entries total 47 sites.
allowed_native = {
    "tests/FloatLibTests/Conformance/Formats/Configured.lean": 2,
    "tests/FloatLibTests/Conformance/Formats/Conversion.lean": 10,
    "tests/FloatLibTests/Conformance/Formats/LowBit.lean": 3,
    "tests/FloatLibTests/Conformance/P3109/Projection.lean": 18,
    "tests/FloatLibTests/Conformance/Posit/ExecutionBoundaries.lean": 14,
}
# Replacements are invisible to collectAxioms. The sole approved implementation replaces
# toDyadic?; its equality theorem follows it in the same file and is registered with
# `@[replacement_proof]`. The four test sites are the inputs of the registration check
# (`Provenance.requireCompiled`): a wrong replacement that `@[compiler_optimize]` must refuse,
# a correct one that it accepts with its registered proof, and two constructor indices written
# by hand that it must refuse, where Lean's generated one is accepted.
allowed_replacements = {
    "FloatLib/Floats/Formats/Posit/Model/Decode.lean": 1,
    "tests/FloatLibTests/Tactic/KernelOptimize.lean": 4,
}
# The inspection command evaluates a closed String in MetaM. The roundoff registry evaluates a
# registered `Extension` declaration, as Lean's attribute registries do. `#roundoff_check` runs a
# program at closed inputs to report its value beside a bound (one evaluation, whose safety
# argument is the second occurrence of the word). The site exporter loads a Lean environment with
# initializers enabled. The test site is a read of the constructor tag written by hand, the
# input that the registration check must refuse under a definition that is not the constructor
# index. None is a numerical implementation or a proof.
allowed_unsafe = {
    "FloatLib/Tactic/FloatInfo/Inspection.lean": 1,
    "FloatLib/Tactic/Roundoff/Check.lean": 2,
    "FloatLib/Tactic/Roundoff/Extension.lean": 1,
    "site/tooling/ExportNodes.lean": 1,
    "tests/FloatLibTests/Tactic/KernelOptimize.lean": 1,
}
# The explicit host boundary is used by native conformance, code generation, and site export.
allowed_imports = {
    "benchmarks/lean/FloatLibBenchmarks/Codegen/ConfiguredBinary.lean": 1,
    "tests/FloatLibTests/Conformance/BinaryInterchange/NativeExecution.lean": 1,
    "site/tooling/ExportNodes.lean": 1,
}
unchecked_module = os.environ["FLOATLIB_UNCHECKED_MODULE"]
# The separate native 16-bit carriers trust host IEEE binary32 and Figueroa's double-rounding
# argument. Arithmetic remains unchecked; narrowing, widening and normalization are proved.
allowed_carrier_imports = {
    "FloatLib/Floats/Formats/IEEE754.lean": 1,
    "tests/FloatLibTests/Regression/BinaryInterchange/NativeHalf.lean": 1,
}
carrier_module = "FloatLib.Floats.Formats.IEEE754.Native.Half"
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


native_sites, replacement_sites, unsafe_sites, import_sites, carrier_import_sites = (
    defaultdict(list) for _ in range(5)
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
                imported_module = "".join(words[after:end])
                if imported_module == unchecked_module:
                    import_sites[path].append(where)
                if imported_module == carrier_module:
                    carrier_import_sites[path].append(where)
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
    check_counts("native 16-bit carrier import", carrier_import_sites, allowed_carrier_imports),
]
if errors:
    print("\n".join(errors), file=sys.stderr)
    sys.exit(1)
print("\n".join(summaries))
PYTHON

# The compiled audit checks the declarations of the modules it imports. Follow its imports
# through the sources: a library module that they do not reach would never be audited. Only the
# unchecked host-FPU module stays outside.
audit_module=FloatLibTests.Conformance.Trust.Axioms
unaudited_modules="$(
  comm -23 \
    <(
      floatlib_source_files |
        awk '$0 == "FloatLib.lean" || /^FloatLib\//' |
        while IFS= read -r source; do
          floatlib_source_module "$source"
        done |
        grep -vxF "$FLOATLIB_UNCHECKED_MODULE" |
        LC_ALL=C sort -u
    ) \
    <(floatlib_source_files | floatlib_reachable_modules "$audit_module")
)"
if [[ -n "$unaudited_modules" ]]; then
  printf '%s\n' "$unaudited_modules" >&2
  printf 'trust-surface check failed: %s\n' \
    "library modules are outside the imports of the axiom audit ($audit_module)" >&2
  exit 1
fi
printf '%s\n' 'Axiom audit imports reach every library module but the unchecked host-FPU module.'

# The compiled audit checks the axioms of loaded FloatLib declarations and verifies that the
# permitted compiler replacement has its unconditional equality proof.
if [[ "$source_only" -eq 1 ]]; then
  printf '%s\n' 'FloatLib source trust-surface audit passed; Lean axiom compilation skipped.'
  exit 0
fi
floatlib_test_lake build FloatLibTests.Conformance.Trust.Axioms

# The audit holds what its imports export, so a private constant that no declaration uses is not
# among its declarations. A plain file loads every level of every module it imports. This one
# imports the lint roots of `lakefile.lean`, whose import closures hold every library module
# (`architecture.sh`), and fails on a constant of a `FloatLib` module that the kernel holds as an
# axiom. Lean keeps a declaration that its kernel rejects as an axiom, so a command that catches
# the rejection and goes on would leave one behind.
mapfile -t lint_roots < <(
  awk '/^def lintRoots/ { inside = 1 } inside { print } inside && /\]/ { exit }' lakefile.lean |
    grep -oE '"FloatLib[A-Za-z0-9_.]*"' |
    tr -d '"'
)
[[ "${#lint_roots[@]}" -gt 0 ]] ||
  { printf 'trust-surface check failed: lakefile.lean names no lint root\n' >&2; exit 1; }
floatlib_lake build "${lint_roots[@]}"
scan="$(mktemp -d "${TMPDIR:-/tmp}/floatlib-axioms.XXXXXX")"
trap 'rm -rf -- "$scan"' EXIT
{
  printf 'import %s\n' "${lint_roots[@]}"
  cat <<'LEAN'
open Lean Elab Command in
run_cmd liftCoreM do
  let environment ← getEnv
  let modules := environment.header.moduleNames
  let mut constants : Nat := 0
  let mut found : Array Name := #[]
  for (name, _) in environment.constants.map₁.toList do
    let some index := environment.getModuleIdxFor? name | continue
    unless (`FloatLib).isPrefixOf modules[index.toNat]! do continue
    constants := constants + 1
    if let some (.axiomInfo _) := environment.checked.get.find? name then found := found.push name
  unless found.isEmpty do
    throwError "constants of the library that the kernel holds as axioms: {found}"
  if constants == 0 then throwError "no constant of a FloatLib module is loaded"
  IO.println s!"No axiom among the {constants} constants of the library, private ones included."
LEAN
} > "$scan/AxiomConstants.lean"
floatlib_lake env lean "$scan/AxiomConstants.lean" ||
  { printf 'trust-surface check failed: a constant of the library is an axiom\n' >&2; exit 1; }

printf '%s\n' 'FloatLib proof trust-surface audit passed.'
