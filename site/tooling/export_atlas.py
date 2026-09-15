#!/usr/bin/env python3
"""Build site/data/nodes.json from the curated phases and the built Lean library.

This is the Python half of the site data pipeline. It runs the Lean exporter
(`ExportNodes.lean`), reduces the dependency graph to the selected nodes, attaches source excerpts
and GitHub links, validates the result against the schema in `site/SITE_SPEC.md`, and writes
`site/data/nodes.json`.

When the working tree differs from HEAD, node URLs are checked against the committed text and
downgraded (file-only or empty) where an exact line anchor would be wrong; see `node_url`.
An unborn HEAD has no revision or diff digest, and all declaration URLs are empty.

Usage (from the repository root, or anywhere):

    python3 site/tooling/export_atlas.py [--skip-lean] [--raw PATH] [--out PATH]

Environment:

    FLOATLIB_BUILD_DIR   Lake build directory holding the compiled library. When unset, the
                          per-checkout default of tests/lib/lake.sh applies, as for every other
                          repository script.

The raw export defaults to ${FLOATLIB_BUILD_DIR}-site-data/nodes.raw.json on local disk.
The reduced nodes.json stays in site/data as a source asset for the reader.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SITE = ROOT / "site"
PHASES = SITE / "content" / "phases.json"
EXPORTER = SITE / "tooling" / "ExportNodes.lean"
DEFAULT_OUT = SITE / "data" / "nodes.json"
REPOSITORY = "https://github.com/lean-dojo/FloatLib"
DEFAULT_BRANCH = "main"

def default_build_dir() -> str:
    """FLOATLIB_BUILD_DIR when set, else the default that tests/lib/lake.sh computes."""
    script = ROOT / "tests" / "lib" / "lake.sh"
    try:
        result = subprocess.run(
            ["bash", "--noprofile", "--norc", "-c",
             'set -euo pipefail; source "$1" >&2; printf %s "${FLOATLIB_BUILD_DIR:?}"',
             "site-build-path", str(script)],
            check=True, capture_output=True, text=True)
    except (OSError, subprocess.CalledProcessError) as error:
        detail = error.stderr.strip() if isinstance(error, subprocess.CalledProcessError) else str(error)
        fail(f"cannot resolve the local Lake build directory from {script}: {detail}")
    build_dir = result.stdout.strip()
    if not build_dir or not Path(build_dir).is_absolute():
        fail(f"{script} did not return an absolute FLOATLIB_BUILD_DIR")
    return build_dir

# The kinds named in SITE_SPEC.md. The exporter also reports "inductive" for plain inductive
# types (rounding modes, status flags, exceptional values) and "axiom"; we keep those labels
# because calling an enumeration a structure would mislead readers, and we report them so the
# reader can style them. Anything else is a curation error.
SPEC_KINDS = {"theorem", "def", "instance", "structure", "class"}
EXTRA_KINDS = {"inductive", "axiom"}
# The em and en dash, written as escapes so a search for the characters over the tree finds only
# text that actually contains one.
DASHES = "\u2014\u2013"


def fail(message: str) -> None:
    print(f"export_atlas: {message}", file=sys.stderr)
    raise SystemExit(1)


def git(*args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=ROOT, check=True, capture_output=True, text=True
    ).stdout.strip()


def head_revision() -> str | None:
    """Return the commit at HEAD, or None only for an unborn branch."""
    result = subprocess.run(
        ["git", "rev-parse", "--verify", "--quiet", "HEAD^{commit}"],
        cwd=ROOT, capture_output=True, text=True,
    )
    if result.returncode == 0:
        return result.stdout.strip()
    # A failed revision lookup alone is not evidence of an empty repository. HEAD must name
    # a branch whose ref does not exist; a detached or corrupt HEAD remains an error.
    ref = git("symbolic-ref", "HEAD")
    exists = subprocess.run(
        ["git", "show-ref", "--verify", "--quiet", ref], cwd=ROOT, capture_output=True,
    )
    if exists.returncode == 1:
        return None
    fail("cannot resolve HEAD to a commit")


def run_exporter(raw: Path) -> None:
    build_dir = default_build_dir()
    if not Path(build_dir).is_dir():
        fail(f"build directory {build_dir} does not exist; set FLOATLIB_BUILD_DIR")
    # The guide includes opt-in APIs that a default `lake build` does not reach.
    # Build the imports explicitly before Lean opens the exporter's environment.
    imports = json.loads(PHASES.read_text()).get("imports", ["FloatLib"])
    build_command = ["lake", f"-KbuildDir={build_dir}", "build", *imports]
    print("export_atlas: " + " ".join(build_command), flush=True)
    result = subprocess.run(build_command, cwd=ROOT)
    if result.returncode != 0:
        fail(f"building the exporter imports failed with status {result.returncode}")
    raw.parent.mkdir(parents=True, exist_ok=True)
    command = [
        "lake", f"-KbuildDir={build_dir}", "env", "lean", "--run",
        str(EXPORTER.relative_to(ROOT)), str(PHASES.relative_to(ROOT)), str(raw),
    ]
    print("export_atlas: " + " ".join(command))
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    sys.stdout.write(result.stdout)
    sys.stderr.write(result.stderr)
    if result.returncode != 0:
        fail(f"the Lean exporter failed with status {result.returncode}")


def load_phases() -> list[dict]:
    spec = json.loads(PHASES.read_text())
    phases = spec["phases"]
    ids = [phase["id"] for phase in phases]
    if len(set(ids)) != len(ids):
        fail("phase ids in phases.json are not unique")
    for phase_id in ids:
        if not re.fullmatch(r"[a-z0-9]+(-[a-z0-9]+)*", phase_id):
            fail(f"phase id {phase_id!r} is not a kebab-case slug")
    return phases


def first_sentence(text: str, limit: int = 90) -> str:
    text = " ".join(text.strip().split())
    text = text.replace("`", "")
    if not text:
        return ""
    match = re.match(r"(.+?[.!?])(\s|$)", text)
    sentence = match.group(1) if match else text
    if len(sentence) > limit:
        sentence = sentence[: limit - 3].rstrip() + "..."
    return sentence


def shallow_dependencies(deps: dict[str, set[str]]) -> dict[str, set[str]]:
    """Transitive reduction: drop every edge implied by a longer path, as the Conway generator does."""

    def ancestors(label: str) -> set[str]:
        seen: set[str] = set()
        pending = list(deps[label])
        while pending:
            dependency = pending.pop()
            if dependency in seen:
                continue
            seen.add(dependency)
            pending.extend(deps[dependency])
        return seen

    ancestor_sets = {label: ancestors(label) for label in deps}
    return {
        label: {
            dependency
            for dependency in dependencies
            if not any(
                dependency in ancestor_sets[other]
                for other in dependencies
                if other != dependency
            )
        }
        for label, dependencies in deps.items()
    }


def find_cycle(deps: dict[str, set[str]]) -> list[str]:
    state: dict[str, int] = {}
    stack: list[str] = []

    def visit(node: str) -> list[str]:
        state[node] = 1
        stack.append(node)
        for dependency in sorted(deps[node]):
            if state.get(dependency) == 1:
                return stack[stack.index(dependency):] + [dependency]
            if dependency not in state:
                cycle = visit(dependency)
                if cycle:
                    return cycle
        stack.pop()
        state[node] = 2
        return []

    for node in deps:
        if node not in state:
            cycle = visit(node)
            if cycle:
                return cycle
    return []


def dirty_files() -> set[str]:
    """Library files that are modified, deleted, added, or untracked relative to HEAD."""
    # Keep the porcelain status columns intact (git() strips leading spaces), and use NUL
    # delimiters so spaces, quoted paths, and rename records cannot corrupt the file names.
    output = subprocess.run(
        ["git", "status", "--porcelain", "-z", "--untracked-files=all", "--",
         "FloatLib", "FloatLib.lean", "lakefile.lean"],
        cwd=ROOT, check=True, capture_output=True, text=True,
    ).stdout
    files = set()
    entries = iter(output.split("\0"))
    for entry in entries:
        if not entry:
            continue
        files.add(entry[3:])
        if "R" in entry[:2] or "C" in entry[:2]:
            next(entries, None)  # porcelain -z puts the original path after the new path
    return files


def committed_files(revision: str) -> set[str]:
    """Library files that exist in the tree of `revision`."""
    return set(git("ls-tree", "-r", "--name-only", revision, "--", "FloatLib").splitlines())


_committed_text: dict[str, list[str]] = {}


def committed_lines(revision: str, file: str) -> list[str]:
    """The text of `file` at `revision`, split into lines (cached per file)."""
    if file not in _committed_text:
        # Not through git(), which strips the output: a stripped file would shift line numbers.
        text = subprocess.run(["git", "show", f"{revision}:{file}"], cwd=ROOT, check=True,
                              capture_output=True, text=True).stdout
        _committed_text[file] = text.split("\n")
    return _committed_text[file]


def node_url(revision: str | None, file: str, line: int, end_line: int, lean_source: str,
             dirty: set[str], committed: set[str]) -> str:
    """The GitHub link for a declaration, honest about uncommitted work.

    SITE_SPEC.md wants `blob/<sha>/<file>#L<line>-L<end>` for every node. That is exact only when
    the file at `revision` holds the same text at those lines. When the working tree differs we
    check: a file GitHub does not have at this revision gets no URL at all (an empty string), a
    file whose committed lines match the excerpt keeps the exact link, and a file whose lines
    differ gets a link to the file without the line fragment, so the anchor cannot land on the
    wrong declaration. This is a recorded deviation from the spec's URL schema, forced by building
    from a dirty tree; a clean checkout makes every URL exact again.
    """
    if revision is None:
        return ""
    exact = f"{REPOSITORY}/blob/{revision}/{file}#L{line}-L{end_line}"
    if file not in dirty:
        return exact
    if file not in committed:
        return ""
    lines = committed_lines(revision, file)
    if "\n".join(lines[line - 1:end_line]) == lean_source:
        return exact
    return f"{REPOSITORY}/blob/{revision}/{file}"


def field_docstring(record: dict) -> str:
    """The docstring shown for a node, with a fallback for undocumented structure fields.

    A structure field is exported as its projection function, and fields often have no doc
    comment of their own. Rather than an empty card we say what the field belongs to and quote
    the structure's docstring. The generated sentence is the only text in `docstring` that is
    not copied verbatim from the library, and the export summary reports each use.
    """
    if record["docstring"]:
        return record["docstring"]
    parent = record.get("structureParent")
    parent_doc = (record.get("structureDocstring") or "").strip()
    if not parent:
        return ""
    field = record["name"].rsplit(".", 1)[-1]
    lead = f"`{field}` is a field of the structure [[{parent}]]"
    if not parent_doc:
        return lead + ", which has no docstring of its own."
    return f"{lead}; the structure's documentation follows.\n\n{parent_doc}"


def worktree_digest() -> str:
    """SHA-256 of `git diff --binary HEAD`, the same figure the oracle scripts record as
    `worktree_diff_sha256` and tests/EXTERNAL.md quotes next to a revision, so an export and a
    validation run from the same uncommitted state can be matched. Untracked files are not part
    of the diff; they are counted in `dirtyFiles` and flagged on their nodes."""
    diff = subprocess.run(
        ["git", "diff", "--binary", "HEAD"], cwd=ROOT, check=True, capture_output=True
    ).stdout
    return hashlib.sha256(diff).hexdigest()


def read_source(file: str, line: int, end_line: int) -> str:
    path = ROOT / file
    if not path.is_file():
        fail(f"source file {file} does not exist")
    lines = path.read_text().splitlines()
    if line < 1 or end_line < line or end_line > len(lines):
        fail(f"declaration range {line}..{end_line} is outside {file} ({len(lines)} lines)")
    return "\n".join(lines[line - 1:end_line])


def build(raw_path: Path, out_path: Path) -> dict:
    phases = load_phases()
    phase_ids = [phase["id"] for phase in phases]
    raw = json.loads(raw_path.read_text())
    records = raw["nodes"]
    if not records:
        fail("the exporter produced no nodes")

    names = [record["name"] for record in records]
    if len(set(names)) != len(names):
        fail("the exporter produced duplicate names")
    selected = set(names)
    curated = {
        node if isinstance(node, str) else node["name"]
        for phase in phases for node in phase["nodes"]
    }
    if selected != curated:
        fail("raw export does not match content/phases.json; rebuild the library and rerun "
             "site/tooling/export.sh without --skip-lean")

    kinds = {record["name"]: record["kind"] for record in records}
    deps: dict[str, set[str]] = {}
    for record in records:
        statement = set(record["statementDependencies"])
        proof = set(record["proofDependencies"])
        if record["kind"] == "theorem":
            # SITE_SPEC: a theorem depends on the definitions it mentions and the theorems it uses.
            # The definitions its proof merely unfolds (kernel structures behind a dispatching
            # runtime body, concrete formats an eligibility check names) are implementation
            # detail, not dependencies a reader wants listed, so only theorems survive from the
            # proof walk. The Lean exporter applies the matching rule to the statement walk by
            # not entering the bodies of runtime definitions for theorem nodes.
            proof = {name for name in proof if kinds.get(name) == "theorem"}
        direct = statement | proof
        direct.discard(record["name"])
        unknown = sorted(direct - selected)
        if unknown:
            fail(f"{record['name']} depends on unselected names: {', '.join(unknown)}")
        deps[record["name"]] = direct
    cycle = find_cycle(deps)
    if cycle:
        fail("dependency graph is cyclic: " + " -> ".join(cycle))
    shallow = shallow_dependencies(deps)

    revision = head_revision()
    branch = (git("symbolic-ref", "--short", "HEAD") if revision is None
              else git("rev-parse", "--abbrev-ref", "HEAD"))
    if branch == "HEAD":
        branch = DEFAULT_BRANCH

    phase_index = {phase_id: index for index, phase_id in enumerate(phase_ids)}
    dirty = dirty_files()
    committed = committed_files(revision) if dirty and revision is not None else set()
    warnings: list[str] = []
    nodes = []
    for record in records:
        name = record["name"]
        if record["phase"] not in phase_index:
            fail(f"{name} is assigned to unknown phase {record['phase']!r}")
        if not record["file"] or record["line"] == 0:
            fail(f"{name} has no source range; is it declared in an imported module?")
        title = record["title"] or first_sentence(record["docstring"]) or name.rsplit(".", 1)[-1]
        kind = record["kind"]
        if kind not in SPEC_KINDS:
            if kind in EXTRA_KINDS:
                warnings.append(f"{name} has kind {kind!r}, which extends the spec vocabulary")
            else:
                fail(f"{name} has unexpected kind {kind!r}")
        if any(dash in title for dash in DASHES):
            fail(f"title of {name} contains an em or en dash")
        if any(dash in record["docstring"] for dash in DASHES):
            warnings.append(f"docstring of {name} contains an em or en dash (copied verbatim)")
        docstring = field_docstring(record)
        if docstring and not record["docstring"]:
            warnings.append(f"{name} has no docstring; the card quotes its structure "
                            f"{record['structureParent']} instead")
        lean_source = read_source(record["file"], record["line"], record["endLine"])
        nodes.append({
            "id": name,
            "name": name,
            "kind": kind,
            "phase": record["phase"],
            "title": title,
            "module": record["module"],
            "file": record["file"],
            "line": record["line"],
            "endLine": record["endLine"],
            "url": node_url(revision, record["file"], record["line"], record["endLine"],
                            lean_source, dirty, committed),
            "statement": record["statement"],
            "docstring": docstring,
            "axioms": list(record["axioms"]),
            "dependencies": sorted(shallow[name], key=names.index),
            "leanSource": lean_source,
            "dirty": revision is None or record["file"] in dirty,
        })

    backwards = [
        (dependency, node["id"])
        for node in nodes
        for dependency in node["dependencies"]
        if phase_index[next(n["phase"] for n in nodes if n["id"] == dependency)]
        > phase_index[node["phase"]]
    ]
    for dependency, dependent in backwards:
        warnings.append(f"dependency runs against phase order: {dependent} uses {dependency}")

    # The URLs point at HEAD on GitHub, but the build directory follows the working tree. Any node
    # whose file is modified or untracked relative to HEAD is checked against the committed text
    # (see node_url): its URL is exact, file-only, or empty accordingly. Every node also carries
    # `dirty`, and `source` records how many library files differ and a digest of the deviation,
    # so the reader can say which excerpts come from uncommitted work.
    dirty_nodes = [node for node in nodes if node["dirty"]]
    source = {"repository": REPOSITORY, "revision": revision, "branch": branch, "dirtyFiles": len(dirty)}
    if dirty and revision is not None:
        source["worktree"] = worktree_digest()
    if revision is None:
        warnings.append(
            f"HEAD is unborn: all {len(nodes)} nodes are uncommitted and have no GitHub URL. "
            "No commit revision or worktree diff digest is available."
        )
    elif dirty_nodes:
        missing = [node for node in dirty_nodes if not node["url"]]
        file_only = [node for node in dirty_nodes if node["url"] and "#L" not in node["url"]]
        exact = len(dirty_nodes) - len(missing) - len(file_only)
        warnings.append(
            f"{len(dirty_nodes)} of {len(nodes)} nodes live in files that differ from HEAD "
            f"{revision[:12]} (uncommitted work, {len(dirty)} library files, worktree digest "
            f"{source['worktree'][:12]}): {len(missing)} in files GitHub does not have at this "
            f"revision (no URL), {len(file_only)} at lines that changed (URL without line anchor), "
            f"{exact} unchanged at their lines (exact URL). Files: "
            + ", ".join(sorted({node['file'] for node in dirty_nodes}))
        )
        warnings.append(
            "Source links are shortened or omitted where local edits would make a link "
            "to the committed declaration inaccurate."
        )

    for phase in phases:
        if any(dash in phase["title"] for dash in DASHES):
            fail(f"title of phase {phase['id']} contains an em or en dash")

    data = {
        "source": source,
        "phases": [
            {"id": phase["id"], "title": phase["title"]}
            for phase in phases
        ],
        "nodes": nodes,
    }
    validate(data)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n")
    report(data, warnings, out_path)
    return data


def validate(data: dict) -> None:
    """Check the exact schema of SITE_SPEC.md so a malformed file never reaches the reader."""

    def expect(condition: bool, message: str) -> None:
        if not condition:
            fail("schema: " + message)

    expect(set(data) == {"source", "phases", "nodes"}, "top level must have source, phases, nodes")
    source = data["source"]
    # The spec names repository, revision, and branch. We add `dirtyFiles` (how many library files
    # differ from the revision) and `worktree` (a digest of the deviation from an existing HEAD).
    # An unborn HEAD has a null revision, no diff digest, and only dirty nodes without URLs.
    required_source = {"repository", "revision", "branch"}
    expect(required_source <= set(source) <= required_source | {"dirtyFiles", "worktree"}, "source keys")
    expect(all(isinstance(source[key], str) and source[key] for key in ("repository", "branch")), "source values")
    revision = source["revision"]
    expect(revision is None or (isinstance(revision, str) and
                               re.fullmatch(r"[0-9a-f]{40}", revision) is not None),
           "revision is a git sha or null for an unborn HEAD")
    expect(isinstance(source.get("dirtyFiles", 0), int) and source.get("dirtyFiles", 0) >= 0, "dirtyFiles is a count")
    expect(revision is not None or source.get("dirtyFiles", 0) > 0,
           "an unborn HEAD has uncommitted library files")
    expect(("worktree" in source) == (revision is not None and source.get("dirtyFiles", 0) > 0),
           "worktree digest exactly when dirty with an existing HEAD")
    if "worktree" in source:
        expect(re.fullmatch(r"[0-9a-f]{64}", source["worktree"]) is not None, "worktree is a sha256")
    expect(isinstance(data["phases"], list) and data["phases"], "phases is a nonempty array")
    phase_ids = []
    for phase in data["phases"]:
        expect(set(phase) == {"id", "title"}, f"phase keys in {phase}")
        expect(all(isinstance(phase[key], str) for key in phase), f"phase values in {phase['id']}")
        expect(phase["id"] and phase["title"], f"phase {phase['id']!r} needs id and title")
        phase_ids.append(phase["id"])
    expect(len(set(phase_ids)) == len(phase_ids), "phase ids unique")
    node_keys = {
        "id", "name", "kind", "phase", "title", "module", "file", "line", "endLine",
        "url", "statement", "docstring", "axioms", "dependencies", "leanSource", "dirty",
    }
    ids = [node["id"] for node in data["nodes"]]
    expect(len(set(ids)) == len(ids), "node ids unique")
    id_set = set(ids)
    used_phases = set()
    for node in data["nodes"]:
        expect(set(node) == node_keys, f"node keys of {node.get('id')}")
        for key in ("id", "name", "kind", "phase", "title", "module", "file", "url", "statement",
                    "docstring", "leanSource"):
            expect(isinstance(node[key], str), f"{node['id']}.{key} is a string")
        expect(node["id"] == node["name"], f"{node['id']}: id is the full Lean name")
        expect(node["kind"] in SPEC_KINDS | EXTRA_KINDS, f"{node['id']}: kind {node['kind']!r}")
        expect(node["phase"] in phase_ids, f"{node['id']}: phase {node['phase']!r} exists")
        expect(node["title"] != "", f"{node['id']}: title is nonempty")
        expect(isinstance(node["dirty"], bool), f"{node['id']}: dirty is a bool")
        expect(isinstance(node["line"], int) and isinstance(node["endLine"], int), f"{node['id']}: lines")
        expect(1 <= node["line"] <= node["endLine"], f"{node['id']}: line range")
        expect(node["file"].endswith(".lean") and (ROOT / node["file"]).is_file(), f"{node['id']}: file")
        expect(node["module"].replace(".", "/") + ".lean" == node["file"], f"{node['id']}: module matches file")
        exact_url = f"{REPOSITORY}/blob/{data['source']['revision']}/{node['file']}#L{node['line']}-L{node['endLine']}"
        if revision is None:
            expect(node["dirty"] and node["url"] == "",
                   f"{node['id']}: an unborn HEAD requires a dirty node without a URL")
        elif node["dirty"]:
            allowed = {exact_url, f"{REPOSITORY}/blob/{data['source']['revision']}/{node['file']}", ""}
            expect(node["url"] in allowed, f"{node['id']}: url of a dirty node")
        else:
            expect(node["url"] == exact_url, f"{node['id']}: url")
        expect(node["statement"] != "", f"{node['id']}: statement is nonempty")
        expect(all(isinstance(a, str) for a in node["axioms"]), f"{node['id']}: axioms are strings")
        expect(all(isinstance(d, str) and d in id_set and d != node["id"] for d in node["dependencies"]),
               f"{node['id']}: dependencies are other node ids")
        expect(len(set(node["dependencies"])) == len(node["dependencies"]), f"{node['id']}: dependencies unique")
        expect(node["leanSource"].count("\n") + 1 == node["endLine"] - node["line"] + 1,
               f"{node['id']}: leanSource has one line per source line")
        used_phases.add(node["phase"])
    for phase_id in phase_ids:
        expect(phase_id in used_phases, f"phase {phase_id} has no nodes")


def report(data: dict, warnings: list[str], out_path: Path) -> None:
    nodes = data["nodes"]
    destination = out_path.relative_to(ROOT) if out_path.is_relative_to(ROOT) else out_path
    print(f"export_atlas: wrote {len(nodes)} nodes to {destination}")
    for phase in data["phases"]:
        local = [node for node in nodes if node["phase"] == phase["id"]]
        edges = sum(len(node["dependencies"]) for node in local)
        print(f"  {phase['id']}: {len(local)} nodes, {edges} reduced edges")
    total_edges = sum(len(node["dependencies"]) for node in nodes)
    kinds: dict[str, int] = {}
    for node in nodes:
        kinds[node["kind"]] = kinds.get(node["kind"], 0) + 1
    axioms = sorted({axiom for node in nodes for axiom in node["axioms"]})
    print(f"  total: {len(nodes)} nodes, {total_edges} reduced edges")
    print("  kinds: " + ", ".join(f"{kind} {count}" for kind, count in sorted(kinds.items())))
    print("  axioms used: " + (", ".join(axioms) if axioms else "none"))
    source = data["source"]
    if source.get("dirtyFiles"):
        dirty_count = sum(1 for n in nodes if n["dirty"])
        no_url = sum(1 for n in nodes if not n["url"])
        file_only = sum(1 for n in nodes if n["url"] and "#L" not in n["url"])
        provenance = (f"differ from {source['revision'][:12]}, digest {source['worktree'][:12]}"
                      if source["revision"] is not None else "are uncommitted (HEAD is unborn)")
        print(f"  working tree: {source['dirtyFiles']} library files {provenance}; "
              f"{dirty_count} nodes are marked dirty "
              f"({no_url} without a GitHub URL, {file_only} with a file-only URL)")
        print("  PUBLISHING NOTE: this export flags itself as uncommitted on every page; commit the "
              "tree and re-export before publishing")
    for warning in warnings:
        print(f"  warning: {warning}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--skip-lean", action="store_true", help="reuse an existing raw export")
    parser.add_argument("--raw", type=Path, default=None,
                        help="raw exporter output (default: "
                             "${FLOATLIB_BUILD_DIR}-site-data/nodes.raw.json)")
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT, help="nodes.json destination")
    args = parser.parse_args()
    if args.raw is None:
        args.raw = Path(f"{default_build_dir()}-site-data") / "nodes.raw.json"
    if not args.skip_lean:
        run_exporter(args.raw)
    elif not args.raw.is_file():
        fail(f"--skip-lean given but {args.raw} does not exist")
    build(args.raw, args.out)


if __name__ == "__main__":
    main()
