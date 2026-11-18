#!/usr/bin/env python3
"""Count duplicate and unused declarations of the library from its source text.

This is a lexical screen, not an elaborated one: it reads declarations with a small parser and
compares their text. It finds candidates for review and gives four numbers that a change should
not increase. It cannot prove that two declarations mean the same or that one is unreachable.

The four counts, over the declarations of `FloatLib.lean` and `FloatLib/` without the examples
(`FloatLib/Examples.lean`, `FloatLib/Examples/`), which are clients of the library as the tests
are:

DUPDEF        definitions (`def`, `abbrev`) with the same signature and the same body, counted as
              the copies beyond the first of each group.
DUPTHM        theorems with the same statement and the same proof, counted the same way.
equivalences  theorems with the same statement, whatever the proof, counted the same way. Two
              names for one fact show up here, and so do theorems that differ only in a variable
              declared outside them, which the screen does not read.
unused        declarations whose last name component occurs nowhere else in the Lean sources of
              the repository. An occurrence in the library counts wherever it is, because a
              tactic may refer to a lemma by a quoted name. An occurrence in examples, tests,
              benchmarks or site tooling counts only inside a proof or a definition: a quoted
              name, as in the list of an axiom audit, and a `#check` or `#print` line are not
              uses. A name that a tactic builds from a string is invisible. Instances and
              declarations registered by an attribute that a tactic or the compiler reads (the
              list `REGISTRATION`) are left out, since nothing has to name them.

A signature is the text between the name and the top-level `:=` or `where`, with whitespace
collapsed, together with the library declarations its identifiers resolve to from the enclosing
namespaces. So `min` in two namespaces with different `min` in scope is not a duplicate.
Opened namespaces, notation and section variables are not resolved.

The screen reads what is written. A declaration that a command generates from a table (the
per-operation capabilities, certificates and candidate sets) is not counted, and a use that such
a command builds from a name template is not seen. So a command either generates a family
together with its uses, or takes the names it refers to as arguments.

usage: source-screen.py [--revision REV] [--list] [--check RECORD]

  --revision REV   read the tree of a git revision instead of the working tree
  --list           print the groups and the unused candidates after the counts
  --check RECORD   fail when a count exceeds the `limit` line of the record file
"""

import argparse
import collections
import io
from pathlib import Path
import re
import subprocess
import sys

START = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:public|private|protected|nonrec|noncomputable|partial|unsafe|meta)\s+)*"
    r"(theorem|lemma|def|abbrev|instance|structure|inductive)\s+([^\s:{(]+)", re.M)
COMMAND = re.compile(
    r"^(?:end\b|namespace\b|section\b|variable\b|open\b|attribute\b|example\b|"
    r"run_cmd\b|#|set_option\b)", re.M)
SCOPE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:public|private|noncomputable|meta)\s+)*"
    r"(namespace|section|end)(?:[ \t]+([^\s]+))?[ \t]*$", re.M)
# An identifier: letters (Greek and subscripts included), digits, `_`, `'`, `!`, `?` and dots.
# Symbols such as `⟩` and `→` end it, so `h.foo⟩` is a use of `foo`.
WORD = re.compile(r"[^\W\d][\w'.!?]*")
# Attributes that register a declaration for lookup by a tactic, an elaborator or the compiler.
REGISTRATION = re.compile(
    r"\b(?:csimp|simp|ext|congr|aesop|fun_prop|continuity|measurability|positivity|"
    r"norm_num|gcongr|kernel_path|kernel_optimize|compiler_optimize|lane_call|"
    r"roundoff_rule|roundoff_extension|replacement_proof|implemented_by|"
    r"command_elab|term_elab|tactic|app_unexpander|delab|simproc|"
    r"builtin_command_elab|builtin_term_elab|builtin_tactic|builtin_simproc)\b")
# In tests, benchmarks and site tooling these are mentions, not uses.
QUOTED_NAME = re.compile(r"`+[^\W\d][\w'.!?]*")
INSPECTION = re.compile(r"^[ \t]*#(?:check|print)\b[^\n]*", re.M)
COUNTS = ("DUPDEF", "DUPTHM", "equivalences", "unused")


def strip_comments(text):
    """Remove nested Lean comments, leaving strings and line numbers intact."""
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif string:
            out.append(text[i])
            if text[i] == "\\" and i + 1 < len(text):
                i += 1
                out.append(text[i])
            elif text[i] == '"':
                string = False
            i += 1
        elif text.startswith("/-", i):
            depth, i = 1, i + 2
            out.append(" ")
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        else:
            string = text[i] == '"'
            out.append(text[i])
            i += 1
    return "".join(out)


def sources(repo, revision):
    """The Lean sources of the working tree, or of a revision, by path."""
    if revision is None:
        paths = subprocess.check_output(
            ["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard"],
            cwd=repo).decode().split("\0")
        return {p: (repo / p).read_text() for p in sorted(set(paths))
                if p.endswith(".lean") and (repo / p).is_file()}
    paths = subprocess.check_output(
        ["git", "ls-tree", "-rz", "--name-only", revision], cwd=repo).decode().split("\0")
    paths = [p for p in paths if p.endswith(".lean")]
    data = subprocess.check_output(
        ["git", "cat-file", "--batch"], cwd=repo,
        input="".join(f"{revision}:{p}\n" for p in paths).encode())
    stream, result = io.BytesIO(data), {}
    for path in paths:
        size = int(stream.readline().decode().split()[2])
        result[path] = stream.read(size).decode()
        assert stream.read(1) == b"\n"
    return result


def split_declaration(fragment):
    """Split at the first `:=` or `where` outside brackets and strings."""
    depth, string, i = 0, False, 0
    while i < len(fragment):
        char = fragment[i]
        if string:
            if char == "\\":
                i += 2
                continue
            if char == '"':
                string = False
        elif char == '"':
            string = True
        elif char in "([{⟨":
            depth += 1
        elif char in ")]}⟩":
            depth -= 1
        elif depth == 0:
            if fragment.startswith(":=", i):
                return fragment[:i], fragment[i + 2:]
            if (fragment.startswith("where", i)
                    and (i == 0 or not (fragment[i - 1].isalnum() or fragment[i - 1] in "_'"))
                    and (i + 5 == len(fragment)
                         or not (fragment[i + 5].isalnum() or fragment[i + 5] in "_'"))):
                return fragment[:i], fragment[i + 5:]
        i += 1
    return fragment, ""


def declarations(clean, path):
    """The declarations of one comment-free source, each with its enclosing namespace."""
    starts = list(START.finditer(clean))
    commands = list(SCOPE.finditer(clean))
    stack, index = [], 0
    normalize = lambda value: re.sub(r"\s+", " ", value).strip()
    for position, match in enumerate(starts):
        line = clean.count("\n", 0, match.start()) + 1
        while index < len(commands) and clean.count("\n", 0, commands[index].start()) + 1 <= line:
            kind, name = commands[index][1], commands[index][2]
            if kind in ("namespace", "section"):
                stack.append((kind, name or ""))
            elif stack:
                if name:
                    while stack and stack[-1][1] != name:
                        stack.pop()
                if stack:
                    stack.pop()
            index += 1
        end = starts[position + 1].start() if position + 1 < len(starts) else len(clean)
        fragment = clean[match.end():end]
        if stop := COMMAND.search(fragment):
            fragment = fragment[:stop.start()]
        signature, body = split_declaration(fragment)
        namespace = ".".join(name for kind, name in stack if kind == "namespace")
        yield {
            "kind": match[1], "name": match[2], "path": path, "line": line,
            "signature": normalize(signature), "body": normalize(body),
            "attributes": re.findall(r"@\[(.*?)\]", match[0], re.S),
            "namespace": namespace,
            "full_name": ".".join(filter(None, (namespace, match[2]))).removeprefix("_root_."),
        }


def resolved_references(item, names):
    """The library declarations that the identifiers of a signature resolve to."""
    binders = set()
    for match in re.finditer(r"[(\[{]\s*([^:()\[\]{}]+)\s*:", item["signature"]):
        binders.update(WORD.findall(match[1]))
    pieces = item["namespace"].split(".") if item["namespace"] else []
    references = set()
    for word in WORD.findall(item["signature"]):
        if word.split(".")[0] in binders:
            continue
        for depth in range(len(pieces), -1, -1):
            candidate = ".".join(pieces[:depth] + [word])
            if candidate in names:
                references.add((word, candidate))
                break
    return tuple(sorted(references))


def groups(items, key):
    found = collections.defaultdict(list)
    for item in items:
        found[key(item)].append(item)
    return [group for group in found.values() if len(group) > 1]


def screen(repo, revision):
    files = sources(repo, revision)
    clean = {path: strip_comments(text) for path, text in files.items()}
    library = [path for path in files
               if path == "FloatLib.lean" or path.startswith("FloatLib/")
               and not path.startswith("FloatLib/Examples")]
    items = [item for path in library for item in declarations(clean[path], path)]
    names = {item["full_name"] for item in items}
    for item in items:
        item["key"] = (item["signature"], resolved_references(item, names))
    definitions = [item for item in items if item["kind"] in ("def", "abbrev") and item["body"]]
    theorems = [item for item in items if item["kind"] in ("theorem", "lemma")]
    uses = collections.Counter()
    for path, text in clean.items():
        if path not in library:
            text = INSPECTION.sub("", QUOTED_NAME.sub(" ", text))
        for word in WORD.findall(text):
            uses.update(part for part in word.split(".") if part)
    registered = lambda item: item["kind"] == "instance" or any(
        REGISTRATION.search(attribute) for attribute in item["attributes"])
    found = {
        "DUPDEF": groups(definitions, lambda item: (item["key"], item["body"])),
        "DUPTHM": groups(theorems, lambda item: (item["key"], item["body"])),
        "equivalences": groups(theorems, lambda item: item["key"]),
    }
    unused = [item for item in items
              if uses[item["name"].rsplit(".", 1)[-1]] == 1 and not registered(item)]
    counts = {name: sum(len(group) - 1 for group in found[name]) for name in found}
    counts["unused"] = len(unused)
    return counts, found, unused


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--revision")
    parser.add_argument("--list", action="store_true")
    parser.add_argument("--check", type=Path)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[2]
    counts, found, unused = screen(repo, args.revision)
    print(" ".join(f"{name}={counts[name]}" for name in COUNTS))
    if args.list:
        for name, values in found.items():
            for group in sorted(values, key=lambda group: (group[0]["path"], group[0]["line"])):
                print(f"\n{name}")
                for item in group:
                    print(f'  {item["path"]}:{item["line"]}: {item["name"]}')
        print("\nunused")
        for item in sorted(unused, key=lambda item: (item["path"], item["line"])):
            print(f'  {item["path"]}:{item["line"]}: {item["name"]}')
    if args.check:
        limit = None
        for line in args.check.read_text().splitlines():
            if line.startswith("limit "):
                limit = dict(field.split("=") for field in line.split()[1:])
        if limit is None:
            sys.exit(f"source screen failed: {args.check} has no `limit` line")
        over = [f"{name} {counts[name]} > {limit[name]}" for name in COUNTS
                if counts[name] > int(limit[name])]
        if over:
            sys.exit("source screen failed: " + ", ".join(over) +
                     f" (run with --list; lower the count or update {args.check})")


if __name__ == "__main__":
    main()
