#!/usr/bin/env python3
"""Check the FloatLib site chapters in site/content/chapters.

For every ``NN-slug.md`` chapter we

* validate the YAML front matter (``number``, ``slug``, ``title``, ``summary``, optional
  ``phases``) against the file name and against SITE_SPEC.md;
* extract the ```` ```lean ```` blocks into one Lean file per chapter, prefixed with
  ``import FloatLib`` and wrapped in ``namespace ChapterNN ... end ChapterNN``, compile it
  with ``lake -KbuildDir=<build> env lean --json`` from the repository root, and map every
  compiler message back to chapter line numbers. A block fenced as ```` ```lean standalone ````
  is compiled as its own file instead, with exactly the imports it carries, for the rare
  example that needs a module ``import FloatLib`` leaves out (the unchecked host FPU API);
* compare the ``-- `` result comments under ``#eval`` and friends with what Lean printed; a
  disagreement is an error, because SITE_SPEC.md says those comments are what the prose claims;
* reject em dashes (U+2014) and en dashes (U+2013) anywhere in the file;
* check that every ``[[Full.Lean.Name]]`` node link resolves to an id in site/data/nodes.json
  (a warning, never a failure, because the data pipeline and the chapters are written
  concurrently and the reader falls back to an inline code span);
* check that every ``![caption](assets/<file>)`` figure exists under content/assets.

We use ``lean --json`` rather than the plain text output because Lean prints information
messages (``#eval`` and ``#check`` results) without a position prefix, which makes plain text
ambiguous when an ``#eval`` result follows a multi-line warning. With JSON every message has
a severity and a position, so we can also list ``#eval`` results next to the chapter line
they came from and compare them with the ``-- `` result comments the prose relies on.

Python 3.12 standard library only. See site/tooling/README.md for usage.
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import os
import re
import shutil
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from pathlib import Path

TOOLING_DIR = Path(__file__).resolve().parent
SITE_DIR = TOOLING_DIR.parent
REPO_ROOT = SITE_DIR.parent

DEFAULT_CHAPTERS_DIR = SITE_DIR / "content" / "chapters"
DEFAULT_NODES_JSON = SITE_DIR / "data" / "nodes.json"
DEFAULT_JOBS = 6
DEFAULT_TIMEOUT = 600.0


def default_build_dir() -> Path:
    """The Lake build directory: FLOATLIB_BUILD_DIR when set, else the per-checkout default that
    tests/lib/lake.sh computes for every other repository script."""
    script = REPO_ROOT / "tests" / "lib" / "lake.sh"
    try:
        result = subprocess.run(
            ["bash", "--noprofile", "--norc", "-c",
             'set -euo pipefail; source "$1" >&2; printf %s "${FLOATLIB_BUILD_DIR:?}"',
             "site-build-path", str(script)],
            check=True, capture_output=True, text=True)
    except (OSError, subprocess.CalledProcessError) as error:
        detail = error.stderr.strip() if isinstance(error, subprocess.CalledProcessError) else str(error)
        raise RuntimeError(
            f"cannot resolve the local Lake build directory from {script}: {detail}") from error
    build_dir = result.stdout.strip()
    if not build_dir or not Path(build_dir).is_absolute():
        raise RuntimeError(f"{script} did not return an absolute FLOATLIB_BUILD_DIR")
    return Path(build_dir)

CHAPTER_FILE_RE = re.compile(r"^(?P<number>\d{2})-(?P<slug>[a-z0-9]+(?:-[a-z0-9]+)*)\.md$")
SLUG_RE = re.compile(r"^[a-z0-9]+(?:-[a-z0-9]+)*$")
FRONT_KEY_RE = re.compile(r"^(?P<key>[A-Za-z_][A-Za-z0-9_-]*):(?:[ \t]+(?P<value>.*))?$")
LIST_ITEM_RE = re.compile(r"^[ \t]*-[ \t]+(?P<value>.*)$")
FENCE_OPEN_RE = re.compile(r"^ {0,3}(?P<fence>`{3,}|~{3,})(?P<info>.*)$")
NODE_LINK_RE = re.compile(r"\[\[(?P<name>[^\[\]]*)\]\]")
FIGURE_RE = re.compile(r"!\[(?P<alt>[^\]]*)\]\((?P<target>[^)\s]*)(?:\s+\"[^\"]*\")?\)")
INLINE_CODE_RE = re.compile(r"(`+)[^`]*?\1")
TRAILING_COMMENT_RE = re.compile(r"^(?P<code>.*\S)[ \t]+--[ \t]*(?P<text>.*?)[ \t]*$")
COMMENT_LINE_RE = re.compile(r"^[ \t]*--[ \t]*(?P<text>.*?)[ \t]*$")
IMPORT_LINE_RE = re.compile(r"^\s*import\s+\S")
TWO_SENTENCES_RE = re.compile(r"[.!?][\"')\]]?\s+[A-Z0-9]")
DASHES = {"\u2014": "em dash (U+2014)", "\u2013": "en dash (U+2013)"}
REQUIRED_KEYS = ("number", "slug", "title", "summary")
OPTIONAL_KEYS = ("phases",)

ERROR = "error"
WARNING = "warning"


@dataclass
class Finding:
    severity: str
    kind: str
    message: str
    line: int | None = None
    column: int | None = None
    file: str | None = None

    def to_json(self) -> dict:
        record = {"severity": self.severity, "kind": self.kind, "message": self.message,
                  "line": self.line, "column": self.column}
        if self.file is not None:
            record["file"] = self.file
        return record


@dataclass
class LeanBlock:
    index: int
    fence_line: int
    lines: list[str]
    check: bool
    standalone: bool = False

    @property
    def first_line(self) -> int:
        return self.fence_line + 1

    @property
    def last_line(self) -> int:
        return self.fence_line + len(self.lines)


@dataclass
class CompileUnit:
    """One generated Lean file: the chapter's shared file or a standalone block."""
    path: Path
    line_map: dict[int, int]
    label: str


@dataclass
class Chapter:
    path: Path
    number: str
    slug: str
    lines: list[str]
    front_matter: dict[str, object] = field(default_factory=dict)
    body_start: int = 0
    title: str = ""
    phases: list[str] = field(default_factory=list)
    blocks: list[LeanBlock] = field(default_factory=list)
    prose: list[bool] = field(default_factory=list)
    findings: list[Finding] = field(default_factory=list)
    node_links: list[str] = field(default_factory=list)
    figures: list[str] = field(default_factory=list)
    lean_file: Path | None = None
    line_map: dict[int, int] = field(default_factory=dict)
    standalone_units: list[CompileUnit] = field(default_factory=list)
    code_lines: set[int] = field(default_factory=set)
    compiled: bool = False
    compile_seconds: float | None = None
    output: list[dict] = field(default_factory=list)
    compiler_noise: list[str] = field(default_factory=list)

    def add(self, severity: str, kind: str, message: str, line: int | None = None,
            column: int | None = None) -> None:
        self.findings.append(Finding(severity, kind, message, line, column))

    def errors(self, strict: bool) -> int:
        return sum(1 for f in self.findings if f.severity == ERROR or (strict and f.severity == WARNING))

    def warnings(self) -> int:
        return sum(1 for f in self.findings if f.severity == WARNING)

    def ok(self, strict: bool) -> bool:
        return self.errors(strict) == 0

    @property
    def checked_blocks(self) -> list[LeanBlock]:
        return [b for b in self.blocks if b.check]

    @property
    def shared_blocks(self) -> list[LeanBlock]:
        return [b for b in self.blocks if b.check and not b.standalone]

    @property
    def standalone_blocks(self) -> list[LeanBlock]:
        return [b for b in self.blocks if b.check and b.standalone]

    @property
    def compile_units(self) -> list[CompileUnit]:
        units = list(self.standalone_units)
        if self.lean_file is not None:
            units.insert(0, CompileUnit(self.lean_file, self.line_map, "shared"))
        return units


@dataclass
class CompileResult:
    seconds: float
    returncode: int | None = None
    messages: list[dict] = field(default_factory=list)
    noise: list[str] = field(default_factory=list)
    timed_out: bool = False
    failure: str | None = None


def display_path(path: Path) -> str:
    """Path relative to the current directory when it is inside it, else absolute.

    build.sh runs from the repository root, so this yields ``site/content/chapters/...`` there,
    which editors can jump to, while fixture runs from elsewhere stay unambiguous.
    """
    try:
        return str(path.resolve().relative_to(Path.cwd().resolve()))
    except ValueError:
        return str(path.resolve())


# --------------------------------------------------------------------------------------
# Discovery
# --------------------------------------------------------------------------------------

def discover_chapters(chapters_dir: Path, only: list[str], run_findings: list[Finding]) -> list[Chapter]:
    chapters: list[Chapter] = []
    for path in sorted(chapters_dir.iterdir()):
        if path.is_dir() or path.suffix != ".md" or path.name.lower() == "readme.md":
            continue
        match = CHAPTER_FILE_RE.match(path.name)
        if match is None:
            run_findings.append(Finding(
                ERROR, "layout",
                "chapter file name must be NN-slug.md (two digits, hyphen, lowercase slug); "
                "this file is skipped", file=display_path(path)))
            continue
        try:
            text = path.read_text(encoding="utf-8")
        except UnicodeDecodeError as error:
            run_findings.append(Finding(ERROR, "layout", f"not valid UTF-8: {error}",
                                        file=display_path(path)))
            continue
        if text.startswith("\ufeff"):
            text = text[1:]
        chapters.append(Chapter(path=path, number=match["number"], slug=match["slug"],
                                lines=text.splitlines()))

    for key in ("number", "slug"):
        seen: dict[str, Chapter] = {}
        for chapter in chapters:
            value = getattr(chapter, key)
            if value in seen:
                run_findings.append(Finding(
                    ERROR, "layout",
                    f"duplicate chapter {key} {value!r}: {display_path(seen[value].path)} and "
                    f"{display_path(chapter.path)}"))
            else:
                seen[value] = chapter

    if only:
        wanted = {token.strip() for token in only}
        chapters = [c for c in chapters if c.number in wanted or c.slug in wanted
                    or f"{c.number}-{c.slug}" in wanted]
    return chapters


# --------------------------------------------------------------------------------------
# Front matter (a small YAML subset: scalars, inline lists, block lists)
# --------------------------------------------------------------------------------------

def unquote(value: str) -> str:
    value = value.strip()
    if len(value) >= 2 and value[0] == value[-1] and value[0] in "\"'":
        inner = value[1:-1]
        if value[0] == '"':
            inner = inner.replace('\\"', '"').replace("\\\\", "\\")
        else:
            inner = inner.replace("''", "'")
        return inner
    # A YAML comment after a scalar.
    if " #" in value:
        value = value.split(" #", 1)[0].rstrip()
    return value


def parse_inline_list(value: str) -> list[str]:
    inner = value.strip()[1:-1].strip()
    if not inner:
        return []
    return [unquote(item) for item in inner.split(",")]


def parse_front_matter(chapter: Chapter) -> None:
    lines = chapter.lines
    if not lines or lines[0].strip() != "---":
        chapter.add(ERROR, "front-matter",
                    "missing front matter: the file must start with a `---` line", line=1)
        return
    end = None
    for index in range(1, len(lines)):
        if lines[index].strip() in ("---", "..."):
            end = index
            break
    if end is None:
        chapter.add(ERROR, "front-matter", "front matter is not closed by a `---` line", line=1)
        return
    chapter.body_start = end + 1

    data: dict[str, object] = {}
    positions: dict[str, int] = {}
    current_list_key: str | None = None
    for index in range(1, end):
        raw = lines[index]
        line_no = index + 1
        stripped = raw.strip()
        if not stripped or stripped.startswith("#"):
            continue
        item = LIST_ITEM_RE.match(raw)
        if item and current_list_key is not None and (raw.startswith(" ") or raw.startswith("-")):
            data[current_list_key].append(unquote(item["value"]))  # type: ignore[union-attr]
            continue
        entry = FRONT_KEY_RE.match(raw)
        if entry is None or raw[0] in " \t":
            chapter.add(ERROR, "front-matter",
                        f"unsupported front matter line {stripped!r}; use `key: value`, "
                        "`key: [a, b]`, or a block list of `- item` lines", line=line_no)
            current_list_key = None
            continue
        key = entry["key"]
        value = entry["value"]
        if key in data:
            chapter.add(ERROR, "front-matter", f"duplicate front matter key {key!r}", line=line_no)
            continue
        positions[key] = line_no
        if value is None or not value.strip():
            data[key] = []
            current_list_key = key
        elif value.strip().startswith("[") and value.strip().endswith("]"):
            data[key] = parse_inline_list(value)
            current_list_key = None
        else:
            data[key] = unquote(value)
            current_list_key = None
    chapter.front_matter = data

    for key in REQUIRED_KEYS:
        if key not in data:
            chapter.add(ERROR, "front-matter", f"front matter is missing `{key}`", line=1)
        elif not isinstance(data[key], str) or not data[key].strip():
            chapter.add(ERROR, "front-matter", f"front matter `{key}` must be a non-empty string",
                        line=positions.get(key, 1))
    for key in data:
        if key not in REQUIRED_KEYS and key not in OPTIONAL_KEYS:
            chapter.add(WARNING, "front-matter",
                        f"front matter key `{key}` is not in SITE_SPEC.md "
                        f"(known keys: {', '.join(REQUIRED_KEYS + OPTIONAL_KEYS)})",
                        line=positions.get(key, 1))

    number = data.get("number")
    if isinstance(number, str) and number.strip():
        if not re.fullmatch(r"\d{2}", number.strip()):
            chapter.add(ERROR, "front-matter",
                        f"`number` must be two digits, found {number!r}", line=positions["number"])
        elif number.strip() != chapter.number:
            chapter.add(ERROR, "front-matter",
                        f"`number` is {number!r} but the file name says {chapter.number!r}",
                        line=positions["number"])
    slug = data.get("slug")
    if isinstance(slug, str) and slug.strip():
        if SLUG_RE.match(slug) is None:
            chapter.add(ERROR, "front-matter",
                        f"`slug` must be lowercase words joined by hyphens, found {slug!r}",
                        line=positions["slug"])
        elif slug != chapter.slug:
            chapter.add(ERROR, "front-matter",
                        f"`slug` is {slug!r} but the file name says {chapter.slug!r}",
                        line=positions["slug"])
    title = data.get("title")
    if isinstance(title, str):
        chapter.title = title.strip()
    summary = data.get("summary")
    if isinstance(summary, str) and TWO_SENTENCES_RE.search(summary.strip()):
        chapter.add(WARNING, "front-matter",
                    "`summary` should be one sentence; this looks like more than one",
                    line=positions["summary"])
    phases = data.get("phases")
    if phases is not None:
        if not isinstance(phases, list):
            chapter.add(ERROR, "front-matter",
                        "`phases` must be a list (`phases: [a, b]` or a block list)",
                        line=positions["phases"])
        else:
            for phase in phases:
                if SLUG_RE.match(phase) is None:
                    chapter.add(ERROR, "front-matter",
                                f"phase id {phase!r} is not a slug", line=positions["phases"])
            chapter.phases = list(phases)


# --------------------------------------------------------------------------------------
# Fenced code blocks
# --------------------------------------------------------------------------------------

def scan_fences(chapter: Chapter) -> None:
    """Find fenced code blocks; collect the Lean ones and mark which lines are prose."""
    lines = chapter.lines
    prose = [True] * len(lines)
    for index in range(min(chapter.body_start, len(lines))):
        prose[index] = False
    open_fence: str | None = None
    open_index = 0
    info = ""
    collected: list[str] = []
    block_count = 0
    for index in range(chapter.body_start, len(lines)):
        line = lines[index]
        if open_fence is None:
            match = FENCE_OPEN_RE.match(line)
            if match and not (match["fence"][0] == "`" and "`" in match["info"]):
                open_fence = match["fence"]
                open_index = index
                info = match["info"].strip()
                collected = []
                prose[index] = False
            continue
        prose[index] = False
        stripped = line.strip()
        if (stripped.startswith(open_fence[0]) and set(stripped) == {open_fence[0]}
                and len(stripped) >= len(open_fence) and len(line) - len(line.lstrip()) <= 3):
            tokens = info.split()
            if tokens and tokens[0] == "lean":
                block_count += 1
                check = "nocheck" not in tokens[1:]
                standalone = "standalone" in tokens[1:]
                block = LeanBlock(index=block_count, fence_line=open_index + 1,
                                  lines=list(collected), check=check, standalone=standalone)
                chapter.blocks.append(block)
                if not check:
                    chapter.add(WARNING, "lean",
                                f"lean block {block_count} is marked `nocheck` and is not compiled",
                                line=block.fence_line)
                has_import = any(IMPORT_LINE_RE.match(code) for code in collected)
                if standalone and not has_import:
                    chapter.add(ERROR, "lean",
                                f"lean block {block_count} is marked `standalone` but has no "
                                "`import` line; a standalone block is compiled as its own file "
                                "and must import what it uses",
                                line=block.fence_line)
                for offset, code in enumerate(collected):
                    if IMPORT_LINE_RE.match(code) and not standalone:
                        chapter.add(ERROR, "lean",
                                    "lean block contains an `import`; the checker already prefixes "
                                    "`import FloatLib`, so remove the import (use `open` instead), "
                                    "or fence the block as ```lean standalone to compile it on its own",
                                    line=open_index + 2 + offset)
                if not any(code.strip() for code in collected):
                    chapter.add(WARNING, "lean", f"lean block {block_count} is empty",
                                line=block.fence_line)
            open_fence = None
            continue
        collected.append(line)
    if open_fence is not None:
        chapter.add(ERROR, "lean", "code fence opened here is never closed", line=open_index + 1)
    chapter.prose = prose


# --------------------------------------------------------------------------------------
# Prose checks
# --------------------------------------------------------------------------------------

def scan_dashes(chapter: Chapter) -> None:
    for index, line in enumerate(chapter.lines, start=1):
        for column, char in enumerate(line, start=1):
            if char in DASHES:
                chapter.add(ERROR, "dash", f"{DASHES[char]}; use a comma, colon, or new sentence",
                            line=index, column=column)


def mask_inline_code(line: str) -> str:
    return INLINE_CODE_RE.sub(lambda m: " " * len(m.group(0)), line)


def scan_node_links(chapter: Chapter, node_ids: set[str] | None) -> None:
    for index, line in enumerate(chapter.lines):
        if not chapter.prose[index]:
            continue
        for match in NODE_LINK_RE.finditer(mask_inline_code(line)):
            name = match["name"]
            column = match.start() + 1
            if not name or name != name.strip() or any(ch.isspace() for ch in name):
                chapter.add(ERROR, "link",
                            f"malformed node link [[{name}]]: the target must be a Lean name "
                            "with no spaces", line=index + 1, column=column)
                continue
            chapter.node_links.append(name)
            if node_ids is not None and name not in node_ids:
                chapter.add(WARNING, "link",
                            f"node link [[{name}]] does not match any id in nodes.json; "
                            "the reader will render it as inline code",
                            line=index + 1, column=column)


def scan_figures(chapter: Chapter, assets_dir: Path) -> None:
    for index, line in enumerate(chapter.lines):
        if not chapter.prose[index]:
            continue
        for match in FIGURE_RE.finditer(mask_inline_code(line)):
            target = match["target"]
            column = match.start() + 1
            normalized = target[2:] if target.startswith("./") else target
            chapter.figures.append(normalized)
            if not match["alt"].strip():
                chapter.add(WARNING, "figure", f"figure {target} has no caption text",
                            line=index + 1, column=column)
            if not normalized.startswith("assets/") or normalized == "assets/":
                chapter.add(ERROR, "figure",
                            f"figure target must be assets/<file> (SITE_SPEC.md), found {target!r}",
                            line=index + 1, column=column)
                continue
            relative = normalized[len("assets/"):]
            if ".." in Path(relative).parts:
                chapter.add(ERROR, "figure", f"figure target {target!r} escapes content/assets",
                            line=index + 1, column=column)
                continue
            if not (assets_dir / relative).is_file():
                chapter.add(ERROR, "figure",
                            f"figure file not found: {display_path(assets_dir / relative)}",
                            line=index + 1, column=column)


# --------------------------------------------------------------------------------------
# Lean extraction and compilation
# --------------------------------------------------------------------------------------

def write_lean_file(chapter: Chapter, scratch: Path) -> None:
    """Write the chapter's shared Lean file and one file per standalone block."""
    namespace = f"Chapter{chapter.number}"
    header = [
        f"-- Generated by site/tooling/check_chapters.py from {display_path(chapter.path)}.",
        "-- Edits here are lost; edit the chapter instead.",
    ]
    blocks = chapter.shared_blocks
    if blocks:
        lean_path = scratch / f"{namespace}.lean"
        out: list[str] = header + ["import FloatLib", "", f"namespace {namespace}"]
        line_map: dict[int, int] = {}
        for block in blocks:
            out.append("")
            out.append(f"-- lean block {block.index}: chapter lines {block.first_line} to {block.last_line}")
            for offset, code in enumerate(block.lines):
                out.append(code)
                line_map[len(out)] = block.first_line + offset
                chapter.code_lines.add(block.first_line + offset)
        out.append("")
        out.append(f"end {namespace}")
        out.append("")
        scratch.mkdir(parents=True, exist_ok=True)
        lean_path.write_text("\n".join(out), encoding="utf-8")
        chapter.lean_file = lean_path
        chapter.line_map = line_map
    # A standalone block is the whole file: its own imports, no namespace wrapper, so that what
    # the chapter shows is exactly what is compiled. Lean wants imports first, so the generated
    # header goes after the block's import lines.
    for block in chapter.standalone_blocks:
        lean_path = scratch / f"{namespace}_block{block.index}.lean"
        out = []
        line_map = {}
        imports_done = False
        for offset, code in enumerate(block.lines):
            if not imports_done and not IMPORT_LINE_RE.match(code) and code.strip():
                out.extend(header + [f"-- lean block {block.index} (standalone): chapter lines "
                                     f"{block.first_line} to {block.last_line}"])
                imports_done = True
            out.append(code)
            line_map[len(out)] = block.first_line + offset
            chapter.code_lines.add(block.first_line + offset)
        out.append("")
        scratch.mkdir(parents=True, exist_ok=True)
        lean_path.write_text("\n".join(out), encoding="utf-8")
        chapter.standalone_units.append(CompileUnit(lean_path, line_map, f"block {block.index}"))


def compile_lean(lean_path: Path, repo_root: Path, build_dir: Path, lake: str,
                 timeout: float) -> CompileResult:
    command = [lake, f"-KbuildDir={build_dir}", "env", "lean", "--json", str(lean_path)]
    env = dict(os.environ, FLOATLIB_BUILD_DIR=str(build_dir))
    start = time.monotonic()
    try:
        proc = subprocess.run(command, cwd=repo_root, env=env, capture_output=True, text=True,
                              errors="replace", timeout=timeout)
    except subprocess.TimeoutExpired:
        return CompileResult(seconds=time.monotonic() - start, timed_out=True)
    except OSError as error:
        return CompileResult(seconds=time.monotonic() - start, failure=str(error))
    result = CompileResult(seconds=time.monotonic() - start, returncode=proc.returncode)
    for line in proc.stdout.splitlines():
        record = None
        if line.startswith("{"):
            try:
                record = json.loads(line)
            except ValueError:
                record = None
        if isinstance(record, dict) and "severity" in record and "pos" in record:
            result.messages.append(record)
        elif line.strip():
            result.noise.append(line)
    result.noise.extend(line for line in proc.stderr.splitlines() if line.strip())
    return result


def result_comment(chapter: Chapter, chapter_line: int) -> list[str] | None:
    """The `-- ` result comment attached to a command.

    Either a trailing comment on the command's own line, or the run of comment-only lines that
    follows the command, skipping indented continuation lines of a multi-line command. We stop at
    a blank line or at the next column-zero command, so a comment that introduces the next
    command is not mistaken for a result.
    """
    trailing = TRAILING_COMMENT_RE.match(chapter.lines[chapter_line - 1])
    if trailing:
        return [trailing["text"]]
    cursor = chapter_line + 1
    while cursor in chapter.code_lines:
        text = chapter.lines[cursor - 1]
        comment = COMMENT_LINE_RE.match(text)
        if comment:
            collected = [comment["text"]]
            cursor += 1
            while cursor in chapter.code_lines:
                more = COMMENT_LINE_RE.match(chapter.lines[cursor - 1])
                if more is None:
                    break
                collected.append(more["text"])
                cursor += 1
            return collected
        if not text.strip() or not text[0].isspace():
            return None
        cursor += 1
    return None


def result_mismatch(actual_text: str, expected: list[str]) -> tuple[str, str] | None:
    """First (printed, claimed) pair of lines that differ, or None when the comment agrees.

    A comment that covers only the first lines of a multi-line output is a partial claim rather
    than a wrong one, so we compare only as many lines as the comment provides. A comment may also
    quote a contiguous excerpt from further down a multi-line report (the planner chapter shows only the
    Execution block of `#float_info`): when its first line occurs verbatim later in the output we
    compare from there, and the comment agrees if some such alignment matches line for line. When
    no alignment matches we report the disagreement against the head of the output, which is the
    common case of a single-line result.
    """
    actual = [line.strip() for line in actual_text.strip().splitlines()] or [""]
    claimed = [line.strip() for line in expected]
    if not claimed:
        return None
    starts = [0] + [index for index, line in enumerate(actual) if index > 0 and line == claimed[0]]
    first_mismatch: tuple[str, str] | None = None
    for start in starts:
        mismatch = next(((printed, said) for printed, said in zip(actual[start:], claimed)
                         if printed != said), None)
        if mismatch is None:
            return None
        if first_mismatch is None:
            first_mismatch = mismatch
    return first_mismatch


def apply_compile_result(chapter: Chapter, unit: CompileUnit, result: CompileResult,
                         timeout: float) -> None:
    chapter.compiled = True
    chapter.compile_seconds = round((chapter.compile_seconds or 0.0) + result.seconds, 2)
    chapter.compiler_noise.extend(result.noise)
    lean_display = display_path(unit.path)
    if result.failure:
        chapter.add(ERROR, "compile", f"could not run lake: {result.failure}")
        return
    if result.timed_out:
        chapter.add(ERROR, "compile", f"compile timed out after {timeout:g} s ({lean_display})")
        return

    saw_error = False
    for message in result.messages:
        severity = message.get("severity")
        pos = message.get("pos") or {}
        lean_line = pos.get("line")
        column = (pos.get("column") or 0) + 1
        text = str(message.get("data", "")).rstrip()
        chapter_line = unit.line_map.get(lean_line)
        where = ""
        if chapter_line is None:
            where = f" (in generated scaffolding, {lean_display}:{lean_line})"
        if severity == "error":
            saw_error = True
            chapter.add(ERROR, "compile", f"lean: {text}{where}", line=chapter_line, column=column)
        elif severity == "warning":
            if message.get("kind") == "hasSorry" or "declaration uses `sorry`" in text:
                chapter.add(ERROR, "sorry",
                            "lean: declaration uses `sorry`; chapter code must be fully proved"
                            + where, line=chapter_line, column=column)
            else:
                chapter.add(WARNING, "compile", f"lean: {text}{where}", line=chapter_line,
                            column=column)
        else:
            expected = result_comment(chapter, chapter_line) if chapter_line is not None else None
            chapter.output.append({"line": chapter_line, "column": column, "text": text,
                                   "claimed": expected})
            mismatch = result_mismatch(text, expected) if expected is not None else None
            if mismatch is not None:
                # An error, not a warning: SITE_SPEC.md says the result comments are what the
                # prose claims, so a stale one must never ship.
                printed, said = mismatch
                chapter.add(ERROR, "result",
                            f"lean printed `{printed}` but the result comment says `{said}`",
                            line=chapter_line, column=column)
    if result.returncode not in (0, None) and not saw_error:
        detail = "\n".join(result.noise) if result.noise else "no diagnostic output"
        chapter.add(ERROR, "compile", f"lean exited with code {result.returncode}: {detail}")


# --------------------------------------------------------------------------------------
# nodes.json
# --------------------------------------------------------------------------------------

def load_nodes(nodes_json: Path, run_findings: list[Finding]) -> tuple[set[str] | None, set[str] | None]:
    if not nodes_json.is_file():
        run_findings.append(Finding(
            WARNING, "link",
            f"{display_path(nodes_json)} does not exist; [[Name]] links and `phases` were not "
            "resolved (run the data export first to check them)"))
        return None, None
    try:
        payload = json.loads(nodes_json.read_text(encoding="utf-8"))
        node_ids = {str(node["id"]) for node in payload.get("nodes", [])}
        phase_ids = {str(phase["id"]) for phase in payload.get("phases", [])}
    except (ValueError, KeyError, TypeError, AttributeError) as error:
        run_findings.append(Finding(ERROR, "link",
                                    f"{display_path(nodes_json)} is not a valid nodes file: {error}"))
        return None, None
    return node_ids, phase_ids


def check_phases(chapter: Chapter, phase_ids: set[str] | None) -> None:
    if phase_ids is None:
        return
    for phase in chapter.phases:
        if phase not in phase_ids:
            chapter.add(WARNING, "front-matter",
                        f"phase {phase!r} is not a phase id in nodes.json", line=1)


# --------------------------------------------------------------------------------------
# Reporting
# --------------------------------------------------------------------------------------

def finding_prefix(file: str | None, finding: Finding) -> str:
    if file is None:
        return finding.severity
    where = file
    if finding.line is not None:
        where += f":{finding.line}"
        if finding.column is not None:
            where += f":{finding.column}"
    return f"{where}: {finding.severity}"


def print_finding(file: str | None, finding: Finding, indent: str = "  ") -> None:
    first, *rest = finding.message.split("\n")
    print(f"{indent}{finding_prefix(file, finding)}: {first}")
    for line in rest:
        print(f"{indent}    {line}")


def sort_key(finding: Finding) -> tuple:
    return (finding.line or 0, finding.column or 0, finding.severity != ERROR, finding.message)


def print_console(chapters: list[Chapter], run_findings: list[Finding], args: argparse.Namespace,
                  node_ids: set[str] | None) -> None:
    nodes_note = (f"{len(node_ids)} node ids from {display_path(args.nodes_json)}"
                  if node_ids is not None else "nodes.json absent, links not resolved")
    compile_note = "compile off" if args.no_compile else f"compile with {args.jobs} jobs"
    print(f"check_chapters: {len(chapters)} chapter(s) in {display_path(args.chapters_dir)}; "
          f"{nodes_note}; {compile_note}; scratch {display_path(args.scratch)}")
    for finding in run_findings:
        print_finding(finding.file, finding, indent="")
    for chapter in chapters:
        blocks = len(chapter.checked_blocks)
        skipped = len(chapter.blocks) - blocks
        standalone = len(chapter.standalone_blocks)
        parts = [f"{blocks} lean block{'s' if blocks != 1 else ''}"]
        if standalone:
            parts.append(f"{standalone} standalone")
        if skipped:
            parts.append(f"{skipped} nocheck")
        if chapter.compiled:
            parts.append(f"{chapter.compile_seconds:.1f}s")
        elif blocks and args.no_compile:
            parts.append("not compiled")
        status = "ok" if chapter.ok(args.strict) else "FAIL"
        counts = []
        errors = chapter.errors(strict=False)
        if errors:
            counts.append(f"{errors} error{'s' if errors != 1 else ''}")
        if chapter.warnings():
            counts.append(f"{chapter.warnings()} warning{'s' if chapter.warnings() != 1 else ''}")
        detail = ", ".join(parts + counts)
        print(f"{chapter.number} {chapter.slug}: {status} ({detail})")
        file = display_path(chapter.path)
        for finding in sorted(chapter.findings, key=sort_key):
            print_finding(file, finding)
        if args.show_output and chapter.output:
            for item in chapter.output:
                where = f"{file}:{item['line']}" if item["line"] is not None else file
                first, *rest = item["text"].split("\n")
                print(f"  {where}: output: {first}")
                for line in rest:
                    print(f"      {line}")
    passed = sum(1 for c in chapters if c.ok(args.strict))
    errors = sum(c.errors(strict=False) for c in chapters) + sum(1 for f in run_findings if f.severity == ERROR)
    warnings = sum(c.warnings() for c in chapters) + sum(1 for f in run_findings if f.severity == WARNING)
    print(f"summary: {passed} of {len(chapters)} chapter(s) passed; {errors} error(s), "
          f"{warnings} warning(s){' (strict: warnings fail)' if args.strict else ''}")


def json_report(chapters: list[Chapter], run_findings: list[Finding], args: argparse.Namespace,
                node_ids: set[str] | None, ok: bool) -> dict:
    return {
        "tool": "site/tooling/check_chapters.py",
        "generatedAt": dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds"),
        "repoRoot": str(args.repo_root),
        "chaptersDir": str(args.chapters_dir),
        "assetsDir": str(args.assets_dir),
        "nodesJson": str(args.nodes_json) if node_ids is not None else None,
        "nodeIds": len(node_ids) if node_ids is not None else None,
        "scratch": str(args.scratch),
        "buildDir": str(args.build_dir) if args.build_dir else None,
        "compile": not args.no_compile,
        "strict": args.strict,
        "ok": ok,
        "findings": [f.to_json() for f in run_findings],
        "chapters": [{
            "number": c.number,
            "slug": c.slug,
            "file": str(c.path.resolve()),
            "title": c.title,
            "phases": c.phases,
            "ok": c.ok(args.strict),
            "leanBlocks": len(c.checked_blocks),
            "leanBlocksSkipped": len(c.blocks) - len(c.checked_blocks),
            "leanFile": str(c.lean_file) if c.lean_file else None,
            "standaloneFiles": [str(u.path) for u in c.standalone_units],
            "compiled": c.compiled,
            "compileSeconds": c.compile_seconds,
            "nodeLinks": c.node_links,
            "figures": c.figures,
            "findings": [f.to_json() for f in sorted(c.findings, key=sort_key)],
            "output": c.output,
            "compilerNoise": c.compiler_noise,
        } for c in chapters],
        "summary": {
            "chapters": len(chapters),
            "passed": sum(1 for c in chapters if c.ok(args.strict)),
            "failed": sum(1 for c in chapters if not c.ok(args.strict)),
            "errors": sum(c.errors(strict=False) for c in chapters)
                      + sum(1 for f in run_findings if f.severity == ERROR),
            "warnings": sum(c.warnings() for c in chapters)
                        + sum(1 for f in run_findings if f.severity == WARNING),
        },
    }


# --------------------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------------------

def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        prog="check_chapters.py",
        description="Validate the FloatLib site chapters and compile their Lean blocks.")
    parser.add_argument("--chapters-dir", type=Path, default=DEFAULT_CHAPTERS_DIR,
                        help="directory of NN-slug.md chapters (default: site/content/chapters)")
    parser.add_argument("--assets-dir", type=Path, default=None,
                        help="directory figures are checked against "
                             "(default: <chapters-dir>/../assets)")
    parser.add_argument("--nodes-json", type=Path, default=DEFAULT_NODES_JSON,
                        help="generated nodes file for [[Name]] links (default: site/data/nodes.json)")
    parser.add_argument("--scratch", type=Path, default=None,
                        help="where the extracted ChapterNN.lean files are written "
                             "(default: FLOATLIB_SITE_SCRATCH, or "
                             "${FLOATLIB_BUILD_DIR}-site-check)")
    parser.add_argument("--repo-root", type=Path, default=REPO_ROOT,
                        help="repository root that `lake env` runs from")
    parser.add_argument("--build-dir", type=Path, default=None,
                        help="Lake build directory passed as -KbuildDir")
    parser.add_argument("--only", action="append", default=[], metavar="NN",
                        help="check only this chapter (number or slug); may be repeated")
    parser.add_argument("--no-compile", action="store_true",
                        help="extract the Lean files but do not compile them")
    parser.add_argument("--jobs", type=int, default=DEFAULT_JOBS,
                        help=f"parallel compiles (default {DEFAULT_JOBS})")
    parser.add_argument("--timeout", type=float, default=DEFAULT_TIMEOUT,
                        help=f"seconds allowed per chapter compile (default {DEFAULT_TIMEOUT:g})")
    parser.add_argument("--json", type=Path, default=None, metavar="PATH",
                        help="write a machine readable report here")
    parser.add_argument("--strict", action="store_true",
                        help="treat warnings (unresolved links, nocheck blocks, compiler warnings) "
                             "as failures; result comment mismatches are always errors")
    parser.add_argument("--show-output", action="store_true",
                        help="print #eval and #check results next to their chapter lines")
    args = parser.parse_args(argv)
    if args.assets_dir is None:
        args.assets_dir = args.chapters_dir.parent / "assets"
    if args.jobs < 1:
        parser.error("--jobs must be at least 1")
    try:
        if args.build_dir is None and (not args.no_compile or (
                args.scratch is None and not os.environ.get("FLOATLIB_SITE_SCRATCH"))):
            args.build_dir = default_build_dir()
        if args.scratch is None:
            args.scratch = Path(os.environ.get("FLOATLIB_SITE_SCRATCH")
                                or f"{args.build_dir}-site-check")
    except RuntimeError as error:
        parser.error(str(error))
    return args


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    if not args.chapters_dir.is_dir():
        print(f"check_chapters: chapters directory not found: {args.chapters_dir}", file=sys.stderr)
        return 2
    lake = None
    if not args.no_compile:
        lake = shutil.which("lake") or str(Path.home() / ".elan" / "bin" / "lake")
        if not Path(lake).is_file():
            print("check_chapters: `lake` not found on PATH or in ~/.elan/bin", file=sys.stderr)
            return 2
        if not (args.build_dir / "lib").is_dir():
            print(f"check_chapters: build directory has no lib/: {args.build_dir} "
                  "(the library must be built there; see site/tooling/README.md)", file=sys.stderr)
            return 2
        if not (args.repo_root / "lakefile.lean").is_file():
            print(f"check_chapters: no lakefile.lean in --repo-root {args.repo_root}", file=sys.stderr)
            return 2

    run_findings: list[Finding] = []
    chapters = discover_chapters(args.chapters_dir, args.only, run_findings)
    if args.only and not chapters:
        print(f"check_chapters: --only {' '.join(args.only)} matched no chapter in "
              f"{display_path(args.chapters_dir)}", file=sys.stderr)
        return 2
    if not chapters:
        run_findings.append(Finding(WARNING, "layout",
                                    f"no chapters found in {display_path(args.chapters_dir)}"))
    node_ids, phase_ids = load_nodes(args.nodes_json, run_findings)

    for chapter in chapters:
        parse_front_matter(chapter)
        scan_fences(chapter)
        scan_dashes(chapter)
        scan_node_links(chapter, node_ids)
        scan_figures(chapter, args.assets_dir)
        check_phases(chapter, phase_ids)
        write_lean_file(chapter, args.scratch)
        if args.no_compile:
            for block in chapter.checked_blocks:
                for offset, code in enumerate(block.lines):
                    if re.search(r"\bsorry\b", code):
                        chapter.add(WARNING, "sorry",
                                    "`sorry` in a lean block (textual scan; compile to confirm)",
                                    line=block.first_line + offset)

    if not args.no_compile:
        to_compile = [(c, unit) for c in chapters for unit in c.compile_units]
        if to_compile:
            with ThreadPoolExecutor(max_workers=min(args.jobs, len(to_compile))) as pool:
                futures = [(c, unit, pool.submit(compile_lean, unit.path, args.repo_root,
                                                 args.build_dir, lake, args.timeout))
                           for c, unit in to_compile]
                for chapter, unit, future in futures:
                    apply_compile_result(chapter, unit, future.result(), args.timeout)

    run_errors = any(f.severity == ERROR or (args.strict and f.severity == WARNING)
                     for f in run_findings)
    ok = all(c.ok(args.strict) for c in chapters) and not run_errors
    print_console(chapters, run_findings, args, node_ids)
    if args.json is not None:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(json_report(chapters, run_findings, args, node_ids, ok),
                                        indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
        print(f"report: {display_path(args.json)}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
