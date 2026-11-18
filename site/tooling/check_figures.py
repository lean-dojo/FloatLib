#!/usr/bin/env python3
"""Check the guide's figures: files, captions, numbers and freshness.

Two checks, both without Lean and without the reader:

* **Text.** Every image line of a chapter is `![alt](assets/<file>.png "caption")` with a
  non-empty alt text and a caption of at most four sentences that ends with a full stop. The
  reader numbers figures `<chapter>.<ordinal>` in the order of the image lines and anchors each
  at `#/chapter/<slug>/figure-<asset stem>`, so every `[Figure N.M](...)` link in the prose must
  carry the number of the figure it points to, every figure must be referred to at least once,
  a chapter must first refer to its figures in the order in which it shows them, and no
  `Figure N.M` may appear without its link.
* **Freshness** (`--fresh`). Every generator under `content/assets/figures/`, and
  `benchmarks/plots/flocq_matched.py`, is run into a scratch
  directory, and every PNG, SVG and view manifest it writes is compared byte for byte with the
  file in `content/assets/`. A benchmark figure that a chapter shows is a copy of the file of the
  same name in `benchmarks/results/figures/`, which `benchmarks/plots/figures.py draw` writes, and
  is compared with it. An asset that no generator writes is reported too. The generators
  refuse text that belongs in a caption (see `figstyle.check_rules`), so a figure that passes
  carries no title, note or sentence. Needs Matplotlib 3.11.0.

usage: python3 site/tooling/check_figures.py [--fresh] [--scratch DIR] [--list]

Exit status 1 when a check fails.
"""

from __future__ import annotations

import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

SITE = Path(__file__).resolve().parents[1]
REPO = SITE.parent
CHAPTERS = SITE / "content" / "chapters"
ASSETS = SITE / "content" / "assets"

IMAGE = re.compile(r'^!\[(?P<alt>[^\]]*)\]\((?P<src>assets/[^\s)]+)(?:\s+"(?P<title>[^"]*)")?\)\s*$')
LINK = re.compile(r"\[(?P<label>Figures? [^\]]+)\]"
                  r"\(#/chapter/(?P<slug>[a-z0-9-]+)/figure-(?P<stem>[a-z0-9-]+)\)")
BARE = re.compile(r"(?<![\[\w])Figures? \d+\.\d+")
SENTENCE_END = re.compile(r"[.!?](?=\s|$)")
MAX_SENTENCES = 4

# Assets that are images but not figures of a chapter.
NOT_GENERATED = {"floatlib-logo.png"}
BENCHMARK_FIGURES = REPO / "benchmarks" / "results" / "figures"


def front_matter(text: str, key: str) -> str:
    match = re.search(rf'^{key}:\s*"?([^"\n]+)"?\s*$', text.split("---", 2)[1], re.M)
    if match is None:
        raise SystemExit(f"front matter has no {key}")
    return match.group(1).strip()


def read_figures() -> tuple[list[dict], list[str]]:
    """Every figure of every chapter, in reading order, and the problems found on the way."""
    figures: list[dict] = []
    problems: list[str] = []
    index: dict[tuple[str, str], dict] = {}
    chapters = sorted(CHAPTERS.glob("*.md"))
    for path in chapters:
        text = path.read_text(encoding="utf-8")
        number = int(front_matter(text, "number"))
        slug = front_matter(text, "slug")
        ordinal = 0
        for lineno, line in enumerate(text.splitlines(), 1):
            if not line.startswith("!["):
                continue
            where = f"{path.name}:{lineno}"
            match = IMAGE.match(line)
            if match is None:
                problems.append(f'{where}: image line is not ![alt](assets/<file> "caption")')
                continue
            ordinal += 1
            stem = Path(match["src"]).stem
            record = dict(chapter=number, slug=slug, where=where, stem=stem,
                          file=Path(match["src"]).name, number=f"{number}.{ordinal}",
                          alt=match["alt"].strip(), caption=(match["title"] or "").strip(),
                          references=0, first=None)
            figures.append(record)
            index[(slug, stem)] = record
            if not (ASSETS / record["file"]).is_file():
                problems.append(f"{where}: {match['src']} does not exist")
            if not record["alt"]:
                problems.append(f"{where}: Figure {record['number']} has no alt text")
            caption = record["caption"]
            if not caption:
                problems.append(f"{where}: Figure {record['number']} has no caption")
            elif not caption.endswith("."):
                problems.append(f"{where}: the caption of Figure {record['number']} does not "
                                "end with a full stop")
            elif len(SENTENCE_END.findall(caption)) > MAX_SENTENCES:
                problems.append(f"{where}: the caption of Figure {record['number']} has more "
                                f"than {MAX_SENTENCES} sentences")
            if caption and caption == record["alt"]:
                problems.append(f"{where}: the alt text of Figure {record['number']} repeats "
                                "its caption")
    for path in chapters:
        text = path.read_text(encoding="utf-8")
        here = front_matter(text, "slug")
        for lineno, line in enumerate(text.splitlines(), 1):
            if line.startswith("!["):
                continue
            where = f"{path.name}:{lineno}"
            for match in LINK.finditer(line):
                record = index.get((match["slug"], match["stem"]))
                if record is None:
                    problems.append(f"{where}: {match[0]} points to no figure")
                    continue
                record["references"] += 1
                if record["first"] is None and match["slug"] == here:
                    record["first"] = (lineno, match.start(), where)
                if record["number"] not in re.findall(r"\d+\.\d+", match["label"]):
                    problems.append(f"{where}: {match['label']!r} links to {record['stem']}, "
                                    f"which is Figure {record['number']}")
            for match in BARE.finditer(LINK.sub("", line)):
                problems.append(f"{where}: {match[0]!r} has no link to its figure")
    latest: dict[str, dict] = {}
    for record in figures:
        if not record["references"]:
            problems.append(f"{record['where']}: Figure {record['number']} ({record['stem']}) "
                            "is never referred to in the prose")
        if record["first"] is None:
            continue
        earlier = latest.get(record["slug"])
        if earlier is not None and record["first"][:2] < earlier["first"][:2]:
            problems.append(f"{record['first'][2]}: Figure {record['number']} is first referred to "
                            f"before Figure {earlier['number']} ({earlier['first'][2]}), but is "
                            "shown after it")
        else:
            latest[record["slug"]] = record
    return figures, problems


def generators() -> list[tuple[Path, list[str]]]:
    """Each generator with the arguments that send its files to the directory `{out}`."""
    jobs: list[tuple[Path, list[str]]] = []
    for script in sorted((ASSETS / "figures").glob("ch*.py")):
        name = ("public-binary-performance" if script.stem == "ch15_public_binary"
                else script.stem.replace("_", "-"))
        jobs.append((script, ["--out", f"{{out}}/{name}.png"]))
    jobs.append((REPO / "benchmarks" / "plots" / "flocq_matched.py",
                 ["--out", "{out}/flocq-matched.png"]))
    return jobs


def is_figure_file(path: Path) -> bool:
    return path.suffix in {".png", ".svg"} or path.name.endswith("-series.json")


def check_fresh(scratch: Path) -> list[str]:
    problems: list[str] = []
    environment = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    for script, arguments in generators():
        command = [sys.executable, str(script)] + [a.format(out=scratch) for a in arguments]
        result = subprocess.run(command, env=environment, capture_output=True, text=True)
        if result.returncode != 0:
            tail = (result.stderr or result.stdout).strip().splitlines()[-1:]
            problems.append(f"{script.relative_to(REPO)} failed: {' '.join(tail)}")
    for source in sorted(BENCHMARK_FIGURES.glob("*.png")):
        if (ASSETS / source.name).is_file():
            shutil.copyfile(source, scratch / source.name)
    written = {path.name for path in scratch.iterdir() if is_figure_file(path)}
    for name in sorted(written):
        kept = ASSETS / name
        if not kept.is_file():
            problems.append(f"{name} is generated but missing from content/assets")
        elif kept.read_bytes() != (scratch / name).read_bytes():
            problems.append(f"content/assets/{name} is stale: regenerate it")
    for path in sorted(ASSETS.iterdir()):
        if is_figure_file(path) and path.name not in written | NOT_GENERATED:
            problems.append(f"content/assets/{path.name} is written by no generator")
    if not problems:
        print(f"freshness: {len(written)} generated files equal content/assets")
    return problems


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--fresh", action="store_true",
                        help="also regenerate every figure and compare it with content/assets")
    parser.add_argument("--scratch", type=Path, default=None,
                        help="directory for the regenerated files (default: a temporary one)")
    parser.add_argument("--list", action="store_true",
                        help="print chapter, number, file and caption of every figure")
    args = parser.parse_args()

    figures, problems = read_figures()
    if args.list:
        for record in figures:
            print("\t".join([str(record["chapter"]), record["number"], record["file"],
                             record["caption"]]))
    else:
        print(f"text: {len(figures)} figures in {len({r['chapter'] for r in figures})} chapters")
    if args.fresh:
        if args.scratch is not None:
            args.scratch.mkdir(parents=True, exist_ok=True)
            problems += check_fresh(args.scratch)
        else:
            scratch = Path(tempfile.mkdtemp(prefix="floatlib-figures-"))
            try:
                problems += check_fresh(scratch)
            finally:
                shutil.rmtree(scratch, ignore_errors=True)
    for problem in problems:
        print(f"error: {problem}", file=sys.stderr)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
