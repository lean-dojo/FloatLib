#!/usr/bin/env python3
"""Small summaries of a run of the standard suites, for the repository, the docs and the figures.

    summarize.py RESULTS [--tools TOOLS.csv] [--out DIRECTORY] [--conditions TEXT]

RESULTS is the directory that `benchmarks/suites/run.sh` wrote (`FLOATLIB_SUITE_RESULTS`), with
`fpbench/`, `inequalities/`, `correct-rounding/` and `testfloat/`. Its `results.csv` files hold
every statement, plan and command, and are tens of megabytes: they stay outside the repository.
This script keeps one short row per case (per group of cases for the hard-to-round inputs) in

    fpbench.csv              one row per program, default precision and method
    fpbench-tools.csv        one row per program, default precision and external tool (`--tools`:
                             the results of `benchmarks/fpbench/tools.py`, which do not depend
                             on FloatLib; without `--tools` the rows of the summary before stay)
    fpbench-comparison.csv   FloatLib's proved numerical bound over each tool's bound
                             (`benchmarks/fpbench/compare.py`), where the contracts allow a ratio
    inequalities.csv         one row per goal and route (`interval`, and `interval` with the
                             constraint engine)
    correct-rounding.csv     one row per domain, source, format, function and outcome, with the
                             number of inputs and the median times
    testfloat.csv            one row per campaign (format, operation, rounding direction)
    counts.csv               suite, group, outcome, count: the numbers the docs quote
    README.md                the same numbers as tables
    provenance.json          commits, toolchain, time window, harness settings, and the size and
                             SHA-256 of each `results.csv` that was read

under DIRECTORY (default `benchmarks/results/suites`). Nothing is measured here. A suite whose
`results.csv` is missing keeps what DIRECTORY has of it from the summary before: its short file,
its counts and its record in `provenance.json`, so one suite can be run again alone. A commit is
named only when a remote branch of the checkout has it.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
import statistics
import subprocess
import sys
from collections import Counter, OrderedDict, defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE.parent / "fpbench"))
csv.field_size_limit(1 << 30)

TOOLS = ("fptaylor", "gappa", "daisy", "satire")


def read(path: Path) -> list:
    with path.open(newline="") as stream:
        return list(csv.DictReader(stream))


def write(path: Path, columns: list, rows: list) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="") as stream:
        writer = csv.writer(stream, lineterminator="\n")
        writer.writerow(columns)
        for row in rows:
            writer.writerow([row.get(column, "") if isinstance(row, dict) else row[i]
                             for i, column in enumerate(columns)])


def milliseconds(nanoseconds: str):
    return round(float(nanoseconds) / 1e6, 3) if nanoseconds not in ("", None) else ""


def median(values: list):
    return round(statistics.median(values)) if values else ""


def source(path: Path) -> dict:
    data = path.read_bytes()
    return {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


PUBLISHED = {}


def named(commit: str) -> str:
    """`commit` when a remote-tracking branch of the checkout contains it, so that a reader can
    look it up, and nothing for a commit that only the measured checkout has."""
    if commit and commit not in PUBLISHED:
        try:
            branches = subprocess.run(["git", "-C", str(ROOT), "branch", "--remotes", "--contains", commit],
                                      capture_output=True, text=True).stdout
        except OSError:
            branches = ""
        PUBLISHED[commit] = bool(branches.strip())
    return commit if commit and PUBLISHED[commit] else ""


def window(rows: list) -> dict:
    stamps = sorted(r["measurement_utc"] for r in rows if r.get("measurement_utc"))
    commits = sorted({named(r.get("floatlib_commit", "")) for r in rows} - {""})
    return {"first_utc": stamps[0] if stamps else "", "last_utc": stamps[-1] if stamps else "",
            "floatlib_commits": commits}


def fpbench(results: Path, out: Path, tools: Path, counts: list, provenance: dict, earlier: dict) -> None:
    path = results / "fpbench" / "results.csv"
    if not path.exists():
        return
    rows = read(path)
    columns = ["id", "source_file", "index", "program", "default_precision", "effective_precision",
               "method", "status", "numeric_status", "proposed_bound", "numeric_bound",
               "elapsed_ms", "numeric_elapsed_ms", "process_elapsed_seconds",
               "numeric_process_elapsed_seconds",
               *[f"{tool}_published_ratio" for tool in TOOLS], "floatlib_commit", "measurement_utc"]
    slim = []
    for row in rows:
        entry = {column: row.get(column, "") for column in columns}
        entry["elapsed_ms"] = milliseconds(row.get("elapsed_ns"))
        entry["numeric_elapsed_ms"] = milliseconds(row.get("numeric_elapsed_ns"))
        entry["floatlib_commit"] = named(row.get("floatlib_commit", ""))
        slim.append(entry)
    write(out / "fpbench.csv", columns, slim)
    for (method, status), count in sorted(Counter((r["method"], r["status"]) for r in rows).items()):
        counts.append(["fpbench", f"{method}, conditional theorem", status, count])
    for (method, status), count in sorted(Counter(
            (r["method"], r["numeric_status"]) for r in rows if r["method"] != "backward").items()):
        counts.append(["fpbench", f"{method}, numerical bound", status, count])

    def within(row: dict, column: str, limit: float = 20.0) -> bool:
        return row.get(column) not in ("", None) and float(row[column]) <= limit
    for method in ("forward", "closed", "backward"):
        counts.append(["fpbench", f"{method}, conditional theorem", "proved within 20 s of process time",
                       sum(1 for r in rows if r["method"] == method and r["status"] == "proved"
                           and within(r, "process_elapsed_seconds"))])
        if method != "backward":
            counts.append(["fpbench", f"{method}, numerical bound", "proved within 20 s of process time",
                           sum(1 for r in rows if r["method"] == method and r["numeric_status"] == "proved"
                               and within(r, "numeric_process_elapsed_seconds"))])
    provenance["fpbench"] = {**window(rows), "rows": len(rows), "results_csv": source(path)}
    if not tools and (out / "fpbench-tools.csv").exists():
        tools = out / "fpbench-tools.csv"       # the rows of the summary before
    if not tools or not tools.exists():
        return
    external = read(tools)
    recorded = bool(external) and "source_sha256" not in external[0]
    if recorded:
        # The short file keeps no source hash. The tools ran on the files that the manifest pins
        # (`fetch.py` refuses any other), so the hash of a row's source is the manifest's.
        pinned = json.loads((HERE.parent / "fpbench" / "fpbench-source.json").read_text())["sha256"]
        for row in external:
            row["source_sha256"] = pinned.get("benchmarks/" + row["source_file"], "")
    keep = ["source_file", "index", "default_precision", "tool", "status", "numeric_bound",
            "bound_kind", "elapsed_seconds", "comparison_contract", "tool_version", "tool_revision"]
    write(out / "fpbench-tools.csv", keep, [{k: r.get(k, "") for k in keep} for r in external])
    for (tool, status), count in sorted(Counter((r["tool"], r["status"]) for r in external).items()):
        counts.append(["fpbench", f"tool {tool}", status, count])
    from compare import compare                      # benchmarks/fpbench/compare.py
    audit = results / "fpbench" / "published-contracts.csv"
    joined = compare(rows, external, read(audit) if audit.exists() else [])
    columns = ["source_file", "index", "default_precision", "program", "effective_precision",
               "numerical_coverage"]
    for method in ("forward", "closed"):
        columns += [f"{method}_numeric_status", f"{method}_numeric_bound"]
    for tool in ("fptaylor", "gappa", "daisy"):
        columns += [f"{tool}_status", f"{tool}_numeric_bound", f"{tool}_bound_kind",
                    f"{tool}_elapsed_seconds", f"{tool}_comparison_contract",
                    f"forward_{tool}_bound_ratio", f"closed_{tool}_bound_ratio"]
    columns += ["forward_fptaylor_published_ratios", "closed_fptaylor_published_ratios"]
    write(out / "fpbench-comparison.csv", columns, joined)
    for coverage, count in sorted(Counter(r["numerical_coverage"] for r in joined).items()):
        counts.append(["fpbench", "numerical coverage (FloatLib and the local tools)", coverage, count])
    for tool in ("fptaylor", "gappa", "daisy"):
        for method in ("forward", "closed"):
            ratios = sum(1 for r in joined if r.get(f"{method}_{tool}_bound_ratio"))
            counts.append(["fpbench", f"{method} bound over the bound of {tool}", "ratio", ratios])
    provenance["fpbench-tools"] = earlier.get("fpbench-tools") if recorded and "fpbench-tools" in earlier \
        else {"rows": len(external), "results_csv": source(tools),
              "note": "external tools, independent of FloatLib's commit"}


def inequalities(results: Path, out: Path, counts: list, provenance: dict) -> None:
    path = results / "inequalities" / "results.csv"
    if not path.exists():
        return
    rows = read(path)
    columns = ["id", "suite", "source_file", "method", "status", "elapsed_ms",
               "process_elapsed_seconds", "process_sampled_peak_rss_kib", "memory_refusal",
               "published_system", "published_total_seconds", "published_verification_seconds",
               "floatlib_commit", "measurement_utc"]
    slim = []
    for row in rows:
        entry = {column: row.get(column, "") for column in columns}
        entry["elapsed_ms"] = milliseconds(row.get("elapsed_ns"))
        log = results / "inequalities" / row.get("log", "") if row.get("log") else None
        refused = (row["status"] == "runner_error" and log is not None and log.is_file()
                   and "excessive memory consumption" in log.read_text(errors="replace"))
        entry["memory_refusal"] = "yes" if refused else ""
        entry["floatlib_commit"] = named(row.get("floatlib_commit", ""))
        slim.append(entry)
    write(out / "inequalities.csv", columns, slim)
    for (suite, method, status), count in sorted(Counter(
            (r["suite"], r["method"], r["status"]) for r in rows).items()):
        counts.append(["inequalities", f"{suite}, {method}", status, count])
    goals = defaultdict(dict)
    for row in rows:
        goals[(row["suite"], row["id"].rsplit(":", 1)[0])][row["method"]] = row["status"]
    union = Counter()
    for (suite, _), routes in goals.items():
        union[(suite, "proved" if "proved" in routes.values() else "not proved")] += 1
    for (suite, status), count in sorted(union.items()):
        counts.append(["inequalities", f"{suite}, either route", status, count])
    provenance["inequalities"] = {**window(rows), "rows": len(rows), "results_csv": source(path)}


def correct_rounding(results: Path, out: Path, counts: list, provenance: dict) -> None:
    path = results / "correct-rounding" / "results.csv"
    if not path.exists():
        return
    rows = read(path)
    groups = OrderedDict()
    for row in rows:
        key = (row.get("domain") or "real", row["source"], row["width"], row["operation"], row["status"])
        groups.setdefault(key, []).append(row)
    columns = ["domain", "source", "width", "operation", "status", "cases", "median_ns",
               "p90_ns", "max_ns", "mpfr_median_ns", "core_math_median_ns"]
    table = []
    for (domain, origin, width, operation, status), members in groups.items():
        def times(column: str) -> list:
            return sorted(float(r[column]) for r in members if r.get(column) not in ("", None))
        mine = times("elapsed_ns")
        table.append([domain, origin, width, operation, status, len(members), median(mine),
                      round(mine[int(0.9 * (len(mine) - 1))]) if mine else "",
                      round(mine[-1]) if mine else "", median(times("mpfr_elapsed_ns")),
                      median(times("core_math_elapsed_ns"))])
        counts.append(["correct-rounding", f"{domain}, {origin}, binary{width}, {operation}", status,
                       len(members)])
    write(out / "correct-rounding.csv", columns, table)
    for (domain, status), count in sorted(Counter(
            (r.get("domain") or "real", r["status"]) for r in rows).items()):
        counts.append(["correct-rounding", f"{domain}, all", status, count])
    provenance["correct-rounding"] = {**window(rows), "rows": len(rows), "results_csv": source(path)}


def testfloat(results: Path, out: Path, counts: list, provenance: dict) -> None:
    path = results / "testfloat" / "results.csv"
    if not path.exists():
        return
    rows = read(path)
    columns = ["id", "format", "operation", "rounding", "status", "cases", "value_mismatches",
               "flag_mismatches", "parse_errors", "generation_seconds", "lean_check_seconds",
               "vector_sha256", "floatlib_commit", "measurement_utc"]
    write(out / "testfloat.csv", columns,
          [{**{c: r.get(c, "") for c in columns}, "floatlib_commit": named(r.get("floatlib_commit", ""))}
           for r in rows])

    def group(row: dict) -> str:
        operation = row["operation"]
        return ("fused multiply-add" if operation == "mulAdd" else
                "conversions between formats" if "_to_" in operation or operation.startswith("to_")
                else "arithmetic, comparisons and the rest")
    for (name, status), members in sorted(_grouped(rows, lambda r: (group(r), r["status"])).items()):
        counts.append(["testfloat", name, status, len(members)])
        counts.append(["testfloat", name, f"{status}: vectors", sum(int(r["cases"] or 0) for r in members)])
    counts.append(["testfloat", "all", "campaigns", len(rows)])
    counts.append(["testfloat", "all", "vectors", sum(int(r["cases"] or 0) for r in rows)])
    counts.append(["testfloat", "all", "value mismatches", sum(int(r["value_mismatches"] or 0) for r in rows)])
    counts.append(["testfloat", "all", "flag mismatches", sum(int(r["flag_mismatches"] or 0) for r in rows)])
    provenance["testfloat"] = {**window(rows), "rows": len(rows), "results_csv": source(path)}


def _grouped(rows: list, key) -> dict:
    groups = defaultdict(list)
    for row in rows:
        groups[key(row)].append(row)
    return groups


def table(header: list, rows: list) -> list:
    right = ["---"] + ["---:"] * (len(header) - 1)
    return ["| " + " | ".join(header) + " |", "| " + " | ".join(right) + " |"] + \
        ["| " + " | ".join(f"{c:,}" if isinstance(c, int) else str(c) for c in row) + " |" for row in rows] + [""]


def readme(out: Path, counts: list, provenance: dict, conditions: str) -> None:
    """`README.md`: the tables the docs quote, from `counts.csv` and the summaries."""
    count = defaultdict(int)
    for suite, group, outcome, value in counts:
        count[(suite, group, outcome)] += int(value)

    def measured(suite: str) -> str:
        record = provenance.get(suite, {})
        commits = ", ".join(f"`{c[:8]}`" for c in record.get("floatlib_commits", []))
        release = re.search(r"version ([0-9.]+)", record.get("lean_version", ""))
        return (f"Measured {record.get('first_utc', '')} to {record.get('last_utc', '')}"
                + (f" at {commits}" if commits else "")
                + (f" with Lean {release.group(1)}." if release else "."))

    lines = ["# Standard suites: results", "",
             "Written by `benchmarks/suites/summarize.py` from the results of "
             "`benchmarks/suites/run.sh`. Each section gives the time of its run: a suite can be run "
             "again alone, and the others keep their results. "
             "The CSV files next to this file have one short row per case; `counts.csv` has every "
             "number of the tables below; `provenance.json` has "
             + ("the commits, " if any(isinstance(record, dict) and record.get("floatlib_commits")
                                       for record in provenance.values()) else "")
             + "the toolchain and the "
             "size and SHA-256 of each full result file, which is not in the repository. "
             "The suite READMEs say what each outcome means.", ""]
    if conditions:
        lines += [conditions, ""]
    if "fpbench" in provenance:
        lines += ["## FPBench with `roundoff`", "", measured("fpbench"), ""]
        rows = []
        for method in ("forward", "closed", "backward"):
            for kind in ("conditional theorem", "numerical bound"):
                group = f"{method}, {kind}"
                if any(key[1] == group for key in count):
                    rows.append([group] + [count[("fpbench", group, status)] for status in
                                           ("proved", "refused", "timeout", "runner_error",
                                            "not_attempted", "translation_refusal")])
        lines += table(["theorem", "proved", "refused", "over the time limit", "out of memory",
                        "not attempted", "not translated"], rows)
        lines += ["`out of memory` is a Lean process that stopped at its 4 GB limit (`lean -M 4096`); "
                  "`not attempted` is a numerical bound whose conditional theorem was not proved.", ""]
        quick = "proved within 20 s of process time"
        lines += ["Of these, proved within 20 seconds of process time: "
                  + ", ".join(f"{group} {count[('fpbench', group, quick)]}" for group in
                              [row[0] for row in rows]) + ".", ""]
        tools = sorted({key[1] for key in count if key[1].startswith("tool ")})
        if tools:
            statuses = sorted({key[2] for key in count if key[1] in tools})
            lines += table(["external tool, run on the same exported program"] + statuses,
                           [[t[5:]] + [count[("fpbench", t, st)] for st in statuses] for t in tools])
            coverage = "numerical coverage (FloatLib and the local tools)"
            lines += ["Programs and default precisions with a numerical bound from both sides: "
                      f"{count[('fpbench', coverage, 'both')]}; from another tool only: "
                      f"{count[('fpbench', coverage, 'other_tool_only')]}; from FloatLib only: "
                      f"{count[('fpbench', coverage, 'lean_only')]}; from neither: "
                      f"{count[('fpbench', coverage, 'neither')]}.", ""]
            comparison = out / "fpbench-comparison.csv"
            rows = []
            for tool in ("fptaylor", "gappa"):
                values = []
                for row in read(comparison):
                    for method in ("forward", "closed"):
                        text = row.get(f"{method}_{tool}_bound_ratio", "")
                        if text:
                            numerator, _, denominator = text.partition("/")
                            values.append(float(numerator) / float(denominator or 1))
                if values:
                    rows.append([tool, len(values), f"{min(values):.4g}", f"{statistics.median(values):.4g}",
                                 f"{max(values):.4g}"])
            if rows:
                lines += table(["FloatLib's bound over the bound of", "ratios", "smallest", "median",
                                "largest"], rows)
    if "inequalities" in provenance:
        lines += ["## Real inequalities with `interval`", "", measured("inequalities"), ""]
        groups = sorted({key[1] for key in count if key[0] == "inequalities" and "either" not in key[1]})
        statuses = ["proved", "refused", "timeout", "runner_error", "translation_refusal",
                    "capability_refusal"]
        statuses = [st for st in statuses if any(count[("inequalities", g, st)] for g in groups)]
        lines += table(["suite and route"] + [st.replace("_", " ") for st in statuses],
                       [[g] + [count[("inequalities", g, st)] for st in statuses] for g in groups])
        either = sorted({key[1] for key in count if key[0] == "inequalities" and "either" in key[1]})
        lines += table(["goals", "proved by at least one route", "by neither"],
                       [[g] + [count[("inequalities", g, "proved")], count[("inequalities", g, "not proved")]]
                        for g in either])
        if "runner_error" in statuses:
            lines += ["`runner error` is a Lean process that stopped at its 4 GB memory limit "
                      "(`lean -M 4096`) in the interpreter; `inequalities.csv` marks those rows in "
                      "`memory_refusal`.", ""]
    if "correct-rounding" in provenance:
        lines += ["## Hard-to-round inputs", "", measured("correct-rounding"), ""]
        lines += table(["domain", "matched", "not representable", "excluded"],
                       [[d] + [count[("correct-rounding", f"{d}, all", st)] for st in
                               ("matched", "translation_refusal", "excluded")] for d in ("real", "complex")
                        if any(key[1] == f"{d}, all" for key in count)])
        lines += ["A complex input `z = x + i x` counts once per part of its result. "
                  "`correct-rounding.csv` has the counts and the median times per source, format and "
                  "function.", ""]
    if "testfloat" in provenance:
        lines += ["## Berkeley TestFloat", "", measured("testfloat"), ""]
        groups = sorted({key[1] for key in count if key[0] == "testfloat" and key[1] != "all"})
        lines += table(["operations", "campaigns that match", "vectors", "campaigns that do not"],
                       [[g, count[("testfloat", g, "matched")], count[("testfloat", g, "matched: vectors")],
                         sum(v for k, v in count.items() if k[0] == "testfloat" and k[1] == g
                             and k[2] not in ("matched",) and not k[2].endswith("vectors"))] for g in groups])
        lines += [f"All: {count[('testfloat', 'all', 'campaigns')]:,} campaigns, "
                  f"{count[('testfloat', 'all', 'vectors')]:,} vectors, "
                  f"{count[('testfloat', 'all', 'value mismatches')]:,} value mismatches, "
                  f"{count[('testfloat', 'all', 'flag mismatches')]:,} flag mismatches.", ""]
    (out / "README.md").write_text("\n".join(lines))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("results", type=Path)
    parser.add_argument("--tools", type=Path, help="results.csv of benchmarks/fpbench/tools.py")
    parser.add_argument("--out", type=Path, default=ROOT / "benchmarks" / "results" / "suites")
    parser.add_argument("--conditions", default="",
                        help="one paragraph on how the run was started (limits, processes at a time)")
    args = parser.parse_args()
    counts, provenance = [], {}
    before = args.out / "provenance.json"
    earlier = json.loads(before.read_text()) if before.exists() else {}
    earlier_counts = read(args.out / "counts.csv") if (args.out / "counts.csv").exists() else []
    for suite, summarize in (
            ("fpbench", lambda: fpbench(args.results, args.out, args.tools, counts, provenance, earlier)),
            ("inequalities", lambda: inequalities(args.results, args.out, counts, provenance)),
            ("correct-rounding", lambda: correct_rounding(args.results, args.out, counts, provenance)),
            ("testfloat", lambda: testfloat(args.results, args.out, counts, provenance))):
        summarize()
        if suite not in provenance and suite in earlier:
            # Not in RESULTS: the suite keeps its short file, its counts and its record.
            counts += [[row["suite"], row["group"], row["outcome"], int(row["count"])]
                       for row in earlier_counts if row["suite"] == suite]
            provenance[suite] = earlier[suite]
            if suite == "fpbench" and "fpbench-tools" in earlier:
                provenance["fpbench-tools"] = earlier["fpbench-tools"]
            print(f"{suite}: no results.csv in {args.results}, the summary before stays")
    write(args.out / "counts.csv", ["suite", "group", "outcome", "count"], counts)
    for suite in ("fpbench", "inequalities", "correct-rounding", "testfloat"):
        record = args.results / suite / "provenance.json"
        if suite in provenance and record.exists():
            harness = json.loads(record.read_text())
            provenance[suite]["lean_version"] = harness.get("lean_version", "")
            provenance[suite]["thread_limit"] = harness.get("thread_limit", "")
            provenance[suite]["workers"] = harness.get("workers", "")
    conditions = args.conditions or earlier.get("conditions", "")
    if conditions:
        provenance["conditions"] = conditions
    (args.out / "provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")
    readme(args.out, counts, provenance, conditions)
    print(f"{len(counts)} counts and {len(provenance)} suites in {args.out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
