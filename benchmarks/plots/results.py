"""The result files of the figures: where they are, how they are read, and how a timing run fills them.

`figures.py` draws from the files under `benchmarks/results/`; this module owns those files.
`install(raw)` turns the logs of one timing run (`timing.py`) into them: the CSV files and tables
of `backends/`, `exact/`, `ieee2019/` and `kernel/`, their README files, and
`figures/measured.json`, the record of what was measured at which commit. Nothing is measured
here: every number is copied from a log that Lean or a benchmark program wrote, and the only
arithmetic is the one the runners' own table scripts do (a fold minus the fold that only
prepares its operands, divided by the number of operands).

Two things are refused. A kernel row whose value is not a numeral is no measurement (a term
that did not elaborate reduces to `sorry` in no time). And a section whose runner failed, or
whose logs have no row, keeps the files of the run before it.
"""
from __future__ import annotations

import csv
import json
import os
import re
import subprocess
import sys
from collections import OrderedDict, defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import timing  # noqa: E402  (the row limit of the wide formats)


def read_csv(path: Path) -> list:
    with open(path, newline="", encoding="utf-8") as handle_:
        return list(csv.DictReader(handle_))


def positive(text):
    """A measured difference, or `None` when it is missing or not above zero."""
    value = number(text)
    return value if value is not None and value > 0 else None


def number(text):
    try:
        return float(text) if text not in ("", None) else None
    except ValueError:
        return None


ROOT = Path(__file__).resolve().parents[2]


# `FLOATLIB_FIGURES_RESULTS` puts the result files and the figures somewhere else (for trying a
# change to this script without touching the recorded results).
RESULTS = Path(os.environ.get("FLOATLIB_FIGURES_RESULTS") or ROOT / "benchmarks" / "results").resolve()


OUT = RESULTS / "figures"


RECORDED = OUT / "recorded"


MEASURED = OUT / "measured.json"


def machine() -> str:
    try:
        text = Path("/proc/cpuinfo").read_text()
        model = re.search(r"model name\s*:\s*(.+)", text).group(1)
        model = re.sub(r"\(R\)|\(TM\)|CPU ", "", model).replace("  ", " ").strip()
        return f"{model}, {text.count('processor')} threads, shared with other jobs"
    except (OSError, AttributeError):
        return "unknown machine"


class Missing(Exception):
    """The input of a figure does not exist; the figure is skipped."""


def need(path, what: str) -> Path:
    if path is None or not Path(path).exists():
        raise Missing(f"{what}: {relative(path) if path is not None else 'no path'}")
    return Path(path)


def relative(path) -> str:
    try:
        return str(Path(path).resolve().relative_to(ROOT))
    except ValueError:
        return str(path)


BASIC = ["add", "sub", "mul", "div", "sqrt", "fma"]


REAL_FUNCTIONS = ["expm1", "logp1", "exp2", "exp2m1", "exp10", "exp10m1", "log2", "log10", "log2p1",
                  "log10p1", "sin", "cos", "tan", "sinPi", "cosPi", "tanPi", "asin", "acos", "atan",
                  "asinPi", "acosPi", "atanPi", "sinh", "cosh", "tanh", "asinh", "acosh", "atanh",
                  "exp", "log", "powr", "compound", "atan2", "atan2Pi"]


EXTRAS = OrderedDict([
    ("add-outcome", "add x y (status := true)"), ("sub-outcome", "sub x y (status := true)"),
    ("mul-outcome", "mul x y (status := true)"), ("div-outcome", "div x y (status := true)"),
    ("sqrt-outcome", "sqrt x (status := true)"), ("fma-outcome", "fma x y z (status := true)"),
    ("roundToIntegral-outcome", "roundToIntegral x (status := true)"),
    ("less", "x < y"), ("equal", "x == y"), ("totalOrder", "totalOrder x y"), ("isNaN", "isNaN x"),
    ("roundToIntegral", "roundToIntegral x"), ("toInt", "x.toInt?"), ("toRat", "toRat? x"),
    ("cast", "cast into the next narrower format"), ("cast-outcome", "the same cast (status := true)"),
    ("decimal", "a decimal literal"), ("rational", "ofRat q, rounded up"),
    ("rational-outcome", "ofRat q (status := true)"),
])


# The same rows as the terms that `extras.sh` reduces, for the table of `kernel/README.md`.
EXTRAS_TERMS = {
    "add-outcome": "`ExecFloat.Binary.add x y (status := true)`",
    "sub-outcome": "`ExecFloat.Binary.sub x y (status := true)`",
    "mul-outcome": "`ExecFloat.Binary.mul x y (status := true)`",
    "div-outcome": "`ExecFloat.Binary.div x y (status := true)`",
    "sqrt-outcome": "`ExecFloat.Binary.sqrt x (status := true)`",
    "fma-outcome": "`ExecFloat.Binary.fma x y z (status := true)`",
    "roundToIntegral-outcome": "`ExecFloat.Binary.roundToIntegral x .nearest (status := true)`",
    "less": "`x < y`", "equal": "`x == y`", "totalOrder": "`ExecFloat.Binary.totalOrder x y`",
    "isNaN": "`ExecFloat.Binary.isNaN x`",
    "roundToIntegral": "`ExecFloat.Binary.roundToIntegral x .nearest`",
    "toInt": "`x.toInt? (mode := .nearest)`", "toRat": "`ExecFloat.Binary.toRat? x`",
    "cast": "`Model.cast` into the next narrower format, between a decode and a store",
    "cast-outcome": "the same cast with `status := true`",
    "decimal": "a decimal literal `(2 * i + 1) / 1000`",
    "rational": "`ExecFloat.Binary.ofRat q (mode := .up)`",
    "rational-outcome": "`ExecFloat.Binary.ofRat q (mode := .up) (status := true)`",
}


LOOPS = OrderedDict([("sumTenth", "1,000 binary32 additions of 0.1"),
                     ("sum64", "sum of 1,000 binary64 values"),
                     ("dot64", "dot product of 1,000 binary64 pairs")])


BITS = {"e4m3": 8, "e5m2": 8, "e4f3": 8, "binary16": 16, "bfloat16": 16, "e8f15": 24, "binary32": 32,
        "binary64": 64, "e15f64": 80, "binary128": 128, "binary256": 256, "binary512": 512,
        "binary1024": 1024, "binary4096": 4096, "decimal32": 32, "decimal64": 64, "decimal128": 128}


IEEE_COUNT = 4          # operand triples per cell of `ieee2019.sh`, as `timing.py` starts it


def commit_of(entry: dict, before: str = "", after: str = "") -> str:
    """The commit that a record names, between `before` and `after`; nothing for a record without one."""
    short = entry.get("short")
    return f"{before}`{short}`{after}" if short else ""


def record_run(raw: Path, commit: str, dirty: bool, started: str, seconds: float, jobs: int,
               threads: int, done: list, own_core: bool = False, shared: frozenset = frozenset()) -> None:
    """`RAW/run.json`: what the timing mode measured, section by section.

    `commit` is empty for a checkout whose commit no remote branch has; the record then names none.
    A run with `--only` measures some sections again and leaves the others as they are, so the
    record keeps, for every section, the start of the run that measured it, and under `runs` the
    runs that still have a section: on a machine that other jobs share, the sections whose cells
    are differences of a few microseconds are best measured again one at a time. `own_core` says
    that the run had core scheduling, and a section not in `shared` then ran with a cookie.
    """
    path = raw / "run.json"
    run = json.loads(path.read_text()) if path.exists() else {"sections": {}}
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    lean = toolchain.rsplit(":", 1)[-1]
    name_of = dict(commit=commit, short=commit[:8]) if commit else {}
    for key in ("commit", "short"):
        run.pop(key, None)
    if "started_utc" in run:    # the sections of a record without `runs` are those of its one run
        for entry in run["sections"].values():
            entry.setdefault("started_utc", run["started_utc"])
        run.setdefault("runs", [dict(started_utc=run["started_utc"], seconds=run.get("seconds", 0),
                                     jobs=run.get("jobs", ""), threads=run.get("threads", ""))])
    run.update(name_of, dirty=dirty, toolchain=toolchain, lean=lean,
               machine=machine(), date=started[:10], started_utc=started, seconds=round(seconds, 1),
               jobs=jobs, threads=threads)
    for name, code, spent in done:
        run["sections"][name] = dict(exit=code, seconds=round(spent, 1), lean=lean, date=started[:10],
                                     started_utc=started, own_core=own_core and name not in shared,
                                     **({"short": commit[:8]} if commit else {}))
    runs = run.get("runs", []) + [dict(started_utc=started, seconds=round(seconds, 1), jobs=jobs,
                                       threads=threads, own_core=own_core)]
    owners = {entry.get("started_utc") for entry in run["sections"].values()}
    run["runs"] = [entry for entry in runs if entry["started_utc"] in owners]
    path.write_text(json.dumps(run, indent=2) + "\n")


def write_rows(path: Path, columns: list, rows: list) -> int:
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", newline="", encoding="utf-8") as handle_:
        writer = csv.writer(handle_, lineterminator="\n")
        writer.writerow(columns)
        writer.writerows(rows)
    return len(rows)


def data_rows(path: Path) -> int:
    return max(0, len(path.read_text().splitlines()) - 1) if path.exists() else 0


def kernel_table(path: Path) -> list:
    """(format, operands, operation, microseconds) from a table of `benchmarks/kernel/run.sh`."""
    rows = []
    for line in path.read_text().splitlines() if path.exists() else []:
        parts = [part.strip() for part in line.strip().strip("|").split("|")]
        if len(parts) == 8 and parts[0] not in ("format", "---"):
            for op, cell in zip(BASIC, parts[2:]):
                value = number(cell.replace(",", ""))
                if value is not None:
                    rows.append([parts[0], parts[1], op, value])
    return rows


def kbench(path: Path) -> list:
    """(format, row, path, nanoseconds) from the `KBENCH` lines of a log of `Harness.lean`.

    A line counts only when the kernel reduced the term to a numeral: a term that did not
    elaborate reduces to something else in no time, and that is not a measurement.
    """
    rows = []
    for line in path.read_text(errors="replace").splitlines() if path.exists() else []:
        parts = line.split()
        if len(parts) == 6 and parts[0] == "KBENCH" and number(parts[4]) is not None and parts[5].isdigit():
            rows.append((parts[1], parts[2], parts[3], float(parts[4])))
    return rows


def log_errors(*paths) -> int:
    """Lean error lines in the logs of a section (`error:` after a file position)."""
    count = 0
    for path in paths:
        for file in ([path] if Path(path).is_file() else sorted(Path(path).glob("**/*.log")) if Path(path).is_dir() else []):
            count += len(re.findall(r"^\S+\.lean:\d+:\d+: error", file.read_text(errors="replace"), flags=re.M))
    return count


def ieee_kernel_rows(logs: list) -> list:
    """The cells of `ieee2019.sh` (its own `awk`, with one more digit): time of the fold minus
    the time of the fold that only prepares the operand, per operand triple."""
    times = {}
    for log in logs:
        for fmt, op, path, ns in kbench(log):
            times[(fmt, op, path)] = ns
    rows, seen = [], []
    for (fmt, op, path), ns in times.items():
        if op.startswith("noop") or (fmt, op) in seen:
            continue
        seen.append((fmt, op))
        decimal = fmt.startswith("decimal")
        kind = ("noop-integral" if op in ("setPayload", "setPayloadSignaling") and not decimal else
                "noop-nan" if op == "getPayload" and not decimal else
                "noop-payload" if op == "getPayload" else "noop")
        cell = []
        for which in ("public", "kernel"):
            base, value = times.get((fmt, kind, which)), times.get((fmt, op, which))
            cell.append("" if base is None or value is None
                        else round((value - base) / IEEE_COUNT / 1000.0, 1))
        rows.append([fmt, BITS.get(fmt, ""), op, cell[0], cell[1]])
    order = list(BITS)
    rows.sort(key=lambda r: order.index(r[0]) if r[0] in order else len(order))
    return rows


def extras_rows(log: Path, count: int = 64) -> list:
    """The cells of `extras.sh` (its own `awk`): (format, row, as written, with the rules) in µs."""
    times = {(fmt, op, path): ns for fmt, op, path, ns in kbench(log)}
    rows, seen = [], []
    for fmt, op, _ in times:
        if op.startswith("noop-") or (fmt, op) in seen:
            continue
        seen.append((fmt, op))
        kind = ("multiplicative" if re.match(r"(mul|div)-", op) else "fused" if op.startswith("fma-") else
                "additive" if re.match(r"(add|sub)-", op) or op in ("less", "equal", "totalOrder") else
                "decimal" if op == "decimal" else "rational" if op.startswith("rational") else "root")
        cell = []
        for which in ("public", "kernel"):
            base, value = times.get((fmt, "noop-" + kind, which)), times.get((fmt, op, which))
            cell.append("" if base is None or value is None else round((value - base) / count / 1000.0, 1))
        rows.append([fmt, BITS.get(fmt, ""), op, cell[0], cell[1]])
    return rows


DURATION = {"ms": 1e-3, "s": 1.0, "µs": 1e-6, "us": 1e-6, "ns": 1e-9}


def loop_rows(log: Path) -> list:
    """(theorem, path, seconds: the fastest run, runs, axioms) from the log of `loops.sh`."""
    best = OrderedDict()
    for line in log.read_text(errors="replace").splitlines() if log.exists() else []:
        match = re.match(r"KLOOP (\S+) (\S+) run \d+: type checking took ([0-9.]+)(ms|s|µs)(.*)", line)
        if match:
            key = (match.group(1), match.group(2))
            value = float(match.group(3)) * DURATION[match.group(4)]
            axioms = re.search(r"depends on axioms: \[([^\]]*)\]", match.group(5))
            entry = best.setdefault(key, [value, 0, axioms.group(1) if axioms else ""])
            entry[0], entry[1] = min(entry[0], value), entry[1] + 1
    return [[name, path, round(v[0], 6), v[1], v[2]] for (name, path), v in best.items()]


def block_rows(logs: list) -> list:
    """(family, row, microseconds) from `MX.lean` and `NVFP4.lean`: `#kernel_cost rewritten`."""
    rows = []
    for log in logs:
        label = None
        for line in log.read_text(errors="replace").splitlines() if log.exists() else []:
            head = re.match(r"(MX|NVFP4)_KERNEL (.+)", line)
            if head:
                label = (head.group(1), head.group(2).strip())
            cost = re.match(r"with the tagged kernel rules: ([0-9.]+) µs", line)
            if cost and label:
                rows.append([label[0], label[1], float(cost.group(1))])
                label = None
    return rows


def merge_coq(target: Path, measured: Path) -> int:
    """`matched.csv`: Lean's column from this run, Coq's columns from the recorded run."""
    recorded = {(r["format"], r["operation"]): r for r in read_csv(RECORDED / "coq-flocq.csv")} \
        if (RECORDED / "coq-flocq.csv").exists() else {}
    rows = []
    for row in read_csv(measured):
        old = recorded.get((row["format"], row["operation"]), {})
        rows.append([row["format"], row["bits"], row["operation"], row["lean_kernel_us"],
                     row.get("flocq_vm_us") or old.get("flocq_vm_us", ""),
                     row.get("flocq_lazy_us") or old.get("flocq_lazy_us", ""),
                     row["values"] if row.get("values") not in ("", "n/a", None)
                     else (old.get("values", "") and f"{old['values']} when Coq ran")])
    return write_rows(target, ["format", "bits", "operation", "lean_kernel_us", "flocq_vm_us",
                               "flocq_lazy_us", "values"], rows)


def table_number(text) -> str:
    value = number(text)
    if value is None:
        return "no result"
    return f"{value:,.0f}" if value >= 100 else f"{value:.1f}" if value < 10 else f"{value:.0f}"


def backends_readme(generated: Path, backends: Path, measured: dict) -> None:
    """`backends/README.md`: where the run was made, then the tables of `suite/tables.py`."""
    body = generated.read_text()
    body = body[body.index("## "):]
    start = body.find("| format | operation | Lean kernel")
    if start >= 0:                      # the Coq columns come from the recorded run
        end = body.find("\n\n", start)
        lines = ["| format | operation | Lean kernel (µs) | Flocq `vm_compute` (µs) | Flocq `lazy` (µs) | values |",
                 "| --- | --- | ---: | ---: | ---: | --- |"]
        for row in read_csv(backends / "matched.csv"):
            lines.append(f"| {row['format']} | {row['operation']} | {table_number(row['lean_kernel_us'])} | "
                         f"{table_number(row['flocq_vm_us'])} | {table_number(row['flocq_lazy_us'])} | "
                         f"{row['values']} |")
        body = body[:start] + "\n".join(lines) + body[end:]
    state = " with uncommitted changes to tracked files" if measured.get("dirty") else ""
    head = [
        "# Benchmark suite: kernel and compiled code", "",
        "This directory records the suite sections of the timing mode of `benchmarks/plots/figures.py`, "
        "which starts `benchmarks/suite/run.sh` section by section: "
        f"{commit_of(measured, 'commit ', state + ', ')}Lean {measured.get('lean', '')}, "
        f"{measured.get('machine', '')}, {measured.get('date', '')}. Other jobs were running, so read "
        "the tables as ratios. `../figures/measured.json` has the exit code and the time of every "
        "section.", "",
        "The timing mode does not run Coq. The two Coq columns of the matched loops are the ones "
        "recorded on 2026-11-15 with Coq 8.20.1 and Flocq 4.2.2 in the image "
        "`leanfloat-flocq-bench:4.2.2`, one container at a time with 8 GB and two CPUs "
        "(`../figures/recorded/coq-flocq.csv`); in that run Coq printed the value that Lean computed "
        "in every row.", "",
        "The figures of these tables are in `../figures/` and are described in "
        "[`../FIGURES.md`](../FIGURES.md): `kernel-binary`, `kernel-operands`, `kernel-vs-coq`, "
        "`kernel-families`, `kernel-all-pairs` and `compiled-precision`.", "",
        "Every number is a time measured on one shared machine. The CSV files next to this file "
        "hold the same numbers.", "", ""]
    (backends / "README.md").write_text("\n".join(head) + body)


def pivot(rows: list, formats: list, value) -> list:
    """A Markdown table with one row per operation and one column per format."""
    operations = list(OrderedDict.fromkeys(r["operation"] for r in rows if r["format"] in formats))
    cells = {(r["operation"], r["format"]): value(r) for r in rows}
    lines = ["| operation | " + " | ".join(formats) + " |", "| --- |" + " ---: |" * len(formats)]
    for operation in operations:
        texts = []
        for fmt in formats:
            cell = number(cells.get((operation, fmt)))
            texts.append("n/a" if cell is None else "< 1" if cell < 0.5 else
                         f"{cell:,.0f}" if cell >= 10 else f"{cell:.1f}")
        lines.append(f"| {operation} | " + " | ".join(texts) + " |")
    return lines + [""]


def ieee_readme(ieee: Path, measured: dict) -> None:
    """`ieee2019/README.md`: where the two CSV files come from, and their six tables."""
    compiled, kernel = read_csv(ieee / "compiled.csv"), read_csv(ieee / "kernel.csv")
    binary = [f for f in BITS if any(r["format"] == f for r in compiled + kernel) and not f.startswith("decimal")]
    decimal = [f for f in ("decimal32", "decimal64", "decimal128") if any(r["format"] == f for r in compiled + kernel)]

    def section(name: str) -> str:
        entry = measured.get("sections", {}).get(name)
        return (f"{commit_of(entry, 'at ', ' ')}on {entry.get('date', '')} (Lean {entry.get('lean', '')})"
                if entry else "in an earlier run")
    lines = [
        "# Compiled and kernel time of the operations of IEEE 754-2019", "",
        "Every operation of IEEE 754-2019 clauses 5 and 9 that FloatLib provides, under its name in "
        "the standard, at the binary widths 8, 16, 32, 64, 128, 256, 1,024 and 4,096 bits and at the "
        "three decimal formats. Written by the timing mode of `benchmarks/plots/figures.py` on one "
        f"shared machine ({measured.get('machine', '')}); `../figures/measured.json` has the exit "
        "code and the time of every section. `n/a` is a cell without a result, and `< 1` a kernel "
        "cell under half a microsecond. A kernel cell is the difference of two folds, and the fold "
        "that is subtracted reads and stores its operand, so an operation that reads less of it "
        "(`radix`, `isCanonical`, a test of the class of a decimal datum) comes out at zero or "
        "below (the CSV keeps the number).", "",
        f"* Compiled time (`compiled.csv`), measured {section('ieee2019-compiled')}: "
        "`execFloatIEEE2019` (`benchmarks/lean/FloatLibBenchmarks/Public/IEEE2019.lean`), "
        "nanoseconds for one call on the descriptor model `Model fmt` or on a decimal `Datum`, the "
        "fastest of five trials of at least 20 ms over 64 operand triples. The reductions take eight "
        "elements or pairs.",
        f"* The rows `exp2` to `rootn` of the binary compiled table, measured {section('functions')}: "
        "the recommended functions of clause 9.2 (`execFloatIEEE2019 functions FORMAT`), one pass "
        "over eight operands up to 128 bits, two operands at 256 bits and one at 1,024 and at 4,096 "
        "bits, where each function runs alone and has no result after 120 seconds.",
        f"* Kernel time (`kernel.csv`), measured {section('ieee2019')}, the formats of 1,024 and "
        f"4,096 bits {section('ieee2019-wide')}: `benchmarks/kernel/ieee2019.sh 4 3`, microseconds "
        "for one evaluation by Lean's kernel on the configured type `ExecFloat.Binary` or on a decimal "
        "`Datum`: as written, and after the rewrite of `float_decide` with the rules tagged "
        "`@[kernel_optimize]`. A cell is the time of a fold over four operand triples minus the time "
        "of a fold that only reads and stores an operand, divided by four, the fastest of three. "
        "The reductions take three elements or two pairs. The decimal operands have full "
        "coefficients, so sums and products drop digits. At 1,024 and 4,096 bits every row runs in "
        f"its own Lean process with a limit of {timing.ROW_SECONDS:,} seconds, a certified function "
        f"of clause 9.2 with a limit of {timing.FUNCTION_ROW_SECONDS:,} seconds, and a row that needs "
        "longer has none. "
        "The payload rows subtract their preparation.", "",
        "The 8-bit format `e4f3` is the IEEE layout with four exponent bits and three fraction bits; "
        "`binary1024` and `binary4096` are the IEEE layouts with 27 and 35 exponent bits. The figure "
        "`kernel-ieee2019` of [`../FIGURES.md`](../FIGURES.md) draws the kernel tables by family, and "
        "`correctly-rounded` the recommended functions.", ""]
    nanoseconds = lambda r: r["nanoseconds"]
    lines += ["## Binary formats, compiled (nanoseconds)", ""] + pivot(compiled, binary, nanoseconds)
    lines += ["## Binary formats, kernel as written (microseconds)", ""] + \
        pivot(kernel, binary, lambda r: r["as_written_microseconds"])
    lines += ["## Binary formats, kernel with the tagged rules (microseconds)", ""] + \
        pivot(kernel, binary, lambda r: r["with_rules_microseconds"])
    lines += ["## Decimal formats, compiled (nanoseconds)", ""] + pivot(compiled, decimal, nanoseconds)
    lines += ["## Decimal formats, kernel as written (microseconds)", ""] + \
        pivot(kernel, decimal, lambda r: r["as_written_microseconds"])
    lines += ["## Decimal formats, kernel with the tagged rules (microseconds)", ""] + \
        pivot(kernel, decimal, lambda r: r["with_rules_microseconds"])
    (ieee / "README.md").write_text("\n".join(lines))


def kernel_readme(kernel: Path, backends: Path, measured: dict) -> None:
    """`kernel/README.md`: the tables of the kernel runners at this checkout."""
    def section(name: str) -> str:
        entry = measured.get("sections", {}).get(name)
        return f"{commit_of(entry, 'at ', ', ')}{entry.get('date', '')}, Lean {entry.get('lean', '')}" \
            if entry else "not measured"

    def cells(source: Path, **where) -> dict:
        found = defaultdict(dict)
        for row in read_csv(source) if source.exists() else []:
            if all(row.get(k) == v for k, v in where.items()) and number(row["microseconds"]) is not None:
                found[(row["format"], row["operands"])][row["operation"]] = float(row["microseconds"])
        return found

    def line(label: list, values: dict) -> str:
        return "| " + " | ".join(label + [f"{values[op]:,.0f}" if op in values else "n/a" for op in BASIC]) + " |"

    def ratios(top: dict, bottom: dict) -> dict:
        return {op: top[op] / bottom[op] for op in BASIC if top.get(op) and bottom.get(op)}

    def ratio_line(label: list, values: dict) -> str:
        return "| " + " | ".join(label + [f"{values[op]:,.0f}x" if op in values else "" for op in BASIC]) + " |"

    header = ["| format | operands | | add | sub | mul | div | sqrt | fma |",
              "| --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |"]
    written = cells(kernel / "as-written.csv")
    now = cells(backends / "kernel-binary.csv", commit="now")
    lines = [
        "# Kernel time of floating-point operations", "",
        "These tables record what Lean's kernel, the proof checker, spends on one operation and on "
        "whole theorems, as written and on the kernel path. They are written by the timing mode of "
        f"`benchmarks/plots/figures.py` on one shared machine ({measured.get('machine', '')}), so read "
        "them as ratios; `../figures/measured.json` has the exit code and the time of every section. "
        "Nothing here times compiled code. The figures `kernel-binary`, `kernel-operands`, "
        "`kernel-extras`, `kernel-loops` and `kernel-all-pairs` of [`../FIGURES.md`](../FIGURES.md) "
        "draw them.", "",
        "- As written: the public operations of FloatLib (`+`, `-`, `*`, `/`, `ExecFloat.sqrt`, "
        "`ExecFloat.fma`), as the kernel reduces them without the kernel path. The kernel path does "
        "not change these operations. For E4M3 and E5M2 these rows are the reference operations "
        "`ExecFloat.Spec.*`, because the kernel cannot evaluate their public operations: they look "
        "answers up in tables of 65,536 entries, and building one table in the kernel ran out of "
        "16 GB after about 220 seconds.",
        "- Kernel path: the operations `KernelPath.Value.*` in the nearest-even direction, rewritten "
        "as `float_decide` rewrites a goal (the rules tagged `@[kernel_optimize]`), so a cell is the "
        "operation that the kernel checks in a proof by `float_decide`.",
        "- A cell is (time of the operation over the operand table - time of a no-operation over "
        "the same table) / number of triples, the fastest run of `Lean.Kernel.whnf`, in "
        "microseconds. `benchmarks/kernel/run.sh` produces the cells.",
        "- Square roots are taken of positive operands in the normal and subnormal classes. The "
        "special class mixes zeros, the smallest subnormal, one, the largest finite value, "
        "infinities and NaNs.",
        "- The operand tables are hard on sums: the two operands of a sum have exponents within "
        "four binades of each other and their signs alternate, so half of the sums cancel leading "
        "bits or carry. The step of an accumulation loop, a sum of two values of one sign that "
        "keeps the exponent of the larger operand, is cheaper: see the loop theorems below.", "",
        "## Eight triples per cell", "",
        f"`benchmarks/kernel/run.sh public 8 3` (as written, {section('kernel-public')}), "
        f"`spec 8 3 e4m3 e5m2` ({section('kernel-spec')}) and `kernel 8 3` (kernel path, "
        f"{section('kernel-binary')}). The as-written cells read and store encodings with the public "
        "conversions of each format, the kernel-path cells with `KernelPath.ofNat` and "
        "`KernelPath.toNat`. One-time work (format constants) is spread over eight operations only. "
        "The ratio is as written over kernel path.", ""] + header
    formats = [f for f in ("binary16", "bfloat16", "binary32", "binary64", "binary128", "e4m3", "e5m2")
               if any(key[0] == f for key in written)]
    for fmt in formats:
        for operands in ("normal", "subnormal", "special"):
            key = (fmt, operands)
            if key in written:
                lines.append(line([fmt, operands, "as written"], written[key]))
            if key in now:
                lines.append(line([fmt, operands, "kernel path"], now[key]))
            if key in written and key in now:
                lines.append(ratio_line([fmt, operands, "ratio"], ratios(written[key], now[key])))
    triples = kernel / "triples64.csv"
    if triples.exists():
        lines += ["", "## Sixty-four triples per cell, the same conversions on both sides", "",
                  "Both sides read and store encodings with `KernelPath.ofNat` and `KernelPath.toNat` "
                  "(`KERNEL_BENCH_CONVERSIONS=kernel`), so a cell is the operation alone, and one-time "
                  "work is spread over 64 operations: `run.sh public 64 2` ("
                  f"{section('kernel-public-64')}), `spec 64 2 e4m3 e5m2` and `kernel 64 5` ("
                  f"{section('kernel-64')}). The special class is left out: it has nine distinct triples, "
                  "and the kernel remembers a repeated computation. The subnormal rows of E5M2 are too "
                  "low on both sides for the same reason (three subnormal fractions).", ""] + header
        public = {**cells(triples, path="public"), **cells(triples, path="spec")}
        rewritten = cells(triples, path="kernel")
        for fmt in formats:
            for operands in ("normal", "subnormal"):
                key = (fmt, operands)
                if key in public:
                    lines.append(line([fmt, operands, "as written"], public[key]))
                if key in rewritten:
                    lines.append(line([fmt, operands, "kernel path"], rewritten[key]))
                if key in public and key in rewritten:
                    lines.append(ratio_line([fmt, operands, "ratio"], ratios(public[key], rewritten[key])))
    wide = [f for f in ("e8f15", "e15f64", "binary256", "binary512", "binary1024", "binary4096")
            if any(key[0] == f for key in now)]
    if wide:
        lines += ["", "## Wide and custom formats", "",
                  "The kernel path in two custom layouts (`e8f15`, 24 bits, and `e15f64`, 80 bits) and in "
                  "the IEEE interchange formats of 256 to 4,096 bits (19, 23, 27 and 35 exponent bits), "
                  "eight triples per cell, the fastest of three runs. The public operations are not "
                  "measured at these widths.", "",
                  "| format | operands | add | sub | mul | div | sqrt | fma |",
                  "| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |"]
        for fmt in wide:
            for operands in ("normal", "subnormal", "special"):
                if (fmt, operands) in now:
                    lines.append(line([fmt, operands], now[(fmt, operands)]))
        lines += ["",
                  "The cost grows slowly with the width: the short paths of addition and multiplication "
                  "do not look at the width, a normal significand has its bit length after one "
                  "comparison, the general rounding finds a bit length beyond 384 bits by a search "
                  "down to a window of 128 bits, and the square root takes sixteen Newton steps when "
                  "eight do not pass its check. No sum, no rounding and no quotient builds a power of "
                  "two of the size of an exponent difference, so a sum with a zero, a product far "
                  "below the subnormal range and a quotient of operands at the two ends of the range "
                  "cost the same at every exponent width (`KernelPath.divCore_def` for the quotient). "
                  "The operations with status flags still put the exact result on a grid of absolute "
                  "exponents; they are meant for formats up to binary256."]
    extras = kernel / "extras.csv"
    if extras.exists():
        data = {(r["format"], r["term"]): (positive(r["as_written_microseconds"]),
                                           positive(r["with_rules_microseconds"])) for r in read_csv(extras)}
        lines += ["", "## Outcomes with status flags, comparisons, conversions and literals", "",
                  f"`benchmarks/kernel/extras.sh 64 5` ({section('extras')}) reduces one term per row "
                  "twice: as written, through the public operations, and after the rewrite that "
                  "`float_decide` applies. Microseconds per operation on normal operands, 64 operand "
                  "triples or literals per cell, the fastest of five runs. A row with `status := true` "
                  "evaluates the delivered value, the comparison of the flags with a record and the "
                  "comparison of the ternary value with a constant, as a statement about an outcome "
                  "does. The cast rows are the reference cast `Model.cast` of a decoded value, stored "
                  "in the destination format; the public conversion `x.cast (target := T)` is not "
                  "rewritten. The rational numbers are `mkRat (2 * i + 1) (3 * i + 7)`, and the time "
                  "the kernel needs to build them is subtracted on both sides. `n/a` is a cell whose "
                  "difference came out at zero or below, which happens to the cheapest terms on a busy "
                  "machine.", "",
                  "| term | binary32 as written | binary32 rewritten | ratio | binary64 as written | "
                  "binary64 rewritten | ratio |", "| --- | ---: | ---: | ---: | ---: | ---: | ---: |"]
        for term in EXTRAS:
            row = [EXTRAS_TERMS[term]]
            for fmt in ("binary32", "binary64"):
                a, b = data.get((fmt, term), (None, None))
                row += [f"{a:,.0f}" if a else "n/a", f"{b:,.0f}" if b else "n/a",
                        f"{a / b:,.0f}x" if a and b else ""]
            lines.append("| " + " | ".join(row) + " |")
    loops = kernel / "loops.csv"
    if loops.exists():
        data = {(r["theorem"], r["path"]): number(r["seconds"]) for r in read_csv(loops)}
        coq = {r["theorem"]: r for r in read_csv(RECORDED / "coq-loops.csv")} \
            if (RECORDED / "coq-loops.csv").exists() else {}
        lines += ["", "## Three theorems about loops of 1,000 steps", "",
                  f"`benchmarks/kernel/loops.sh 3` ({section('loops')}) type-checks each theorem of "
                  "`Loops.lean` three times by `decide +kernel` on the public operations and by "
                  "`float_decide`, and prints the `type checking` time of Lean's profiler; the table "
                  "has the fastest run. `FlocqConversion.v` states the same three results for Coq "
                  "8.20.1 with Flocq 4.2.2; its two columns are the `Time Qed` lines recorded on "
                  "2026-11-15 in the container `leanfloat-flocq-bench:4.2.2` (8 GB, 2 CPUs).", "",
                  "| theorem | `decide +kernel`, public operations | `float_decide` | Coq, kernel "
                  "conversion (recorded) | Coq, bytecode VM (recorded) |",
                  "| --- | ---: | ---: | ---: | ---: |"]
        for name, label in LOOPS.items():
            public, fast = data.get((name, "public")), data.get((name, "kernel"))
            row = coq.get(name, {})
            lines.append(f"| {label} | {public:.2f} s | {fast:.3f} s | "
                         f"{row.get('coq_kernel_conversion_seconds', '')} s | {row.get('coq_vm_seconds', '')} s |"
                         if public and fast else f"| {label} | n/a | n/a | | |")
        lines += ["",
                  "The `float_decide` column is the kernel's check of the loop. Each proof has two "
                  "more lemmas, the rewrite of the goal and the statement itself, which the kernel "
                  "checks in milliseconds. Each Lean theorem depends on `propext`, `Classical.choice` "
                  "and `Quot.sound` only (the `axioms` column of `loops.csv`). The Coq file computes "
                  "the binary64 operands once with `vm_compute` and stores them as lists, so that its "
                  "conversions contain floating-point operations only; Lean computes the operands "
                  "inside the kernel."]
    exhaustive = backends / "exhaustive.csv"
    if exhaustive.exists():
        lines += ["", "## Statements about all 65,536 pairs of encodings", "",
                  "Seconds of kernel time to check one statement about all pairs "
                  f"({section('exhaustive')}): the loop of `float_decide` over the pairs "
                  "(`benchmarks/kernel/Exhaustive.lean`: addition and multiplication of E4M3 commute "
                  "on all pairs of encodings that are not both NaN), and one run of each side on "
                  "rows of 65,536 lanes (`lane_decide`, `benchmarks/suite/Lanes.lean`), where the "
                  "time is the sum over the lane widths that were tried.", "",
                  "| statement | method | seconds | lane widths tried |", "| --- | --- | ---: | ---: |"]
        for row in read_csv(exhaustive):
            attempts = row["attempts"] if "lane" in row["method"] else ""
            lines.append(f"| {row['statement']} | {row['method']} | {float(row['seconds']):.2f} | {attempts} |")
    (kernel / "README.md").write_text("\n".join(lines) + "\n")


def install(raw: Path) -> None:
    """Result files under `benchmarks/results/` from the logs of a timing run in `raw`.

    A section whose runner failed, or that left no row, keeps the files of the run before it,
    and `measured.json` keeps saying which run each section's files are from.
    """
    run = json.loads(need(raw / "run.json", "the record of a timing run").read_text())
    measured = json.loads(MEASURED.read_text()) if MEASURED.exists() else {"sections": {}}
    backends, kernel, ieee, exact = (RESULTS / d for d in ("backends", "kernel", "ieee2019", "exact"))
    suite = raw / "suite"

    def ran(name: str) -> bool:
        return run["sections"].get(name, {}).get("exit") == 0

    logs = {"kernel-binary": [suite / "kernel-binary"], "families": [suite / "families.log"],
            "exhaustive": [suite / "exhaustive-loop.log", suite / "exhaustive-lanes.log"],
            "matched": [suite / "matched" / "lean"], "kernel-public": [raw / "kernel" / "public.log"],
            "kernel-spec": [raw / "kernel" / "spec.log"], "extras": [raw / "kernel" / "extras.log"],
            "kernel-public-64": [raw / "kernel" / "triples64" / "public.log"],
            "kernel-spec-64": [raw / "kernel" / "triples64" / "spec.log"],
            "kernel-64": [raw / "kernel" / "triples64" / "kernel.log"],
            "loops": [raw / "kernel" / "loops.log"],
            "blocks": [raw / "kernel" / "mx.log", raw / "kernel" / "nvfp4.log"],
            "ieee2019": [raw / "ieee2019" / "ieee2019.log"],
            "ieee2019-wide": [raw / "ieee2019-wide" / "ieee2019.log"],
            "exact": [raw / "exact" / f for f in ("operations.log", "workloads.log", "baseline.log",
                                                  "tactic.log")]}
    # (`exact-native` ends with a statement that `native_decide` refuses: that error is its result.)

    def keep(name: str, rows: int) -> None:
        errors = log_errors(*logs.get(name, []))
        entry = dict(run["sections"][name], rows=rows, errors=errors)
        note = f", {errors} Lean error line(s) in its logs" if errors else ""
        if rows > 0:
            measured["sections"][name] = entry
            print(f"  {name}: {rows} rows installed{note}")
        else:
            print(f"  {name}: no row in the logs, the earlier files stay{note}")

    for name, files in (("kernel-binary", ["kernel-binary.csv"]), ("families", ["families.csv"]),
                        ("exhaustive", ["exhaustive.csv"]),
                        ("compiled", ["compiled-sweep.csv", "compiled-fp8.csv", "compiled-posit.csv"]),
                        ("compiled-comparison", ["compiled-comparison.csv"])):
        if ran(name):
            count = 0
            for file in files:
                if data_rows(suite / file):
                    (backends / file).write_bytes((suite / file).read_bytes())
                    count += data_rows(suite / file)
            keep(name, count)
    if ran("matched"):
        source = suite / "matched" / "matched.csv"
        keep("matched", merge_coq(backends / "matched.csv", source) if data_rows(source) else 0)

    written = []
    for name, path in (("kernel-public", "public"), ("kernel-spec", "spec")):
        if ran(name):
            rows = kernel_table(raw / "kernel" / f"{path}.md")
            if rows:
                (kernel / f"{path}.md").write_bytes((raw / "kernel" / f"{path}.md").read_bytes())
            written += [[f, BITS.get(f, ""), operands, op, value, path] for f, operands, op, value in rows]
            keep(name, len(rows))
    if written:
        old = [[r[k] for k in ("format", "bits", "operands", "operation", "microseconds", "path")]
               for r in (read_csv(kernel / "as-written.csv") if (kernel / "as-written.csv").exists() else [])
               if r["path"] not in {row[5] for row in written}]
        write_rows(kernel / "as-written.csv",
                   ["format", "bits", "operands", "operation", "microseconds", "path"], old + written)

    wide = []
    for name, path in (("kernel-public-64", "public"), ("kernel-spec-64", "spec"), ("kernel-64", "kernel")):
        if ran(name):
            rows = kernel_table(raw / "kernel" / "triples64" / f"{path}.md")
            wide += [[f, BITS.get(f, ""), operands, op, value, path] for f, operands, op, value in rows]
            keep(name, len(rows))
    if wide:
        old = [[r[k] for k in ("format", "bits", "operands", "operation", "microseconds", "path")]
               for r in (read_csv(kernel / "triples64.csv") if (kernel / "triples64.csv").exists() else [])
               if r["path"] not in {row[5] for row in wide}]
        write_rows(kernel / "triples64.csv",
                   ["format", "bits", "operands", "operation", "microseconds", "path"], old + wide)

    if ran("ieee2019") or ran("ieee2019-wide"):
        measured_logs = [raw / d / "ieee2019.log" for d, name in (("ieee2019", "ieee2019"),
                                                                   ("ieee2019-wide", "ieee2019-wide")) if ran(name)]
        rows = ieee_kernel_rows(measured_logs)
        formats = {r[0] for r in rows}
        old = [[r[k] for k in ("format", "bits", "operation", "as_written_microseconds",
                               "with_rules_microseconds")]
               for r in (read_csv(ieee / "kernel.csv") if (ieee / "kernel.csv").exists() else [])
               if r["format"] not in formats]
        if rows:
            write_rows(ieee / "kernel.csv", ["format", "bits", "operation", "as_written_microseconds",
                                             "with_rules_microseconds"], old + rows)
        for name, directory in (("ieee2019", "ieee2019"), ("ieee2019-wide", "ieee2019-wide")):
            if ran(name):
                keep(name, len([r for r in ieee_kernel_rows([raw / directory / "ieee2019.log"])]))
    if ran("ieee2019-compiled") or ran("functions"):
        # `compiled.csv`: the operations (one run of the executable) and then the recommended
        # functions of clause 9.2 (one run per format); a part that did not run keeps its rows.
        def rows_of(log: Path) -> list:
            return [line for line in log.read_text(errors="replace").splitlines()
                    if re.match(r"(binary|decimal),[^,]+,\d+,[^,]+,\d+,", line)] if log.exists() else []

        old = (ieee / "compiled.csv").read_text().splitlines()[1:] if (ieee / "compiled.csv").exists() else []
        names = {line.split(",")[3] for line in rows_of(raw / "ieee2019" / "functions.log")} or \
            {line.split(",")[3] for line in old[-400:] if line.startswith("binary,")} & set(REAL_FUNCTIONS + [
                "pow", "rSqrt", "hypot", "pown", "rootn", "expm1", "logp1", "exp", "log"])

        def is_function(line: str) -> bool:
            return line.startswith("binary,") and line.split(",")[3] in names

        operations = rows_of(raw / "ieee2019" / "compiled.log") if ran("ieee2019-compiled") else \
            [line for line in old if not is_function(line)]
        functions = rows_of(raw / "ieee2019" / "functions.log") if ran("functions") else \
            [line for line in old if is_function(line)]
        if operations or functions:
            (ieee / "compiled.csv").write_text("\n".join(
                ["radix,format,bits,operation,nanoseconds,checksum"] + operations + functions) + "\n")
        if ran("ieee2019-compiled"):
            keep("ieee2019-compiled", len(operations))
        if ran("functions"):
            keep("functions", len(functions))

    if ran("extras"):
        rows = extras_rows(raw / "kernel" / "extras.log")
        if rows:
            write_rows(kernel / "extras.csv", ["format", "bits", "term", "as_written_microseconds",
                                               "with_rules_microseconds"], rows)
            if (raw / "kernel" / "extras.md").exists():
                (kernel / "extras.md").write_bytes((raw / "kernel" / "extras.md").read_bytes())
        keep("extras", len(rows))
    if ran("loops"):
        rows = loop_rows(raw / "kernel" / "loops.log")
        if rows:
            write_rows(kernel / "loops.csv", ["theorem", "path", "seconds", "runs", "axioms"], rows)
        keep("loops", len(rows))
    if ran("blocks"):
        rows = block_rows([raw / "kernel" / "mx.log", raw / "kernel" / "nvfp4.log"])
        if rows:
            write_rows(kernel / "blocks.csv", ["family", "row", "with_rules_microseconds"], rows)
        keep("blocks", len(rows))

    copied = 0
    for name, files in (("exact", ("operations.log", "workloads.log", "baseline.log", "tactic.log")),
                        ("exact-native", ("native.log",)), ("exact-compiled", ("compiled.log", "load.log"))):
        if ran(name):
            count = 0
            for file in files:
                source = raw / "exact" / file
                if source.exists() and source.stat().st_size:
                    (exact / file).write_bytes(source.read_bytes())
                    count += len(source.read_text(errors="replace").splitlines())
            keep(name, count)
            copied += count
    if copied:      # the tables of `benchmarks/exact/tables.py`, from the logs now in place
        (exact / "toolchain.log").write_text((ROOT / "lean-toolchain").read_text())
        subprocess.run([sys.executable, "-I", str(ROOT / "benchmarks/exact/tables.py"), str(exact)],
                       check=True, stdout=subprocess.DEVNULL)

    for key in ("commit", "short", "dirty", "toolchain", "lean", "machine", "date", "started_utc",
                "seconds", "jobs", "threads", "runs"):
        if run.get(key) is None:        # a run that names no commit leaves none of an earlier run
            measured.pop(key, None)
        else:
            measured[key] = run[key]
    if all(ran(name) for name in ("kernel-binary", "matched", "families", "exhaustive", "compiled",
                                  "compiled-comparison")) \
            and (suite / "README.md").exists():
        backends_readme(suite / "README.md", backends, measured)
    if any(ran(name) for name in ("ieee2019", "ieee2019-wide", "ieee2019-compiled", "functions")):
        ieee_readme(ieee, measured)
    if any(ran(name) for name in ("kernel-binary", "kernel-public", "kernel-spec", "extras", "loops",
                                  "exhaustive", "kernel-64")):
        kernel_readme(kernel, backends, measured)
    OUT.mkdir(parents=True, exist_ok=True)
    MEASURED.write_text(json.dumps(measured, indent=2) + "\n")
