#!/usr/bin/env python3
"""Tables of the benchmark suite, from the logs of `benchmarks/suite/run.sh`.

    tables.py OUT

Reads whatever sections are present in OUT and writes one CSV per section and `README.md` with
every table. A section that was not run is left out. Nothing is measured here.

    kernel-binary/kernel.md        -> kernel-binary.csv  (and kernel-binary-base/kernel.md, the
                                      same section run in a checkout of another commit, when
                                      present)
    matched/lean/*.log, flocq/*.log -> matched.csv (matched.py)
    families.log                   -> families.csv
    exhaustive-loop.log, exhaustive-lanes.log -> exhaustive.csv
    compiled/sweep.log, fp8.log, posit/, comparison/ -> compiled-sweep.csv, compiled-fp8.csv,
                                      compiled-posit.csv, compiled-comparison.csv
"""
import csv
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import matched  # noqa: E402

OPS = ["add", "sub", "mul", "div", "sqrt", "fma"]
BITS = {
    "e4m3": 8, "e5m2": 8, "binary16": 16, "e8f15": 24, "bfloat16": 16, "binary32": 32,
    "binary64": 64, "e15f64": 80, "binary128": 128, "binary256": 256, "binary512": 512,
    "binary1024": 1024, "binary4096": 4096,
}


def read_kernel_table(path: Path):
    """{(format, operands): {op: microseconds or None}} from a table of run.sh."""
    cells = {}
    if not path.exists():
        return cells
    for line in path.read_text().splitlines():
        parts = [part.strip() for part in line.strip().strip("|").split("|")]
        if len(parts) != 8 or parts[0] in ("format", "---"):
            continue
        values = {}
        for op, text in zip(OPS, parts[2:]):
            try:
                values[op] = float(text.replace(",", ""))
            except ValueError:
                values[op] = None
        cells[(parts[0], parts[1])] = values
    return cells


def number(value) -> str:
    if value is None:
        return "no result"
    if value >= 100:
        return f"{value:,.0f}"
    return f"{value:.1f}" if value < 10 else f"{value:.0f}"


def kernel_binary(out: Path, lines: list) -> None:
    now = read_kernel_table(out / "kernel-binary" / "kernel.md")
    if not now:
        return
    base = read_kernel_table(out / "kernel-binary-base" / "kernel.md")
    with open(out / "kernel-binary.csv", "w", newline="") as handle:
        writer = csv.writer(handle, lineterminator="\n")
        writer.writerow(["commit", "format", "bits", "operands", "operation", "microseconds"])
        for label, cells in (("now", now), ("base", base)):
            for (name, operands), values in cells.items():
                for op in OPS:
                    writer.writerow([label, name, BITS.get(name, ""), operands, op,
                                     "" if values[op] is None else values[op]])
    lines += [
        "## Kernel time per operation, binary formats",
        "",
        "Microseconds of kernel time for one operation as `float_decide` rewrites it, nearest",
        "even, eight operand triples per cell, the fastest of three runs",
        "(`benchmarks/kernel/run.sh kernel 8 3`). `e8f15` is a custom layout of 24 bits and",
        "`e15f64` one of 80 bits." + (
            " The `base` rows are the same run in a checkout of the commit this work started"
            " from." if base else ""),
        "",
    ]
    # The column that tells the two runs apart is there only when there are two.
    label = (lambda text: f" {text} |") if base else (lambda text: "")
    lines += [
        "| format | bits | operands |" + label("commit") + " add | sub | mul | div | sqrt | fma |",
        "| --- | ---: | --- |" + label("---") + " ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for (name, operands), values in now.items():
        row = " | ".join(number(values[op]) for op in OPS)
        lines.append(f"| {name} | {BITS.get(name, '')} | {operands} |{label('now')} {row} |")
        if (name, operands) in base:
            row = " | ".join(number(base[(name, operands)][op]) for op in OPS)
            lines.append(f"| {name} | {BITS.get(name, '')} | {operands} | base | {row} |")
    lines.append("")


def matched_section(out: Path, lines: list) -> None:
    directory = out / "matched"
    if not (directory / "lean").exists() or not list((directory / "lean").glob("*.log")):
        return
    status = matched.table(directory)
    lines += [
        "## The same loops in Lean's kernel and in Coq with Flocq",
        "",
        "Microseconds per operation in a loop of 100 operations (10 from 512 bits on), on the",
        "same operands: Lean's kernel on the rewritten term (`#kernel_cost rewritten`), and Coq",
        "8.20.1 with Flocq 4.2.2 (`BinarySingleNaN`, `mode_NE`) under `vm_compute` and under",
        "`lazy`, in a container with 8 GB and two CPUs. `no result` means that the evaluation",
        "did not finish within 300 seconds or ran out of the 8 GB. `values` says whether Coq",
        "printed the value that Lean computed.",
        "",
        (directory / "matched.md").read_text(),
    ]
    if status:
        lines += ["**Some values differ between the two sides: see the table.**", ""]


def families(out: Path, lines: list) -> None:
    log = out / "families.log"
    if not log.exists():
        return
    rows, label = [], None
    for line in log.read_text(errors="replace").splitlines():
        match = re.match(r"KCOST (.*)", line)
        if match:
            label = match.group(1)
            rows.append({"operation": label, "as_written_us": None, "rules_us": None})
        match = re.match(r"as written: ([0-9.]+) µs", line)
        if match and rows:
            rows[-1]["as_written_us"] = float(match.group(1))
        match = re.match(r"with the tagged kernel rules: ([0-9.]+) µs", line)
        if match and rows:
            rows[-1]["rules_us"] = float(match.group(1))
    with open(out / "families.csv", "w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=["operation", "as_written_us", "rules_us"],
                                lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)
    lines += [
        "## Kernel time of one operation, other families",
        "",
        "Median microseconds of one kernel evaluation of the public operation on stored codes,",
        "as written and after the rewrite with the tagged kernel rules (`#kernel_cost`,",
        "`benchmarks/suite/Families.lean`). A single evaluation includes about 100 microseconds",
        "of fixed work that a loop pays once. `no rule` means that no tagged rule applies, so",
        "`float_decide` evaluates the operation as written. A row that compares a rational",
        "result with a constant includes about 800 microseconds for that comparison.",
        "",
        "| operation | as written (µs) | with the tagged rules (µs) |",
        "| --- | ---: | ---: |",
    ]
    for row in rows:
        rules = "no rule" if row["rules_us"] is None else number(row["rules_us"])
        lines.append(f"| {row['operation']} | {number(row['as_written_us'])} | {rules} |")
    lines.append("")


def seconds(text: str) -> float:
    match = re.match(r"([0-9.]+)(ms|s)", text)
    value = float(match.group(1))
    return value / 1000 if match.group(2) == "ms" else value


def exhaustive(out: Path, lines: list) -> None:
    rows = []
    loop = out / "exhaustive-loop.log"
    if loop.exists():
        times = re.findall(r"type checking took ([0-9.]+m?s)", loop.read_text(errors="replace"))
        for name, text in zip(["e4m3 add-commutes", "e4m3 mul-commutes"], times):
            rows.append({"statement": name, "method": "float_decide loop",
                         "seconds": seconds(text), "attempts": 1})
    lanes = out / "exhaustive-lanes.log"
    if lanes.exists():
        label, total, attempts = None, 0.0, 0
        for line in lanes.read_text(errors="replace").splitlines() + ["KLANES end"]:
            match = re.match(r"KLANES (.*)", line)
            if match:
                if label:
                    rows.append({"statement": label, "method": "lane_decide",
                                 "seconds": total, "attempts": attempts})
                label, total, attempts = match.group(1), 0.0, 0
            match = re.match(r"type checking took ([0-9.]+m?s)", line)
            if match and label:
                total += seconds(match.group(1))
                attempts += 1
    if not rows:
        return
    with open(out / "exhaustive.csv", "w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=["statement", "method", "seconds", "attempts"],
                                lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)
    lines += [
        "## Statements about all 65,536 pairs of encodings",
        "",
        "Seconds of kernel time to check one statement about all pairs: the loop of",
        "`float_decide` over the pairs (`benchmarks/kernel/Exhaustive.lean`) and one run of each",
        "side on rows of 65,536 lanes (`lane_decide`, `benchmarks/suite/Lanes.lean`). The lane",
        "time is the sum over the lane widths that were tried (`attempts`): a run that does not",
        "fit lanes of 16 bits is repeated with 32 and then 64. The binary16 rows cover a slice",
        "of 65,536 pairs of encodings. `add-table` is the kernel check of one packed table.",
        "",
        "| statement | method | seconds | lane widths tried |",
        "| --- | --- | ---: | ---: |",
    ]
    for row in rows:
        lines.append(f"| {row['statement']} | {row['method']} | {row['seconds']:.2f} | "
                     f"{row['attempts'] if row['method'] == 'lane_decide' else ''} |")
    lines.append("")


def compiled(out: Path, lines: list) -> None:
    directory = out / "compiled"
    if not directory.exists():
        return
    lines += ["## Compiled code", ""]
    sweep = directory / "sweep.log"
    if sweep.exists():
        # ExecFloat,operation,precision,backend,throughput,_,iterations,nanoseconds,checksum
        cells, backends, precisions = {}, {}, []
        for line in sweep.read_text(errors="replace").splitlines():
            parts = line.split(",")
            if len(parts) != 9 or parts[0] != "ExecFloat":
                continue
            operation, precision = parts[1], int(parts[2])
            if precision not in precisions:
                precisions.append(precision)
            cells[(precision, operation)] = float(parts[7]) / float(parts[6])
            backends[(precision, operation)] = parts[3]
        if cells:
            with open(out / "compiled-sweep.csv", "w", newline="") as handle:
                writer = csv.writer(handle, lineterminator="\n")
                writer.writerow(["precision", "operation", "nanoseconds", "backend"])
                for (precision, operation), nanos in cells.items():
                    writer.writerow([precision, operation, f"{nanos:.1f}",
                                     backends[(precision, operation)]])
            lines += [
                "### FloatLib, six operations at 17 significand precisions",
                "",
                "Nanoseconds per compiled public operation (`execFloatSweep all`, one run, loop",
                "time divided by the iteration count). The precision is the number of",
                "significand bits: 24 is binary32, 53 binary64, 113 binary128. `compiled-sweep.csv`",
                "also records the backend that the planner selected for each cell.",
                "",
                "| significand bits | add | sub | mul | div | sqrt | fma |",
                "| ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
            ]
            for precision in precisions:
                row = " | ".join(
                    number(cells.get((precision, op))) for op in OPS)
                lines.append(f"| {precision} | {row} |")
            lines.append("")
    fp8 = directory / "fp8.log"
    if fp8.exists():
        # implementation,format,storageBits,precision,backend,policy,expectedCalls,operation,
        # iterations,totalNanos,sink
        cells, formats = {}, []
        for line in fp8.read_text(errors="replace").splitlines():
            parts = line.split(",")
            if len(parts) != 11 or not parts[0].startswith("ExecFloat "):
                continue
            kind = parts[0].split()[1]
            if parts[1] not in formats:
                formats.append(parts[1])
            cells[(parts[1], kind, parts[7])] = float(parts[9]) / float(parts[8])
        if cells:
            with open(out / "compiled-fp8.csv", "w", newline="") as handle:
                writer = csv.writer(handle, lineterminator="\n")
                writer.writerow(["format", "type", "operation", "nanoseconds"])
                for (name, kind, operation), nanos in cells.items():
                    writer.writerow([name, kind, operation, f"{nanos:.1f}"])
            lines += [
                "### FP8 formats",
                "",
                "Nanoseconds per compiled operation (`execFloatFP8Bench`, one run): the nominal",
                "type of the format, whose capability is static, and the same layout given as a",
                "descriptor at run time.",
                "",
                "| format | type | add | sub | mul | div | sqrt | fma |",
                "| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |",
            ]
            for name in formats:
                for kind in ("nominal", "descriptor"):
                    row = " | ".join(number(cells.get((name, kind, op))) for op in OPS)
                    lines.append(f"| {name} | {kind} | {row} |")
            lines.append("")
    posit = directory / "posit" / "plots" / "posit-summary.csv"
    if posit.exists():
        cells, widths = {}, []
        with open(posit, newline="") as handle:
            for row in csv.DictReader(handle):
                width = int(row["totalBits"])
                if width not in widths:
                    widths.append(width)
                cells[(width, row["operation"])] = float(row["medianNanosPerOp"])
        widths.sort()
        with open(out / "compiled-posit.csv", "w", newline="") as handle:
            writer = csv.writer(handle, lineterminator="\n")
            writer.writerow(["bits", "operation", "nanoseconds"])
            for (width, operation), nanos in sorted(cells.items()):
                writer.writerow([width, operation, f"{nanos:.1f}"])
        lines += [
            "### Posits",
            "",
            "Median nanoseconds per compiled posit operation over nine trials",
            "(`benchmarks/scripts/posit.sh`), by the total width of the posit.",
            "",
            "| bits | add | sub | mul | div | sqrt | fma |",
            "| ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
        ]
        for width in widths:
            row = " | ".join(number(cells.get((width, op))) for op in OPS)
            lines.append(f"| {width} | {row} |")
        lines.append("")
    summary = directory / "comparison" / "plots" / "summary.csv"
    if summary.exists():
        series = {
            "ExecFloat binary proved software": "FloatLib",
            "MPFR (binary) software reference": "MPFR",
            "Berkeley SoftFloat IEEE software": "SoftFloat",
            "Native C IEEE FPU": "native FPU",
            "ExecFloat Posit proved software": "FloatLib posit",
        }
        cells, widths = {}, []
        with open(summary, newline="") as handle:
            for row in csv.DictReader(handle):
                name = series.get(row["series"])
                if name is None:
                    continue
                width = int(row["totalBits"])
                if width not in widths:
                    widths.append(width)
                cells[(width, row["operation"], name)] = float(row["medianNanosPerOp"])
        widths.sort()
        with open(out / "compiled-comparison.csv", "w", newline="") as handle:
            writer = csv.writer(handle, lineterminator="\n")
            writer.writerow(["bits", "operation", "implementation", "nanoseconds"])
            for (width, operation, name), nanos in sorted(cells.items()):
                writer.writerow([width, operation, name, f"{nanos:.1f}"])
        names = ["FloatLib", "MPFR", "SoftFloat", "native FPU", "FloatLib posit"]
        lines += [
            "### FloatLib next to MPFR, Berkeley SoftFloat and the native FPU",
            "",
            "Nanoseconds per operation in the scalar dependency chain of",
            "`benchmarks/scripts/format-comparison.sh` (one development trial, calibrated loops of",
            "about 200 ms). MPFR runs at the precision, exponent range and rounding of the binary",
            "format of that width. SoftFloat and the native FPU exist for binary32 and binary64.",
            "The posit column is FloatLib's posit of the same storage width.",
            "",
            "| bits | operation | " + " | ".join(names) + " |",
            "| ---: | --- | " + " | ".join("---:" for _ in names) + " |",
        ]
        for width in widths:
            for operation in OPS:
                if not any((width, operation, name) in cells for name in names):
                    continue
                row = " | ".join(
                    number(cells[(width, operation, name)]) if (width, operation, name) in cells
                    else "" for name in names)
                lines.append(f"| {width} | {operation} | {row} |")
        lines.append("")


def main() -> int:
    if len(sys.argv) != 2:
        print(__doc__)
        return 2
    out = Path(sys.argv[1])
    lines = [
        "# Benchmark suite: kernel and compiled code",
        "",
        "Produced by `benchmarks/suite/run.sh`. Every number is a time measured on one shared",
        "machine while other jobs were running, so read the tables as ratios. The CSV files next",
        "to this file hold the same numbers.",
        "",
    ]
    kernel_binary(out, lines)
    matched_section(out, lines)
    families(out, lines)
    exhaustive(out, lines)
    compiled(out, lines)
    (out / "README.md").write_text("\n".join(lines) + "\n")
    print(f"wrote {out / 'README.md'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
