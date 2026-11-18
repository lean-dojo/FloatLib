#!/usr/bin/env python3
"""Verify the retained Flocq comparison and optionally regenerate its website figure.

The archive keeps the raw timings of all nine trials, complete numerical outputs, and
the campaign records together. Verification reads it directly and rebuilds the
nine-trial medians in matched-benchmark-summary.csv. No extraction, build, or timing
run is needed.

The figure follows the figure rules of the library and the guide's `figstyle.py`: the image
holds the six panels with their letters, axes with units and a legend of short series names.
What was measured, on which machine and how (nine trials, matching precision and exponent
bounds, the square-root blocks at 1,024 bits and above) is in the caption of the chapter and
in `benchmarks/results/flocq-matched/README.md`, not in the drawing.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import math
from pathlib import Path
import statistics
import zipfile


RESULTS = Path(__file__).resolve().parents[1] / "results" / "flocq-matched"
ARCHIVE_SHA256 = "177b818bc1026cb33bcb06b8881b895886052f6ca497c422cdb8d045e27d9b43"
TRIALS = 9
MAIN_SOURCE = "main/raw/trial-*.csv"
BALANCED_SOURCE = "balanced-sqrt/results-9trials/raw.csv"
SUMMARY_FIELDS = (
    "series", "implementation", "family", "format", "totalBits", "operation",
    "executionClass", "backend", "measurementMethod", "iterations", "blocks", "trials",
    "medianNanosPerOp", "minimumNanosPerOp", "maximumNanosPerOp", "source",
)
SERIES_NAMES = {
    "ExecFloat": "ExecFloat binary proved software",
    "Flocq": "Flocq binary reference (precision model)",
    "MPFR": "MPFR (binary) software reference",
}
EXPONENT_BITS = {
    6: 3, 8: 4, 16: 5, 32: 8, 64: 11, 128: 15,
    256: 19, 512: 19, 1024: 19, 2048: 19, 4096: 19,
}
OPERATIONS = {
    "add": "addition", "sub": "subtraction", "mul": "multiplication",
    "div": "division", "sqrt": "square root", "fma": "fused multiply-add",
}
# Implementation, legend name, its name in the guide's series map (`figstyle.SERIES`), and the
# colour, marker and line style of that map for a `figstyle` that does not have it.
SERIES = (
    ("ExecFloat", "FloatLib", "FloatLib", "#0072B2", "o", "-"),
    ("Flocq", "Flocq 4.2.2, extracted", "Flocq", "#D55E00", "s", "-"),
    ("MPFR", "MPFR", "MPFR", "#009E73", "D", "-"),
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def read_csv(data: bytes) -> list[dict[str, str]]:
    return list(csv.DictReader(io.StringIO(data.decode())))


def key(row: dict[str, str]) -> tuple[str, int, str]:
    return row["implementation"], int(row["totalBits"]), row["operation"]


def digest(value: str) -> int:
    """OCaml prints Int64 as signed decimal; C and Lean print unsigned decimal."""
    n = int(value)
    require(-(1 << 63) <= n < (1 << 64), "Digest outside signed/unsigned 64-bit range")
    return n % (1 << 64)


def check_prefixes(rows: list[dict[str, str]], iterations: int) -> None:
    groups: dict[tuple[int, str], set[tuple[int, int, int]]] = {}
    for row in rows:
        prefix = (
            int(row["agreementIterations"]),
            digest(row["agreementSink"]),
            digest(row["agreementFixtureTraceDigest"]),
        )
        require(prefix[0] == iterations, "Unexpected agreement-prefix length")
        groups.setdefault((int(row["totalBits"]), row["operation"]), set()).add(prefix)
    require(all(len(values) == 1 for values in groups.values()), "Agreement-prefix mismatch")


def normalize(sign: int, significand: int, exponent: int) -> tuple[int, int, int]:
    require(sign in (0, 1) and significand >= 0, "Malformed finite value")
    if significand == 0:
        return sign, 0, 0
    shift = (significand & -significand).bit_length() - 1
    return sign, significand >> shift, exponent + shift


def numerical_values(data: bytes, *, packed: bool) -> dict:
    """Compare complete values, including zero signs, rather than truncated hashes."""
    values = {}
    for line in data.decode().splitlines():
        fields = line.split("|")
        width, operation, index = int(fields[0]), fields[1], int(fields[2])
        require(width in EXPONENT_BITS, "Unexpected numerical-check width")
        if packed:
            require(len(fields) == 4, "Malformed packed value")
            bits = int(fields[3])
            require(0 <= bits < 1 << width, "Packed value outside its width")
            fraction_bits = width - EXPONENT_BITS[width] - 1
            sign = bits >> (width - 1)
            exp = (bits >> fraction_bits) & ((1 << EXPONENT_BITS[width]) - 1)
            fraction = bits & ((1 << fraction_bits) - 1)
            require(exp != (1 << EXPONENT_BITS[width]) - 1, "Nonfinite benchmark value")
            bias = (1 << (EXPONENT_BITS[width] - 1)) - 1
            significand = fraction if exp == 0 else (1 << fraction_bits) + fraction
            value = normalize(sign, significand, max(1, exp) - bias - fraction_bits)
        else:
            require(fields[3] in ("finite", "zero"), "Nonfinite benchmark value")
            if fields[3] == "zero":
                require(len(fields) == 7 and fields[5:] == ["0", "0"], "Malformed zero")
                value = normalize(int(fields[4]), 0, 0)
            else:
                require(len(fields) == 7 and int(fields[5]) > 0, "Malformed finite value")
                value = normalize(int(fields[4]), int(fields[5]), int(fields[6]))
        record = width, operation, index
        require(record not in values, "Duplicate numerical record")
        values[record] = value
    expected = {
        (width, operation, index)
        for width in EXPONENT_BITS
        for operation in (*OPERATIONS, "input-x", "input-y", "input-sqrt")
        for index in range(16)
    }
    require(values.keys() == expected, "Incomplete numerical-check matrix")
    return values


def select(main: list[list[dict[str, str]]],
           balanced: list[dict[str, str]]) -> list[dict[str, str]]:
    """Nine-trial medians per cell; complete-block square roots replace the main chain."""
    expected = {
        (impl, width, operation)
        for impl, *_ in SERIES for width in EXPONENT_BITS for operation in OPERATIONS
    }
    replacements = {(impl, width, "sqrt") for impl, *_ in SERIES
                    for width in (1024, 2048, 4096)}
    require(len(main) == TRIALS, "Unexpected number of main trials")
    for trial in main:
        require(len(trial) == len(expected) and {key(r) for r in trial} == expected,
                "Incomplete or duplicate main matrix")
    require(len(balanced) == len(replacements) * TRIALS, "Incomplete balanced matrix")
    groups: dict[tuple[str, int, str], list[dict[str, str]]] = {}
    for cell in expected - replacements:
        groups[cell] = [next(r for r in trial if key(r) == cell) for trial in main]
    for row in balanced:
        require(key(row) in replacements, "Unexpected balanced cell")
        groups.setdefault(key(row), []).append(row)
    selected = []
    for cell in sorted(expected):
        rows = groups[cell]
        balanced_cell = cell in replacements
        if balanced_cell:
            require(sorted(int(r["trial"]) for r in rows) == list(range(1, TRIALS + 1)),
                    f"Balanced trials incomplete: {cell}")
        first = rows[0]
        identity = ("family", "format", "executionClass", "backend", "measurementMethod",
                    "iterations")
        require(all(all(r[f] == first[f] for f in identity) for r in rows),
                f"Cell identity or iteration count changed between trials: {cell}")
        times = []
        for r in rows:
            n, elapsed = int(r["iterations"]), int(r["totalNanos"])
            require(n > 0 and elapsed >= 50_000_000, f"Insufficient timed duration: {cell}")
            times.append(elapsed / n)
        if balanced_cell:
            require(len({r["blocks"] for r in rows}) == 1
                    and int(first["iterations"]) == 16 * int(first["blocks"]),
                    f"Incomplete balanced fixture block: {cell}")
            method, source = "result-dependent-complete-16-fixture-blocks", BALANCED_SOURCE
        else:
            method, source = "result-dependent-fixture-chain", MAIN_SOURCE
        require(first["measurementMethod"] == method, f"Unexpected measurement method: {cell}")
        selected.append({
            "series": SERIES_NAMES[cell[0]], "implementation": cell[0],
            "family": first["family"], "format": first["format"],
            "totalBits": str(cell[1]), "operation": cell[2],
            "executionClass": first["executionClass"], "backend": first["backend"],
            "measurementMethod": method, "iterations": first["iterations"],
            "blocks": first["blocks"] if balanced_cell else "", "trials": str(TRIALS),
            "medianNanosPerOp": f"{statistics.median(times):.9f}",
            "minimumNanosPerOp": f"{min(times):.9f}",
            "maximumNanosPerOp": f"{max(times):.9f}",
            "source": source,
        })
    return selected


def write_summary(rows: list[dict[str, str]]) -> bytes:
    stream = io.StringIO()
    writer = csv.DictWriter(stream, fieldnames=SUMMARY_FIELDS, lineterminator="\n")
    writer.writeheader()
    writer.writerows(rows)
    return stream.getvalue().encode()


def read_trials(archive: zipfile.ZipFile) -> tuple[list[list[dict[str, str]]], list[dict[str, str]]]:
    main = [read_csv(archive.read(f"main/raw/trial-{t:02d}.csv")) for t in range(1, TRIALS + 1)]
    return main, read_csv(archive.read(BALANCED_SOURCE))


def verify(results: Path) -> list[dict[str, str]]:
    archive_bytes = (results / "matched-comparison-evidence.zip").read_bytes()
    require(hashlib.sha256(archive_bytes).hexdigest() == ARCHIVE_SHA256,
            "Evidence archive SHA-256 differs")
    summary_bytes = (results / "matched-benchmark-summary.csv").read_bytes()
    with zipfile.ZipFile(io.BytesIO(archive_bytes)) as archive:
        names = archive.namelist()
        require(len(names) == len(set(names)), "Duplicate archive member")
        hashes = json.loads(archive.read("SHA256.json"))
        require(set(names) == set(hashes) | {"SHA256.json"}, "Archive inventory differs")
        for name, expected_hash in hashes.items():
            require(hashlib.sha256(archive.read(name)).hexdigest() == expected_hash,
                    f"Archive member hash differs: {name}")
        require(summary_bytes == archive.read("matched-benchmark-summary.csv"),
                "Selected CSV differs from archived CSV")
        main, balanced = read_trials(archive)
        for trial in main:
            check_prefixes(trial, 256)
        check_prefixes([row for trial in main for row in trial], 256)
        check_prefixes(balanced, 16)
        rows = select(main, balanced)
        require(write_summary(rows) == summary_bytes,
                "Summary differs from the nine-trial medians of the raw trials")
        values = [
            numerical_values(archive.read(f"numerical-audit/{lane}-values.txt"),
                             packed=lane == "floatlib")
            for lane in ("floatlib", "mpfr", "flocq")
        ]
        require(values[0] == values[1] == values[2], "Complete numerical values disagree")
    return rows


def plot(rows: list[dict[str, str]], output: Path) -> None:
    """Draw the six-panel overview at `output` and, beside it, one view per operation."""
    import sys

    sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "site" / "content" / "assets"
                           / "figures"))
    import figstyle
    import matplotlib.pyplot as plt
    from matplotlib.ticker import FixedLocator, FuncFormatter, NullLocator
    import format_comparison

    figstyle.setup()
    shared = getattr(figstyle, "SERIES", {})
    handles = {}
    decades = [10, 1e3, 1e5, 1e7, 1e9]

    def draw_panel(ax, operation):
        for impl, label, name, color, marker, line in SERIES:
            look = dict(color=color, marker=marker, linestyle=line)
            look.update(shared.get(name, {}))
            data = sorted((r for r in rows if r["implementation"] == impl
                           and r["operation"] == operation), key=lambda r: int(r["totalBits"]))
            handles[label], = ax.plot(
                [int(r["totalBits"]) for r in data],
                [float(r["medianNanosPerOp"]) for r in data], label=label, **look)
        ax.set_xscale("log", base=2)
        ax.set_yscale("log")
        ax.set_xlim(4.8, 5500)
        ax.set_ylim(3, 3e9)
        ax.xaxis.set_major_locator(FixedLocator([8, 32, 256, 4096]))
        ax.xaxis.set_major_formatter(FuncFormatter(lambda value, _: f"{int(value):,}"))
        ax.xaxis.set_minor_locator(NullLocator())
        ax.yaxis.set_major_locator(FixedLocator(decades))
        ax.yaxis.set_major_formatter(
            FuncFormatter(lambda value, _: f"$10^{{{round(math.log10(value))}}}$"))
        ax.yaxis.set_minor_locator(NullLocator())
        ax.grid(True, axis="y")
        ax.grid(False, axis="x")

    width_label, time_label = "format width (bits)", "time per operation (ns)"
    fig, axes = plt.subplots(2, 3, figsize=(figstyle.WIDTH, 5.6), sharex=True, sharey=True,
                             layout="constrained")
    for index, (ax, operation) in enumerate(zip(axes.flat, OPERATIONS)):
        draw_panel(ax, operation)
        if hasattr(figstyle, "panel_title"):
            figstyle.panel_title(ax, index, OPERATIONS[operation])
        else:
            ax.set_title(f"({chr(ord('a') + index)}) {OPERATIONS[operation]}", loc="left",
                         fontsize=plt.rcParams["axes.labelsize"])
    for ax in axes[-1]:
        ax.set_xlabel(width_label)
    fig.supylabel(time_label, fontsize=plt.rcParams["axes.labelsize"])
    fig.legend(list(handles.values()), list(handles), loc="outside lower center", ncol=3,
               frameon=False)
    output.parent.mkdir(parents=True, exist_ok=True)
    figstyle.save(fig, output.name, output)

    # One view per operation for narrow screens. The guide's `figstyle` lays it out and writes
    # the selector where it can; otherwise the layout of the format comparison does, with no
    # context line and no notes.
    descriptions = {}
    for operation, title in OPERATIONS.items():
        single, ax = plt.subplots()
        draw_panel(ax, operation)
        ax.set_xlabel(width_label)
        ax.set_ylabel(time_label)
        if hasattr(figstyle, "compact_view"):
            figstyle.compact_view(single, ax, title=title, handles=list(handles.values()),
                                  labels=list(handles))
            figstyle.save_view(single, output, operation)
        else:
            format_comparison.compact_operation_layout(
                single, ax, title=title, context="", handles=list(handles.values()),
                labels=list(handles), notes=())
            for text in single.texts:
                text.set_fontweight("normal")
            format_comparison.save_operation_svg(single, output, operation)
        descriptions[operation] = (
            f"{title.capitalize()}: time per operation against format width, both on "
            "logarithmic axes, with one line each for FloatLib, extracted Flocq and MPFR at "
            "eleven matching binary formats from 6 to 4,096 bits."
        )
    write = getattr(figstyle, "write_views", format_comparison.write_operation_series)
    write(
        output, descriptions,
        overview_alt="Six panels, one per arithmetic operation: time per operation against "
        "format width, both on logarithmic axes, with one line each for FloatLib, extracted "
        "Flocq and MPFR at eleven matching binary formats from 6 to 4,096 bits.",
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--results", type=Path, default=RESULTS)
    parser.add_argument("--out", type=Path, help="Write the figure after verification")
    args = parser.parse_args()
    rows = verify(args.results)
    print("Matched Flocq results verified: raw timing selection, agreement prefixes, complete values.")
    if args.out:
        plot(rows, args.out)
        print(f"Wrote {args.out}")


if __name__ == "__main__":
    main()
