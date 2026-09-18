#!/usr/bin/env python3
"""Verify the retained Flocq comparison and optionally regenerate its website figure.

The archive keeps the raw timings, complete numerical outputs, and captured sources
together. Verification reads it directly; no extraction, build, or timing run is needed.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
from pathlib import Path
import zipfile


RESULTS = Path(__file__).resolve().parents[1] / "results" / "flocq-matched"
ARCHIVE_SHA256 = "66d84170e28bb0c347a5d75de9c4e9f84c576db7a17163cb1db3904759da82e8"
EXPONENT_BITS = {
    6: 3, 8: 4, 16: 5, 32: 8, 64: 11, 128: 15,
    256: 19, 512: 19, 1024: 19, 2048: 19, 4096: 19,
}
OPERATIONS = {
    "add": "Addition", "sub": "Subtraction", "mul": "Multiplication",
    "div": "Division", "sqrt": "Square root", "fma": "Fused multiply-add",
}
SERIES = (
    ("ExecFloat", "FloatLib binary (proved)", "#2a78d6", "s", "-"),
    ("Flocq", "Extracted Flocq", "#60656f", "D", "--"),
    ("MPFR", "MPFR", "#eb6834", "^", ":"),
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
        main = read_csv(archive.read("main/trial-01.csv"))
        balanced = read_csv(archive.read("balanced-sqrt/raw.csv"))
        expected = {
            (impl, width, operation)
            for impl, *_ in SERIES for width in EXPONENT_BITS for operation in OPERATIONS
        }
        replacements = {(impl, width, "sqrt") for impl, *_ in SERIES
                        for width in (1024, 2048, 4096)}
        require(len(main) == len(expected) and {key(r) for r in main} == expected,
                "Incomplete or duplicate main matrix")
        require(len(balanced) == len(replacements)
                and {key(r) for r in balanced} == replacements,
                "Incomplete or duplicate balanced matrix")
        check_prefixes(main, 256)
        check_prefixes(balanced, 16)
        raw_by_key = {key(r): r for r in main}
        raw_by_key.update({key(r): r for r in balanced})
        rows = read_csv(summary_bytes)
        require(len(rows) == len(expected) and {key(r) for r in rows} == expected,
                "Incomplete or duplicate summary matrix")
        for row in rows:
            cell = key(row)
            raw = raw_by_key[cell]
            require(all(row[column] == value for column, value in raw.items()
                        if column != "trial"), f"Summary differs from raw cell: {cell}")
            require(int(row["trials"]) == 1, "Unexpected number of trials")
            n, elapsed = int(row["iterations"]), int(row["totalNanos"])
            require(n > 0 and elapsed >= 50_000_000, "Insufficient timed duration")
            require(row["nanosPerOp"] == f"{elapsed / n:.9f}", "Time per operation differs")
            if cell in replacements:
                require(int(raw["trial"]) == 1 and n == 16 * int(row["blocks"]),
                        "Incomplete balanced fixture block")
                method = "result-dependent-complete-16-fixture-blocks"
                source = "balanced-sqrt/raw.csv"
            else:
                require(row["blocks"] == "", "Unexpected fixture-block count")
                method = "result-dependent-fixture-chain"
                source = "main/trial-01.csv"
            require(row["measurementMethod"] == method and row["source"] == source,
                    "Incorrect source selection or measurement method")
        values = [
            numerical_values(archive.read(f"numerical-audit/{lane}-values.txt"),
                             packed=lane == "floatlib")
            for lane in ("floatlib", "mpfr", "flocq")
        ]
        require(values[0] == values[1] == values[2], "Complete numerical values disagree")
    return rows


def plot(rows: list[dict[str, str]], output: Path) -> None:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.ticker import FixedLocator, FuncFormatter, NullLocator

    plt.rcParams.update({
        "font.family": "DejaVu Sans", "font.size": 11,
        "text.color": "#172333", "axes.labelcolor": "#172333",
        "xtick.color": "#586474", "ytick.color": "#586474",
        "axes.spines.top": False, "axes.spines.right": False,
        "axes.edgecolor": "#b9c5d5",
    })
    fig, axes = plt.subplots(2, 3, figsize=(12.8, 6.2), sharex=True, sharey=True)
    handles = {}
    tick_labels = {10: "10 ns", 1e3: "1 µs", 1e5: "100 µs", 1e7: "10 ms", 1e9: "1 s"}
    for ax, (operation, title) in zip(axes.flat, OPERATIONS.items()):
        for impl, label, color, marker, style in SERIES:
            data = sorted((r for r in rows if r["implementation"] == impl
                           and r["operation"] == operation), key=lambda r: int(r["totalBits"]))
            line, = ax.plot(
                [int(r["totalBits"]) for r in data],
                [float(r["nanosPerOp"]) for r in data],
                color=color, marker=marker, linestyle=style,
                linewidth=2.1 if impl == "ExecFloat" else 1.7, markersize=4.5,
            )
            handles[label] = line
        ax.set_title(title, fontsize=13, loc="left", pad=6)
        ax.set_xscale("log", base=2)
        ax.set_yscale("log")
        ax.set_xlim(4.8, 5500)
        ax.set_ylim(3, 3e9)
        ax.xaxis.set_major_locator(FixedLocator([8, 32, 256, 4096]))
        ax.xaxis.set_major_formatter(FuncFormatter(lambda value, _: f"{int(value):,}"))
        ax.xaxis.set_minor_locator(NullLocator())
        ax.yaxis.set_major_locator(FixedLocator(list(tick_labels)))
        ax.yaxis.set_major_formatter(FuncFormatter(lambda value, _: tick_labels[value]))
        ax.yaxis.set_minor_locator(NullLocator())
        ax.grid(alpha=.22, linewidth=.7)
    fig.legend(list(handles.values()), list(handles), loc="upper center",
               bbox_to_anchor=(.55, .995), ncol=3, frameon=False, fontsize=12)
    fig.text(.009, .49, "Time per operation · lower is faster",
             rotation=90, ha="left", va="center", fontsize=12)
    fig.text(.55, .018, "Encoded width (bits) · logarithmic axes",
             ha="center", va="bottom", fontsize=12)
    fig.subplots_adjust(left=.09, right=.985, bottom=.115, top=.88, wspace=.13, hspace=.3)
    output.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output, dpi=180)
    plt.close(fig)


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
