#!/usr/bin/env python3
"""Collect complete native/kernel N1169 timing logs, rejecting partial evaluations."""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
import statistics
from decimal import Decimal
from pathlib import Path

NATIVE = re.compile(
    r"^FIXED_NATIVE (.+) width=(\d+) trial=(\d+) ns=(\d+) sink=(\d+)"
    r"(?: value=(\d+))?$", re.M)
KERNEL = re.compile(r"^FIXED_KERNEL (.+) width=(\d+)( tagged_only=true)?$", re.M)


def kernel_rows(path: Path, allow_incomplete_tail: bool = False) -> tuple[dict, list]:
    text = path.read_text()
    if re.search(r"(?:^|\n).*error:", text):
        raise ValueError(f"Lean error in {path}")
    markers = list(KERNEL.finditer(text))
    if not markers:
        raise ValueError(f"no kernel observations in {path}")
    rows = {}
    omitted = []
    for index, marker in enumerate(markers):
        end = markers[index + 1].start() if index + 1 < len(markers) else len(text)
        block = text[marker.end():end]
        written = re.search(r"as written: ([\d.]+) µs", block)
        rewritten = re.search(r"with the tagged kernel rules: ([\d.]+) µs", block)
        # A truncated numeral is not a normalized result, even when it contains digits.
        value = re.search(r"^value: (\d+)\n", block, re.M)
        key = marker.group(1), int(marker.group(2))
        tagged_only = marker.group(3) is not None
        if tagged_only and (not key[0].startswith("countls") or key[1] < 1024):
            raise ValueError(f"unexpected omitted baseline: {key}")
        if not value or (tagged_only and (written or not rewritten)) or (
                not tagged_only and not written):
            if allow_incomplete_tail and index == len(markers) - 1:
                omitted.append(dict(operation=key[0], width=key[1]))
                continue
            raise ValueError(f"incomplete kernel normalization: {marker.group(0)} in {path}")
        if not rewritten and "no tagged kernel rule applies" not in block:
            raise ValueError(f"missing rewrite outcome: {marker.group(0)} in {path}")
        if key in rows:
            raise ValueError(f"duplicate kernel row {key}")
        rows[key] = dict(
            kernel_written_ns=None if written is None else int(Decimal(written.group(1)) * 1000),
            kernel_tagged_ns=int(Decimal((rewritten or written).group(1)) * 1000),
            kernel_changed=rewritten is not None,
            kernel_value=int(value.group(1)))
    return rows, omitted


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--catalog", type=Path, required=True)
    parser.add_argument("--native", type=Path, required=True)
    parser.add_argument("--kernel", type=Path, action="append", required=True)
    parser.add_argument("--partial-kernel", type=Path, action="append", default=[])
    parser.add_argument("--revision", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if not re.fullmatch("[0-9a-f]{40}", args.revision):
        parser.error("--revision must be a complete Git commit identifier")
    catalog = json.loads(args.catalog.read_text())
    expected = {(case["label"], width): case for width in catalog["widths"]
                for case in catalog["cases"] if width >= case["minimum"]}
    native = {}
    for match in NATIVE.finditer(args.native.read_text()):
        label, width, trial, nanos, sink, value = match.groups()
        key = label, int(width)
        trials = native.setdefault(key, {})
        if int(trial) in trials:
            raise ValueError(f"duplicate native trial {key}: {trial}")
        trials[int(trial)] = dict(ns=int(nanos), sink=int(sink),
                                  value=None if value is None else int(value))
    kernels = {}
    interrupted = {}
    for path in [*args.kernel, *args.partial_kernel]:
        rows, omitted = kernel_rows(path, path in args.partial_kernel)
        if path in args.partial_kernel:
            interrupted[path.name] = dict(
                accepted_complete_rows=len(rows), omitted_incomplete_tail=omitted,
                reason="Whole-file job timeout; only complete newline-terminated results accepted.")
        overlap = kernels.keys() & rows.keys()
        if overlap:
            raise ValueError(f"duplicate kernel observations: {overlap}")
        kernels.update(rows)
    for name, data in [("native", native), ("kernel", kernels)]:
        missing, extra = expected.keys() - data.keys(), data.keys() - expected.keys()
        if missing or extra:
            raise ValueError(f"{name}: {len(missing)} missing, {len(extra)} extra; "
                             f"examples {list(missing)[:4]}, {list(extra)[:4]}")
    output = []
    for key, case in expected.items():
        trials = native[key]
        if set(trials) != {0, 1, 2} or len({t["sink"] for t in trials.values()}) != 1:
            raise ValueError(f"incomplete trials or inconsistent checksums: {key}")
        values = {t["value"] for t in trials.values()}
        if values != {kernels[key]["kernel_value"]}:
            raise ValueError(f"native/kernel input or result mismatch: {key}: {values}")
        label, width = key
        output.append(dict(
            operation=label,
            declaration=case["declaration"] if not label.startswith("input-") else None,
            width=width,
            ctype=case["type"],
            conforms_to_layout_minima=width >= 48,
            compiled_ns=int(statistics.median(t["ns"] for t in trials.values())),
            **kernels[key],
            native_trials=[trials[index] for index in range(3)]))
    logs = [args.native, *args.kernel, *args.partial_kernel, args.catalog]
    report = dict(
        source_commit=args.revision,
        standard="WG14 N1169, ISO/IEC TR 18037:2006(E), §§4.1–4.2",
        lean="4.35.0",
        input_sha256={path.name: hashlib.sha256(path.read_bytes()).hexdigest()
                      for path in logs},
        harness_sha256={
            path.name: hashlib.sha256(path.read_bytes()).hexdigest()
            for path in [
                Path(__file__),
                Path(__file__).with_name("fixed-point-matrix.py"),
                Path(__file__).parent.parent /
                "lean/FloatLibBenchmarks/Standards/FixedPoint.lean",
            ]},
        interrupted_kernel_logs=interrupted,
        method=dict(
            compiled="Native Lean, three trials of 4 × 32 preconstructed code inputs. "
                     "Median per-call time, including observation and checksum accumulation.",
            kernel="Lean kernel, stored literal coefficients with kernel-checked range proofs. "
                   "Median of 3–200 warm evaluations over about 20 ms for seed 1, including "
                   "result observation; rewriting and elaboration are outside the timer.",
            common="Every output is observed. Native seed-1 observations must equal the kernel "
                   "numerals. No baseline subtraction. Nearest-even, saturation, ordinary "
                   "full-precision arithmetic; shift count 2, fixed integer operands and text."),
        limitations=[
            "These are operation/layout samples, not worst-case or distributional bounds.",
            "Both modes start from stored inputs, but native trials average 32 samples and the "
            "kernel measures seed 1. Their timings are not matched single-input latency.",
            "8-, 16- and 32-bit whole layouts are extensions below C's mandatory minima; "
            "epsilon macros require a valid whole layout and are omitted at those widths.",
            "The input controls are harness measurements, not standard operations.",
            "Constant.parse and Constant.translate are measured separately; the latter uses "
            "an already parsed literal. Formatted conversions measure one resolved numeric "
            "field, not whole C streams. Observations are checksums, not injective encodings.",
            "At 1024 and 4096 bits, countlsfx measures only the tagged logarithm path. "
            "The unoptimized linear-search baseline is omitted and represented by null. "
            "Wide kernel files raise maxRecDepth to 32768 and exponentiation.threshold to 8192.",
        ],
        rows=output)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.with_suffix(".json").write_text(json.dumps(report, indent=2) + "\n")
    with args.output.with_suffix(".csv").open("w") as stream:
        columns = ["operation", "declaration", "width", "conforms_to_layout_minima",
                   "compiled_ns", "kernel_written_ns", "kernel_tagged_ns", "kernel_changed"]
        writer = csv.DictWriter(stream, fieldnames=columns, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(output)
    print(json.dumps(dict(
        rows=len(output),
        compiled_target_pass=sum(row["compiled_ns"] <= 100000 for row in output),
        kernel_target_pass=sum(row["kernel_tagged_ns"] <= 100000 for row in output)),
        indent=2))


if __name__ == "__main__":
    main()
