#!/usr/bin/env python3
"""Join retained timing attempts, rejecting incomplete or inconsistent observations."""
from __future__ import annotations

import argparse
import csv
from decimal import Decimal
import hashlib
import json
from pathlib import Path
import re
import statistics
import sys

sys.set_int_max_str_digits(0)

NATIVE = re.compile(
    r"^MATRIX_NATIVE (\S+) (\S+) width=(\d+) trial=(\d+) count=(\d+) "
    r"elapsed=(\d+) ns=(\d+) sink=(\d+) value=(\d+)\n", re.M)


def parse_native(text, family, label, width):
    """Require all three complete trials and agreement of their observed outputs."""
    trials = {}
    if "error:" in text:
        raise ValueError("native error in nominally successful attempt")
    for match in NATIVE.finditer(text):
        f, name, w, trial, count, elapsed, nanos, sink, value = match.groups()
        if (f, name, int(w)) != (family, label, width):
            raise ValueError("native row identity differs from attempt")
        trial, count, elapsed, nanos = map(int, (trial, count, elapsed, nanos))
        if trial in trials or not count or elapsed // count != nanos:
            raise ValueError("duplicate trial or invalid elapsed/count normalization")
        trials[trial] = dict(count=count, elapsed_ns=elapsed, ns=nanos,
                             sink=int(sink), value=int(value))
    if set(trials) != {0, 1, 2}:
        raise ValueError("native attempt does not contain exactly three complete trials")
    for key in ["count", "sink", "value"]:
        if len({trial[key] for trial in trials.values()}) != 1:
            raise ValueError(f"native trials disagree on {key}")
    return dict(ns=int(statistics.median(t["ns"] for t in trials.values())),
                value=trials[0]["value"], trials=[trials[i] for i in range(3)])


KERNEL_MARKER = re.compile(
    r"^MATRIX_KERNEL (\S+) (\S+) width=(\d+) case=(\d+)\n", re.M)


def parse_kernel(text, family, label, width, index, *, shared_batch=False):
    """A time is admissible only with a complete newline-terminated kernel numeral."""
    marker = f"MATRIX_KERNEL {family} {label} width={width} case={index}\n"
    if text.count(marker) != 1 or "error:" in text:
        raise ValueError("kernel attempt has an error or lacks its unique identity marker")
    result = text.split(marker, 1)[1]
    if shared_batch:
        next_marker = KERNEL_MARKER.search(result)
        if next_marker:
            result = result[:next_marker.start()]
    elif len(KERNEL_MARKER.findall(text)) != 1:
        raise ValueError("undeclared kernel batch in an individual attempt")
    timing = re.findall(r"^with the tagged kernel rules: ([\d.]+) µs\n", result, re.M)
    value = re.findall(r"^value: (\d+)\n", result, re.M)
    if len(timing) != 1 or len(value) != 1:
        raise ValueError("kernel attempt lacks a complete tagged time and numeral")
    return dict(ns=int(Decimal(timing[0]) * 1000), value=int(value[0]))


def validate_kernel_batch(text, catalog, width, indices):
    """Accept all members only when the complete declared batch is present."""
    if not indices or len(indices) != len(set(indices)):
        raise ValueError("empty or duplicated kernel batch")
    if any(not isinstance(i, int) or not 0 <= i < len(catalog["cases"]) for i in indices):
        raise ValueError("unknown kernel batch member")
    expected = [(catalog["family"], catalog["cases"][i]["label"], str(width), str(i))
                for i in indices]
    if KERNEL_MARKER.findall(text) != expected:
        raise ValueError("kernel batch output differs from its declared members")
    return {
        i: parse_kernel(text, catalog["family"], catalog["cases"][i]["label"], width, i,
                        shared_batch=True)
        for i in indices
    }


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--catalog", type=Path, required=True)
    parser.add_argument("--raw", type=Path, action="append", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--allow-missing", action="store_true")
    args = parser.parse_args()
    catalog = json.loads(args.catalog.read_text())
    expected = {(width, index, mode) for width in catalog["widths"]
                for index in range(len(catalog["cases"])) for mode in ["native", "kernel"]}
    attempts = {}
    for directory in args.raw:
        for path in sorted(directory.glob("*.json")):
            attempt = json.loads(path.read_text())
            key = attempt["width"], attempt["case"], attempt["mode"]
            if key not in expected or key in attempts:
                raise ValueError(f"unknown or duplicate attempt: {key}")
            case = catalog["cases"][key[1]]
            if attempt["family"] != catalog["family"] or attempt["label"] != case["label"]:
                raise ValueError(f"wrong case identity: {path}")
            if attempt["catalog_sha256"] != digest(args.catalog):
                raise ValueError(f"catalog changed after measurement: {path}")
            log = path.with_suffix(".log")
            if digest(log) != attempt["log_sha256"]:
                raise ValueError(f"retained log changed: {path}")
            if key[2] == "kernel" and (
                    digest(path.with_suffix(".lean")) != attempt["kernel_input_sha256"]):
                raise ValueError(f"retained kernel source changed: {path}")
            if attempt["status"] == "pass":
                if attempt["exit"] != 0:
                    raise ValueError("successful status with unsuccessful process exit")
                text = log.read_text()
                if attempt.get("kernel_input_kind") == "shared-batch":
                    if key[2] != "kernel":
                        raise ValueError("batch metadata on a native attempt")
                    parsed = validate_kernel_batch(
                        text, catalog, key[0], attempt["kernel_batch_cases"])[key[1]]
                else:
                    parsed = parse_native(text, catalog["family"], case["label"], key[0]) if (
                        key[2] == "native") else parse_kernel(
                            text, catalog["family"], case["label"], key[0], key[1])
                attempt["observation"] = parsed
            elif attempt["exit"] == 0:
                raise ValueError("unsuccessful status with successful process exit")
            attempt["record"] = str(path)
            attempts[key] = attempt
    missing = expected - attempts.keys()
    if missing and not args.allow_missing:
        raise ValueError(f"{len(missing)} unattempted observations: {sorted(missing)[:8]}")
    rows = []
    for width in catalog["widths"]:
        for index, case in enumerate(catalog["cases"]):
            native, kernel = [attempts.get((width, index, mode)) for mode in ["native", "kernel"]]
            observations = [a.get("observation") if a else None for a in [native, kernel]]
            if all(observations) and observations[0]["value"] != observations[1]["value"]:
                raise ValueError(f"native and kernel results differ: {width}, {case['label']}")
            row = dict(operation=case["label"], declaration=case["declaration"], width=width,
                       case_metadata={key: value for key, value in case.items()
                                      if key not in {"label", "declaration", "inputs",
                                                     "fixture", "expression"}},
                       compiled_ns=observations[0]["ns"] if observations[0] else None,
                       kernel_tagged_ns=observations[1]["ns"] if observations[1] else None,
                       native_status=native["status"] if native else "unattempted",
                       kernel_status=kernel["status"] if kernel else "unattempted",
                       result_agreement=bool(all(observations)),
                       native=native, kernel=kernel)
            rows.append(row)
    report = dict(
        family=catalog["family"], catalog_sha256=digest(args.catalog),
        source_commits=sorted({a["source_commit"] for a in attempts.values()}),
        method=dict(
            compiled="Three trials over eight preconstructed inputs, with an adaptive 1–32 "
                     "passes per trial. Median nanoseconds per call includes full observation "
                     "and checksum accumulation. No overhead subtraction.",
            kernel="Only the proved tagged rewrite is timed; elaboration and rewriting are "
                   "outside the timer. One warm-up, median of 3–200 evaluations targeting "
                   "20 ms. Literal words for native seed zero, including carrier construction. "
                   "Declared shared batches run sequentially in one Lean process; each case "
                   "retains the complete successful process output and source. Wall time and "
                   "RSS belong to the whole batch, not to an individual operation.",
            validation="Both successful modes must produce the same complete-result checksum. "
                       "Every accepted timing has a complete retained output and successful exit."),
        limitations=[
            "These fixed-format, fixed-policy samples are not worst-case bounds.",
            "Native timings average eight samples; kernel timings use only seed zero.",
            "Observers force every output word but their checksums need not be injective.",
            "Only the tagged kernel path is measured; no unoptimized latency is inferred.",
            "A timed-out or failed attempt has no numerical timing; elapsed wall time is "
            "retained only as process evidence.",
        ] + catalog.get("limitations", [
            "Posits use standard es=2. P3109 uses signed extended descriptors with three "
            "exponent bits, nearest-even rounding, no saturation and three-element blocks.",
        ]),
        all_cases_attempted=not missing,
        all_results_measured=all(row["result_agreement"] for row in rows),
        rows=rows)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.with_suffix(".json").write_text(json.dumps(report, indent=2) + "\n")
    with args.output.with_suffix(".csv").open("w") as stream:
        writer = csv.DictWriter(stream, fieldnames=[
            "operation", "declaration", "width", "compiled_ns", "kernel_tagged_ns",
            "native_status", "kernel_status", "result_agreement"], extrasaction="ignore")
        writer.writeheader()
        writer.writerows(rows)
    print(json.dumps(dict(rows=len(rows), attempts=len(attempts), missing=len(missing),
                          complete_pairs=sum(row["result_agreement"] for row in rows))))


if __name__ == "__main__":
    main()
