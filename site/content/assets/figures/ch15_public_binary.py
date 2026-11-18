#!/usr/bin/env python3
"""Plot retained ordinary public Binary timings; never run arithmetic benchmarks.

Sources: benchmarks/results/public-binary/{measurements.csv,metadata.json} and
the selected fixture/check archive identified by metadata.json. Checks cover file
hashes, the complete measurement matrix, pairing, timing arithmetic, input hashes,
retained full-encoding receipts, and warmup checksums. The campaign checked the full
timed checksums; this script does not repeat millions of checksum iterations.

Run from anywhere:
    python3 ch15_public_binary.py [--results DIR] [--out PNG] [--low-out PNG]
                                 [--summary JSON]
    python3 ch15_public_binary.py --check-only

The schema and metadata supply the campaign identity and trial count. Replacing the
retained data does not require changing plotting constants or benchmark numbers.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
import csv
import hashlib
import io
import itertools
import json
import math
from pathlib import Path
import statistics
import sys
import zipfile

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as fs  # noqa: E402


RESULTS = fs.REPO / "benchmarks/results/public-binary"
OPERATIONS = ("add", "sub", "mul", "div", "sqrt", "fma")
ARMS = ("binary", "mpfr")
OUT_NAME = "public-binary-performance.png"
LOW_OUT_NAME = "public-binary-low-precision.png"
MASK = (1 << 64) - 1
SEED = 14695981039346656037


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def stats(values):
    return {
        "median": statistics.median(values),
        "minimum": min(values),
        "maximum": max(values),
    }


def warmup_sink(outputs, count):
    sink = SEED
    for i in range(count - 1, -1, -1):
        sink = ((sink ^ (int(outputs[i & 15]) & MASK)) * 1099511628211) & MASK
    return str(sink)


def load(results):
    metadata = json.loads((results / "metadata.json").read_text())
    require(metadata["schema"] == "floatlib-public-binary-v3", "Unknown data schema")
    raw = (results / metadata["measurements"]["file"]).read_bytes()
    require(sha256(raw) == metadata["measurements"]["sha256"], "CSV hash mismatch")
    rows = list(csv.DictReader(io.StringIO(raw.decode())))
    formats = {f["name"]: f for f in metadata["formats"]}
    require(len(formats) == len(metadata["formats"]), "Duplicate format")
    require(formats, "Empty format matrix")
    wide_widths = [f["width"] for f in formats.values() if f["width"] >= 32]
    require(wide_widths and len(set(wide_widths)) == len(wide_widths),
            "Wide-format plot needs distinct encoded widths")
    require(any(f["width"] < 32 for f in formats.values()), "Missing low-precision formats")
    require(set(metadata["measurements"]["arms"]) == set(ARMS), "Unexpected arms")
    for f in formats.values():
        require(f["width"] == 1 + f["e"] + f["f"] and f["precision"] == f["f"] + 1,
                f"Invalid format layout: {f['name']}")
    trials = metadata["protocol"]["trials"]
    require(isinstance(trials, int) and trials > 0, "Invalid trial count")
    require(len(rows) == metadata["measurements"]["rows"] ==
            len(formats) * len(OPERATIONS) * len(ARMS) * trials, "Incomplete CSV")

    evidence = metadata["fixture_archive"]
    archive_bytes = (results / evidence["file"]).read_bytes()
    require(len(archive_bytes) == evidence["bytes"] and
            sha256(archive_bytes) == evidence["sha256"], "Fixture archive hash mismatch")
    with zipfile.ZipFile(io.BytesIO(archive_bytes)) as archive:
        require(len(archive.namelist()) == len(set(archive.namelist())), "Duplicate archive member")
        manifest = json.loads(archive.read("sha256.json"))
        require(set(archive.namelist()) == set(manifest) | {"sha256.json"},
                "Archive contains unaccounted files")
        for name, digest in manifest.items():
            require(sha256(archive.read(name)) == digest, f"Fixture hash mismatch: {name}")
        cases = json.loads(archive.read("cases.json"))
        checks = json.loads(archive.read("validation.json"))
        by_case = {}
        for case in cases:
            key = (case["format"], case["operation"])
            require(key not in by_case and case["input_class"] == "ordinary",
                    f"Duplicate or nonordinary fixture: {key}")
            require(len(case["expected"]) == metadata["protocol"]["input_count"] == 16,
                    f"Wrong fixture count: {key}")
            data = archive.read("inputs/" + case["input"])
            require(sha256(data) == case["input_sha256"], f"Input identity mismatch: {key}")
            triples = [line.split() for line in data.decode().splitlines() if line.strip()]
            width = formats[key[0]]["width"]
            require(len(triples) == 16 and all(
                len(t) == 3 and all(0 <= int(x) < (1 << width) for x in t) for t in triples),
                f"Invalid input encodings: {key}")
            require(all(0 <= int(x) < (1 << width) for x in case["expected"]),
                    f"Invalid expected encodings: {key}")
            by_case[key] = case
    wanted_cases = set(itertools.product(formats, OPERATIONS))
    require(set(by_case) == wanted_cases, "Incomplete fixture matrix")
    metadata_cases = {(c["format"], c["operation"]): c for c in metadata["cases"]}
    require(len(metadata_cases) == len(metadata["cases"]) and set(metadata_cases) == wanted_cases,
            "Incomplete metadata fixture matrix")
    for key, case in metadata_cases.items():
        require(all(by_case[key][field] == case[field] for field in case),
                f"Metadata and archived fixture disagree: {key}")
    check_index = {(c["format"], c["operation"]): c for c in checks}
    require(len(check_index) == len(checks) and set(check_index) == wanted_cases,
            "Incomplete full-encoding check matrix")
    for key, check in check_index.items():
        require(check["status"] == check["agreement"] == "pass" and
                set(check["arms"]) == set(ARMS) and
                check["input_sha256"] == by_case[key]["input_sha256"],
                f"Failed or mismatched full-encoding receipt: {key}")
        require(all(a["status"] == "pass" and a["count"] == 16 for a in check["arms"].values()),
                f"Failed full-encoding arm: {key}")
        require(all(a["values"] == by_case[key]["expected"] for a in check["arms"].values()),
                f"Full result encodings disagree with the oracle: {key}")

    index = {}
    per_arm = defaultdict(list)
    sink_index = {}
    for row in rows:
        key = (row["format"], row["operation"], row["arm"], int(row["trial"]))
        require(key not in index, f"Duplicate measurement: {key}")
        require(row["input_class"] == "ordinary" and row["output_check"] == "pass",
                f"Unverified or wrong workload: {key}")
        f = formats[row["format"]]
        require((int(row["width"]), int(row["precision"]), int(row["exponent_bits"])) ==
                (f["width"], f["precision"], f["e"]), f"Format mismatch: {key}")
        count, nanos, warmup = (int(row[k]) for k in ("iterations", "nanoseconds", "warmup"))
        require(count > 0 and count % 16 == 0 and nanos > 0 and 0 < warmup <= 512,
                f"Invalid timing counts: {key}")
        value = float(row["ns_per_operation"])
        require(math.isfinite(value) and math.isclose(value, nanos / count, rel_tol=1e-12),
                f"Timing arithmetic mismatch: {key}")
        expected_warmup = warmup_sink(by_case[key[:2]]["expected"], warmup)
        require(row["warmup_sink"] == expected_warmup, f"Warmup checksum mismatch: {key}")
        require(0 <= int(row["sink"]) <= MASK, f"Invalid result checksum: {key}")
        sink_key = (*key[:2], count, row["warmup_sink"])
        require(sink_index.setdefault(sink_key, row["sink"]) == row["sink"],
                f"Inconsistent result checksum: {key}")
        require(check_index[key[:2]]["arms"][row["arm"]]["backend"] == row["backend"],
                f"Backend mismatch between validation and timing: {key}")
        index[key] = row
        per_arm[key[:3]].append(row)
    wanted = set(itertools.product(formats, OPERATIONS, ARMS, range(1, trials + 1)))
    require(set(index) == wanted, "Incomplete trial/operation/arm matrix")
    require(metadata["validation"]["finite_status"] == "pass" and
            metadata["validation"]["finite_cases"] == len(wanted_cases) and
            metadata["validation"]["timing_trials"] == len(rows),
            "Validation summary disagrees with measurements")
    require(sum(int(r["throttled_us"]) for r in rows) ==
            metadata["protocol"]["quota_throttled_us"], "Throttling summary mismatch")
    for key, group in per_arm.items():
        require(len({(r["iterations"], r["warmup"]) for r in group}) == 1,
                f"Counts changed after calibration: {key}")
    environments = {(e["format"], e["operation"]): e for e in metadata["environment"]}
    require(len(environments) == len(metadata["environment"]) and
            set(environments) == wanted_cases, "Incomplete execution environment matrix")
    for name, operation, trial in itertools.product(formats, OPERATIONS, range(1, trials + 1)):
        group = [index[(name, operation, arm, trial)] for arm in ARMS]
        require(len({(r["node"], r["cpu"]) for r in group}) == 1,
                f"Arms did not share a CPU: {(name, operation, trial)}")
        env = environments[(name, operation)]
        require(group[0]["node"] == env["node"] and int(group[0]["cpu"]) == env["cpu"]
                and env["affinity"] == [env["cpu"]],
                f"Affinity mismatch: {name} {operation}")
        delta = int(group[0]["order"]) - int(group[1]["order"])
        require({int(r["order"]) for r in group} == {0, 1},
                f"Invalid execution order: {name} {operation}")
        if trial > 1:
            previous = [index[(name, operation, arm, trial - 1)] for arm in ARMS[:2]]
            prior_delta = int(previous[0]["order"]) - int(previous[1]["order"])
            require(delta == -prior_delta, f"Order did not reverse: {name} {operation}")

    cells = []
    for f in sorted(formats.values(), key=lambda f: f["width"]):
        for operation in OPERATIONS:
            values = {
                arm: [float(index[(f["name"], operation, arm, t)]["ns_per_operation"])
                      for t in range(1, trials + 1)]
                for arm in ARMS
            }
            gap = [c / m for c, m in zip(values[ARMS[0]], values[ARMS[1]])]
            cells.append({
                "format": f["name"], "width": f["width"], "operation": operation,
                "ns_per_operation": {a: stats(v) for a, v in values.items()},
                "current_over_mpfr": {**stats(gap), "trials": gap},
            })
    summary = {
        "campaign": metadata["campaign"], "trials": trials,
        "cells": cells,
    }
    return metadata, summary


def plot(metadata, summary, out, *, low_precision=False):
    """Six panels, one per operation, and the same panels again as single views for phones."""
    fs.setup()
    fig, axes = fs.figure(5.7, nrows=2, ncols=3, sharex=True, sharey=True)
    fig.subplots_adjust(left=0.10, right=0.99, top=0.94, bottom=0.26 if low_precision else 0.23,
                        hspace=0.28, wspace=0.10)
    formats = sorted(
        (f for f in metadata["formats"] if (f["width"] < 32) == low_precision),
        key=lambda f: (f["width"], f["e"], f["f"]),
    )
    positions = list(range(len(formats))) if low_precision else [f["width"] for f in formats]
    cells = {(c["format"], c["operation"]): c for c in summary["cells"]}
    arms = ((ARMS[0], "FloatLib"), (ARMS[1], "MPFR"))
    xlabel = "format" if low_precision else "encoded width (bits)"
    ylabel = "time per operation (ns)"

    def draw_panel(ax, operation):
        for arm_index, (arm, name) in enumerate(arms):
            values = [cells[(f["name"], operation)]["ns_per_operation"][arm] for f in formats]
            centers = [v["median"] for v in values]
            x = ([p + (arm_index - 0.5) * 0.22 for p in positions]
                 if low_precision else positions)
            style = fs.series(name, markersize=4.5)
            if low_precision:
                style["linestyle"] = "none"
            ax.errorbar(x, centers,
                        yerr=[[v["median"] - v["minimum"] for v in values],
                              [v["maximum"] - v["median"] for v in values]],
                        capsize=2, elinewidth=fs.LW_AXIS, **style)
        ax.set_yscale("log")
        if low_precision:
            labels = [
                f["name"] if f["name"] in ("binary16", "bfloat16") else f"E{f['e']}M{f['f']}"
                for f in formats
            ]
            ax.set_xticks(positions, labels=labels, rotation=45, ha="right",
                          rotation_mode="anchor")
        else:
            ax.set_xscale("log", base=2)
            ax.set_xticks(positions, labels=[f"{w:,}" for w in positions], rotation=45)
        ax.tick_params(axis="x", labelsize=fs.SIZE_SMALL)
        ax.minorticks_off()

    for index, (ax, operation) in enumerate(zip(axes.flat, OPERATIONS)):
        draw_panel(ax, operation)
        fs.panel_title(ax, index, fs.OPERATION_LABEL[operation])
    handles, labels = axes[0, 0].get_legend_handles_labels()
    fs.legend(fig, handles, labels, loc="lower center", bbox_to_anchor=(0.54, 0.0), ncols=2)
    fig.supylabel(ylabel, x=0.012, fontsize=fs.SIZE_LABEL)
    fig.supxlabel(xlabel, x=0.54, y=0.075, fontsize=fs.SIZE_LABEL)
    limits = {op: (ax.get_xlim(), ax.get_ylim()) for op, ax in zip(OPERATIONS, axes.flat)}
    target = fs.save(fig, LOW_OUT_NAME if low_precision else OUT_NAME, out=out)

    descriptions = {}
    for operation in OPERATIONS:
        single, ax = fs.plt.subplots()
        draw_panel(ax, operation)
        ax.set_xlim(limits[operation][0])
        ax.set_ylim(limits[operation][1])
        ax.set_ylabel(ylabel)
        ax.set_xlabel(xlabel)
        if not low_precision:
            for text in ax.get_xticklabels():
                text.set_rotation(0)
            fs.stagger_labels(ax)
        handles, labels = ax.get_legend_handles_labels()
        fs.compact_view(single, ax, title=fs.OPERATION_LABEL[operation], handles=handles,
                        labels=labels)
        fs.save_view(single, target, operation)
        horizontal = ("six formats below 32 bits" if low_precision
                      else "encoded width on a logarithmic axis")
        name = fs.OPERATION_LABEL[operation]
        descriptions[operation] = (
            f"{name[0].upper()}{name[1:]}: FloatLib and MPFR time per operation in nanoseconds "
            f"on a logarithmic vertical axis, against {horizontal}. Markers are medians and "
            "whiskers run from the fastest to the slowest trial."
        )
    fs.write_views(
        target, descriptions,
        overview_alt="Six panels, one per operation: FloatLib and MPFR time per operation in "
        f"nanoseconds, {'for six formats below 32 bits' if low_precision else 'against encoded width'}, "
        "with whiskers from the fastest to the slowest trial. "
        + ("The vertical axes are logarithmic." if low_precision else "Both axes are logarithmic."),
    )
    return target


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--results", type=Path, default=RESULTS)
    parser.add_argument("--out", type=Path)
    parser.add_argument("--low-out", type=Path)
    parser.add_argument("--summary", type=Path)
    parser.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    metadata, summary = load(args.results)
    if args.summary:
        args.summary.write_text(json.dumps(summary, indent=2) + "\n")
    print(f"verified {metadata['measurements']['rows']} rows, "
          f"{len(summary['cells'])} cases")
    if not args.check_only:
        print(f"wrote {plot(metadata, summary, args.out)}")
        low_out = args.low_out or (args.out.with_name(LOW_OUT_NAME) if args.out else None)
        print(f"wrote {plot(metadata, summary, low_out, low_precision=True)}")


if __name__ == "__main__":
    main()
