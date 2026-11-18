#!/usr/bin/env python3
"""Summarize the native and kernel MX runs without including Lake build times."""
import argparse
import csv
import hashlib
import json
from pathlib import Path
import re
import statistics


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("log", type=Path)
    parser.add_argument("out", type=Path)
    args = parser.parse_args()
    text = args.log.read_text()
    commits = re.findall(r"(?m)^[0-9a-f]{40}$", text)
    if len(commits) != 1:
        raise ValueError("The log must identify exactly one source commit")
    native = re.findall(
        r"MX_FINITE (\w+) bits=(\d+) trial=(\d+) reference_ns=(\d+) "
        r"compiled_ns=(\d+) sink=(\d+)", text)
    if len(native) != 18:
        raise ValueError("Expected six profiles with three complete trials")
    grouped = {}
    for profile, bits, trial, slow, fast, sink in native:
        grouped.setdefault(profile, []).append({
            "bits": int(bits), "trial": int(trial), "reference_ns": int(slow),
            "compiled_ns": int(fast), "checksum": int(sink),
        })
    rows = []
    for profile, trials in grouped.items():
        if sorted(t["trial"] for t in trials) != [0, 1, 2]:
            raise ValueError(f"Missing or repeated trial: {profile}")
        if len({t["checksum"] for t in trials}) != 1:
            raise ValueError(f"Unstable checksum: {profile}")
        for path in ("reference", "compiled"):
            rows.append({
                "operation": "element-conversion", "profile": profile,
                "bits": trials[0]["bits"], "path": path,
                "median_ns": statistics.median(t[path + "_ns"] for t in trials),
                "input": "1024 precomputed signed rationals (i - 512) / 37",
            })
    kernel = re.findall(
        r"MX_KERNEL (\w+) (finite|block32 element)\n"
        r"with the tagged kernel rules: ([\d.]+) µs\nvalue: (\d+)", text)
    if len(kernel) != 7:
        raise ValueError("Expected six element kernel observations and one block observation")
    for profile, scope, cost, value in kernel:
        scalar = scope == "finite"
        rows.append({
            "operation": "element-conversion" if scalar else "vector-conversion-element",
            "profile": profile, "bits": grouped[profile][0]["bits"], "path": "kernel",
            "median_ns": round(float(cost) * 1000),
            "input": "7/3" if scalar else "32 rationals (i + 1) * 7/3; observe element 2",
            "value": int(value),
        })
    result = {
        "source_commit": commits[0], "standard": "OCP MX v1.0, §§5.3 and 6.3",
        "lean": "4.35.0", "log_sha256": hashlib.sha256(args.log.read_bytes()).hexdigest(),
        "method": {
            "compiled": "Native Lean; 3 trials, 2*1024 reference and 32*1024 bisection calls "
                        "per trial. Inputs prepared before timing; every output checksummed. "
                        "Every distinct input is also compared before timing.",
            "kernel": "Lean proof kernel with registered equality rewrites. Median of warm "
                      "evaluations, at least 3 and at most 200 over approximately 20 ms. "
                      "Includes exact input construction; excludes rewriting/elaboration.",
        },
        "limitations": [
            "These are finite SAT conversion rows, not an entire MX operation matrix.",
            "The block row observes one stored element; it is not complete-vector throughput.",
            "Kernel and compiled rows use different input preparation and cannot be compared "
            "as if they timed the same harness.",
            "The measured kernel paths do not meet the 100000 ns target.",
        ],
        "native_trials": grouped, "rows": rows,
    }
    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / "mx.json").write_text(json.dumps(result, indent=2) + "\n")
    fields = ["source_commit", "standard", "operation", "profile", "bits", "path",
              "median_ns", "input", "value"]
    with (args.out / "mx.csv").open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=fields)
        writer.writeheader()
        for row in rows:
            writer.writerow({"source_commit": commits[0], "standard": result["standard"], **row})
    print(f"{len(rows)} benchmark rows recorded at {commits[0]}")


if __name__ == "__main__":
    main()
