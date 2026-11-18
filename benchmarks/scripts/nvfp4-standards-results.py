#!/usr/bin/env python3
"""Record exact-policy NVFP4 timings; native inputs are materialized before reads."""
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
        raise ValueError("Expected exactly one source commit")
    observations = re.findall(
        r"NVFP4 (\w+) n=(\d+) trial=(\d+) ns=(\d+) sink=(\d+)", text)
    if len(observations) != 24:
        raise ValueError("Expected four operations, two tensor sizes, three trials")
    groups = {}
    for op, n, trial, elapsed, sink in observations:
        groups.setdefault((op, int(n)), []).append({
            "trial": int(trial), "ns": int(elapsed), "checksum": int(sink)})
    rows = []
    for (op, n), trials in groups.items():
        if sorted(t["trial"] for t in trials) != [0, 1, 2]:
            raise ValueError(f"Incomplete trials: {op}, {n}")
        if len({t["checksum"] for t in trials}) != 1:
            raise ValueError(f"Unstable checksum: {op}, {n}")
        rows.append({
            "operation": op, "elements": n, "path": "compiled",
            "median_ns": statistics.median(t["ns"] for t in trials),
            "observation": "all stored codes" if op == "quantize" else
                           "all decoded values" if op == "decode" else "binary32 word",
            "trials": trials,
        })
    kernel = re.findall(
        r"NVFP4_KERNEL ([\w-]+) n=(\d+)\n"
        r"with the tagged kernel rules: ([\d.]+) µs\nvalue: (\d+)", text)
    if len(kernel) != 5:
        raise ValueError("Expected five kernel observations")
    for op, n, elapsed, value in kernel:
        rows.append({
            "operation": op, "elements": int(n), "path": "kernel",
            "median_ns": round(float(elapsed) * 1000),
            "observation": "binary32 word" if op.startswith("Dot") else "one code/value",
            "value": int(value),
        })
    result = {
        "source_commit": commits[0], "reference": "NVIDIA arXiv:2509.25149v2, Appendix B",
        "lean": "4.35.0", "log_sha256": hashlib.sha256(args.log.read_bytes()).hexdigest(),
        "method": {
            "compiled": "Native Lean, 3 trials with 4 repetitions of 16 inputs each. "
                        "Exact rational policy with supplied outer scale one; inputs "
                        "(i - n/2 + j)/7. All outputs checksummed. Decode and dot inputs "
                        "are materialized arrays of stored codes before timing.",
            "kernel": "Lean kernel with registered equality rewrites; warm median, at least "
                      "3 and at most 200 samples over approximately 20 ms. Quantization "
                      "includes input construction and observes one code. Decode/dot "
                      "use literal stored codes. Rewriting and elaboration excluded.",
        },
        "limitations": [
            "Vendor description, not a standard; exact-policy model, not GPU performance.",
            "The compiled and kernel workloads differ and are not directly comparable.",
            "Only 16- and 64-element tensors; the complete operation/size matrix is open.",
            "Pre-materialization exploratory decode/dot rows are invalid as stored-read timings.",
        ],
        "rows": rows,
    }
    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / "nvfp4.json").write_text(json.dumps(result, indent=2) + "\n")
    fields = ["source_commit", "reference", "operation", "elements", "path",
              "median_ns", "observation"]
    with (args.out / "nvfp4.csv").open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=fields, extrasaction="ignore")
        writer.writeheader()
        for row in rows:
            writer.writerow({"source_commit": commits[0], "reference": result["reference"], **row})
    print(f"{len(rows)} benchmark rows recorded at {commits[0]}")


if __name__ == "__main__":
    main()
