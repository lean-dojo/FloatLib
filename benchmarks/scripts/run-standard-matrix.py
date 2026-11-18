#!/usr/bin/env python3
"""Run a sequential, resumable interval of the standard timing matrix.

Run this script through the campaign's resource-gated, memory-capped job wrapper.
Each case has its own timeout and retained source/output/time files. Only an
atomic outcome JSON marks a completed attempt; an interrupted parent leaves the
case eligible for retry. This script never starts a worker pool or a server.
"""
from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--catalog", type=Path, required=True)
    parser.add_argument("--mode", choices=["native", "kernel"], required=True)
    parser.add_argument("--width", type=int, required=True)
    parser.add_argument("--executable", type=Path)
    parser.add_argument("--kernel-source", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--first", type=int, default=0)
    parser.add_argument("--last", type=int)
    parser.add_argument("--timeout", type=int, default=30)
    parser.add_argument("--budget-seconds", type=int, default=490)
    parser.add_argument("--revision", required=True)
    args = parser.parse_args()
    if not re.fullmatch("[0-9a-f]{40}", args.revision):
        parser.error("--revision must be a full Git commit")
    revision = subprocess.check_output(
        ["git", "-C", str(ROOT), "rev-parse", "HEAD"], text=True).strip()
    if revision != args.revision:
        raise ValueError(f"requested revision {args.revision}, current HEAD {revision}")
    catalog = json.loads(args.catalog.read_text())
    if args.width not in catalog["widths"]:
        raise ValueError("width is absent from the catalog")
    last = len(catalog["cases"]) if args.last is None else args.last
    if not 0 <= args.first <= last <= len(catalog["cases"]):
        raise ValueError("invalid case interval")
    if args.timeout < 1 or args.budget_seconds < args.timeout + 10:
        raise ValueError("the case timeout must fit within the total time budget")
    if args.mode == "native" and not args.executable:
        parser.error("--native requires --executable")
    if args.mode == "kernel" and not args.kernel_source:
        parser.error("--kernel requires --kernel-source")
    args.output.mkdir(parents=True, exist_ok=True)
    kernel_header, kernel_cases = None, None
    if args.mode == "kernel":
        source = args.kernel_source.read_text()
        markers = list(re.finditer(
            r'^#print "MATRIX_KERNEL (\S+) (\S+) width=(\d+) case=(\d+)"\n', source, re.M))
        if len(markers) != len(catalog["cases"]):
            raise ValueError("kernel source does not cover the catalog exactly")
        kernel_header = source[:markers[0].start()]
        kernel_cases = {}
        for index, marker in enumerate(markers):
            family, label, width, number = marker.groups()
            if (family != catalog["family"] or int(width) != args.width or int(number) != index
                    or label != catalog["cases"][index]["label"]):
                raise ValueError("kernel marker differs from its catalog")
            end = markers[index + 1].start() if index + 1 < len(markers) else len(source)
            kernel_cases[index] = source[marker.start():end]
    executable_hash = digest(args.executable) if args.executable else None
    started = time.monotonic()
    counts = {"attempted": 0, "resumed": 0, "passed": 0, "failed": 0, "timeout": 0}
    for index in range(args.first, last):
        case = catalog["cases"][index]
        stem = args.output / f"{args.mode}-{args.width}-{index:03d}"
        record = stem.with_suffix(".json")
        if record.exists():
            previous = json.loads(record.read_text())
            if (previous["source_commit"] != revision or previous["label"] != case["label"]
                    or previous["catalog_sha256"] != digest(args.catalog)
                    or previous["executable_sha256"] != executable_hash):
                raise ValueError(f"resume provenance mismatch: {record}")
            counts["resumed"] += 1
            continue
        if time.monotonic() - started + args.timeout + 10 > args.budget_seconds:
            print(json.dumps(dict(event="budget", next_case=index, **counts)), flush=True)
            return
        if args.mode == "native":
            command = [str(args.executable.resolve()), str(args.width), str(index), str(index + 1)]
            input_hash = None
        else:
            fixture = stem.with_suffix(".lean")
            fixture.write_text(kernel_header + kernel_cases[index])
            input_hash = digest(fixture)
            command = ["lake", "-d", "benchmarks", "env", "lean", str(fixture.resolve())]
        command = ["timeout", "--signal=TERM", "--kill-after=5", str(args.timeout),
                   "/usr/bin/time", "-v", "-o", str(stem.with_suffix(".time").resolve()),
                   *command]
        timestamp = datetime.datetime.now(datetime.timezone.utc).isoformat()
        begin = time.monotonic()
        with stem.with_suffix(".log").open("w") as log:
            result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
        elapsed = time.monotonic() - begin
        status = "pass" if result.returncode == 0 else (
            "timeout" if result.returncode in [124, 137] else "failed")
        outcome = dict(
            family=catalog["family"], label=case["label"], case=index, width=args.width,
            mode=args.mode, source_commit=revision, catalog_sha256=digest(args.catalog),
            executable_sha256=executable_hash, kernel_input_sha256=input_hash,
            log_sha256=digest(stem.with_suffix(".log")), timestamp=timestamp,
            timeout_seconds=args.timeout, elapsed_seconds=elapsed, exit=result.returncode,
            status=status, command=command)
        temporary = record.with_suffix(".json.pending")
        temporary.write_text(json.dumps(outcome, indent=2) + "\n")
        os.replace(temporary, record)
        counts["attempted"] += 1
        counts["passed" if status == "pass" else status] += 1
        print(json.dumps(dict(event="case", case=index, label=case["label"],
                              width=args.width, mode=args.mode, status=status,
                              elapsed_seconds=round(elapsed, 3))), flush=True)
    print(json.dumps(dict(event="complete", **counts)), flush=True)


if __name__ == "__main__":
    main()
