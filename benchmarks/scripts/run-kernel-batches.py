#!/usr/bin/env python3
"""Measure sequential kernel cases in one Lean process, retaining its complete evidence.

No parallel workers are started. A successful process is copied, without truncation,
to each case record; collection validates every member of the declared batch.
Failed batches supply no accepted observations and fall back to individual attempts.
"""
import argparse
import datetime
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
LANE = ROOT.parent
MATRIX = ROOT / "benchmarks/results/standards-matrix"
MARKER = re.compile(
    r'^#print "MATRIX_KERNEL (\S+) (\S+) width=(\d+) case=(\d+)"\n', re.M)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checkout", type=Path, required=True)
    parser.add_argument("--seconds", type=int, default=530)
    parser.add_argument("--batch-size", type=int, default=12)
    parser.add_argument("--timeout", type=int, default=60)
    parser.add_argument("--individual-timeout", type=int, default=10)
    parser.add_argument("--max-width", type=int, default=128)
    args = parser.parse_args()
    checkout = args.checkout.resolve()
    revision = subprocess.check_output(
        ["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True).strip()
    if revision != "ea6f769efd739b01e16a04daec61123406a2d48f":
        raise ValueError("This continuation requires the frozen measured revision")
    if not 1 <= args.batch_size <= 12 or args.timeout < 1:
        raise ValueError("Invalid batch limits")
    module = importlib.util.spec_from_file_location(
        "collector", ROOT / "benchmarks/scripts/collect-standard-matrix.py")
    collector = importlib.util.module_from_spec(module)
    module.loader.exec_module(collector)
    digest = collector.digest
    begin = time.monotonic()
    environment = dict(os.environ, FLOATLIB_BUILD_DIR=str(checkout / ".lake/build"))
    for width in [8, 16, 32, 64, 128, 256, 1024, 4096]:
        if width > args.max_width:
            break
        for family in ["posit", "p3109"]:
            directory = MATRIX / family
            catalog_path = directory / "catalog.json"
            catalog = json.loads(catalog_path.read_text())
            source = (directory / f"Kernel{width}.lean").read_text()
            markers = list(MARKER.finditer(source))
            if len(markers) != len(catalog["cases"]):
                raise ValueError("Kernel source does not cover its catalog")
            header = source[:markers[0].start()]
            cases = {}
            for index, marker in enumerate(markers):
                f, label, w, i = marker.groups()
                if (f, label, int(w), int(i)) != (
                        catalog["family"], catalog["cases"][index]["label"], width, index):
                    raise ValueError("Kernel source identity disagrees with catalog")
                end = markers[index + 1].start() if index + 1 < len(markers) else len(source)
                cases[index] = source[marker.start():end]
            output = directory / "raw-ea6f769"
            output.mkdir(exist_ok=True)
            executable = checkout / ".lake/build/bin" / f"{family}Matrix"
            executable_hash = digest(executable)
            missing = [
                index for index in range(len(cases))
                if not any((raw / f"kernel-{width}-{index:03d}.json").exists()
                           for raw in directory.glob("raw*"))
            ]
            for start in range(0, len(missing), args.batch_size):
                indices = missing[start:start + args.batch_size]
                remaining = int(args.seconds - (time.monotonic() - begin))
                if remaining < args.timeout + 15:
                    print(json.dumps(dict(event="batch-budget", family=family,
                                          width=width, next_case=indices[0])), flush=True)
                    return
                evidence = LANE / "kernel-batches" / family
                evidence.mkdir(parents=True, exist_ok=True)
                stem = evidence / f"{width}-{indices[0]:03d}-{indices[-1]:03d}"
                process_record = stem.with_suffix(".json")
                # A previously failed whole batch is never repeatedly retried.
                previous = json.loads(process_record.read_text()) if process_record.exists() else None
                success = previous is not None and previous["exit"] == 0
                if previous is None:
                    source_path = stem.with_suffix(".lean")
                    source_path.write_text(header + "".join(cases[index] for index in indices))
                    command = [
                        "timeout", "--signal=TERM", "--kill-after=5", str(args.timeout),
                        "/usr/bin/time", "-v", "-o", str(stem.with_suffix(".time")),
                        "lake", "-d", "benchmarks", "env", "lean", str(source_path)]
                    timestamp = datetime.datetime.now(datetime.timezone.utc).isoformat()
                    process_begin = time.monotonic()
                    with stem.with_suffix(".log").open("w") as log:
                        result = subprocess.run(command, cwd=checkout, env=environment,
                                                stdout=log, stderr=subprocess.STDOUT)
                    previous = dict(
                        exit=result.returncode, command=command, timestamp=timestamp,
                        elapsed_seconds=time.monotonic() - process_begin,
                        kernel_input_sha256=digest(source_path),
                        log_sha256=digest(stem.with_suffix(".log")),
                        source_commit=revision, catalog_sha256=digest(catalog_path),
                        executable_sha256=executable_hash, cases=indices)
                    process_record.write_text(json.dumps(previous, indent=2) + "\n")
                    success = result.returncode == 0
                if (previous["cases"] != indices or previous["source_commit"] != revision
                        or previous["executable_sha256"] != executable_hash
                        or previous["catalog_sha256"] != digest(catalog_path)
                        or previous["log_sha256"] != digest(stem.with_suffix(".log"))
                        or previous["kernel_input_sha256"] != digest(stem.with_suffix(".lean"))):
                    raise ValueError("Retained batch provenance changed")
                if success:
                    text = stem.with_suffix(".log").read_text()
                    collector.validate_kernel_batch(text, catalog, width, indices)
                    for index in indices:
                        target = output / f"kernel-{width}-{index:03d}"
                        for suffix in [".lean", ".log", ".time"]:
                            shutil.copyfile(stem.with_suffix(suffix), target.with_suffix(suffix))
                        record = dict(
                            family=catalog["family"], label=catalog["cases"][index]["label"],
                            case=index, width=width, mode="kernel", source_commit=revision,
                            catalog_sha256=previous["catalog_sha256"],
                            executable_sha256=executable_hash,
                            kernel_input_sha256=previous["kernel_input_sha256"],
                            log_sha256=previous["log_sha256"], timestamp=previous["timestamp"],
                            timeout_seconds=args.timeout,
                            elapsed_seconds=previous["elapsed_seconds"], exit=0, status="pass",
                            command=previous["command"], kernel_input_kind="shared-batch",
                            kernel_batch_cases=indices,
                            process_scope="Complete sequential batch; wall time and RSS are shared. "
                                          "Only this case's tagged evaluation time is its latency.")
                        pending = target.with_suffix(".json.pending")
                        pending.write_text(json.dumps(record, indent=2) + "\n")
                        os.replace(pending, target.with_suffix(".json"))
                    print(json.dumps(dict(event="batch-pass", family=family, width=width,
                                          cases=indices, elapsed=previous["elapsed_seconds"])),
                          flush=True)
                else:
                    print(json.dumps(dict(event="batch-fallback", family=family, width=width,
                                          cases=indices, exit=previous["exit"])), flush=True)
                    for index in indices:
                        remaining = int(args.seconds - (time.monotonic() - begin))
                        if remaining < args.individual_timeout + 15:
                            return
                        command = [
                            sys.executable, str(checkout / "benchmarks/scripts/run-standard-matrix.py"),
                            "--catalog", str(catalog_path), "--mode", "kernel",
                            "--width", str(width), "--first", str(index), "--last", str(index + 1),
                            "--executable", str(executable), "--kernel-source",
                            str(directory / f"Kernel{width}.lean"), "--output", str(output),
                            "--budget-seconds", str(remaining), "--timeout",
                            str(args.individual_timeout), "--revision", revision]
                        subprocess.run(command, cwd=checkout, env=environment, check=True)
    print(json.dumps(dict(event="batch-campaign-complete", max_width=args.max_width)), flush=True)


if __name__ == "__main__":
    main()
