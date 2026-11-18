"""Select binary32 candidates from CORE-MATH's exhaustive validation input space.

This is an explicitly recorded numerical screen, not a proof of global hardness.
The selected bit patterns are JSON data; Runtime.lean reads them through its shared
case interface. A completed range is reusable only with identical source hashes.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "suites"))
from common import ROOT, digest, write_json
from corpus import OPERATIONS
from fetch import fetch
from process import run as monitored


def screen(output: Path, operation: str, start: int, end: int, keep: int, timeout: int):
    output.mkdir(parents=True, exist_ok=True)
    source = fetch(HERE / "core-math-source.json")
    sources = [HERE / "hard32.c", *(source / f"src/binary64/{op}/{op}.c"
                                  for op in OPERATIONS)]
    binary = output / "hard32"
    stamp = output / "hard32.stamp"
    command = ["gcc", "-O3", "-std=gnu11", "-frounding-math", "-fno-fast-math",
               *(str(path) for path in sources), "-lmpfr", "-lgmp", "-lm", "-o", str(binary)]
    signature = hashlib.sha256(
        ("\n".join(command) + "\n".join(digest(path) for path in sources)).encode()).hexdigest()
    if not binary.exists() or not stamp.exists() or stamp.read_text() != signature:
        usage = monitored(command, cwd=ROOT, log=output / "compile.log", timeout=180)
        write_json(output / "compile.json", {"command": command, **usage})
        if usage["exit_code"]:
            raise RuntimeError("Binary32 screen compilation failed; see compile.log")
        stamp.write_text(signature)
    identity = f"{operation}-{start:08x}-{end:x}-{keep}"
    raw, result = output / (identity + ".jsonl"), output / (identity + ".json")
    command = [str(binary), operation, str(start), str(end), str(keep)]
    signature = hashlib.sha256(
        ("\n".join(command) + digest(binary) + digest(Path(__file__))).encode()).hexdigest()
    if result.exists():
        cached = json.loads(result.read_text())
        if cached["signature"] == signature and cached["status"] == "completed":
            return cached
    usage = monitored(command, cwd=ROOT, log=raw, timeout=timeout)
    record = {
        "signature": signature, "command": command, "usage": usage,
        "core_math_revision": json.loads((HERE / "core-math-source.json").read_text())["revision"],
        "binary_sha256": digest(binary), "screen_sha256": digest(HERE / "hard32.c"),
        "status": "completed" if usage["exit_code"] == 0 else "incomplete",
        "scope": "Normal binary32 output magnitudes; ranking from binary64 CORE-MATH values",
        "claim": "Selected candidates, not a certified global hardest-case list",
        "verification": "Selected distances recomputed at MPFR 256 and 512 bits",
        "rows": [],
    }
    if usage["exit_code"] == 0:
        record["rows"] = [json.loads(line) for line in raw.read_text().splitlines()]
        coverage = record["rows"][0]
        if coverage["visited"] != end - start or coverage["selected"] != len(record["rows"]) - 1:
            raise ValueError("Screen output coverage does not match the requested range")
    write_json(result, record)
    print(operation, record["status"], usage, flush=True)
    return record


def cases(directory: Path):
    inventory, selected = [], []
    for path in sorted(directory.glob("*.json")):
        record = json.loads(path.read_text())
        if record.get("status") != "completed" or "rows" not in record:
            continue
        coverage, *candidates = record["rows"]
        inventory.append({
            "source": "CORE-MATH binary32 exhaustive input screen",
            "source_revision": record["core_math_revision"],
            "operation": coverage["operation"], "width": 32,
            "source_cases": coverage["visited"], "selected_cases": len(candidates),
            "status": "screened", "selection": record["claim"],
            "normal_outputs": coverage["normal_outputs"],
            "start_bits": coverage["start"], "end_bits_exclusive": coverage["end"],
            "screen_result_sha256": digest(path),
        })
        for candidate in candidates:
            selected.append({
                "id": f"core-screen:32:{candidate['operation']}:{candidate['bits']:08x}",
                "source": "CORE-MATH binary32 exhaustive input screen",
                "source_revision": record["core_math_revision"], "width": 32,
                "operation": candidate["operation"], "bits": candidate["bits"],
                "input_class": "derived midpoint-near candidate; normal output magnitude",
                "hardness_bits_256": candidate["hardness_bits_256"],
                "hardness_bits_512": candidate["hardness_bits_512"],
                "screen_result_sha256": digest(path),
            })
    # Overlapping explicitly requested ranges must not duplicate runtime observations.
    return inventory, list({row["id"]: row for row in selected}.values())


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("operation", choices=OPERATIONS)
    parser.add_argument("--start", type=lambda value: int(value, 0), default=0)
    parser.add_argument("--end", type=lambda value: int(value, 0), default=1 << 32)
    parser.add_argument("--keep", type=int, default=32)
    parser.add_argument("--timeout", type=int, default=450)
    args = parser.parse_args()
    screen(args.output.resolve(), args.operation, args.start, args.end, args.keep, args.timeout)
