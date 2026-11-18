"""Exact source coordinates and deterministic samples from published worst-case files."""
from __future__ import annotations
import hashlib
import heapq
import json
import math
import struct
from fractions import Fraction
from pathlib import Path
from sexpr import number

OPERATIONS = ("exp", "log", "expm1", "log1p")
HERE = Path(__file__).resolve().parent


def input_bits(text, width):
    """Refuse a source value requiring any rounding to enter the stated format."""
    value = float.fromhex(text) if "0x" in text.lower() else float(text)
    code = ">f" if width == 32 else ">d"
    packed = struct.pack(code, value)
    decoded = struct.unpack(code, packed)[0]
    if math.isfinite(value) and number(text) != Fraction.from_float(decoded):
        raise ValueError(f"Source input is not exactly representable in binary{width}: {text}")
    return int.from_bytes(packed, "big")


def core_cases(samples):
    """Count every .wc row; select smallest SHA-256 ranks per supported source file."""
    manifest = json.loads((HERE / "core-math-source.json").read_text())
    root = HERE / "upstream/core-math"
    inventory, selected = [], []
    for path in sorted((root / "src").glob("binary*/*/*.wc")):
        relative = str(path.relative_to(root))
        width = int(path.parts[-3].removeprefix("binary"))
        operation = path.parts[-2]
        supported = width in (32, 64) and operation in OPERATIONS
        heap, count, malformed = [], 0, 0
        with path.open() as stream:
            for line_number, line in enumerate(stream, 1):
                text = line.split("#", 1)[0].strip()
                if not text:
                    continue
                count += 1
                if not supported:
                    continue
                identity = f"core-math:{relative}:{line_number}"
                rank = int.from_bytes(hashlib.sha256(identity.encode()).digest(), "big")
                # Parsing only retained candidates keeps the inventory inexpensive.
                if samples and len(heap) >= samples and rank >= -heap[0][0]:
                    continue
                row = {
                    "id": identity, "source": "CORE-MATH",
                    "source_revision": manifest["revision"],
                    "source_file": relative, "source_sha256": manifest["sha256"][relative],
                    "source_line": line_number, "source_input": text,
                    "width": width, "operation": operation,
                    "input_class": "published worst-case file (also includes boundary tests)",
                }
                try:
                    row["bits"] = input_bits(text, width)
                except (ValueError, OverflowError) as error:
                    row.update(status="translation_refusal", reason=str(error))
                    malformed += 1
                if samples:
                    heapq.heappush(heap, (-rank, identity, row))
                    if len(heap) > samples:
                        heapq.heappop(heap)
                else:
                    selected.append(row)
        if samples:
            selected.extend(row for _, _, row in sorted(heap, reverse=True))
        inventory.append({
            "source": "CORE-MATH", "source_file": relative,
            "source_revision": manifest["revision"],
            "source_sha256": manifest["sha256"][relative],
            "width": width, "operation": operation, "source_cases": count,
            "selected_cases": min(samples, count) if samples and supported
                              else count if supported else 0,
            "status": "sampled" if supported and samples else
                      "selected_all" if supported else "capability_refusal",
            "reason": "" if supported else "No corresponding FloatLib correctly rounded API",
            "selection": f"smallest {samples} SHA-256(source path:line) ranks" if samples
                         else "all source rows",
        })
    for operation in OPERATIONS:
        inventory.append({
            "source": "CORE-MATH", "width": 32, "operation": operation,
            "source_revision": manifest["revision"], "source_cases": 2**32,
            "selected_cases": 0, "status": "not_run",
            "reason": "Upstream validates unary binary32 exhaustively; no .wc file supplied",
            "selection": "No binary64 worst case is relabeled as a binary32 hard case",
        })
    return inventory, selected


def calibration_cases():
    """Small exact-value checks for the MPFR setup, separate from corpus measurements."""
    rows = []
    for width in (32, 64):
        one = input_bits("1", width)
        sign = 1 << (width - 1)
        for operation, bits, expected in [
            ("exp", 0, one), ("log", one, 0), ("expm1", 0, 0),
            ("expm1", sign, sign), ("log1p", 0, 0), ("log1p", sign, sign),
        ]:
            rows.append({"id": f"calibration:{width}:{operation}:{bits}",
                         "width": width, "operation": operation, "bits": bits,
                         "known_exact": expected})
    return rows
