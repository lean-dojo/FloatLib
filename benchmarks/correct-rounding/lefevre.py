"""Read Lefèvre's published testlibm binary strings without rounding their inputs."""
from __future__ import annotations
from collections import Counter, defaultdict
from fractions import Fraction
import hashlib
import heapq
import json
import lzma
import re
import struct
from pathlib import Path

from fetch import fetch

HERE = Path(__file__).resolve().parent
ALIASES = {"exp": "exp", "log": "log", "em1": "expm1", "l1p": "log1p"}
PATTERN = re.compile(r"([+-]?)([01])\.([01]+)[Ee]([+-]?\d+)$")


def binary_value(text):
    match = PATTERN.fullmatch(text)
    if not match:
        raise ValueError("Unsupported binary source number: " + text)
    sign, integer, fraction, exponent = match.groups()
    mantissa = int(integer + fraction, 2)
    value = Fraction(mantissa) * Fraction(2) ** (int(exponent) - len(fraction))
    return (-value if sign == "-" else value), len(fraction) + 1, sign == "-"


def binary_bits(text, width):
    value, precision, negative = binary_value(text)
    packed = struct.pack(">f" if width == 32 else ">d", float(value))
    decoded = struct.unpack(">f" if width == 32 else ">d", packed)[0]
    if Fraction.from_float(decoded) != value:
        raise ValueError("Source number is outside the exact IEEE encoding range")
    bits = int.from_bytes(packed, "big")
    if value == 0 and negative:
        bits |= 1 << (width - 1)
    return bits


def cases(samples):
    manifest_path = HERE / "lefevre-source.json"
    manifest = json.loads(manifest_path.read_text())
    root = fetch(manifest_path)
    inventory, selected = [], []
    for filename in ("testlibm-data.xz", "hrcases-explog.xz"):
        counts, heaps = Counter(), defaultdict(list)
        with lzma.open(root / filename, "rt") as stream:
            for line_number, line in enumerate(stream, 1):
                text = line.strip()
                if not text or text.startswith("#"):
                    continue
                fields = text.split()
                if len(fields) != 5:
                    raise ValueError(f"Unexpected testlibm record: {filename}:{line_number}")
                mode, function, argument, expected, last_bit = fields
                _, precision, _ = binary_value(argument)
                width = {24: 32, 53: 64}.get(precision, 0)
                operation = ALIASES.get(function, function)
                key = mode, operation, width, precision
                counts[key] += 1
                # Record whole unsupported groups in coverage, without hiding their row counts.
                if mode != "N" or function not in ALIASES or not width:
                    continue
                identity = f"lefevre:{filename}:{line_number}"
                rank = int.from_bytes(hashlib.sha256(identity.encode()).digest(), "big")
                heap = heaps[key]
                if samples and len(heap) >= samples and rank >= -heap[0][0]:
                    continue
                row = {
                    "id": identity, "source": "Lefèvre testlibm",
                    "source_revision": manifest["version"], "source_file": filename,
                    "source_sha256": manifest["files"][filename]["sha256"],
                    "source_line": line_number, "source_input": argument,
                    "source_rounding": mode, "source_last_bit": last_bit,
                    "width": width, "operation": operation,
                    "input_class": "published hard-to-round data",
                }
                try:
                    # Make the pair available only after both conversions succeed.
                    row["bits"], row["published_expected"] = (
                        binary_bits(argument, width), binary_bits(expected, width))
                except (ValueError, OverflowError) as error:
                    row.update(status="translation_refusal", reason=str(error))
                if samples:
                    heapq.heappush(heap, (-rank, identity, row))
                    if len(heap) > samples:
                        heapq.heappop(heap)
                else:
                    selected.append(row)
        if samples:
            for key in sorted(heaps):
                selected.extend(row for _, _, row in sorted(heaps[key], reverse=True))
        for (mode, operation, width, precision), count in sorted(counts.items()):
            reason = ("FloatLib's correctly rounded elementary API fixes nearest-even"
                      if mode != "N" else
                      "No corresponding FloatLib correctly rounded elementary API"
                      if operation not in ALIASES.values() else
                      "Source precision is not binary32 or binary64" if not width else "")
            inventory.append({
                "source": "Lefèvre testlibm", "source_file": filename,
                "source_revision": manifest["version"],
                "source_sha256": manifest["files"][filename]["sha256"],
                "operation": operation, "width": width, "precision": precision,
                "rounding": mode, "source_cases": count,
                "selected_cases": 0 if reason else min(samples, count) if samples else count,
                "status": "capability_refusal" if reason else "sampled" if samples else "selected_all",
                "reason": reason,
                "selection": f"smallest {samples} SHA-256(file:line) ranks per group"
                             if samples else "all source rows",
            })
    return inventory, selected
