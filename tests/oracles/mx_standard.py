"""MX v1.0 block conversion against gfloat and Microsoft microxcaling.

Reuse the repository's binary32 block generator and Lean oracle protocol.
Reference arithmetic uses binary64: scaling these binary32 inputs by powers
of two is exact. Codes and decoded binary32 observations are both checked.
Only differences that the input alone determines count as known.
"""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import types

import numpy as np
import torch
import gfloat
from gfloat import formats

from block_formats import mx_blocks, run_oracle, words


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--oracle", required=True)
    parser.add_argument("--microxcaling", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--count", type=int, default=64)
    parser.add_argument("--seed", type=int, default=20261116)
    args = parser.parse_args()
    torch.set_num_threads(8)
    torch.set_num_interop_threads(1)
    package = types.ModuleType("mx")
    package.__path__ = [str(args.microxcaling / "mx")]
    sys.modules["mx"] = package
    from mx.mx_ops import _quantize_mx
    from mx.formats import ElemFormat

    rng = np.random.default_rng(args.seed)
    cases = []
    differences = []
    unexplained = 0
    for profile, block_name, micro_name in [
        ("e5m2", "mxfp8_e5m2", "fp8_e5m2"),
        ("e4m3", "mxfp8_e4m3", "fp8_e4m3"),
        ("e3m2", "mxfp6_e3m2", "fp6_e3m2"),
        ("e2m3", "mxfp6_e2m3", "fp6_e2m3"),
        ("e2m1", "mxfp4_e2m1", "fp4_e2m1"),
        ("int8", "mxint8", "int8"),
    ]:
        descriptor = getattr(formats, "format_info_" + block_name)
        data = mx_blocks(profile, 32, rng, args.count)
        rows = [words(row) for row in data]
        actual = run_oracle(args.oracle, ["mx", profile, "floor"], rows)
        if any(result is None for result in actual):
            raise RuntimeError("Lean oracle rejected a finite generated block")
        reference = []
        for row in data.astype(np.float64):
            scale = gfloat.compute_scale_amax(descriptor.etype.emax, row)
            encoded = list(gfloat.encode_block(descriptor, scale, row / scale))
            decoded = list(gfloat.decode_block(descriptor, encoded))
            reference.append(([encoded[0]], encoded[1:], words(decoded)))
        micro = _quantize_mx(
            torch.tensor(data, dtype=torch.float64, device="cpu"), 8,
            getattr(ElemFormat, micro_name), axes=[-1], block_size=32,
            shared_exp_method="max", round="even", custom_cuda=False,
            flush_fp32_subnorms=False,
        ).numpy()
        counts = {"gfloat_scale": 0, "gfloat_element": 0, "gfloat_value": 0,
                  "microxcaling_value": 0}
        causes = {}

        def record(row, reference_name, field, lane, expected, got, cause):
            nonlocal unexplained
            causes[cause or "unexplained"] = causes.get(cause or "unexplained", 0) + 1
            if cause is None:
                unexplained += 1
            differences.append({
                "profile": profile, "row": row, "reference": reference_name,
                "field": field, "lane": lane, "expected": expected, "actual": got,
                "input_word": rows[row][lane] if field != "scale" else rows[row],
                "cause": cause,
            })

        for row, (expected, got) in enumerate(zip(reference, actual, strict=True)):
            for field, wanted, found in zip(
                ("scale", "element", "value"), expected, got, strict=True
            ):
                if len(wanted) != len(found):
                    raise RuntimeError("Oracle field length mismatch")
                counts["gfloat_" + field] += len(wanted)
                for lane, (e, a) in enumerate(zip(wanted, found, strict=True)):
                    if e == a:
                        continue
                    cause = None
                    if (field == "scale" and not np.any(data[row]) and
                            e == 0 and a == 127):
                        cause = "all-zero block: the specification leaves the scale open (FloatLib stores 2^0)"
                    record(row, "gfloat", field, lane, e, a, cause)
            for lane, (e, a) in enumerate(zip(words(micro[row]), got[2], strict=True)):
                counts["microxcaling_value"] += 1
                if e == a:
                    continue
                cause = None
                # A known difference: an input negative zero, whose sign the element keeps.
                if e == 0 and a == 0x80000000 and rows[row][lane] == 0x80000000:
                    cause = "input negative zero: the element keeps the sign"
                # Two's-complement INT8 has only the all-zero code, so a negative
                # value that rounds to zero is stored as that code. Check that exact situation.
                if (profile == "int8" and e == 0x80000000 and a == 0 and
                        got[1][lane] == 0 and rows[row][lane] & 0x80000000):
                    cause = "INT8 negative zero has no stored encoding"
                # MX §5.3.4 explicitly permits leaving the -2 encoding unused.
                scale = 2.0 ** (got[0][0] - 127)
                if (profile == "int8" and got[1][lane] == 128 and
                        a == words([-2.0 * scale])[0] and
                        e == words([-127.0 / 64.0 * scale])[0]):
                    cause = "permitted INT8 range choice: asymmetric versus symmetric"
                record(row, "microxcaling", "value", lane, e, a, cause)
        result = {"profile": profile, "blocks": len(rows),
                  "comparisons": counts, "differences_by_cause": causes}
        cases.append(result)
        print(json.dumps(result), flush=True)

    commit = subprocess.check_output(
        ["git", "-C", str(args.microxcaling), "rev-parse", "HEAD"], text=True
    ).strip()
    report = {
        "document": "OCP Microscaling Formats (MX) Specification v1.0 (2023-09-07)",
        "clauses": ["5.1", "5.2", "5.3", "5.4", "6.3"],
        "gfloat": "0.5.2", "torch": torch.__version__,
        "microxcaling_commit": commit,
        "microxcaling_source_sha256": {
            path: hashlib.sha256((args.microxcaling / "mx" / path).read_bytes()).hexdigest()
            for path in ("mx_ops.py", "elemwise_ops.py", "formats.py")
        },
        "seed": args.seed, "random_draws_per_profile": args.count,
        "cases": cases, "differences": differences,
        "unexplained_mismatches": unexplained,
        "status": "pass-with-known-differences"
                  if unexplained == 0 else "fail",
        "limitations": [
            "Finite binary32 blocks only; exceptional decoding has separate Lean regressions.",
            "Random and boundary blocks are not exhaustive over 32-element vectors.",
            "References run on CPU with binary64 intermediates, not accelerator kernels.",
            "Decoded observations are rounded once to binary32.",
        ],
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2) + "\n")
    raise SystemExit(unexplained != 0)


if __name__ == "__main__":
    main()
