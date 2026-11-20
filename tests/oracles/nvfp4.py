"""NVFP4 exact policies and binary32 arithmetic checked under separate contracts.

The exact reference uses gfloat's decoded values, exact Fraction distances and
MPFR binary32 observations. The implementation reference is CPU torchao, which
is compared with `Block.nvfp4Working`, the library's quantizer on binary32
encodings (`oracle block nvfp4f32`). No near-tie tolerance or class of ignored
discrepancies is used.
"""

import argparse
from fractions import Fraction
from functools import lru_cache
import hashlib
import importlib.metadata
import json
from pathlib import Path
import struct

import gfloat
from gfloat import formats
import gmpy2
import numpy as np

from block_formats import nvfp4_blocks, run_oracle, words


@lru_cache(maxsize=None)
def positive_values(profile):
    descriptor = getattr(formats, "format_info_ocp_" + profile)
    end = 127 if profile == "e4m3" else 8
    return tuple(Fraction(float(gfloat.decode_float(descriptor, code).fval))
                 for code in range(end))


def nearest(profile, value):
    values = positive_values(profile)
    return min(range(len(values)), key=lambda code: (abs(values[code] - value), code % 2))


def from_word(word):
    return Fraction(struct.unpack("<f", struct.pack("<I", word))[0])


def rounded_word(value, negative_zero=False):
    if value == 0:
        return 0x80000000 if negative_zero else 0
    with gmpy2.context(gmpy2.ieee(32)):
        rounded = float(gmpy2.mpfr(gmpy2.mpq(value.numerator, value.denominator)))
    return struct.unpack("<I", struct.pack("<f", rounded))[0]


def exact(row, two_level, floor):
    outer = from_word(row[0]) if two_level else Fraction(1)
    data = row[1:] if two_level else row
    if outer <= 0:
        raise ValueError("This corpus requires a positive finite outer scale")
    scales, codes, values = [], [], []
    for offset in range(0, len(data), 16):
        block = data[offset:offset + 16]
        decoded = [from_word(word) for word in block]
        ideal = max(map(abs, decoded)) / outer / 6
        if floor:
            ideal = max(ideal, Fraction(1, 64))
        scale_code = nearest("e4m3", ideal)
        total_scale = positive_values("e4m3")[scale_code] * outer
        scales.append(scale_code)
        for word, value in zip(block, decoded, strict=True):
            normalized = abs(value / total_scale) if total_scale else Fraction(0)
            code = nearest("e2m1", normalized)
            negative = bool(word >> 31)
            result = positive_values("e2m1")[code] * total_scale
            codes.append(code + (8 if negative else 0))
            values.append(rounded_word(-result if negative else result, negative))
    return scales, codes, values


def compare(name, expected, actual, fields):
    count = 0
    mismatches = []
    bad = 0
    for index, (want, got) in enumerate(zip(expected, actual, strict=True)):
        if got is None or len(got) != 3:
            raise ValueError(f"Malformed response in {name} at row {index}: {got}")
        for field in fields:
            if len(want[field]) != len(got[field]):
                raise ValueError(f"Wrong response length in {name}, row {index}, field {field}")
            for position, (a, b) in enumerate(zip(want[field], got[field], strict=True)):
                count += 1
                if a != b:
                    bad += 1
                    if len(mismatches) < 20:
                        mismatches.append({"row": index, "field": field, "position": position,
                                           "expected": a, "actual": b})
    return {"name": name, "rows": len(expected), "comparisons": count,
            "mismatches": bad, "first_mismatches": mismatches}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--oracle", required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--count", type=int, default=64)
    parser.add_argument("--seed", type=int, default=20261116)
    args = parser.parse_args()
    import torch
    from torchao.prototype.mx_formats.nvfp4_tensor import (
        nvfp4_quantize, per_tensor_amax_to_scale)
    from torchao.prototype.mx_formats.kernels import unpack_uint4
    import torchao.prototype.mx_formats.nvfp4_tensor as reference

    torch.set_num_threads(4)
    rng = np.random.default_rng(args.seed)
    half = np.array([struct.unpack("<e", struct.pack("<H", word))[0]
                     for word in range(65536) if word & 0x7C00 != 0x7C00],
                    dtype=np.float32).reshape(-1, 16)
    grid = [float(v) for v in positive_values("e2m1")]
    represented = np.array([[s * v for v in grid + [-v for v in grid]]
                            for s in map(float, positive_values("e4m3"))], dtype=np.float32)
    single = np.concatenate([nvfp4_blocks(rng, args.count, 1), half, represented])
    two = nvfp4_blocks(rng, args.count, 4)
    cases, policy_differences = [], []
    corpus_digests = {}
    skipped_zero_tensors = 0
    for mode, tensors in [("single", single), ("two", two)]:
        rows, expected_torch = [], []
        for data in tensors:
            tensor = torch.from_numpy(data.copy()).reshape(1, -1)
            outer = None
            if mode == "two":
                if tensor.abs().max() == 0:
                    skipped_zero_tensors += 1
                    continue
                outer = per_tensor_amax_to_scale(tensor.abs().max())
                if not torch.isfinite(outer) or outer <= 0:
                    raise ValueError("The two-level corpus left the positive finite outer domain")
            scale, packed = nvfp4_quantize(tensor, 16, outer)
            row = words(data)
            if outer is not None:
                row = words(outer.reshape(1).numpy()) + row
            rows.append(row)
            expected_torch.append((scale.view(torch.uint8).reshape(-1).tolist(),
                                   unpack_uint4(packed).reshape(-1).tolist(), []))
        corpus_digests[mode] = hashlib.sha256(json.dumps(rows).encode()).hexdigest()
        for variant in ("exact", "clamp"):
            expected = [exact(row, mode == "two", variant == "clamp") for row in rows]
            actual = run_oracle(args.oracle, ["nvfp4", mode, variant], rows)
            cases.append(compare(f"exact rational {mode} {variant}", expected, actual, (0, 1, 2)))
            difference = compare(f"torchao versus exact {mode} {variant}",
                                 expected_torch, expected, (0, 1))
            difference["interpretation"] = (
                "Different contracts: the exact policy rounds each exact quotient once and "
                "has a floor of 2^-6 on the block scale only in the clamp variant, and the "
                "reference computes in binary32. These counts are reported as they are.")
            policy_differences.append(difference)
        actual = run_oracle(args.oracle, ["nvfp4f32", mode], rows)
        if any(result is None or result[2] for result in actual):
            raise ValueError("Unexpected binary32-model response")
        cases.append(compare(f"torchao binary32 {mode}", expected_torch, actual, (0, 1)))
    mismatch_count = sum(case["mismatches"] for case in cases)
    result = {
        "source": "NVIDIA, Pretraining Large Language Models with NVFP4, "
                  "arXiv:2509.25149v2, Appendix B; vendor description, not a standard",
        "reference_versions": {name: importlib.metadata.version(name)
                               for name in ("gfloat", "torchao", "gmpy2")},
        "torch": torch.__version__,
        "torchao_source_sha256": hashlib.sha256(Path(reference.__file__).read_bytes()).hexdigest(),
        "corpus": "Seeded random/adversarial 16-element blocks; every finite binary16 "
                  "word occurs in a block; all 127 nonnegative finite E4M3 scales applied "
                  "to all sixteen E2M1 codes; four-block two-level tensors",
        "seed": args.seed, "corpus_sha256": corpus_digests,
        "skipped_zero_two_level_tensors": skipped_zero_tensors,
        "cases": cases, "policy_differences": policy_differences,
        "comparisons": sum(case["comparisons"] for case in cases),
        "mismatches": mismatch_count,
        "status": "pass" if mismatch_count == 0 else "fail",
        "limitations": [
            "Finite inputs only; whole tensors and rational inputs are not exhaustive.",
            "Two-level tests use supplied positive binary32 scales; all-zero dynamic "
            "outer-scale handling is not claimed to match torchao.",
            "The binary32 comparison covers the tensors of this corpus, in which no "
            "binary32 operation overflows; nvfp4_working.py compares the overflow cases "
            "with hardware binary32.",
            "No GPU kernel, GEMM accumulation precision or stochastic rounding is tested.",
        ],
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    if mismatch_count:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
