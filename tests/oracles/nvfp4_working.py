"""NVFP4 quantized in binary32: the library quantizer against hardware binary32.

`Block.nvfp4Working` is FloatLib's quantizer on binary32 encodings, in the order of torchao's
`nvfp4_quantize`. This script repeats that order with NumPy's float32, which is the binary32
arithmetic of the processor, and rounds to E4M3 and E2M1 with exact fractions. It then compares
the scale codes and the element codes with the output of `oracle block nvfp4f32`, bit for bit
and with no tolerance.

The corpus has ordinary tensors, tensors whose outer scale is tiny (the scale quotient or the
reciprocal overflows), tensors with huge elements (the product overflows), subnormals and zeros.
A zero element under a reciprocal that overflowed is `0 * inf`, a NaN: such a block is counted
and left out, because the element code of a NaN is not part of the format.

No torchao is needed. `tests/oracles/nvfp4.py` compares the same Lean command with torchao.
"""

import argparse
from fractions import Fraction
import json
from pathlib import Path
import struct

import numpy as np

from block_formats import run_oracle


def table(exponent_bits, mantissa_bits, bias, top):
    """Finite nonnegative values of a small binary format, indexed by code."""
    values = []
    for code in range(top + 1):
        e, m = code >> mantissa_bits, code & ((1 << mantissa_bits) - 1)
        if e == 0:
            values.append(Fraction(m, 1 << mantissa_bits) * Fraction(2) ** (1 - bias))
        else:
            values.append((1 + Fraction(m, 1 << mantissa_bits)) * Fraction(2) ** (e - bias))
    assert e < (1 << exponent_bits)
    return values


E4M3 = table(4, 3, 7, 126)   # 0 .. 448; code 127 is the NaN of the FN encoding
E2M1 = table(2, 1, 1, 7)     # 0, 1/2, 1, 3/2, 2, 3, 4, 6


def nearest(values, magnitude):
    """Nearest code to an exact nonnegative magnitude, ties to the even code, saturating."""
    return min(range(len(values)), key=lambda code: (abs(values[code] - magnitude), code % 2))


def exact(x):
    return Fraction(float(x))


def reference(row, two_level):
    """Scale codes and element codes of one tensor, or None when a product is a NaN."""
    f32 = np.float32
    outer = f32(1.0)
    data = np.array(row, dtype=np.uint32).view(np.float32)
    if two_level:
        outer, data = data[0], data[1:]
    scales, codes = [], []
    overflow = {"scale": False, "reciprocal": False, "product": False}
    with np.errstate(over="ignore", invalid="ignore", divide="ignore", under="ignore"):
        for offset in range(0, len(data), 16):
            block = data[offset:offset + 16]
            amax = np.max(np.abs(block))
            scaled = (amax / f32(6.0)) / outer
            clamped = np.clip(scaled, f32(2.0 ** -6), f32(448.0))
            scale_code = nearest(E4M3, exact(clamped))
            back = f32(float(E4M3[scale_code]))
            reciprocal = (f32(1.0) / outer) / back
            raw = block * reciprocal
            product = np.clip(raw, f32(-6.0), f32(6.0))
            if np.isnan(product).any():
                return None
            overflow["scale"] |= bool(np.isinf(scaled))
            overflow["reciprocal"] |= bool(np.isinf(reciprocal))
            overflow["product"] |= bool(np.isinf(raw).any()) and not bool(np.isinf(reciprocal))
            scales.append(scale_code)
            for value in product:
                code = nearest(E2M1, abs(exact(value)))
                codes.append(code + (8 if np.signbit(value) else 0))
    return scales, codes, overflow


def words(values):
    return np.asarray(values, dtype=np.float32).view(np.uint32).tolist()


def word(sign, exponent, fraction):
    return (sign << 31) | (exponent << 23) | fraction


def corpus(rng, count, blocks):
    """Rows of binary32 words: an outer scale followed by `blocks` blocks of 16."""
    rows = []
    for index in range(count):
        centre = int(rng.integers(20, 235))
        kind = index % 8
        spread = (0, 2, 6, 30, 2, 2, 2, 60)[kind]
        low, high = max(0, centre - spread), min(254, centre + spread)
        if kind == 4:
            low = 0  # subnormals and zeros among the elements
        data = [word(int(rng.integers(2)), int(rng.integers(low, high + 1)),
                     int(rng.integers(1 << 23))) for _ in range(16 * blocks)]
        if kind in (4, 5):
            data[int(rng.integers(len(data)))] = word(int(rng.integers(2)), 0, 0)
        if kind == 6:
            # one huge element, so that its product with the reciprocal overflows
            data[int(rng.integers(len(data)))] = word(int(rng.integers(2)), 254,
                                                      int(rng.integers(1 << 23)))
        # outer scales: near amax / (6 * 448), far too small, far too large
        choice = index % 5
        if choice in (0, 1):
            exponent = min(254, max(1, centre - 12 + int(rng.integers(-1, 2))))
        elif choice == 2:
            exponent = int(rng.integers(0, 12))       # tiny, subnormal included
        elif choice == 3:
            exponent = int(rng.integers(240, 255))    # huge
        else:
            exponent = int(rng.integers(1, 255))
        fraction = int(rng.integers(1 << 23))
        outer = word(0, exponent, fraction if (exponent or fraction) else 1)
        rows.append([outer] + data)
    return rows


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--oracle", required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--count", type=int, default=4000)
    parser.add_argument("--seed", type=int, default=20261119)
    args = parser.parse_args()
    rng = np.random.default_rng(args.seed)
    cases = []
    for mode, two_level in (("single", False), ("two", True)):
        rows = corpus(rng, args.count, 2)
        if not two_level:
            rows = [row[1:] for row in rows]
        expected = [reference(row, two_level) for row in rows]
        kept = [index for index, want in enumerate(expected) if want is not None]
        actual = run_oracle(args.oracle, ["nvfp4f32", mode], [rows[index] for index in kept])
        comparisons = mismatches = saturated = 0
        overflows = {"scale": 0, "reciprocal": 0, "product": 0}
        first = []
        for index, got in zip(kept, actual, strict=True):
            want = expected[index]
            if got is None:
                raise ValueError(f"The oracle refused row {index} of {mode}")
            for field in (0, 1):
                if len(want[field]) != len(got[field]):
                    raise ValueError(f"Wrong response length in {mode}, row {index}")
                for position, (a, b) in enumerate(zip(want[field], got[field], strict=True)):
                    comparisons += 1
                    if a != b:
                        mismatches += 1
                        if len(first) < 20:
                            first.append({"row": index, "field": field, "position": position,
                                          "expected": a, "actual": b})
            saturated += sum(1 for code in want[1] if code & 7 == 7)
            for name, seen in want[2].items():
                overflows[name] += seen
        cases.append({"name": f"hardware binary32 {mode}", "rows": len(rows),
                      "rows_compared": len(kept), "rows_with_a_nan_product": len(rows) - len(kept),
                      "comparisons": comparisons, "saturated_elements": saturated,
                      "rows_where_the_scale_quotient_overflows": overflows["scale"],
                      "rows_where_the_reciprocal_overflows": overflows["reciprocal"],
                      "rows_where_a_product_overflows": overflows["product"],
                      "mismatches": mismatches, "first_mismatches": first})
    mismatch_count = sum(case["mismatches"] for case in cases)
    result = {
        "reference": "NumPy float32 (the processor's binary32) in the order of torchao's "
                     "nvfp4_quantize, with E4M3 and E2M1 rounded by exact fractions",
        "numpy": np.__version__, "seed": args.seed, "cases": cases,
        "comparisons": sum(case["comparisons"] for case in cases),
        "mismatches": mismatch_count,
        "status": "pass" if mismatch_count == 0 else "fail",
        "limitations": [
            "Finite inputs and positive finite outer scales only.",
            "A block with a zero element under an overflowed reciprocal is left out.",
            "This is not torchao: tests/oracles/nvfp4.py makes that comparison.",
        ],
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    if mismatch_count:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
