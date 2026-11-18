#!/usr/bin/env python3
"""Compare FloatLib's block-format quantizers and decoders with reference implementations.

The references are torchao's MX and NVFP4 quantizers, Microsoft's microxcaling MX library, and
PyTorch's float8 casts. FloatLib runs through `oracle block`, which reads tensors of binary32 words
and writes stored codes and decoded values. Every comparison is bit for bit: scale codes, element
codes, and decoded binary32 words.

    python3 tests/oracles/block_formats.py --oracle BUILD/bin/oracle \
        --torchao PY_TARGET_DIR --microxcaling CLONE_DIR --out RESULT.json

The inputs are random tensors and adversarial ones: block maxima at binade boundaries, ties of the
element rounding, saturation, zeros and negative zeros, and scales at both ends of the scale
format's range. Inputs that are not finite are not generated; the oracle takes finite words.
"""

import argparse
import json
import os
import struct
import subprocess
import sys

os.environ.setdefault("CUDA_VISIBLE_DEVICES", "")

import numpy as np


def words(array):
    """Binary32 words of a float32 array, as Python ints."""
    return np.asarray(array, dtype=np.float32).reshape(-1).view(np.uint32).tolist()


def run_oracle(oracle, case, rows):
    """Run `oracle block CASE` on rows of words; return (scales, codes, values) per row."""
    text = "\n".join(" ".join(format(w, "x") for w in row) for row in rows) + "\n"
    done = subprocess.run([oracle, "block", *case], input=text, capture_output=True, text=True)
    if done.returncode:
        raise RuntimeError(f"oracle {case} exited {done.returncode}: {done.stderr[:500]}")
    lines = done.stdout.splitlines()
    if len(lines) != len(rows):
        raise RuntimeError(f"oracle {case}: {len(lines)} lines for {len(rows)} rows: {done.stderr[:500]}")
    out = []
    for line in lines:
        if line.startswith("error"):
            out.append(None)
            continue
        parts = [part.split() for part in line.split("|")]
        scales = [int(v) for v in parts[0]]
        codes = [int(v) for v in parts[1]]
        values = [None if v == "x" else int(v) for v in parts[2]] if len(parts) > 2 else []
        out.append((scales, codes, values))
    return out


# ---------------------------------------------------------------------------------------------
# Inputs
# ---------------------------------------------------------------------------------------------

def f32(x):
    return np.asarray(x, dtype=np.float32)


def nextafter(x, toward):
    return np.nextafter(f32(x), f32(toward), dtype=np.float32)


def element_values(name):
    """Nonnegative finite values of an element format, as Python floats (exact)."""
    if name == "int8":
        return [k / 64.0 for k in range(128)]
    ebits, mbits, bias = {"e2m1": (2, 1, 1), "e2m3": (2, 3, 1), "e3m2": (3, 2, 3),
                           "e4m3": (4, 3, 7), "e5m2": (5, 2, 15)}[name]
    values = []
    for e in range(2 ** ebits):
        for m in range(2 ** mbits):
            if e == 0:
                v = m / 2 ** mbits * 2.0 ** (1 - bias)
            else:
                v = (1 + m / 2 ** mbits) * 2.0 ** (e - bias)
            values.append(v)
    if name == "e5m2":
        values = [v for v in values if v <= 57344.0]
    if name == "e4m3":
        values = [v for v in values if v <= 448.0]
    return sorted(set(values))


def mx_blocks(profile, block, rng, count):
    """Random and adversarial blocks for an MX profile with power-of-two scales."""
    rows = []
    grid = element_values(profile)
    mids = [(a + b) / 2 for a, b in zip(grid, grid[1:])]
    top = grid[-1]
    for _ in range(count):
        scale = 2.0 ** rng.integers(-30, 30)
        rows.append(rng.standard_normal(block) * scale)
        rows.append(rng.uniform(-1, 1, block) * scale)
        rows.append(np.sign(rng.standard_normal(block)) * np.exp(rng.uniform(-12, 4, block)) * scale)
    for k in list(range(-140, -110, 3)) + list(range(-20, 21, 4)) + list(range(100, 128, 3)):
        base = 2.0 ** k if k > -150 else 0.0
        for amax in (base, float(nextafter(base, 0)), float(nextafter(base, np.inf)),
                     base * 1.5, base * 1.75, base * 1.99):
            if not np.isfinite(f32(amax)) or amax == 0:
                continue
            row = rng.uniform(-1, 1, block) * amax * 0.9
            row[rng.integers(block)] = amax * rng.choice([-1.0, 1.0])
            rows.append(row)
    for e in range(-6, 7, 3):
        scale = 2.0 ** e
        ties = np.array(mids + [-m for m in mids], dtype=np.float64) * scale
        for start in range(0, len(ties), block - 1):
            row = np.zeros(block)
            chunk = ties[start:start + block - 1]
            row[:len(chunk)] = chunk
            row[block - 1] = top * scale * 0.999 if top * scale * 0.999 > abs(chunk).max() else abs(chunk).max()
            rows.append(row)
        over = np.linspace(top, 2 * top, block) * scale
        rows.append(over * rng.choice([-1.0, 1.0], block))
    rows.append(np.zeros(block))
    rows.append(-np.zeros(block))
    row = np.zeros(block)
    row[3] = -0.0
    row[5] = 1.0
    rows.append(row)
    row = np.full(block, 1e-45)
    rows.append(row)
    row = np.zeros(block)
    row[0] = 3.0e38
    row[1] = -1.0e38
    rows.append(row)
    return np.array(rows, dtype=np.float32)


def nvfp4_blocks(rng, count, blocks_per_tensor):
    """Random and adversarial tensors of 16-element blocks for NVFP4."""
    rows = []
    width = 16 * blocks_per_tensor
    grid = element_values("e2m1")
    mids = [(a + b) / 2 for a, b in zip(grid, grid[1:])]
    scales = sorted({(1 + m / 8) * 2.0 ** e for e in range(-6, 6) for m in range(8)})
    for _ in range(count):
        scale = 2.0 ** rng.integers(-12, 12)
        rows.append(rng.standard_normal(width) * scale)
        rows.append(np.sign(rng.standard_normal(width)) * np.exp(rng.uniform(-8, 3, width)) * scale)
        row = rng.standard_normal(width) * scale
        row[rng.integers(width)] *= 64
        rows.append(row)
    for s in scales[::5]:
        row = np.zeros(width)
        for b in range(blocks_per_tensor):
            vals = np.array(mids + [-m for m in mids] + [6.0, -6.0])[:16] * s
            rng.shuffle(vals)
            row[16 * b:16 * b + 16] = vals
        rows.append(row)
        row = rng.uniform(-6, 6, width) * s
        row[0] = 6 * s
        rows.append(row)
        row = rng.uniform(-6, 6, width) * s
        row[0] = float(nextafter(6 * s, np.inf))
        rows.append(row)
    rows.append(np.zeros(width))
    row = np.zeros(width)
    row[0] = 1.0
    row[17 % width] = -0.0
    rows.append(row)
    row = rng.standard_normal(width) * 1e-6
    row[0] = 5.0
    rows.append(row)
    row = rng.standard_normal(width) * 1e-30
    rows.append(row)
    return np.array(rows, dtype=np.float32)


# ---------------------------------------------------------------------------------------------
# Comparisons
# ---------------------------------------------------------------------------------------------

class Report:
    def __init__(self):
        self.cases = []

    def add(self, name, reference, floatlib, rows, expected, got,
            labels=("scales", "codes", "values"), classify=None):
        """`expected` and `got` are lists per row of tuples aligned with `labels`.

        `classify(row, field, position, expected_row, got_row)` names the cause of a mismatch.
        A mismatch without a named cause is counted as `unexplained`.
        """
        counts = {label: 0 for label in labels}
        totals = {label: 0 for label in labels}
        causes = {}
        examples = {}
        bad_rows = 0
        errors = 0
        for index, (e, g) in enumerate(zip(expected, got)):
            if g is None:
                errors += 1
                continue
            row_bad = False
            for position, label in enumerate(labels):
                if e[position] is None:
                    continue
                ev, gv = list(e[position]), list(g[position])
                totals[label] += len(ev)
                diff = [k for k, (a, b) in enumerate(zip(ev, gv)) if a != b]
                if len(ev) != len(gv):
                    diff = diff or [min(len(ev), len(gv))]
                for k in diff:
                    counts[label] += 1
                    row_bad = True
                    cause = classify(index, label, k, e, g) if classify else None
                    cause = cause or "unexplained"
                    causes[cause] = causes.get(cause, 0) + 1
                    if len(examples.setdefault(cause, [])) < 3:
                        examples[cause].append({
                            "row": index, "field": label, "position": k,
                            "input": [format(w, "08x") for w in rows[index]],
                            "reference": ev[k] if k < len(ev) else None,
                            "floatlib": gv[k] if k < len(gv) else None,
                        })
            bad_rows += row_bad
        self.cases.append({
            "case": name, "reference": reference, "floatlib": floatlib, "rows": len(rows),
            "oracle_errors": errors, "compared": totals, "mismatches": counts,
            "mismatched_rows": bad_rows, "causes": causes, "examples": examples,
        })
        print(f"{name:40s} rows {len(rows):5d} compared {sum(totals.values()):8d} "
              f"mismatches {sum(counts.values()):6d} {causes}", flush=True)


def floats(row_words):
    return [struct.unpack("<f", struct.pack("<I", w))[0] for w in row_words]


def exact_floor_log2(x):
    """Floor of the binary logarithm of a positive float, exactly."""
    from fractions import Fraction
    q = Fraction(x)
    e = q.numerator.bit_length() - q.denominator.bit_length()
    if Fraction(2) ** e > q:
        e -= 1
    return e


E2M1_TIES = [0.25, 0.75, 1.25, 1.75, 2.5, 3.5, 5.0]


def e4m3_value(code):
    e, m = (code >> 3) & 15, code & 7
    v = m / 8 * 2.0 ** -6 if e == 0 else (1 + m / 8) * 2.0 ** (e - 7)
    return -v if code & 128 else v


def mx_torchao_cause(rows):
    def cause(row, field, position, e, g):
        values = floats(rows[row])
        amax = max(abs(v) for v in values)
        if amax == 0:
            return "all-zero block: the specification leaves the scale open (FloatLib stores 2^0)"
        if e[0] is not None and e[0][0] == 0:
            return "stored scale 2^-127: FloatLib divides by the stored scale"
        return None
    return cause


def microxcaling_cause(rows, profile):
    def cause(row, field, position, e, g):
        values = floats(rows[row])
        amax = max(abs(v) for v in values)
        if amax == 0:
            return None
        exact = exact_floor_log2(amax)
        approx = int(np.floor(np.log2(np.float32(amax))))
        if exact != approx:
            return "block maximum one ulp below a power of two: FloatLib has the exact exponent"
        if profile == "int8":
            got_value = g[2][position]
            if got_value is not None:
                x = values[position]
                scale = 2.0 ** (exact - 0)
                if x < 0 and struct.unpack("<f", struct.pack("<I", got_value))[0] == -2.0 * scale:
                    return "INT8 negative endpoint: FloatLib stores -2 (two's complement); the symmetric range ends at -127/64"
        return None
    return cause


def nvfp4_cause(rows, two_level):
    from fractions import Fraction

    def cause(row, field, position, e, g):
        data = rows[row][1:] if two_level else rows[row]
        outer = Fraction(floats(rows[row][:1])[0]) if two_level else Fraction(1)
        values = floats(data)
        if field == "scales":
            block = values[16 * position:16 * position + 16]
            ideal = Fraction(max(abs(v) for v in block)) / 6 / outer
            if ideal < Fraction(1, 64):
                return "exact block scale below 2^-6"
            return None
        block = position // 16
        if e[0][block] != g[0][block]:
            return "element of a block whose stored scale differs"
        scale = Fraction(e4m3_value(e[0][block])) * outer
        if scale == 0:
            return None
        y = abs(Fraction(values[position]) / scale)
        for tie in E2M1_TIES:
            if abs(y - Fraction(tie)) <= Fraction(tie) / 2 ** 20:
                return "scaled input within 2^-20 of a rounding tie: the exact format rounds the exact quotient once"
        return None
    return cause


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--oracle", required=True)
    parser.add_argument("--torchao", required=True, help="directory holding the torchao package")
    parser.add_argument("--microxcaling", required=True, help="clone of microsoft/microxcaling")
    parser.add_argument("--out", required=True)
    parser.add_argument("--count", type=int, default=150, help="random draws per generator")
    parser.add_argument("--seed", type=int, default=20261114)
    args = parser.parse_args()

    sys.path.insert(0, args.torchao)
    sys.path.insert(0, args.microxcaling)
    import torch
    from torchao.prototype.mx_formats.mx_tensor import to_mx, to_dtype
    from torchao.prototype.mx_formats.config import ScaleCalculationMode
    from torchao.prototype.mx_formats.constants import DTYPE_FP6_E2M3, DTYPE_FP6_E3M2
    from torchao.prototype.mx_formats.nvfp4_tensor import nvfp4_quantize, per_tensor_amax_to_scale
    from torchao.prototype.mx_formats.kernels import (
        unpack_uint4, f32_to_f4_unpacked, f32_to_f6_e2m3_unpacked, f32_to_f6_e3m2_unpacked)
    from mx.mx_ops import _quantize_mx
    from mx.formats import ElemFormat

    torch.set_num_threads(4)
    rng = np.random.default_rng(args.seed)
    report = Report()

    # ---- OCP MX against torchao ---------------------------------------------------------
    torchao_dtypes = {
        "e4m3": torch.float8_e4m3fn, "e5m2": torch.float8_e5m2,
        "e2m3": DTYPE_FP6_E2M3, "e3m2": DTYPE_FP6_E3M2, "e2m1": torch.float4_e2m1fn_x2,
    }
    modes = {"floor0": ScaleCalculationMode.FLOOR, "ceil": ScaleCalculationMode.CEIL,
             "rceil": ScaleCalculationMode.RCEIL}
    mx_inputs = {}
    for profile in ["e4m3", "e5m2", "e2m3", "e3m2", "e2m1", "int8"]:
        mx_inputs[profile] = mx_blocks(profile, 32, rng, args.count)
    for profile, dtype in torchao_dtypes.items():
        data = mx_inputs[profile]
        rows = [words(row) for row in data]
        for policy, mode in modes.items():
            tensor = torch.from_numpy(data.copy())
            scale, lp = to_mx(tensor, dtype, 32, mode)
            scale_codes = scale.view(torch.uint8).reshape(len(data)).tolist()
            if profile == "e2m1":
                codes = unpack_uint4(lp).reshape(len(data), 32).tolist()
            else:
                codes = lp.view(torch.uint8).reshape(len(data), 32).tolist()
            decoded = to_dtype(lp, scale, dtype, 32, torch.float32)
            values = [words(row) for row in decoded.reshape(len(data), 32).numpy()]
            expected = [([s], c, v) for s, c, v in zip(scale_codes, codes, values)]
            got = run_oracle(args.oracle, ["mx", profile, policy], rows)
            report.add(f"mx {profile} {policy}", f"torchao to_mx {mode.value}",
                       f"Standard.format .{profile} with policy {policy}", rows, expected, got,
                       classify=mx_torchao_cause(rows))
        # FloatLib's own all-zero convention against torchao FLOOR
        tensor = torch.from_numpy(data.copy())
        scale, lp = to_mx(tensor, dtype, 32, ScaleCalculationMode.FLOOR)
        scale_codes = scale.view(torch.uint8).reshape(len(data)).tolist()
        codes = (unpack_uint4(lp) if profile == "e2m1" else lp.view(torch.uint8)).reshape(len(data), 32).tolist()
        expected = [([s], c, None) for s, c in zip(scale_codes, codes)]
        got = run_oracle(args.oracle, ["mx", profile, "floor"], rows)
        report.add(f"mx {profile} floor (FloatLib zero rule)", "torchao to_mx floor",
                   f"Standard.format .{profile} with Standard.policy", rows, expected, got,
                   classify=mx_torchao_cause(rows))

    # ---- OCP MX against microxcaling (decoded values) -------------------------------------
    mx_formats = {"e5m2": ElemFormat.fp8_e5m2, "e4m3": ElemFormat.fp8_e4m3, "e3m2": ElemFormat.fp6_e3m2,
                  "e2m3": ElemFormat.fp6_e2m3, "e2m1": ElemFormat.fp4_e2m1, "int8": ElemFormat.int8}
    for profile, fmt in mx_formats.items():
        data = mx_inputs[profile]
        rows = [words(row) for row in data]
        out = _quantize_mx(torch.from_numpy(data.copy()), 8, fmt, shared_exp_method="max",
                           axes=[-1], block_size=32, round="even")
        expected = [(None, None, words(row)) for row in out.numpy()]
        got = run_oracle(args.oracle, ["mx", profile, "floor"], rows)
        # compare values with the sign of zero ignored and NaN (overflowed scale) as None
        def norm(ws):
            return [None if (w & 0x7fffffff) > 0x7f800000 else (0 if (w & 0x7fffffff) == 0 else w) for w in ws]
        expected = [(None, None, norm(e[2])) for e in expected]
        got = [None if g is None else (g[0], g[1], [None if v is None else (0 if (v & 0x7fffffff) == 0 else v) for v in g[2]]) for g in got]
        report.add(f"mx {profile} values", "microxcaling _quantize_mx round=even",
                   f"Standard.format .{profile} with Standard.policy, decoded", rows, expected, got,
                   classify=microxcaling_cause(rows, profile))

    # ---- NVFP4 against torchao ------------------------------------------------------------
    single = nvfp4_blocks(rng, args.count, 1)
    rows = [words(row) for row in single]
    scale, lp = nvfp4_quantize(torch.from_numpy(single.copy()), 16, None)
    scale_codes = scale.view(torch.uint8).reshape(len(single), 1).tolist()
    codes = unpack_uint4(lp).reshape(len(single), 16).tolist()
    expected = [(s, c, None) for s, c in zip(scale_codes, codes)]
    for case, label in ((["nvfp4", "single", "exact"], "exact scales, no floor"),
                        (["nvfp4", "single", "clamp"], "exact scales, floor 2^-6"),
                        (["nvfp4f32", "single"], "binary32 arithmetic in torchao's order")):
        got = run_oracle(args.oracle, case, rows)
        report.add(" ".join(case), "torchao nvfp4_quantize, single level", label, rows, expected, got,
                   classify=nvfp4_cause(rows, False))

    two = nvfp4_blocks(rng, args.count, 4)
    tensors = torch.from_numpy(two.copy())
    rows, expected = [], []
    for row in tensors:
        amax = row.abs().max()
        if amax == 0:
            continue
        outer = per_tensor_amax_to_scale(amax)
        scale, lp = nvfp4_quantize(row.reshape(1, -1).contiguous(), 16, outer)
        rows.append(words(outer.reshape(1).numpy()) + words(row.numpy()))
        expected.append((scale.view(torch.uint8).reshape(-1).tolist(),
                         unpack_uint4(lp).reshape(-1).tolist(), None))
    for case, label in ((["nvfp4", "two", "exact"], "exact scales, no floor"),
                        (["nvfp4", "two", "clamp"], "exact scales, floor 2^-6"),
                        (["nvfp4f32", "two"], "binary32 arithmetic in torchao's order")):
        got = run_oracle(args.oracle, case, rows)
        report.add(" ".join(case), "torchao nvfp4_quantize, supplied outer scale", label, rows, expected, got,
                   classify=nvfp4_cause(rows, True))

    # ---- Element casts against PyTorch dtypes and torchao kernels --------------------------
    sweep = []
    for name in ["e4m3", "e5m2", "e2m1", "e2m3", "e3m2"]:
        grid = element_values(name)
        mids = [(a + b) / 2 for a, b in zip(grid, grid[1:])]
        points = grid + mids + [float(nextafter(m, 0)) for m in mids] + [float(nextafter(m, np.inf)) for m in mids]
        points += [grid[-1] * f for f in (1.0001, 1.03, 1.0357142857142858, 1.04, 1.07, 1.0714285714285714, 1.08, 1.5, 2.0, 1000.0)]
        sweep.append(np.array(points + [-p for p in points], dtype=np.float32))
    randoms = (rng.standard_normal(4000) * np.exp(rng.uniform(-12, 12, 4000))).astype(np.float32)

    def cast_case(name, fmt, mode, reference_name, reference_codes, data):
        rows = [words(data)]
        expected = [(None, reference_codes, None)]
        got = run_oracle(args.oracle, ["cast", fmt, mode], rows)
        limit = {"e4m3": 448.0, "e5m2": 57344.0}.get(fmt)

        def cause(row, field, position, e, g):
            x = abs(floats(rows[row])[position])
            if limit is not None and x > limit:
                return ("overflow: PyTorch saturates E4M3; the OVF conversion gives NaN" if fmt == "e4m3"
                        else "overflow: PyTorch gives the E5M2 infinity; the SAT conversion clamps")
            return None

        report.add(name, reference_name, f"Codec.ofFormat .{fmt} ({mode})", rows, expected, got,
                   classify=cause)

    data = np.concatenate([sweep[0], randoms])
    ref = torch.from_numpy(data.copy()).to(torch.float8_e4m3fn).view(torch.uint8).tolist()
    cast_case("cast e4m3 saturate", "e4m3", "saturate", "torch float32 -> float8_e4m3fn", ref, data)
    cast_case("cast e4m3 native", "e4m3", "native", "torch float32 -> float8_e4m3fn", ref, data)
    data = np.concatenate([sweep[1], randoms])
    ref = torch.from_numpy(data.copy()).to(torch.float8_e5m2).view(torch.uint8).tolist()
    cast_case("cast e5m2 native", "e5m2", "native", "torch float32 -> float8_e5m2", ref, data)
    cast_case("cast e5m2 saturate", "e5m2", "saturate", "torch float32 -> float8_e5m2", ref, data)
    data = np.concatenate([sweep[2], randoms])
    ref = f32_to_f4_unpacked(torch.from_numpy(data.copy())).tolist()
    cast_case("cast e2m1", "e2m1", "native", "torchao f32_to_f4_unpacked", ref, data)
    data = np.concatenate([sweep[3], randoms])
    ref = f32_to_f6_e2m3_unpacked(torch.from_numpy(data.copy())).tolist()
    cast_case("cast e2m3", "e2m3", "native", "torchao f32_to_f6_e2m3_unpacked", ref, data)
    data = np.concatenate([sweep[4], randoms])
    ref = f32_to_f6_e3m2_unpacked(torch.from_numpy(data.copy())).tolist()
    cast_case("cast e3m2", "e3m2", "native", "torchao f32_to_f6_e3m2_unpacked", ref, data)

    # ---- Decoders: every code of the float8 dtypes ------------------------------------------
    for name, dtype in (("e4m3", torch.float8_e4m3fn), ("e5m2", torch.float8_e5m2)):
        decoded = torch.arange(256, dtype=torch.uint8).view(dtype).to(torch.float32).numpy()
        finite = np.isfinite(decoded)
        data = decoded[finite]
        rows = [words(data)]
        expected = [(None, np.arange(256)[finite].tolist(), words(data))]
        got = run_oracle(args.oracle, ["cast", name, "native"], rows)
        report.add(f"decode {name}", f"torch {name} -> float32, all finite codes",
                   f"Codec.ofFormat .{name} decode", rows, expected, got)

    import torchao
    meta = {
        "torch": torch.__version__, "numpy": np.__version__,
        "torchao": getattr(torchao, "__version__", "unknown"),
        "seed": args.seed, "count": args.count,
    }
    with open(args.out, "w") as handle:
        json.dump({"meta": meta, "cases": report.cases}, handle, indent=1)
    print("written", args.out)


if __name__ == "__main__":
    main()
