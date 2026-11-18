#!/usr/bin/env python3
"""Generate direct standard-name timing calls from the N1169 declaration schemas.

No generated library definitions or width-specific implementations are introduced.
The native and kernel files come from the same operation expressions.
"""
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
WIDTHS = [8, 16, 32, 64, 128, 256, 1024, 4096]
PREFIX = "FloatLib.Floats.Formats.FixedPoint.Embedded."


def catalog() -> list[dict]:
    source = (ROOT / "FloatLib/Floats/Formats/FixedPoint/Embedded/Standard.lean").read_text()
    rows = []

    def add(label, kind, length, signed, expression, *, minimum=0, declaration=None):
        typ = f"⟨.{kind}, .{length}, {str(signed).lower()}, false⟩"
        rows.append(dict(label=label, type=typ, signed=signed,
                         expression=expression.replace(".nearestEven", "rounding"), minimum=minimum,
                         declaration=PREFIX + (declaration or label)))

    pattern = r"^stdfix (\w+) (\w+) (\w+) (\w+) for \.(\w+), \.(\w+), (true|false)$"
    for match in re.finditer(pattern, source, re.M):
        rnd, count, bits, from_bits, kind, length, sign = match.groups()
        args = kind, length, sign == "true"
        add(rnd, *args, f"observe ({rnd} l .even s.x 2)")
        add(count, *args, f"{count} l s.x")
        add(bits, *args, f"observeInt ({bits} l s.x)")
        add(from_bits, *args, f"observe ({from_bits} l (bitsfx s.x))")
    for name, kind, length in re.findall(
            r"^stdfix_abs (\w+) for \.(\w+), \.(\w+)$", source, re.M):
        add(name, kind, length, True, f"(Format.toBits ({name} l s.x)).toNat")
    pattern = (r"^stdfix_mixed (\w+) (\w+) (\w+) (\w+) for "
               r"\.(\w+), \.(\w+), (true|false)$")
    for match in re.finditer(pattern, source, re.M):
        mul, div, quotient, integer, kind, length, sign = match.groups()
        args = kind, length, sign == "true"
        add(mul, *args, f"observeInteger ({mul} l (.signed width) 17 s.x)")
        add(div, *args, f"observeInteger ({div} l (.signed width) 17 s.y)")
        add(quotient, *args, f"observe ({quotient} l .nearestEven 17 31)")
        add(integer, *args, f"observeInteger ({integer} l (.signed width) s.x s.y)")
    for name, kind, length, sign in re.findall(
            r"^stdfix_text (\w+) for \.(\w+), \.(\w+), (true|false)$", source, re.M):
        add(name, kind, length, sign == "true", f"observeText ({name} l .nearestEven text)")

    # Operators are measured on both kinds and signs; the exact names remain in the manifest.
    for kind in ["fract", "accum"]:
        for signed in [True, False]:
            args = kind, "default", signed
            suffix = f"-{kind}-{'signed' if signed else 'unsigned'}"

            def op(name, expression):
                add(name + suffix, *args, expression, declaration=name)

            op("input", "(Format.toBits s.x).toNat + (Format.toBits s.y).toNat")
            for symbol in ["+", "-", "*", "/"]:
                op(f"Binary.«{symbol}»",
                   f"observe (Binary.«{symbol}» l environment t t s.x s.y)")
                op(f"Assignment.«{symbol}=»",
                   f"observe (Assignment.«{symbol}=» l environment t t s.x s.y)")
                op(f"IntegerLeft.«{symbol}»",
                   f"observe (IntegerLeft.«{symbol}» .nearestEven .SAT 17 s.x)")
                op(f"IntegerRight.«{symbol}»",
                   f"observe (IntegerRight.«{symbol}» .nearestEven .SAT s.x 17)")
                op(f"Assignment.IntegerLeft.«{symbol}=»",
                   f"observeInteger (Assignment.IntegerLeft.«{symbol}=» "
                   f"(.signed width) .nearestEven .SAT 17 s.x)")
                op(f"Assignment.IntegerRight.«{symbol}=»",
                   f"observe (Assignment.IntegerRight.«{symbol}=» .nearestEven .SAT s.x 17)")
            for symbol in ["<<", ">>"]:
                op(f"Binary.«{symbol}»",
                   f"observe (Binary.«{symbol}» .nearestEven .SAT s.x 2)")
                op(f"Assignment.«{symbol}=»",
                   f"observe (Assignment.«{symbol}=» .nearestEven .SAT s.x 2)")
            for symbol in ["++", "--"]:
                op(f"Prefix.«{symbol}»", f"observe (Prefix.«{symbol}» .nearestEven .SAT s.x)")
                op(f"Postfix.«{symbol}»",
                   f"(match Postfix.«{symbol}» .nearestEven .SAT s.x with "
                   "| none => 0 | some (old, new) => "
                   "1 + (Format.toBits old).toNat + (Format.toBits new).toNat)")
            op("Unary.«+»", "(Format.toBits (Unary.«+» s.x)).toNat")
            op("Unary.«-»", "observe (Unary.«-» .nearestEven .SAT s.x)")
            op("Unary.«!»", "observeInt (Unary.«!» s.x)")
            for symbol in ["==", "!=", "<", "<=", ">", ">="]:
                op(f"Compare.«{symbol}»", f"(Compare.«{symbol}» s.x s.y).toNat")
                op(f"IntegerLeft.«{symbol}»",
                   f"(IntegerLeft.«{symbol}» 17 s.x).toNat")
                op(f"IntegerRight.«{symbol}»",
                   f"(IntegerRight.«{symbol}» s.x 17).toNat")
            op("Assignment.«=»", "observe (Assignment.«=» f .nearestEven .SAT (Format.decode s.x))")
            op("convert", "observe (convert f .nearestEven .SAT (mkRat 17 31))")
            op("toInteger", "observeInteger (toInteger (.signed width) (Format.decode s.x))")
            spec = ("r" if kind == "fract" else "k") if signed else (
                "R" if kind == "fract" else "K")
            op("Formatted.fprintf",
               f"(Formatted.fprintf l .{spec} .default .nearestEven {{ precision := some 6 }} s.x).length")
            op("Formatted.fscanf",
               f"observeScan (Formatted.fscanf l .{spec} .default .nearestEven none text)")
            op("Constant.translate",
               "observe (Constant.translate l .even "
               "{ spelling := \"0.5\", type := t, value := mkRat 1 2, hexadecimal := false })")
            constant_suffix = ("" if signed else "u") + ("r" if kind == "fract" else "k")
            op("Constant.parse", f'observeLiteral (Constant.parse "0.5{constant_suffix}")')

    # Macros and typedef descriptors have separate constant-result timing rows.
    for stem, integer, kind, length, sign in re.findall(
            r"^stdfix_limits (\w+) (\w+) for \.(\w+), \.(\w+), (true|false)$",
            source, re.M):
        args = kind, length, sign == "true"
        add(stem + "_FBIT", *args, f"{stem}_FBIT l")
        add(stem + "_MAX", *args, f"(Format.toBits ({stem}_MAX l)).toNat")
        add(stem + "_EPSILON", *args,
            f"(Format.toBits ({stem}_EPSILON l (layout_valid width hw))).toNat", minimum=48)
        add(integer, *args, f"observeInt (({integer} l).maxValue)")
    for name, kind, length in re.findall(
            r"^stdfix_min (\w+) for \.(\w+), \.(\w+)$", source, re.M):
        add(name, kind, length, True, f"(Format.toBits ({name} l)).toNat")
    for name, length, sign in re.findall(
            r"^stdfix_ibit (\w+) for \.(\w+), (true|false)$", source, re.M):
        add(name, "accum", length, sign == "true", f"{name} l")
    assert len({row["label"] for row in rows}) == len(rows)
    return rows


HEADER = """/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
-- Generated by benchmarks/scripts/fixed-point-matrix.py.
import FloatLibBenchmarks.Standards.FixedPoint
open FloatLib.Numerics FloatLib.Floats.Formats.FixedPoint.Embedded
open FloatLibBenchmarks.Standards.FixedPoint
"""


def generate(output: Path):
    rows = catalog()
    output.mkdir(parents=True, exist_ok=True)
    (output / "catalog.json").write_text(json.dumps(
        dict(widths=WIDTHS, cases=rows), indent=2) + "\n")
    native = ["module\n\n", HEADER]
    groups = [rows[start:start + 16] for start in range(0, len(rows), 16)]
    for index, group in enumerate(groups):
        native += [f"private def group{index} (width : Nat) : IO Unit := do\n",
                   "  let l := layout width\n"]
        for row in group:
            indent = "  "
            if row["minimum"]:
                native.append(f"  if hw : {row['minimum']} ≤ width then\n")
                indent += "  "
            native += [f"{indent}let t : CType := {row['type']}\n",
                       f"{indent}let f := l.format t\n",
                       f'{indent}measure "{row["label"]}" width f fun '
                       f'{"s" if "s." in row["expression"] else "_s"} => {row["expression"]}\n']
    native += ["/-- Run the selected standard timing cases. -/\npublic def main : IO Unit := do\n", f"  for width in {str(WIDTHS)} do\n"]
    native += [f"    group{index} width\n" for index in range(len(groups))]
    (ROOT / "benchmarks/lean/FloatLibBenchmarks/Standards/FixedPointMatrix.lean").write_text(
        "".join(native))
    for width in WIDTHS:
        lines = [HEADER,
                 "set_option maxRecDepth 32768\nset_option exponentiation.threshold 8192\n",
                 f"private def width : Nat := {width}\n",
                 "private def l : Layout := layout width\n"]
        if width >= 48:
            lines.append("private theorem hw : 48 ≤ width := by decide\n")
        for index, row in enumerate(rows):
            if width < row["minimum"]:
                continue
            expression = row["expression"]
            typ = row["type"]
            sample = f"fixed_sample% {width} {str(row['signed']).lower()} 1"
            binding = "s" if "s." in expression else "_s"
            # The unoptimized greatest-index search is linear in the width.
            # At large widths measure the proved logarithm replacement directly.
            tagged_only = width >= 1024 and row["label"].startswith("countls")
            marker = " tagged_only=true" if tagged_only else ""
            mode = "rewritten " if tagged_only else ""
            lines += [f'#print "FIXED_KERNEL {row["label"]} width={width}{marker}"\n',
                      f"#kernel_cost {mode}(let t : CType := " + typ +
                      f"; let f := l.format t; let {binding} : Sample f := {sample}; " +
                      expression + ")\n"]
        (output / f"Kernel{width}.lean").write_text("".join(lines))
    print(json.dumps(dict(cases=len(rows), native_rows=sum(
        width >= row["minimum"] for width in WIDTHS for row in rows)), indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--generate", required=True, type=Path)
    args = parser.parse_args()
    generate(args.generate)
