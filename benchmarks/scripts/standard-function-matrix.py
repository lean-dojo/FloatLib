#!/usr/bin/env python3
"""Generate standard-name native and kernel calls from one operation catalog.

Only benchmark clients are generated. The library remains descriptor-parametric.
Native clients select a statically instantiated width, with optional case bounds
for resuming an interrupted run. Kernel clients use the same observed expression.
"""
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
WIDTHS = [8, 16, 32, 64, 128, 256, 1024, 4096]


def posit_catalog():
    prefix = "FloatLib.Floats.ExecFloat.Posit."
    rows = []

    def add(name, expression, declaration=None):
        rows.append(dict(label=name, expression=expression,
                         declaration=prefix + (declaration or name)))

    def scalar(name, arguments):
        add(name, f"ExecFloat.Posit.toNatBits (ExecFloat.Posit.{name} {arguments})")

    add("input", "ExecFloat.Posit.toNatBits s.x + ExecFloat.Posit.toNatBits s.y")
    rows[-1]["declaration"] = None
    add("quire-input", "s.q.toNatBits + s.r.toNatBits")
    rows[-1]["declaration"] = None
    for name in ["addition", "subtraction", "multiplication", "division"]:
        scalar(name, "s.x s.y")
    scalar("negate", "s.x")
    scalar("sqrt", "s.x")
    for suffix in ["Equal", "NotEqual", "Greater", "GreaterEqual", "Less", "LessEqual"]:
        name = "compare" + suffix
        add(name, f"(ExecFloat.Posit.{name} s.x s.z).toNat")
    source = (ROOT / "FloatLib/Floats/Formats/Posit/Configured/StandardFunctions.lean").read_text()
    special = {"hypot", "pow", "arcTan2", "arcTan2Pi", "fMM", "compound", "rootn",
               "display", "parse", "ofFixedInt", "toFixedInt", "ofUnsigned", "toUnsigned"}
    for name in re.findall(r"^posit_reference (\w+)$", source, re.M):
        if name not in special:
            scalar(name, "s.y" if name == "arcCosH" else "s.x")
    for name in ["hypot", "pow", "arcTan2", "arcTan2Pi"]:
        scalar(name, "s.x s.y")
    scalar("fMM", "s.x s.y s.z")
    for name in ["compound", "rootn"]:
        scalar(name, "s.x 3")
    add("display", "observeString (ExecFloat.Posit.display s.x)")
    add("parse", "observeParse (width := width) (valid := by decide) "
                 '(ExecFloat.Posit.parse "0.812345678901234567890123456789")')
    scalar("ofFixedInt", "(Numerics.Representations.FixedInt.ofInt (width := width) 17)")
    scalar("ofUnsigned", "(BitVec.ofNat width 17)")
    # The destination annotation fixes the independent configured carrier.
    for row in rows[-2:]:
        row["expression"] = row["expression"][:-1] + " : ExecFloat.Posit width (by decide))"
    add("toFixedInt", "(ExecFloat.Posit.toFixedInt width s.y).toNatBits")
    add("toUnsigned", "(ExecFloat.Posit.toUnsigned width s.y).toNat")
    add("pₘToₙ-widen", "ExecFloat.Posit.toNatBits "
        "(ExecFloat.Posit.pₘToₙ s.x : ExecFloat.Posit (2 * width) (by decide))", "pₘToₙ")
    add("pₘToₙ-narrow", "ExecFloat.Posit.toNatBits "
        "(ExecFloat.Posit.pₘToₙ s.x : ExecFloat.Posit (width / 2) (by decide))", "pₘToₙ")
    qargs = {
        "pToQ": "s.x", "qNegate": "s.q", "qAbs": "s.q",
        "qAddP": "s.q s.x", "qSubP": "s.q s.x",
        "qAddQ": "s.q s.r", "qSubQ": "s.q s.r",
        "qMulAdd": "s.q s.x s.y", "qMulSub": "s.q s.x s.y",
    }
    for name, arguments in qargs.items():
        add("Quire." + name, f"(ExecFloat.Posit.Quire.{name} {arguments}).toNatBits")
    add("Quire.qToP", "ExecFloat.Posit.toNatBits "
        "(ExecFloat.Posit.Quire.qToP s.q : ExecFloat.Posit width (by decide))")
    add("cast-fromIEEE32", "observeOutcome ExecFloat.Posit.toNatBits "
        "(s.ieee.cast (target := ExecFloat.Posit width (by decide)) "
        "(mode := ({} : ExecFloat.NoRoundingDirection)))")
    rows[-1]["declaration"] = "FloatLib.Floats.ExecFloat.cast"
    for mode in ["nearest", "nearestAway", "towardZero", "up", "down", "away"]:
        add("cast-toIEEE32-" + mode, "observeOutcome ExecFloat.Binary.toNatBits "
            f"(s.x.cast (target := Binary32) (mode := Numerics.RoundingMode.{mode}))")
        rows[-1]["declaration"] = "FloatLib.Floats.ExecFloat.cast"
    assert len(rows) == len({row["label"] for row in rows})
    return rows


def p3109_catalog():
    public = "FloatLib.Floats.ExecFloat.P3109."
    internal = "FloatLib.Floats.Formats.P3109."
    rows = []

    def add(name, expression, declaration=None):
        rows.append(dict(label=name, expression=expression,
                         declaration=declaration or public + name))

    def scalar(name, arguments, qualifier="ExecFloat.P3109", declaration=None):
        add(name, f"ExecFloat.P3109.toNatBits ({qualifier}.{name} {arguments})", declaration)

    add("input", "s.x.toNatBits + s.y.toNatBits")
    rows[-1]["declaration"] = None
    add("block-input", "observeBlock s.a + observeBlock s.b")
    rows[-1]["declaration"] = None
    arithmetic = ROOT / "FloatLib/Floats/Formats/P3109/Arithmetic"
    unary = ["Negate", "Abs", "Recip", "Sqrt", "RSqrt"]
    binary = ["CopySign", "Add", "Subtract", "Multiply", "Divide", "Hypot"]
    extrema_source = (arithmetic / "Extrema/Runtime.lean").read_text()
    extrema_source = extrema_source.split("namespace FloatLib.Floats.ExecFloat.P3109")[1]
    extrema = re.findall(r"def ((?:Minimum|Maximum)\w*) \(", extrema_source)
    for name in unary:
        scalar(name, "s.x")
    for name in binary + extrema:
        scalar(name, "s.x s.y")
    for name in ["FMA", "FAA"]:
        scalar(name, "s.x s.y s.z")
    scalar("Clamp", "s.x s.z s.y")
    functions = (ROOT / "FloatLib/Floats/Formats/P3109/Functions/Runtime.lean").read_text()
    unary_functions = re.findall(r"^unary_function (\w+) :=", functions, re.M)
    for name in unary_functions:
        scalar(name, "s.y" if name == "ArcCosh" else "s.x")
    for name in ["ArcTan2", "ArcTan2Pi"]:
        scalar(name, "s.x s.y")
    for name in re.findall(r"def (Compare\w+) \(", extrema_source) + ["TotalOrder"]:
        add(name, f"(ExecFloat.P3109.{name} s.x s.z).toNat")
    for name in ["IsZero", "IsNaN", "IsInfinite", "IsFinite", "IsSignMinus", "IsOne",
                 "IsNormal", "IsSubnormal"]:
        add(name, f"(ExecFloat.P3109.{name} s.x).toNat")
    add("Class", "observeClass (ExecFloat.P3109.Class s.x)")
    for name in ["NextGreaterThan", "NextLessThan"]:
        scalar(name, "s.x")
    for name in ["BitwidthOf", "PrecisionOf", "ExponentBitwidthOf",
                 "TrailingSignificandBitwidthOf", "ExponentBiasOf"]:
        add(name, f"Formats.P3109.Format.{name} f", internal + "Format." + name)
    for name, case in [("SignednessOf", "signed"), ("DomainOf", "extended")]:
        add(name, f"(decide (Formats.P3109.Format.{name} f = .{case})).toNat",
            internal + "Format." + name)
    for name in ["MaxFiniteOf", "MinFiniteOf", "MinPositiveOf", "MaxSubnormalOf", "MinNormalOf"]:
        add(name, f"(Formats.P3109.Format.{name} f).toNatBits", internal + "Format." + name)
    for name, observer in [("RoundOf", "observeRounding"), ("SatOf", "observeSaturation")]:
        add(name, f"{observer} (Formats.P3109.ProjectionPolicy.{name} {{}})",
            internal + "ProjectionPolicy." + name)
    destination = "(Formats.P3109.Arithmetic.Destination.p3109 f)"
    mixed = "Formats.P3109.Arithmetic.Mixed"
    scalar("Convert", destination + " s.x", mixed, internal + "Arithmetic.Mixed.Convert")
    # The block and scaled schemas have the same three arities.
    block_unary = ["Convert", "Abs", "Negate", "Recip"]
    block_binary = ["CopySign", "Add", "Subtract", "Multiply", "Divide"] + extrema
    block_ternary = ["FMA", "FAA", "Clamp"]
    for names, arguments, scale_args in [
        (block_unary, "s.a", "s.a.scale s.x"),
        (block_binary, "s.a s.b", "s.a.scale s.x s.b.scale s.y"),
        (block_ternary, "s.a s.b s.c", "s.a.scale s.x s.b.scale s.y s.c.scale s.z"),
    ]:
        for name in names:
            if name == "Clamp":
                arguments_here = "s.a s.c s.b"
                scaled_here = "s.a.scale s.x s.c.scale s.z s.b.scale s.y"
            else:
                arguments_here, scaled_here = arguments, scale_args
            block_name, scaled_name = "Block" + name, "Scaled" + name
            add(block_name, f"observeBlock (Formats.P3109.Block.{block_name} "
                f"{destination} blockPolicy {arguments_here} resultScale)",
                internal + "Block." + block_name)
            scalar(scaled_name, f"{destination} {scaled_here}", mixed,
                   internal + "Arithmetic.Mixed." + scaled_name)
    for name in ["Sqrt", "RSqrt"] + unary_functions:
        block_name, scaled_name = "Block" + name, "Scaled" + name
        operand = "s.b" if name == "ArcCosh" else "s.a"
        value = "s.y" if name == "ArcCosh" else "s.x"
        add(block_name, f"observeBlock (Formats.P3109.Block.{block_name} "
            f"f blockPolicy {operand} resultScale)", internal + "Block." + block_name)
        scalar(scaled_name, f"f {operand}.scale {value}", mixed,
               internal + "Arithmetic.Mixed." + scaled_name)
    for name in ["Hypot", "ArcTan2", "ArcTan2Pi"]:
        block_name, scaled_name = "Block" + name, "Scaled" + name
        add(block_name, f"observeBlock (Formats.P3109.Block.{block_name} "
            f"f blockPolicy s.a s.b resultScale)", internal + "Block." + block_name)
        scalar(scaled_name, "f s.a.scale s.x s.b.scale s.y", mixed,
               internal + "Arithmetic.Mixed." + scaled_name)
    for name in ["BlockReduceAdd", "BlockReduceMultiply", "BlockDotProduct"]:
        args = "s.a s.b" if name == "BlockDotProduct" else "s.a"
        scalar(name, f"{destination} {{}} {args}", "Formats.P3109.Block",
               internal + "Block." + name)
    add("ConvertFromBlock", f"observeValues (Formats.P3109.Block.ConvertFromBlock "
        f"{destination} blockPolicy s.a)", internal + "Block.ConvertFromBlock")
    add("ConvertToBlock", f"observeBlock (Formats.P3109.Block.ConvertToBlock "
        f"{destination} blockPolicy s.a.values resultScale)", internal + "Block.ConvertToBlock")
    # Use a P3109 scale destination here so its actual stored word is observable.
    add("ConvertToBlockMaxAbsFinite",
        f"(let result := Formats.P3109.Block.ConvertToBlockMaxAbsFinite {destination} "
        f"{destination} {{}} blockPolicy s.a.values; "
        "result.scale.toNatBits + 2 ^ width * observeValues result.values)",
        internal + "Block.ConvertToBlockMaxAbsFinite")
    assert len(rows) == len({row["label"] for row in rows})
    return rows


def header(family, kernel=False):
    return f"""/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
-- Generated by benchmarks/scripts/standard-function-matrix.py.
import FloatLibBenchmarks.Standards.{family}
{"import FloatLibBenchmarks.Standards.Literal" if kernel else ""}
open FloatLib FloatLib.Floats FloatLibBenchmarks.Standards
open FloatLibBenchmarks.Standards.{family}
set_option maxRecDepth 32768
set_option exponentiation.threshold 131072
"""


def generate(family, output):
    rows = posit_catalog() if family == "Posit" else p3109_catalog()
    output.mkdir(parents=True, exist_ok=True)
    (output / "catalog.json").write_text(json.dumps(
        dict(family=family, widths=WIDTHS, cases=rows), indent=2) + "\n")
    native_root = ROOT / "benchmarks/lean/FloatLibBenchmarks/Standards"
    modules = native_root / (family + "Matrix")
    modules.mkdir(parents=True, exist_ok=True)
    group_size = 12
    for width in WIDTHS:
        native = ["module\n\n", header(family),
                  f"namespace FloatLibBenchmarks.Standards.{family}Matrix.Width{width}\n"]
        for start in range(0, len(rows), group_size):
            native += [
                f"private def width{width}group{start} (first last : Nat) : IO Unit := do\n",
                f"  let width := {width}\n",
                f"  let inputs := (List.range 8).toArray.map (sample width (by decide))\n",
            ]
            if family == "P3109":
                native.append("  let f := format width (by decide)\n")
            for index in range(start, min(start + group_size, len(rows))):
                row = rows[index]
                binding = "s" if "s." in row["expression"] else "_s"
                native += [f"  if first ≤ {index} && {index} < last then\n",
                           f'    measure "{family}" "{row["label"]}" width inputs '
                           f'fun {binding} => {row["expression"]}\n']
        native += ["/-- Run the selected standard-operation interval at this static width. -/\n",
                   "public def run (first last : Nat) : IO Unit := do\n"]
        for start in range(0, len(rows), group_size):
            native.append(f"  width{width}group{start} first last\n")
        native.append(f"end FloatLibBenchmarks.Standards.{family}Matrix.Width{width}\n")
        (modules / f"Width{width}.lean").write_text("".join(native))
    native = [
        "module\n\n",
        "-- Generated by benchmarks/scripts/standard-function-matrix.py.\n",
        *[f"import FloatLibBenchmarks.Standards.{family}Matrix.Width{width}\n"
          for width in WIDTHS],
        "/-- Run the selected standard timing cases. -/\npublic def main (args : List String) : IO Unit := do\n",
        '  let width := (args[0]?.getD "8").toNat!\n',
        '  let first := (args[1]?.getD "0").toNat!\n',
        f'  let last := (args[2]?.getD "{len(rows)}").toNat!\n',
    ]
    for width in WIDTHS:
        native.append(f"  if width == {width} then\n")
        native.append(f"    FloatLibBenchmarks.Standards.{family}Matrix.Width{width}.run first last\n")
    (native_root / f"{family}Matrix.lean").write_text("".join(native))
    for width in WIDTHS:
        lines = [header(family, kernel=True), f"private def width : Nat := {width}\n"]
        if family == "P3109":
            lines.append("private def f := format width (by decide)\n")
        for index, row in enumerate(rows):
            expression = row["expression"]
            sample_term = f"{family.lower()}_sample% {width} 0"
            binding = "s" if "s." in expression else "_s"
            sample_type = "Sample width (by decide)"
            lines += [
                f'#print "MATRIX_KERNEL {family} {row["label"]} width={width} case={index}"\n',
                f"#kernel_cost rewritten (let {binding} : {sample_type} := {sample_term}; "
                + expression + ")\n",
            ]
        (output / f"Kernel{width}.lean").write_text("".join(lines))
    print(json.dumps(dict(family=family, cases=len(rows), rows=len(rows) * len(WIDTHS))))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--family", choices=["Posit", "P3109"], required=True)
    parser.add_argument("--generate", type=Path, required=True)
    args = parser.parse_args()
    generate(args.family, args.generate)
