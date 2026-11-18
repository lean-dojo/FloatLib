#!/usr/bin/env python3
"""Write Native.lean: the same closed statements by `decide +kernel` and by `native_decide`.

usage: native.py OUT.lean WORKLOADS.lean

The file is generated, and not kept in the repository, because FloatLib's trust check counts every
use of `native_decide` in a Lean source file. Each statement appears twice, timed by
`#time_command` of `Harness.lean`: tag `native/NAME|kernel` and tag `native/NAME|native`. The packed
rows are read from WORKLOADS.lean so that both files use the same data.
"""
import sys

out, workloads = sys.argv[1], sys.argv[2]
rows = [line for line in open(workloads).read().splitlines()
        if line.startswith(("packed_row rowU256", "packed_row rowV256"))]

STATEMENTS = [
    ("3 ^ (p - 1) % p = 1 for p = 2 ^ 255 - 19",
     "Nat.beq (powMod 3 (2 ^ 255 - 20) (2 ^ 255 - 19)) 1 = true"),
    ("3 ^ (p - 1) % p = 1 for p = 2 ^ 1279 - 1",
     "Nat.beq (powMod 3 (2 ^ 1279 - 2) (2 ^ 1279 - 1)) 1 = true"),
    ("the square root of 2 ^ 2001 + 12345, checked",
     "isRoot 2 (isqrt (2 ^ 2001 + 12345)) (2 ^ 2001 + 12345) = true"),
    ("sum of 1 / k ^ 2 for k ≤ 40 below 1.63, on fractions",
     "Frac.lt (inverseSquares 40) ⟨163, 0, 100, by decide⟩ = true"),
    ("exp (7/5) ≤ 4.0553 on the grid, degree 20, 64 bits",
     "decide ((Enclosure.BinaryGrid.exp (mkRat 7 5) 20 64).hi ≤ mkRat 40553 10000) = true"),
    ("packed row product of 256 lanes with its guards and norm",
     "(Packed.guard 160 60 256 rowU256 && Packed.guard 160 60 256 rowV256 && "
     "Nat.ble (Packed.absSum 160 511 (Int.mul (Packed.toInt 160 256 rowU256) "
     "(Packed.toInt 160 256 rowV256))) (2 ^ 140)) = true"),
]

lines = [
    "import Harness",
    "import FloatLib.Numerics.Kernel.ModProof",
    "import FloatLib.Numerics.Kernel.RootProof",
    "import FloatLib.Numerics.Kernel.FracProof",
    "import FloatLib.Tactic.PackedRow",
    "import FloatLib.Numerics.Enclosure.Elementary.BinaryGridRuntime",
    "open FloatLibBenchmarks.Exact FloatLib.Numerics FloatLib.Numerics.Kernel",
    "set_option maxRecDepth 100000",
    "",
    "/-- `1 + 1/4 + … + 1/n²` on fractions, unreduced. -/",
    "def inverseSquares : Nat → Frac",
    "  | 0 => Frac.ofNat 0",
    "  | n + 1 => Frac.add (inverseSquares n) ⟨1, 0, (n + 1) * (n + 1), Nat.mul_pos (Nat.succ_pos n) (Nat.succ_pos n)⟩",
    "",
] + rows + [""]
for name, statement in STATEMENTS:
    for label, tactic in (("kernel", "decide +kernel"), ("native", "native_decide")):
        lines.append(f'#time_command "native/{name}|{label}" in')
        lines.append(f"example : {statement} := by {tactic}")
    lines.append("")
open(out, "w").write("\n".join(lines))
