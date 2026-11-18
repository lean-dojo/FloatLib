#!/usr/bin/env python3
"""Matched kernel loops for Lean's kernel and for Coq with Flocq.

Both sides run the same five loops on the same operands in a binary interchange format with
`prec` significand bits: `count` times `s + x`, `s * y`, `s / y`, `sqrt s` and `s * y + x`
(fused), starting from `x`, where `x` is `floor(2^(prec+2) / 3) / 2^(prec+2)` rounded to the
format and `y = 1 + 2^-20`, to nearest even.

    matched.py gen OUT [FORMAT...]   write OUT/lean/Matched_F.lean and OUT/flocq/F_{vm,lazy}.v
    matched.py table OUT             read OUT/lean/*.log and OUT/flocq/*.log, write
                                     OUT/matched.csv and OUT/matched.md, and check that both
                                     sides computed the same values

The Lean file measures the loops as `float_decide` rewrites them (`#kernel_cost rewritten`).
The Coq files evaluate them with `vm_compute` and with `lazy`. Lean prints the encoding of each
result and Coq prints `mantissa mod 1000003 + exponent`: `table` compares the two.
"""
import csv
import re
import sys
from fractions import Fraction
from pathlib import Path

# name: (exponent bits, fraction bits, loop count for vm_compute, loop count for lazy)
FORMATS = {
    "binary32": (8, 23, 100, 100),
    "binary64": (11, 52, 100, 100),
    "binary128": (15, 112, 100, 100),
    "binary256": (19, 236, 100, 100),
    "binary512": (23, 488, 10, 10),
    "binary1024": (27, 996, 10, 10),
    "binary4096": (35, 4060, 10, 10),
}
OPS = ["add", "mul", "div", "sqrt", "fma"]


def encode(value: Fraction, exp_bits: int, frac_bits: int) -> int:
    """The encoding of a positive normal value rounded to nearest even."""
    prec = frac_bits + 1
    exponent = value.numerator.bit_length() - value.denominator.bit_length()
    if Fraction(2) ** exponent > value:
        exponent -= 1
    scaled = value / Fraction(2) ** (exponent - (prec - 1))
    mantissa = scaled.numerator // scaled.denominator
    rest = scaled - mantissa
    if rest > Fraction(1, 2) or (rest == Fraction(1, 2) and mantissa % 2 == 1):
        mantissa += 1
    if mantissa == 2 ** prec:
        mantissa //= 2
        exponent += 1
    bias = 2 ** (exp_bits - 1) - 1
    return ((exponent + bias) << frac_bits) | (mantissa - 2 ** (prec - 1))


def observation(bits: int, exp_bits: int, frac_bits: int) -> int:
    """What the Coq side prints for the finite value with this encoding."""
    prec = frac_bits + 1
    bias = 2 ** (exp_bits - 1) - 1
    field = (bits >> frac_bits) & (2 ** exp_bits - 1)
    fraction = bits & (2 ** frac_bits - 1)
    if field == 0:
        return fraction % 1000003 + (1 - bias - (prec - 1))
    return (2 ** (prec - 1) + fraction) % 1000003 + (field - bias - (prec - 1))


def lean_source(name: str, exp_bits: int, frac_bits: int, count: int) -> str:
    prec = frac_bits + 1
    x = encode(Fraction(2 ** (prec + 2) // 3, 2 ** (prec + 2)), exp_bits, frac_bits)
    y = encode(Fraction(2 ** 20 + 1, 2 ** 20), exp_bits, frac_bits)
    steps = {
        "add": f"s + KernelPath.ofNat {x}",
        "mul": f"s * KernelPath.ofNat {y}",
        "div": f"s / KernelPath.ofNat {y}",
        "sqrt": "ExecFloat.sqrt s",
        "fma": f"ExecFloat.fma s (KernelPath.ofNat {y}) (KernelPath.ofNat {x})",
    }
    lines = [
        "import FloatLib.Tactic.KernelCost",
        "import FloatLib.Tactic.KernelEval",
        "import FloatLib.Floats.Formats.BinaryInterchange.Configured",
        "import FloatLib.Floats.Formats.BinaryInterchange.Configured.KernelPath",
        "import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Value",
        "open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange",
        "set_option maxRecDepth 1000000",
        f"abbrev T := ExecFloat.Binary (exponentBits := {exp_bits}) (fractionBits := {frac_bits})",
    ]
    for op in OPS:
        lines.append(f'#print "MATCHED {name} {op} {count}"')
        lines.append(
            "#kernel_cost rewritten KernelPath.toNat (Nat.rec (motive := fun _ => T) "
            f"(KernelPath.ofNat {x}) (fun _ s => {steps[op]}) {count})"
        )
    return "\n".join(lines) + "\n"


def coq_source(exp_bits: int, frac_bits: int, count: int, strategy: str) -> str:
    prec = frac_bits + 1
    emax = 2 ** (exp_bits - 1)
    head = f"""From Coq Require Import ZArith.
From Flocq Require Import Core.Core IEEE754.BinarySingleNaN.
Open Scope Z_scope.
Definition prec : Z := {prec}.
Definition emax : Z := {emax}.
#[global] Instance Hprec : Prec_gt_0 prec. Proof. reflexivity. Qed.
#[global] Instance Hmax : Prec_lt_emax prec emax. Proof. reflexivity. Qed.
Definition F := binary_float prec emax.
Definition mk (m e : Z) : F := binary_normalize prec emax Hprec Hmax mode_NE m e false.
Definition x : F := mk (Z.pow 2 (prec + 2) / 3) (- (prec + 2)).
Definition y : F := mk (Z.pow 2 20 + 1) (-20).
Definition obs (s : F) : Z :=
  match s with B754_finite _ m e _ => Z.modulo (Zpos m) 1000003 + e | _ => -1 end.
Fixpoint loop (n : nat) (f : F -> F) (s : F) : F :=
  match n with O => s | S k => loop k f (f s) end.
"""
    steps = {
        "add": "fun s => Bplus mode_NE s x",
        "mul": "fun s => Bmult mode_NE s y",
        "div": "fun s => Bdiv mode_NE s y",
        "sqrt": "fun s => Bsqrt mode_NE s",
        "fma": "fun s => Bfma mode_NE s y x",
    }
    body = "".join(
        f"Timeout 300 Time Eval {strategy} in obs (loop {count} ({steps[op]}) x).\n" for op in OPS
    )
    return head + body


def generate(out: Path, names) -> None:
    (out / "lean").mkdir(parents=True, exist_ok=True)
    (out / "flocq").mkdir(parents=True, exist_ok=True)
    for name in names:
        exp_bits, frac_bits, vm_count, lazy_count = FORMATS[name]
        (out / "lean" / f"Matched_{name}.lean").write_text(
            lean_source(name, exp_bits, frac_bits, vm_count)
        )
        (out / "flocq" / f"{name}_vm.v").write_text(
            coq_source(exp_bits, frac_bits, vm_count, "vm_compute")
        )
        (out / "flocq" / f"{name}_lazy.v").write_text(
            coq_source(exp_bits, frac_bits, lazy_count, "lazy")
        )


def read_lean(log: Path):
    """(op -> microseconds per operation, op -> encoding) from one Lean log."""
    times, values = {}, {}
    op, count = None, 1
    for line in log.read_text(errors="replace").splitlines():
        match = re.search(r"MATCHED (\S+) (\S+) (\d+)", line)
        if match:
            op, count = match.group(2), int(match.group(3))
        match = re.search(r"with the tagged kernel rules: ([0-9.]+) µs", line)
        if match and op:
            times[op] = float(match.group(1)) / count
        match = re.match(r"value: (\d+)", line)
        if match and op:
            values[op] = int(match.group(1))
    return times, values


def read_coq(log: Path, count: int):
    """(op -> microseconds per operation, op -> printed value) from one Coq log.

    A statement that timed out or was killed ends the list: Coq stops at the first error."""
    times, values = {}, {}
    if not log.exists():
        return times, values
    text = log.read_text(errors="replace")
    printed = re.findall(r"=\s*(-?\d+)\s*\n\s*: Z\s*\nFinished transaction in ([0-9.]+) secs", text)
    for op, (value, seconds) in zip(OPS, printed):
        times[op] = float(seconds) * 1e6 / count
        values[op] = int(value)
    return times, values


def table(out: Path) -> int:
    rows, mismatches = [], 0
    for name, (exp_bits, frac_bits, vm_count, lazy_count) in FORMATS.items():
        lean_log = out / "lean" / f"Matched_{name}.log"
        if not lean_log.exists():
            continue
        lean_times, lean_values = read_lean(lean_log)
        vm_times, vm_values = read_coq(out / "flocq" / f"{name}_vm.log", vm_count)
        lazy_times, lazy_values = read_coq(out / "flocq" / f"{name}_lazy.log", lazy_count)
        for op in OPS:
            expected = None
            if op in lean_values:
                expected = observation(lean_values[op], exp_bits, frac_bits)
            agreement = "n/a"
            for values in (vm_values, lazy_values):
                if op in values and expected is not None:
                    if values[op] == expected and agreement != "DIFFERENT":
                        agreement = "same"
                    elif values[op] != expected:
                        agreement = "DIFFERENT"
                        mismatches += 1
            rows.append(
                {
                    "format": name,
                    "bits": exp_bits + frac_bits + 1,
                    "operation": op,
                    "lean_kernel_us": lean_times.get(op),
                    "flocq_vm_us": vm_times.get(op),
                    "flocq_lazy_us": lazy_times.get(op),
                    "values": agreement,
                }
            )
    with open(out / "matched.csv", "w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()),
                                lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)

    def cell(value):
        if value is None:
            return "no result"
        return f"{value:,.0f}" if value >= 10 else f"{value:.1f}"

    lines = [
        "| format | operation | Lean kernel (µs) | Flocq `vm_compute` (µs) | Flocq `lazy` (µs) "
        "| values |",
        "| --- | --- | ---: | ---: | ---: | --- |",
    ]
    for row in rows:
        lines.append(
            f"| {row['format']} | {row['operation']} | {cell(row['lean_kernel_us'])} | "
            f"{cell(row['flocq_vm_us'])} | {cell(row['flocq_lazy_us'])} | {row['values']} |"
        )
    (out / "matched.md").write_text("\n".join(lines) + "\n")
    print("\n".join(lines))
    return 1 if mismatches else 0


def main() -> int:
    if len(sys.argv) < 3 or sys.argv[1] not in ("gen", "table"):
        print(__doc__)
        return 2
    out = Path(sys.argv[2])
    if sys.argv[1] == "gen":
        generate(out, sys.argv[3:] or list(FORMATS))
        return 0
    return table(out)


if __name__ == "__main__":
    sys.exit(main())
