#!/usr/bin/env python3
"""Write Exact.v: Coq's Z, Q and bignums on operands of the sizes of the Lean table.

usage: gen.py OUT.v [SIZE...]

Every row runs one operation in a loop under `vm_compute` and prints a line
`ROW name bits iterations`, followed by Coq's `Finished transaction in … secs`. `run.sh` divides.
The operands are pseudo-random numbers of exactly the given number of bits, written in
hexadecimal.
"""
import random
import sys

out = sys.argv[1]
sizes = [int(s) for s in sys.argv[2:]] or [64, 1024, 4096, 16384, 100000]
random.seed(20261115)


def rnd(bits):
    return random.getrandbits(bits) | (1 << (bits - 1))


lines = [
    "Require Import ZArith QArith Zpow_facts.",
    "Require Import Bignums.BigZ.BigZ.",
    "Open Scope Z_scope.",
    "Fixpoint loop (n : nat) (f : Z -> Z) (x : Z) : Z :=",
    "  match n with O => x | S k => loop k f (f x) end.",
    "Fixpoint loopB (n : nat) (f : bigZ -> bigZ) (x : bigZ) : bigZ :=",
    "  match n with O => x | S k => loopB k f (f x) end.",
    "Fixpoint loopQ (n : nat) (f : Q -> Q) (x : Q) : Q :=",
    "  match n with O => x | S k => loopQ k f (f x) end.",
    "Definition low (x : Z) : Z := Z.land x 255.",
]


def row(name, bits, iters, term):
    lines.append(f'Goal True. idtac "ROW {name} {bits} {iters}". Abort.')
    lines.append(f"Time Eval vm_compute in ({term}).")


# Iterations per row and size, chosen so that each row takes a few seconds at most. Coq's `Z` is a
# list of binary digits, so one product of two numbers of 16,384 bits takes about twenty seconds.
ITERS = {
    "Z.add": {64: 20000, 1024: 20000, 4096: 5000, 16384: 1000, 100000: 200},
    "Z.mul+Z.modulo": {64: 2000, 1024: 20, 4096: 2, 16384: 1},
    "Z.leb": {64: 20000, 1024: 20000, 4096: 5000, 16384: 1000, 100000: 200},
    "Z.gcd": {64: 1, 1024: 1, 4096: 1, 16384: 1},
    "Z.log2": {64: 1, 1024: 1, 4096: 1, 16384: 1, 100000: 1},
    "BigZ.add": {64: 20000, 1024: 20000, 4096: 20000, 16384: 2000, 100000: 2000},
    "BigZ.mul+BigZ.modulo": {64: 2000, 1024: 2000, 4096: 200, 16384: 20, 100000: 2},
    "Q: x + b < c, unreduced": {64: 200, 1024: 20, 4096: 2, 16384: 1},
    "Qred": {64: 1, 1024: 1, 4096: 1, 16384: 1},
    "Zpow_mod": {64: 1, 256: 1, 512: 1},
}

for bits in sorted(set(sizes) | {256, 512}):
    a, b, m = rnd(bits), rnd(bits), rnd(bits)
    lines.append(f"Definition a{bits} : Z := {hex(a)}.")
    lines.append(f"Definition b{bits} : Z := {hex(b)}.")
    lines.append(f"Definition m{bits} : Z := {hex(m)}.")
    lines.append(f"Definition A{bits} : bigZ := Eval vm_compute in BigZ.of_Z a{bits}.")
    lines.append(f"Definition B{bits} : bigZ := Eval vm_compute in BigZ.of_Z b{bits}.")
    lines.append(f"Definition M{bits} : bigZ := Eval vm_compute in BigZ.of_Z m{bits}.")
    terms = {
        "Z.add": "low (loop {n} (fun x => Z.land (x + b{w}) m{w}) a{w})",
        "Z.mul+Z.modulo": "low (loop {n} (fun x => (x * b{w}) mod m{w}) a{w})",
        "Z.leb": "low (loop {n} (fun x => if Z.leb x b{w} then x + 1 else x - 1) a{w})",
        "Z.gcd": "low (Z.gcd a{w} b{w})",
        "Z.log2": "Z.log2 a{w}",
        "BigZ.add": "low (BigZ.to_Z (loopB {n} (fun x => BigZ.land (BigZ.add x B{w}) M{w}) A{w}))",
        "BigZ.mul+BigZ.modulo":
            "low (BigZ.to_Z (loopB {n} (fun x => BigZ.modulo (BigZ.mul x B{w}) M{w}) A{w}))",
        "Q: x + b < c, unreduced":
            "low (Qnum (loopQ {n} (fun x => if Qlt_le_dec (Qplus x (Qmake b{w} 12345)) "
            "(Qmake m{w} 7) then Qmake (Qnum x mod m{w}) (Qden x) "
            "else Qmake (Qnum x mod m{w} + 1) (Qden x)) (Qmake a{w} (Z.to_pos b{w}))))",
        "Qred": "low (Qnum (Qred (Qmake a{w} (Z.to_pos b{w}))))",
        "Zpow_mod": "low (Zpow_mod a{w} b{w} m{w})",
    }
    for name, term in terms.items():
        if bits in ITERS[name] and (bits in sizes or name == "Zpow_mod"):
            row(name, bits, ITERS[name][bits], term.format(n=ITERS[name][bits], w=bits))

open(out, "w").write("\n".join(lines) + "\n")
