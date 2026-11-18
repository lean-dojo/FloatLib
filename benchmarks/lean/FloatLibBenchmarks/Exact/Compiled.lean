/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Numerics.Kernel.Ball
import FloatLib.Numerics.Kernel.Root
import FloatLib.Numerics.Packed.Basic
import FloatLib.Numerics.Exact.IntegerRoot.Runtime

/-!
# Compiled code on the rows of the exact kernel table

`exactCompiled` times the operations of `benchmarks/exact/Operations.lean` as compiled code, on
operands of the same sizes, and prints one line `COMPILED tag bits=<size> ns=<time per call>` per
cell. `benchmarks/exact/run.sh compiled` puts these next to the kernel times of the same tags.
The operands are pseudo-random and differ from the kernel run's; only their sizes agree.
-/

open FloatLib.Numerics FloatLib.Numerics.Kernel

namespace FloatLibBenchmarks.Exact.Compiled

/-- A pseudo-random natural number of exactly `bits` bits. -/
def operand (seed bits : Nat) : Nat := Id.run do
  let mut state : UInt64 := seed.toUInt64 * 6364136223846793005 + 1442695040888963407
  let mut value := 0
  for _ in [0:(bits + 63) / 64] do
    state := state ^^^ (state <<< 13)
    state := state ^^^ (state >>> 7)
    state := state ^^^ (state <<< 17)
    value := (value <<< 64) ||| state.toNat
  return (value % 2 ^ bits) ||| 2 ^ (bits - 1)

/-- Time `count` calls of `f` and print the time of one. The first operand changes with every call. -/
@[noinline] def measure (tag : String) (bits count : Nat) (f : Nat → Nat → Nat) (a b : Nat) :
    IO Unit := do
  let start ← IO.monoNanosNow
  let mut sink := 0
  for i in [0:count] do
    sink := sink ^^^ f (a + i) b
  let stop ← IO.monoNanosNow
  IO.println s!"COMPILED {tag} bits={bits} ns={(stop - start) / count} sink={sink % 1000}"

/-- `a ^ e % n` by squaring, one bit of the exponent per step. -/
def powModBinary (a e n : Nat) : Nat := Id.run do
  let mut result := 1 % n
  let mut base := a % n
  let mut exponent := e
  while exponent != 0 do
    if exponent % 2 == 1 then result := result * base % n
    base := base * base % n
    exponent := exponent / 2
  return result

/-- The number of calls for operands of `bits` bits. -/
def calls (bits : Nat) : Nat := max 20 (20000000 / (bits * (Nat.log2 bits + 1)))

end FloatLibBenchmarks.Exact.Compiled

open FloatLibBenchmarks.Exact.Compiled in
/-- Print the table of compiled times. -/
public def main : IO Unit := do
  for bits in [64, 1024, 4096, 16384, 100000] do
    let a := operand 1 bits
    let b := operand 2 bits
    let n := calls bits
    measure "nat/Nat.add" bits (8 * n) (fun x y => x + y) a b
    measure "nat/Nat.mul" bits n (fun x y => x * y) a b
    measure "nat/Nat.div (2n by n bits)" bits n (fun x y => x * y / y) a b
    measure "nat/Nat.gcd" bits (n / 8 + 1) (fun x y => Nat.gcd x y) a b
    measure "nat/Kernel.size" bits (8 * n) (fun x _ => size x) a b
    measure "nat/Kernel.isqrt" bits (n / 16 + 1) (fun x _ => isqrt x) a b
    measure "root/IntegerRoot.newton 3" bits (n / 16 + 1) (fun x _ => IntegerRoot.newton 3 x) a b
    measure "root/IntegerRoot.Seeded.newton 3" bits (n / 16 + 1)
      (fun x _ => IntegerRoot.Seeded.newton 3 x) a b
    measure "int/Signed.mul" bits n (fun x y => (Signed.mul ⟨x, 0⟩ ⟨0, y⟩).minus) a b
    measure "rat/a + b < c (Rat)" bits (n / 8 + 1)
      (fun x y => if mkRat x (y + 1) + mkRat (-(y : Int)) (x + 1) < mkRat x (y + 1) then 1 else 0) a b
    measure "rat/a + b < c (Frac)" bits n
      (fun x y => if Frac.lt (Frac.add ⟨x, 0, y + 1, Nat.succ_pos y⟩ ⟨0, y, x + 1, Nat.succ_pos x⟩)
        ⟨x, 0, y + 1, Nat.succ_pos y⟩ then 1 else 0) a b
    measure "dyad/Dyad.add" bits (4 * n) (fun x y => (Dyad.add ⟨x, 0, 17⟩ ⟨0, y, 5⟩).minus) a b
    measure "ball/Ball.mul" bits n (fun x y => (Ball.mul ⟨x, 0, 3, 17⟩ ⟨0, y, 2, 5⟩).minus) a b
  for bits in [64, 256, 1024, 4096] do
    let a := operand 3 bits
    let e := operand 4 bits
    let modulus := operand 5 bits
    measure "mod/powModWindow 0 (binary)" bits (max 3 (2000000000 / (bits * bits * bits)))
      (fun x y => powModBinary x e y) a modulus
