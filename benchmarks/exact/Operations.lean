/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
import Harness
import FloatLib.Numerics.Kernel.Ball
import FloatLib.Numerics.Kernel.Bisection
import FloatLib.Numerics.Kernel.CBall
import FloatLib.Numerics.Kernel.CFix
import FloatLib.Numerics.Kernel.Mod
import FloatLib.Numerics.Kernel.Multiplicative
import FloatLib.Numerics.Kernel.Q
import FloatLib.Numerics.Kernel.Root
import FloatLib.Numerics.Kernel.Seq
import FloatLib.Numerics.Kernel.Strict
import FloatLib.Numerics.Exact.SignedRat
import Mathlib.Data.Nat.Digits.Defs

/-!
# Kernel cost of one exact operation, by type and size

Each row is one operation on operands of the given number of bits, timed in Lean's kernel by
`#kernel_op` (see `Harness.lean`). The rows come in pairs: the operation as core Lean or FloatLib
defines it, and the kernel form of `FloatLib.Numerics.Kernel`. `benchmarks/exact/run.sh` turns
the output into the tables of `benchmarks/results/exact/`. The operations that FloatLib defines
outside this layer (intervals, elementary enclosures, integer roots) are in `Baseline.lean`.
-/

open FloatLibBenchmarks.Exact
open FloatLib.Numerics FloatLib.Numerics.Kernel

/-! ## Natural numbers -/
#kernel_op "nat/Nat.add" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 32) fun a b : Nat => Nat.add a b
#kernel_op "nat/a + b" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 32) fun a b : Nat => a + b
#kernel_op "nat/Nat.mul" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 32) fun a b : Nat => Nat.mul a b
#kernel_op "nat/a * b" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 32) fun a b : Nat => a * b
#kernel_op "nat/Nat.div (2n by n bits)" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 32) fun a b c : Nat => Nat.div (Nat.mul a b) c
#kernel_op "nat/Nat.gcd" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 8) fun a b : Nat => Nat.gcd a b
#kernel_op "nat/Nat.ble" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 32) fun a b : Nat => Nat.ble a b
#kernel_op "nat/decide (a ≤ b)" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 32) fun a b : Nat => decide (a ≤ b)
#kernel_op "nat/Nat.log2" (sizes := [64, 1024, 4096]) (count := 4) fun a : Nat => Nat.log2 a
#kernel_op "nat/Kernel.size" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 16) fun a : Nat => size a
#kernel_op "nat/Nat.testBit" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 32) fun a : Nat => Nat.testBit a 40
#kernel_op "nat/Kernel.testBit" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 32) fun a : Nat => testBit a 40

#kernel_op "nat/(Nat.digits 2 n).sum" (sizes := [64, 1024]) (count := 4) fun a : Nat => (Nat.digits 2 a).sum
#kernel_op "nat/Kernel.popCount" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 4) fun a : Nat => popCount a
#kernel_op "nat/Nat.sqrt" (sizes := [64, 1024, 4096]) (count := 2) (reps := 1) fun a : Nat => Nat.sqrt a
#kernel_op "nat/Kernel.isqrt" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 4) fun a : Nat => isqrt a
#kernel_op "nat/Kernel.isRoot 3" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 8) fun a b : Nat => isRoot 3 a (Nat.mul (Nat.mul a a) (Nat.add a b))

/-! ## Integers -/
#kernel_op "int/a + b" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 32) fun a b : Nat => Z.natAbs (Int.ofNat a + Int.negSucc b)
#kernel_op "int/Z.add" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 32) fun a b : Nat => Z.natAbs (Z.add (Int.ofNat a) (Int.negSucc b))
#kernel_op "int/a * b" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 32) fun a b : Nat => Z.natAbs (Int.ofNat a * Int.negSucc b)
#kernel_op "int/Z.mul" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 32) fun a b : Nat => Z.natAbs (Z.mul (Int.ofNat a) (Int.negSucc b))
#kernel_op "int/decide (a ≤ b)" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 32) fun a b : Nat => decide (Int.negSucc a ≤ Int.ofNat b)
#kernel_op "int/Int.ble'" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 32) fun a b : Nat => Int.ble' (Int.negSucc a) (Int.ofNat b)
#kernel_op "int/a / b" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 32) fun a b c : Nat => Z.natAbs (Int.negSucc (a * b) / Int.ofNat c)
#kernel_op "int/Z.ediv" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 32) fun a b c : Nat => Z.natAbs (Z.ediv (Int.negSucc (a * b)) (Int.ofNat c))
#kernel_op "int/Signed.mul" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 32) fun a b : Nat => Signed.natAbs (Signed.mul ⟨a, 0⟩ ⟨0, b⟩)
#kernel_op "int/y² = x³ + a x + b (Int)" (sizes := [64, 1024, 4096]) (count := 32) fun x y a b : Nat =>
  decide ((Int.ofNat y) * (Int.ofNat y) = (Int.ofNat x) * (Int.ofNat x) * (Int.ofNat x) + (Int.negSucc a) * (Int.ofNat x) + (Int.ofNat b))
#kernel_op "int/y² = x³ + a x + b (Z)" (sizes := [64, 1024, 4096]) (count := 32) fun x y a b : Nat =>
  Int.beq' (Z.mul (Int.ofNat y) (Int.ofNat y)) (Z.add (Z.add (Z.mul (Z.mul (Int.ofNat x) (Int.ofNat x)) (Int.ofNat x)) (Z.mul (Int.negSucc a) (Int.ofNat x))) (Int.ofNat b))

/-! ## Rationals: the core `Rat` rows include building the two operands with `mkRat` -/
#kernel_op "rat/mkRat (two operands)" (sizes := [64, 1024, 4096, 16384]) (count := 8) fun a b c d : Nat =>
  Nat.add (mkRat (Int.ofNat a) b).den (mkRat (Int.negSucc c) d).den
#kernel_op "rat/a + b < c (Rat)" (sizes := [64, 1024, 4096, 16384]) (count := 8) fun a b c d : Nat =>
  decide (mkRat (Int.ofNat a) b + mkRat (Int.negSucc c) d < mkRat (Int.ofNat a) b)
#kernel_op "rat/a * b < c (Rat)" (sizes := [64, 1024, 4096, 16384]) (count := 8) fun a b c d : Nat =>
  decide (mkRat (Int.ofNat a) b * mkRat (Int.negSucc c) d < mkRat (Int.ofNat a) b)
#kernel_op "rat/a + b < c (Frac)" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 8) fun a b c d : Nat =>
  Frac.lt (Frac.add ⟨a, 0, Nat.succ b, Nat.succ_pos _⟩ ⟨0, c, Nat.succ d, Nat.succ_pos _⟩) ⟨a, 0, Nat.succ b, Nat.succ_pos _⟩
#kernel_op "rat/a * b < c (Frac)" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 8) fun a b c d : Nat =>
  Frac.lt (Frac.mul ⟨a, 0, Nat.succ b, Nat.succ_pos _⟩ ⟨0, c, Nat.succ d, Nat.succ_pos _⟩) ⟨a, 0, Nat.succ b, Nat.succ_pos _⟩
#kernel_op "rat/Frac.normalize" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 8) fun a b : Nat =>
  (Frac.normalize ⟨a, 0, Nat.succ b, Nat.succ_pos _⟩).den

/-! ## Core `Rat` with the kernel functions `Q`: the operands are built by `Q.mk` -/
#kernel_op "rat/Q.mk (two operands)" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 8) fun a b c d : Nat =>
  Nat.add (Q.mk (Int.ofNat a) b).den (Q.mk (Int.negSucc c) d).den
#kernel_op "rat/a + b < c (Q)" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 8) fun a b c d : Nat =>
  Q.lt (Q.add (Q.mk (Int.ofNat a) b) (Q.mk (Int.negSucc c) d)) (Q.mk (Int.ofNat a) b)
#kernel_op "rat/a * b < c (Q)" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 8) fun a b c d : Nat =>
  Q.lt (Q.mul (Q.mk (Int.ofNat a) b) (Q.mk (Int.negSucc c) d)) (Q.mk (Int.ofNat a) b)
#kernel_op "rat/a ^ 21 (Rat)" (sizes := [64, 1024]) (count := 4) fun a b : Nat => ((mkRat (Int.negSucc a) b) ^ 21).den
#kernel_op "rat/a ^ 21 (Q)" (sizes := [64, 1024, 4096]) (count := 4) fun a b : Nat => (Q.pow (Q.mk (Int.negSucc a) b) 21).den
#kernel_op "rat/SignedRat a + b" (sizes := [64, 1024]) (count := 4) fun a b c d : Nat =>
  (FloatLib.Numerics.SignedRat.add (.ofRat (mkRat (Int.ofNat a) b)) (.ofRat (mkRat (Int.negSucc c) d))).value.den
#kernel_op "rat/SignedRat a * b" (sizes := [64, 1024]) (count := 4) fun a b c d : Nat =>
  (FloatLib.Numerics.SignedRat.mul (.ofRat (mkRat (Int.ofNat a) b)) (.ofRat (mkRat (Int.negSucc c) d))).value.den

/-! ## Dyadic numbers `(plus - minus) / 2 ^ scale` and balls of this layer -/
#kernel_op "dyad/Dyad.add" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 16) fun a b : Nat => (Dyad.add ⟨a, 0, 17⟩ ⟨0, b, 5⟩).minus
#kernel_op "dyad/Dyad.mul" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 16) fun a b : Nat => (Dyad.mul ⟨a, 0, 17⟩ ⟨0, b, 5⟩).minus
#kernel_op "dyad/Dyad.lt" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 16) fun a b : Nat => Dyad.lt ⟨a, 0, 17⟩ ⟨b, 0, 5⟩
#kernel_op "dyad/Dyad.roundDown" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 16) fun a : Nat => (Dyad.roundDown ⟨0, a, 60⟩ 30).minus
#kernel_op "dyad/Dyad.trimDown 53" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 16) fun a : Nat => (Dyad.trimDown ⟨0, a, 60⟩ 53).minus
#kernel_op "ball/Ball.add" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 16) fun a b : Nat => (Ball.add ⟨a, 0, 3, 17⟩ ⟨0, b, 2, 5⟩).minus
#kernel_op "ball/Ball.mul" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 16) fun a b : Nat => (Ball.mul ⟨a, 0, 3, 17⟩ ⟨0, b, 2, 5⟩).minus
#kernel_op "ball/Ball.mul, round 64" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 16) fun a b : Nat => ((Ball.mul ⟨a, 0, 3, 64⟩ ⟨0, b, 2, 64⟩).round 64).minus
#kernel_op "ball/Ball.le" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 16) fun a b : Nat => Ball.le ⟨a, 0, 3, 17⟩ ⟨b, 0, 2, 5⟩
#kernel_op "ball/Ball.inv, near one, as many digits" (sizes := [64]) (count := 16) fun a : Nat => (Ball.inv ⟨a, 0, 3, 64⟩ 64).plus
#kernel_op "ball/Ball.inv, near one, as many digits" (sizes := [1024]) (count := 16) fun a : Nat => (Ball.inv ⟨a, 0, 3, 1024⟩ 1024).plus
#kernel_op "ball/Ball.inv, near one, as many digits" (sizes := [4096]) (count := 16) fun a : Nat => (Ball.inv ⟨a, 0, 3, 4096⟩ 4096).plus
#kernel_op "ball/Ball.inv, near one, as many digits" (sizes := [16384]) (count := 16) fun a : Nat => (Ball.inv ⟨a, 0, 3, 16384⟩ 16384).plus
#kernel_op "ball/Ball.inv, near one, as many digits" (sizes := [100000]) (count := 16) fun a : Nat => (Ball.inv ⟨a, 0, 3, 100000⟩ 100000).plus
#kernel_op "ball/Ball.div, near one, as many digits" (sizes := [64]) (count := 16) fun a b : Nat => (Ball.div ⟨0, a, 3, 64⟩ ⟨b, 0, 2, 64⟩ 64).minus
#kernel_op "ball/Ball.div, near one, as many digits" (sizes := [1024]) (count := 16) fun a b : Nat => (Ball.div ⟨0, a, 3, 1024⟩ ⟨b, 0, 2, 1024⟩ 1024).minus
#kernel_op "ball/Ball.div, near one, as many digits" (sizes := [4096]) (count := 16) fun a b : Nat => (Ball.div ⟨0, a, 3, 4096⟩ ⟨b, 0, 2, 4096⟩ 4096).minus
#kernel_op "ball/Ball.div, near one, as many digits" (sizes := [16384]) (count := 16) fun a b : Nat => (Ball.div ⟨0, a, 3, 16384⟩ ⟨b, 0, 2, 16384⟩ 16384).minus
#kernel_op "ball/Ball.div, near one, as many digits" (sizes := [100000]) (count := 16) fun a b : Nat => (Ball.div ⟨0, a, 3, 100000⟩ ⟨b, 0, 2, 100000⟩ 100000).minus
#kernel_op "ball/Ball.apart" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 16) fun a b : Nat => Ball.apart ⟨a, b, 3, 17⟩

/-! ## Complex balls, and complex numbers in fixed point at the scale of the operands -/
#kernel_op "complex/CBall.add" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 16) fun a b : Nat =>
  (CBall.add ⟨⟨a, 0, 3, 17⟩, ⟨0, b, 2, 5⟩⟩ ⟨⟨b, 0, 2, 5⟩, ⟨a, 0, 3, 17⟩⟩).re.plus
#kernel_op "complex/CBall.mul" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 16) fun a b : Nat =>
  (CBall.mul ⟨⟨a, 0, 3, 17⟩, ⟨0, b, 2, 5⟩⟩ ⟨⟨b, 0, 2, 5⟩, ⟨a, 0, 3, 17⟩⟩).re.plus
#kernel_op "complex/CBall.mul, round 64" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 16) fun a b : Nat =>
  ((CBall.mul ⟨⟨a, 0, 3, 64⟩, ⟨0, b, 2, 64⟩⟩ ⟨⟨b, 0, 2, 64⟩, ⟨a, 0, 3, 64⟩⟩).round 64).re.plus
#kernel_op "complex/CFix.mul, as many digits" (sizes := [64]) (count := 16) fun a b : Nat => (CFix.mul 64 ⟨a, b, 1, true⟩ ⟨b, a, 1, true⟩).re
#kernel_op "complex/CFix.mul, as many digits" (sizes := [1024]) (count := 16) fun a b : Nat => (CFix.mul 1024 ⟨a, b, 1, true⟩ ⟨b, a, 1, true⟩).re
#kernel_op "complex/CFix.mul, as many digits" (sizes := [4096]) (count := 16) fun a b : Nat => (CFix.mul 4096 ⟨a, b, 1, true⟩ ⟨b, a, 1, true⟩).re

/-! ## Lists of 256 entries: core `List` against `Seq`, and the cover check of `Multiplicative` -/
#kernel_op "list/(List.range 256).map, length" (sizes := [64, 1024]) (count := 16) fun a : Nat =>
  ((List.range 256).map fun i => Nat.add a i).length
#kernel_op "list/Seq.tabulate 256, Seq.len" (sizes := [64, 1024]) (count := 16) fun a : Nat =>
  Seq.len (Seq.tabulate 256 fun i => Nat.add a i.val)
#kernel_op "list/(List.range 256).map, getD 200" (sizes := [64, 1024]) (count := 16) fun a : Nat =>
  ((List.range 256).map fun i => Nat.add a i).getD 200 0
#kernel_op "list/Seq.tabulate 256, Seq.getD 200" (sizes := [64, 1024]) (count := 16) fun a : Nat =>
  Seq.getD (Seq.tabulate 256 fun i => Nat.add a i.val) 200 0
#kernel_op "list/Split.cover of 1 to 64" (sizes := [64]) (count := 16) fun a : Nat =>
  Split.cover 1 64 (Seq.tabulate 64 fun i => Nat.succ i.val) (Nat.mod a 1) 64

/-! ## Bisection and strict application -/
#kernel_op "search/Kernel.bisect, square root" (sizes := [64, 1024, 4096]) (count := 4) fun a : Nat =>
  Kernel.bisect (fun r => Nat.ble (Nat.mul r r) a) (Nat.div (Nat.succ (size a)) 2) 0
#kernel_op "search/Kernel.isqrt" (sizes := [64, 1024, 4096]) (count := 4) fun a : Nat => isqrt a
#kernel_op "search/strict (a * b), then successor" (sizes := [64, 1024, 4096, 16384, 100000]) (count := 32) fun a b : Nat =>
  strict (Nat.mul a b) fun n => Nat.succ n

/-! ## Modular powers `a ^ e % n` with all three of the given size -/
#kernel_op "mod/powMod" (sizes := [64, 256, 1024, 4096]) (count := 2) (reps := 1) fun a e n : Nat => powMod a e n
#kernel_op "mod/powModWindow 0 (binary)" (sizes := [64, 256, 1024, 4096]) (count := 2) (reps := 1) fun a e n : Nat => powModWindow 0 a e n
#kernel_op "mod/invMod" (sizes := [64, 256, 1024, 4096]) (count := 4) (reps := 1) fun a n : Nat => invMod a n
#kernel_op "mod/isInvMod" (sizes := [64, 256, 1024, 4096]) (count := 32) fun a x n : Nat => isInvMod a x n
