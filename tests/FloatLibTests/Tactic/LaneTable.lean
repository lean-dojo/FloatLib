/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import Lean.Elab.Command
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.KernelPath
public import FloatLib.Floats.Formats.OCP.FP8.KernelTables
public import FloatLib.Tactic.FloatDecide

/-!
# Packed table command tests

The tests check table lookup, rejection of an entry that exceeds its lane width,
use of certified FP8 tables by `float_decide`, and that a frame which the kernel rejects leaves
no declaration behind.
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.Lanes

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.KernelPath
open FloatLib.Numerics

/-- The products of the numbers below 16, in lanes of eight bits. -/
lane_table products (width := 8) (size := 16) := fun a b => Nat.mul a b

example : Packed.lane 8 (7 * 16 + 9) products = 63 := by decide +kernel

example (a b : Fin 16) : Packed.lane 8 (a.val * 16 + b.val) products = Nat.mul a.val b.val :=
  products.lookup a b

/-! A value that does not fit the lanes of the table is refused. -/

/-- error: lane_table: the check failed: the value 16 at the pair (2, 8) does not fit 4 bits -/
#guard_msgs in
lane_table tooWide (width := 4) (size := 16) := fun a b => Nat.mul a b

/-! The squares of the products pass through sixteen bits, one more than a lane of the first
frame holds, so the kernel rejects the table of that frame and the second frame gives it. Lean
keeps a rejected declaration as an axiom; the command takes it out again. -/

/-- The high byte of the square of a product of two numbers below 16. -/
lane_table squares (width := 8) (size := 16) :=
  fun a b => Nat.shiftRight (Nat.mul (Nat.mul a b) (Nat.mul a b)) 8

example : Packed.lane 8 (15 * 16 + 15) squares = 197 := by decide +kernel

example (a b : Fin 16) :
    Packed.lane 8 (a.val * 16 + b.val) squares =
      Nat.shiftRight (Nat.mul (Nat.mul a.val b.val) (Nat.mul a.val b.val)) 8 :=
  squares.lookup a b

-- No constant of this module is an axiom.
run_cmd Lean.Elab.Command.liftCoreM do
  let environment := (← Lean.getEnv).setExporting false
  for (name, info) in environment.constants.map₂.toList do
    if info matches .axiomInfo _ then
      throwError "{name} is an axiom"

/-- With the tables imported, a product of E4M3 values is a lookup: `1.0 * 2.0 = 2.0`. -/
example : KernelPath.toNat ((KernelPath.ofNat 0x38 : E4M3) * KernelPath.ofNat 0x40) = 0x40 := by
  float_decide

/-- The rewrite of `float_decide` leaves a lookup in the packed table, for every pair. -/
example (a b : Nat) :
    KernelPath.toNat ((KernelPath.ofNat a : E4M3) + KernelPath.ofNat b) =
      Nat.land (Nat.shiftRight E4M3.kernelAdd
        (Nat.mul 8 (Nat.add (Nat.mul (Nat.mod a 256) 256) (Nat.mod b 256)))) 255 := by
  set_option backward.isDefEq.respectTransparency false in
  simp only [kernel_optimize]
  rfl

/-- The table of E5M2 products holds the staged product of every pair of encodings. -/
example (a b : Fin 256) :
    Packed.lane 8 (a.val * 256 + b.val) E5M2.kernelMul =
      KernelPath.mul (StaticByte.Family.format E5M2.Family) .nearest a.val b.val :=
  E5M2.kernelMul.lookup a b

end FloatLibTests.Conformance.BinaryInterchange.Lanes
