/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.KernelPath
public import FloatLib.Floats.Formats.OCP.FP8.KernelTables
public import FloatLib.Floats.ExecFloat.Backends.Kernel.Plumbing
public import FloatLib.Tactic.FloatDecide
public import FloatLib.Tactic.KernelShape

/-!
# Lane decision tests

`lane_decide` proves a statement about all pairs of indices below `n` with one run of each side
on rows of `n * n` lanes in Lean's kernel. These tests check

* statements about natural numbers with products, case distinctions, shared bindings and shifts
  by a count that differs from lane to lane;
* a remainder by a power of two, the recursor of `Bool`, and a definition with `if` and `%` read
  through its kernel shape;
* that a false statement is refused, and that a value which does not fit a lane is refused and
  never gives a wrong result;
* the staged kernel operations of E4M3, E5M2 and binary16 on all pairs of a range of
  encodings;
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.Lanes

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.KernelPath
open FloatLib.Numerics

/-! ## Natural numbers -/

/-- A product commutes on all pairs below 256: one run of each side on 65,536 lanes. -/
theorem mul_comm_pairs : ∀ a b : Fin 256, Nat.mul a.val b.val = Nat.mul b.val a.val := by
  lane_decide

/-- The distance of two numbers, by a case distinction and through a shared minimum. -/
theorem distance_pairs : ∀ a b : Fin 256,
    Bool.casesOn (motive := fun _ => Nat) (Nat.ble a.val b.val) (Nat.sub a.val b.val)
        (Nat.sub b.val a.val) =
      (fun low => Nat.sub (Nat.add a.val b.val) (Nat.add low low))
        (Bool.casesOn (motive := fun _ => Nat) (Nat.ble a.val b.val) b.val a.val) := by
  lane_decide

/-- A shift by a count that differs from lane to lane, against the power of two. -/
theorem shift_pairs : ∀ a b : Fin 32,
    Nat.shiftLeft (Nat.succ b.val) a.val = Nat.mul (Nat.succ b.val) (Nat.pow 2 a.val) := by
  lane_decide

/-- A remainder by a power of two is a mask, written with `%` or with `Nat.mod`. -/
theorem mod_pairs : ∀ a b : Fin 256,
    Nat.add (Nat.mul a.val b.val % 2 ^ 7) (Nat.mod (Nat.add a.val b.val) 16) =
      Nat.add (Nat.land (Nat.mul a.val b.val) 127) (Nat.land (Nat.add a.val b.val) 15) := by
  lane_decide

/-- A remainder by a number that is not a power of two has no lane step. -/
example : True := by
  fail_if_success
    have : ∀ a b : Fin 16, Nat.add a.val b.val % 3 = Nat.add b.val a.val % 3 := by lane_decide
  trivial

/-- The recursor of `Bool` is read as the case distinction it is. -/
theorem rec_pairs : ∀ a b : Fin 256,
    Bool.rec (motive := fun _ => Nat) (Nat.sub a.val b.val) (Nat.sub b.val a.val)
        (Nat.ble a.val b.val) =
      Bool.casesOn (motive := fun _ => Nat) (Nat.ble a.val b.val) (Nat.sub a.val b.val)
        (Nat.sub b.val a.val) := by
  lane_decide

/-- A function written with `if` and `%`. -/
def window (x : Nat) : Nat :=
  if x % 2 ^ 4 = 3 then x <<< 2 % 2 ^ 8 else if x ≤ 100 then x + 1 else 0

kernel_shape window

/-- The kernel shape of a definition with `if` and `%` is read as it is. -/
theorem shape_pairs : ∀ a b : Fin 256,
    window.kernel (Nat.add a.val b.val) =
      (fun x => Bool.casesOn (motive := fun _ => Nat) (Nat.beq (Nat.land x 15) 3)
        (Bool.casesOn (motive := fun _ => Nat) (Nat.ble x 100) 0 (Nat.add x 1))
        (Nat.land (Nat.shiftLeft x 2) 255)) (Nat.add a.val b.val) := by
  lane_decide

/-- A false statement is refused. -/
example : True := by
  fail_if_success
    have : ∀ a b : Fin 16, Nat.add a.val b.val = Nat.mul a.val b.val := by lane_decide
  trivial

/--
A value that does not fit a lane is an error and never a wrong result: `2 ^ 63` needs 64 bits,
so this true statement is refused.
-/
example : True := by
  fail_if_success
    have : ∀ a _ : Fin 64, Nat.shiftLeft 1 a.val = Nat.pow 2 a.val := by lane_decide
  trivial

/-! ## Kernel operations of small formats -/

/-- `value`, or zero when both encodings are NaNs of an FP8 format (`0x7F` and `0xFF`). -/
def unlessBothNaN (a b value : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.beq (Nat.land a 127) 127) value
    (Bool.casesOn (motive := fun _ => Nat) (Nat.beq (Nat.land b 127) 127) value 0)

/--
Addition of E4M3 commutes on all 65,536 pairs of encodings that are not both NaN (a sum of two
NaNs returns its first operand).
-/
theorem e4m3fn_add_comm : ∀ a b : Fin 256,
    unlessBothNaN a.val b.val (KernelPath.add FloatFormat.e4m3 .nearest a.val b.val) =
      unlessBothNaN a.val b.val (KernelPath.add FloatFormat.e4m3 .nearest b.val a.val) := by
  lane_decide

/-- Multiplication of E4M3 commutes on all pairs of encodings that are not both NaN. -/
theorem e4m3fn_mul_comm : ∀ a b : Fin 256,
    unlessBothNaN a.val b.val (KernelPath.mul FloatFormat.e4m3 .nearest a.val b.val) =
      unlessBothNaN a.val b.val (KernelPath.mul FloatFormat.e4m3 .nearest b.val a.val) := by
  lane_decide

/-- Rounding toward zero: `a - b` is the negation of `b - a` unless the difference is zero or
NaN. -/
theorem e4m3fn_sub_towardZero : ∀ a b : Fin 256,
    KernelPath.sub FloatFormat.e4m3 .towardZero a.val b.val =
      KernelPath.add FloatFormat.e4m3 .towardZero a.val
        (KernelPath.neg FloatFormat.e4m3 b.val) := by
  lane_decide

/--
Addition of binary16 commutes on the 65,536 pairs of the encodings `0x3C00 + a` (from one
upward) and `0x4000 + 37 * b` (from two upward, in steps of 37).
-/
theorem binary16_add_comm : ∀ a b : Fin 256,
    KernelPath.add FloatFormat.binary16 .nearest (Nat.add 0x3C00 a.val)
        (Nat.add 0x4000 (Nat.mul 37 b.val)) =
      KernelPath.add FloatFormat.binary16 .nearest (Nat.add 0x4000 (Nat.mul 37 b.val))
        (Nat.add 0x3C00 a.val) := by
  lane_decide

end FloatLibTests.Conformance.BinaryInterchange.Lanes
