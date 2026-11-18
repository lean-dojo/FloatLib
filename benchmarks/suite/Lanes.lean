/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
import FloatLib.Tactic.FloatDecide
import FloatLib.Floats.Formats.BinaryInterchange.Configured.KernelPath
import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Lanes

/-!
# Statements about all pairs of encodings, by one run on all lanes

The statements of `benchmarks/kernel/Exhaustive.lean` (addition and multiplication of E4M3
commute on all 65,536 pairs of encodings that are not both NaN), stated on the staged kernel
operations and proved by `lane_decide`: one evaluation of each side on rows of 65,536 lanes. The
same for E5M2, and for a slice of 65,536 pairs of binary16 encodings. `benchmarks/suite/run.sh
exhaustive` prints the time that Lean's kernel spends on each theorem. A theorem that needs a
wider lane than the first frame also pays for the narrower attempts: each attempt is one line of
the profile.

The last command builds one packed table (`lane_table`): its elaboration computes the table and
its kernel check proves the lookup theorem.
-/

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.KernelPath
open FloatLib.Numerics.Packed

namespace FloatLibBenchmarks.Lanes

set_option maxRecDepth 100000000
set_option Elab.async false

/-- `value`, or zero when both encodings are NaNs of E4M3 (`0x7F` and `0xFF`). -/
def unlessBothNaN (a b value : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.beq (Nat.land a 127) 127) value
    (Bool.casesOn (motive := fun _ => Nat) (Nat.beq (Nat.land b 127) 127) value 0)

/-- `value`, or zero when both encodings are NaNs of E5M2 (magnitudes above `0x7C`). -/
def unlessBothNaN5 (a b value : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.ble 0x7D (Nat.land a 127)) value
    (Bool.casesOn (motive := fun _ => Nat) (Nat.ble 0x7D (Nat.land b 127)) value 0)

#print "KLANES e4m3 add-commutes"
theorem e4m3fn_add_comm : ∀ a b : Fin 256,
    unlessBothNaN a.val b.val (KernelPath.add FloatFormat.e4m3 .nearest a.val b.val) =
      unlessBothNaN a.val b.val (KernelPath.add FloatFormat.e4m3 .nearest b.val a.val) := by
  lane_decide

#print "KLANES e4m3 mul-commutes"
theorem e4m3fn_mul_comm : ∀ a b : Fin 256,
    unlessBothNaN a.val b.val (KernelPath.mul FloatFormat.e4m3 .nearest a.val b.val) =
      unlessBothNaN a.val b.val (KernelPath.mul FloatFormat.e4m3 .nearest b.val a.val) := by
  lane_decide

#print "KLANES e5m2 add-commutes"
theorem e5m2_add_comm : ∀ a b : Fin 256,
    unlessBothNaN5 a.val b.val (KernelPath.add FloatFormat.e5m2 .nearest a.val b.val) =
      unlessBothNaN5 a.val b.val (KernelPath.add FloatFormat.e5m2 .nearest b.val a.val) := by
  lane_decide

#print "KLANES e5m2 mul-commutes"
theorem e5m2_mul_comm : ∀ a b : Fin 256,
    unlessBothNaN5 a.val b.val (KernelPath.mul FloatFormat.e5m2 .nearest a.val b.val) =
      unlessBothNaN5 a.val b.val (KernelPath.mul FloatFormat.e5m2 .nearest b.val a.val) := by
  lane_decide

#print "KLANES binary16-slice add-commutes"
theorem binary16_add_comm : ∀ a b : Fin 256,
    KernelPath.add FloatFormat.binary16 .nearest (Nat.add 0x3C00 a.val)
        (Nat.add 0x4000 (Nat.mul 37 b.val)) =
      KernelPath.add FloatFormat.binary16 .nearest (Nat.add 0x4000 (Nat.mul 37 b.val))
        (Nat.add 0x3C00 a.val) := by
  lane_decide

#print "KLANES binary16-slice mul-commutes"
theorem binary16_mul_comm : ∀ a b : Fin 256,
    KernelPath.mul FloatFormat.binary16 .nearest (Nat.add 0x3C00 a.val)
        (Nat.add 0x4000 (Nat.mul 37 b.val)) =
      KernelPath.mul FloatFormat.binary16 .nearest (Nat.add 0x4000 (Nat.mul 37 b.val))
        (Nat.add 0x3C00 a.val) := by
  lane_decide

#print "KLANES e4m3 add-table"
/-- The packed table of E4M3 sums. -/
lane_table addTable (width := 8) (size := 256) := KernelPath.add FloatFormat.e4m3 .nearest

#print axioms e4m3fn_add_comm
#print axioms addTable.lookup

end FloatLibBenchmarks.Lanes
