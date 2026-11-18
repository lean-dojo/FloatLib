/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
import FloatLib.Tactic.FloatDecide
import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.KernelPath
import FloatLib.Floats.Formats.OCP.FP8.E4M3

/-!
# Two statements about all pairs of E4M3 encodings

Addition and multiplication of E4M3 commute on all 65,536 pairs of encodings, except that a
sum or product of two NaNs returns its first operand. `float_decide` checks each statement with
one loop over the pairs in Lean's kernel (`forall_fin_pairs`): two operations and one comparison
per pair. `exhaustive.sh` prints the kernel time of each theorem.
-/

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange

namespace FloatLibBenchmarks.KernelExhaustive

set_option maxRecDepth 10000000

/--
Addition of E4M3 commutes on every pair of encodings that are not both NaN. The two NaN
encodings are `0x7F` and `0xFF`, and a sum of two NaNs returns its first operand.
-/
theorem add_comm_all : ∀ a b : Fin 256, (a.val % 128 = 127 ∧ b.val % 128 = 127) ∨
    KernelPath.toNat ((KernelPath.ofNat a : E4M3) + KernelPath.ofNat b) =
      KernelPath.toNat ((KernelPath.ofNat b : E4M3) + KernelPath.ofNat a) := by
  float_decide

/-- Multiplication of E4M3 commutes on every pair of encodings that are not both NaN. -/
theorem mul_comm_all : ∀ a b : Fin 256, (a.val % 128 = 127 ∧ b.val % 128 = 127) ∨
    KernelPath.toNat ((KernelPath.ofNat a : E4M3) * KernelPath.ofNat b) =
      KernelPath.toNat ((KernelPath.ofNat b : E4M3) * KernelPath.ofNat a) := by
  float_decide

#print axioms add_comm_all
#print axioms mul_comm_all

end FloatLibBenchmarks.KernelExhaustive
