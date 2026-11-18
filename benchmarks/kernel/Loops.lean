/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
import FloatLib.Tactic.FloatDecide
import FloatLib.Floats.Formats.BinaryInterchange.Configured
import FloatLib.Floats.Formats.BinaryInterchange.Configured.KernelPath
import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Value

/-!
# Three loops for timing proofs by kernel evaluation

`sumTenth n` adds binary32 `0.1` to zero `n` times. `sum64 n` adds `n` binary64 operands left
to right, and `dot64 n` is the dot product of two streams of `n` operands, a multiplication and
an addition per term, without a fused multiply-add. The operands come from `operand`, a formula
on natural numbers that Coq evaluates the same way (`FlocqConversion.v`).

`loops.sh` type-checks the statement that each loop of 1,000 steps has its encoding, once with
`decide +kernel` on the public operations and once with `float_decide`.
-/

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange

namespace FloatLibBenchmarks.KernelLoops

/-- binary32 `0.1`. -/
def tenth : Binary32 := 0.1

/-- `0.1` added to zero `n` times in binary32. -/
def sumTenth (n : Nat) : Binary32 := (List.range n).foldl (fun s _ => s + tenth) 0

/--
The encoding of the `i`-th binary64 operand of stream `k`: a pseudo-random fraction, an exponent
within four binades of one, and a sign that changes every third operand.
-/
def operand (k i : Nat) : Nat :=
  Nat.add
    (Nat.add (Nat.mul (Nat.mod (Nat.div i 3) 2) (Nat.pow 2 63))
      (Nat.mul (Nat.add 1019 (Nat.mod (Nat.add (Nat.mul i 7) k) 9)) (Nat.pow 2 52)))
    (Nat.mod
      (Nat.add (Nat.mul (Nat.add i (Nat.mul k 1000)) 6364136223846793005) 1442695040888963407)
      (Nat.pow 2 52))

/-- The sum of the first `n` operands of stream 0, added left to right in binary64. -/
def sum64 (n : Nat) : Binary64 :=
  (List.range n).foldl (fun s i => s + KernelPath.ofNat (operand 0 i)) 0

/-- The dot product of the first `n` operands of streams 0 and 1 in binary64, without FMA. -/
def dot64 (n : Nat) : Binary64 :=
  (List.range n).foldl
    (fun s i => s + KernelPath.ofNat (operand 0 i) * KernelPath.ofNat (operand 1 i)) 0

end FloatLibBenchmarks.KernelLoops
