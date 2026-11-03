/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals
public import FloatLib.Floats.Formats.BinaryInterchange.Configured

/-!
# Elementary functions

What is `sin 0.5` in binary32, and what does FloatLib promise about the answer? This example
imports `Configured.Transcendentals`, because `import FloatLib` doesn't provide those functions.
It computes a sine/cosine pair, composes `exp`, `log`, and `tanh` at one format, and then writes
the same formula once for any scalar type that supplies those functions.

The functions used here are deterministic approximations that preserve extra working bits before a
final rounding. They are not proved correctly rounded, and the API promises neither a general
ULP bound nor a proved real-error bound for compositions, where each function boundary rounds
again. These are proved correctly rounded: `pi` for IEEE formats, `pow` of a positive base
whenever its enclosure search settles, and `ExecFloat.Binary.Certified.exp` and `log` when their
rational enclosure refinement succeeds. The arithmetic operations have complete refinement
proofs. The last section switches the generic formula to correctly rounded `exp` and `log`.
-/

@[expose] public section

namespace FloatLib.Examples.Transcendentals

open FloatLib.Numerics
open FloatLib.Floats

/-- Trigonometric arguments are in radians. This is one half radian. -/
private def angle : Binary32 :=
  0.5

/-! ## Compute related functions together -/

private def sineAndCosine : Binary32 × Binary32 :=
  ExecFloat.Binary.sinCos angle
-- (0.47942555, 0.87758255)

/-
Each component is the shortest decimal that reads back as the computed binary32 value. `sinCos`
returns both values from one argument reduction, avoiding a separate reduction for each function.
The real sine and cosine are approximately 0.4794255386 and 0.8775825619, so for this input both
differences are below one binary32 ULP. This is an example calculation, not a general theorem.
Lean's native `Float.sin 0.5` prints 0.479426.
-/

/-! ## Compose functions at one chosen format -/

private def composed : Binary32 :=
  let positive := ExecFloat.Binary.exp angle + 1
  let logarithm := ExecFloat.Binary.log positive
  ExecFloat.Binary.tanh logarithm
-- 0.7504904

/-
The stored value is 0.7504904270172119140625, and the real value of `tanh(log(exp(0.5) + 1))` is
approximately 0.7504904226. The named intermediate values make the evaluation order visible: `exp`
rounds to a Binary32, the addition rounds again, and so do `log` and `tanh`. Four roundings, not
one, which is why we make no correct-rounding claim for the composition. The argument to `log` is
positive in this example.
-/

/-! ## Reuse the formula with another scalar type -/

/--
Compute `tanh(log(exp(x) + 1))`. The scalar type supplies the elementary functions, addition,
and the literal 1. This is the same formula as `composed` above.
-/
def smoothPositivePart {Scalar : Type} [MathFunctions Scalar] [OfNat Scalar 1] [Add Scalar]
    (x : Scalar) : Scalar :=
  let positive := MathFunctions.exp x + 1
  let logarithm := MathFunctions.log positive
  MathFunctions.tanh logarithm

private def genericBinaryResult : Binary32 :=
  smoothPositivePart angle
-- 0.7504904

private def genericNativeResult : Float :=
  smoothPositivePart 0.5
-- 0.750490

/-
The generic function gives the same value as `composed` at `Binary32`, because the
`MathFunctions` instance for a binary format is the same named implementation. At `Float` it uses
Lean's native elementary functions from the host C library, so the two results share a formula but
not an implementation or a rounding history.
-/

/-! ## Switch to correctly rounded `exp` and `log` -/

section CorrectlyRounded

open scoped FloatLib.Floats.Formats.BinaryInterchange.CorrectlyRoundedMath

private def correctlyRoundedResult : Binary32 :=
  smoothPositivePart angle
-- 0.7504904

end CorrectlyRounded

/-
Inside the scope, `MathFunctions.exp` and `MathFunctions.log` on an IEEE format are
`ExecFloat.Binary.CorrectlyRounded.exp` and `log`, so each of those two steps is the nearest-even
rounding of the real function (`ExecFloat.Binary.CorrectlyRounded.toReal_exp_eq_roundAt` and
`toReal_log_eq_roundAt`).
The addition and `tanh` still round on their own, so the composition rounds four times and we make
no correct-rounding claim for it either. At this input the result is the same binary32 value as
`genericBinaryResult`, and the correctly rounded and approximate `exp 0.5` agree as well.
-/

end FloatLib.Examples.Transcendentals
