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
imports `Configured.Transcendentals`; `import FloatLib` does not provide those functions. It
computes a sine/cosine pair, composes `exp`, `log`, and `tanh` at one format, and then writes
the same formula once for any scalar type that supplies those functions.

The binary implementations are deterministic approximations that preserve extra working bits
before a final rounding. They are not correctly rounded, and the API currently promises neither a
general ULP bound nor a proved real-error bound for compositions; each function boundary rounds
again. The arithmetic operations have complete refinement proofs.
-/

@[expose] public section

namespace FloatLib.Examples.Transcendentals

open FloatLib.Numerics
open FloatLib.Floats

private abbrev Binary32 :=
  ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)

/-- Trigonometric arguments are in radians. This is one half radian. -/
private def angle : Binary32 :=
  0.5

/-! ## Compute related functions together -/

private def sineAndCosine : Binary32 × Binary32 :=
  ExecFloat.Binary.sinCos angle
-- (4021713 * 2^-23, 0.877582550048828125)

/-
That is approximately (0.47942555, 0.87758255). `sinCos` returns both values from one argument
reduction, avoiding a separate reduction for each function. The real sine and cosine are
approximately 0.4794255386 and 0.8775825619; for this input the differences are below one binary32
ULP. This is an example calculation, not a general theorem. Lean's native `Float.sin 0.5` prints
0.479426.
-/

/-! ## Compose functions at one chosen format -/

private def composed : Binary32 :=
  let positive := ExecFloat.Binary.exp angle + 1
  let logarithm := ExecFloat.Binary.log positive
  ExecFloat.Binary.tanh logarithm
-- 3147785 * 2^-22

/-
That is approximately 0.75049043; the real value of `tanh(log(exp(0.5) + 1))` is approximately
0.7504904226. The named intermediate values make the evaluation order visible: `exp` rounds to
a Binary32, the addition rounds again, and so do `log` and `tanh`. Four roundings, not one,
which is why we make no correct-rounding claim for the composition. The argument to `log` is
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
-- 3147785 * 2^-22

private def genericNativeResult : Float :=
  smoothPositivePart 0.5
-- 0.750490

/-
The generic function gives exactly `composed` at `Binary32`, because the `MathFunctions` instance
for a binary format is the same named implementation. At `Float` it uses Lean's native elementary
functions from the host C library, so the two results share a formula but not an implementation or
a rounding history.
-/

end FloatLib.Examples.Transcendentals
