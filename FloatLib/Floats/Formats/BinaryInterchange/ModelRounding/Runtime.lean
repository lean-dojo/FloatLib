/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Init.Data.Float.Model.Unpacked.Operations.Div
public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Rational
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Executable normalization for binary interchange formats

These computations normalize exact integer mantissas with round-to-nearest, ties-to-even.
Mantissa widths and target exponents are parameters; no named binary format is selected.

Proofs relating these computations to Lean's logical floating-point model are kept in
`ModelRounding.Proof`, so executable clients can import this module without the large semantic
proof layer.

## References

- IEEE Standard for Floating-Point Arithmetic, IEEE 754-2019, Section 4.3.1.
- Lean 4, `Init.Data.Float.Model.Unpacked.Round`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open Float.Model.UnpackedFloat
open FloatLib.Numerics

/-- Round an exact integer mantissa after expressing it at `targetExponent`. -/
def roundMantissaAtExponentEven
    (mantissa : Nat) (exponent targetExponent : Int) : Nat :=
  if exponent ≤ targetExponent then
    roundShiftRightEven mantissa (targetExponent - exponent).toNat
  else
    mantissa <<< (exponent - targetExponent).toNat

/-- Round a positive integer mantissa to the precision specified by `leadingBit + 1`;
a rounding carry can produce one extra bit. -/
def roundMantissaToLeadingBitEven (mantissa leadingBit : Nat) : Nat :=
  if leadingBit ≤ mantissa.log2 then
    roundShiftRightEven mantissa (mantissa.log2 - leadingBit)
  else
    mantissa <<< (leadingBit - mantissa.log2)

/-- Complete model rounding after the first rounded mantissa and exponent are known. -/
def finishRoundedMantissa
    (spec : Float.Model.Format) (sign : Sign) (rounded : Nat × Int) :
    Float.Model.UnpackedFloat :=
  let final := Float.Model.UnpackedFloat.shiftToTargetExponent
    spec rounded.1 rounded.2 .exact
  if h : final.1.mantissa = 0 then
    .zero sign
  else
    .finite sign final.1.mantissa final.2 (Nat.pos_of_ne_zero h)

end Model
end FloatLib.Floats.Formats.BinaryInterchange
