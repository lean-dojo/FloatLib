/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.WideLimb.Core.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Generic.QuotientRound.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Spec.Division

/-!
# Width-generic wide-limb division

Finite inputs are decoded directly from their limb fields. Division uses one arbitrary-precision
integer quotient, fusing significand scaling with the extra bit needed for nearest-even rounding.
For normal operands, a significand comparison determines the ratio's leading exponent. Subnormal
operands use the general leading-exponent computation and the same certified rounder.

The finite path includes zero operands, subnormal results, underflow, and overflow in every IEEE
rounding direction. Only non-finite operands use the reference operation. Their value result is
independent of rounding direction. `Division.Proof` establishes the complete codec refinement.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb

open FloatLib.Numerics

/-- Integer significand read from a stored value, including subnormal and zero significands. -/
@[inline] def divisionMantissa {fmt : FloatFormat} (value : Value fmt) : Nat :=
  if expWord value == 0 then (fraction value).toNat else (normalMantissa value).toNat

/-- The ratio exponent needs only a comparison when both significands are normalized. -/
@[inline] def divisionRatioExponent {fmt : FloatFormat} (x y : Value fmt) (num den : Nat) : Int :=
  if expWord x == 0 || expWord y == 0 then RationalBinary.floorLog2 num den
  else if den ≤ num then 0 else -1

/-- Try finite wide-limb division, in any IEEE rounding direction and without a precision bound. -/
def divFiniteWithRounding? (fmt : FloatFormat) (mode : IEEERoundingMode)
    (x y : Value fmt) : Option (Value fmt) :=
  if expWord x == expAllOnes fmt || expWord y == expAllOnes fmt then
    none
  else
    let sign := Bool.xor (signBit x) (signBit y)
    let num := divisionMantissa x
    let den := divisionMantissa y
    let result :=
      if den == 0 then
        if num == 0 then invalidResult fmt else nativeOverflow fmt sign
      else if num == 0 then
        zero fmt sign
      else
        let exponent :=
          Int.ofNat ((expWord x).toNat - 1) - Int.ofNat ((expWord y).toNat - 1)
        FiniteQuotientRound.roundAtExponent fmt mode sign num den exponent
          (divisionRatioExponent x y num den)
    some (ofModel result)

/-- Total wide-limb division with the reference exceptional-value policy. -/
def divWithRounding (fmt : FloatFormat) (mode : IEEERoundingMode)
    (x y : Value fmt) : Value fmt :=
  match divFiniteWithRounding? fmt mode x y with
  | some result => result
  | none => ofModel (Spec.div (toModel x) (toModel y))

/-- Nearest-even division for the configured wide-limb backend. -/
@[inline] def div (fmt : FloatFormat) (x y : Value fmt) : Value fmt :=
  divWithRounding fmt .nearestEven x y

end FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb
