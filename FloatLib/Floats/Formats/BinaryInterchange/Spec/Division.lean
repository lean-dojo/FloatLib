/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Rational
public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Decode

/-!
# Division specification

This exact-rational reference operation defines the proof target for every validated
`FloatFormat`.

Finite operands with a nonzero divisor are divided as an exact scaled rational and rounded to
nearest with ties to even.
Special operands and division by zero follow the descriptor's encoding policy. This module defines
the value-only reference operation; explicit rounding directions and status flags belong to the
separate directed and status APIs. Word and arbitrary-width division kernels refine this same
reference definition.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.Spec

/-- Division result when at least one operand is non-finite. -/
@[inline] def divSpecial {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  match chooseNaN2 x y with
  | some nan => nan
  | none =>
      if isInf x then
        if isInf y then invalidResult fmt
        else nativeOverflow fmt (signBit x != signBit y)
      else if isInf y then
        zero fmt (signBit x != signBit y)
      else
        invalidResult fmt

/-- Exact rational division followed by nearest-even rounding in the destination descriptor. -/
@[inline] def div {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  match toDyadic? x, toDyadic? y with
  | some dx, some dy =>
      let sign := Bool.xor dx.negative dy.negative
      if dy.significand == 0 then
        if dx.significand == 0 then invalidResult fmt
        else nativeOverflow fmt sign
      else if dx.significand == 0 then
        zero fmt sign
      else
        roundRatScaled fmt sign dx.significand dy.significand (dx.exponent - dy.exponent)
  | _, _ => divSpecial x y

end FloatLib.Floats.Formats.BinaryInterchange.Model.Spec
