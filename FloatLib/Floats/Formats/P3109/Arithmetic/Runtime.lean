/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Projection.Rational.Runtime

/-!
# Exact rational arithmetic for P3109

The closed operations in `Arithmetic` evaluate finite operands in `Rat`, retaining infinities
and the report's single NaN. In particular, division by zero returns NaN, including infinity
divided by zero. FMA and fused add-add form the complete exact expression before projection.

Each `ExecFloat.P3109` operation projects into `(target := ...)`, by default the format of its
operands, with `(mode := ...)` and `(saturation := ...)` options that default to nearest-even
rounding and no saturation request. `unary`, `binary`, and `ternary` apply any exact closed
operation to operands of independent descriptors. No IEEE exception flags or floating-point
environment are used.

Exact rational intermediates can require large integers when the descriptor has a wide exponent
range. This implementation does not promise a fixed workspace bound for arbitrary descriptors.

## Reference

IEEE Working Group P3109, *Interim Report on Arithmetic Formats for Machine Learning*,
version 4.0.3 (1 September 2026), §§4.10.1–4.10.8, revision `34f5964`.
This is an unapproved working-group report, not an approved IEEE standard.
<https://github.com/P3109/Public/tree/34f5964d9bb2382b2665d15467fc3517b990b308>.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109.Arithmetic

/-- The report's single exceptional datum. -/
def nan : NumericalValue Rat := .exceptional (.nan)

/-- Exact rational observation of a decoded binary datum. -/
def toRat : NumericalValue FloatLib.Numerics.Dyadic → NumericalValue Rat
  | .finite value => .finite value.toRat
  | .infinity negative => .infinity negative
  | .exceptional _ => nan

/-- Negation in the report's closed extended domain. -/
def neg : NumericalValue Rat → NumericalValue Rat
  | .finite value => .finite (-value)
  | .infinity negative => .infinity (!negative)
  | .exceptional _ => nan

/-- Absolute value in the report's closed extended domain. -/
def abs : NumericalValue Rat → NumericalValue Rat
  | .finite value => .finite (if value < 0 then -value else value)
  | .infinity _ => .infinity false
  | .exceptional _ => nan

/-- Copying a sign treats zero as nonnegative and propagates either NaN operand. -/
def copySign (value sign : NumericalValue Rat) : NumericalValue Rat :=
  match sign with
  | .exceptional _ => nan
  | .infinity negative => if negative then neg (abs value) else abs value
  | .finite sign => if sign < 0 then neg (abs value) else abs value

/-- Exact addition, with the indeterminate result NaN for opposite infinities. -/
def add : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat
  | .exceptional _, _ | _, .exceptional _ => nan
  | .infinity left, .infinity right =>
      if left == right then .infinity left else nan
  | .infinity negative, .finite _ | .finite _, .infinity negative => .infinity negative
  | .finite left, .finite right => .finite (left + right)

/-- Exact subtraction, with no projection of the negated operand. -/
def sub (left right : NumericalValue Rat) : NumericalValue Rat :=
  add left (neg right)

/-- Exact multiplication, with NaN for zero times infinity. -/
def mul : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat
  | .exceptional _, _ | _, .exceptional _ => nan
  | .infinity left, .infinity right => .infinity (left != right)
  | .infinity negative, .finite value | .finite value, .infinity negative =>
      if value == 0 then nan else .infinity (negative != decide (value < 0))
  | .finite left, .finite right => .finite (left * right)

/-- Exact division, with NaN for every zero denominator and for infinity over infinity. -/
def div : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat
  | .exceptional _, _ | _, .exceptional _ => nan
  | .infinity _, .infinity _ => nan
  | .finite _, .infinity _ => .finite 0
  | .infinity negative, .finite value =>
      if value == 0 then nan else .infinity (negative != decide (value < 0))
  | .finite left, .finite right =>
      if right == 0 then nan else .finite (left / right)

/-- Exact reciprocal, before the sole destination projection. -/
def recip (value : NumericalValue Rat) : NumericalValue Rat :=
  div (.finite 1) value

/-- Exact fused multiply-add, with no intermediate rounding or saturation. -/
def fma (left right addend : NumericalValue Rat) : NumericalValue Rat :=
  add (mul left right) addend

/-- Exact fused add-add, with no intermediate rounding or saturation. -/
def faa (left middle right : NumericalValue Rat) : NumericalValue Rat :=
  add (add left middle) right

end FloatLib.Floats.Formats.P3109.Arithmetic

namespace FloatLib.Floats.ExecFloat.P3109

open Formats.P3109

variable {source leftFormat rightFormat thirdFormat format : Format}

/-- Exact closed rational value of a P3109 operand. -/
@[inline] def toClosedRat (value : ExecFloat.P3109 source) : NumericalValue Rat :=
  Arithmetic.toRat value.decode

/--
Apply an exact unary closed operation and project the result once into `target`, by default the
operand's format, rounding in `mode` before `saturation` applies.
-/
@[inline] def unary (operation : NumericalValue Rat → NumericalValue Rat)
    (value : ExecFloat.P3109 source) (target : Format := source)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  projectRat (operation value.toClosedRat) mode saturation

/--
Apply an exact binary closed operation to both decoded operands, then project once into
`target`, by default the left operand's format.
-/
@[inline] def binary
    (operation : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat)
    (left : ExecFloat.P3109 leftFormat) (right : ExecFloat.P3109 rightFormat)
    (target : Format := leftFormat) (mode : RoundingMode := .nearest)
    (saturation : SaturationMode := .none) : ExecFloat.P3109 target :=
  projectRat (operation left.toClosedRat right.toClosedRat) mode saturation

/--
Evaluate a complete exact ternary closed expression, then project once into `target`, by default
the first operand's format.
-/
@[inline] def ternary
    (operation : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat →
      NumericalValue Rat)
    (left : ExecFloat.P3109 leftFormat) (right : ExecFloat.P3109 rightFormat)
    (third : ExecFloat.P3109 thirdFormat) (target : Format := leftFormat)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  projectRat (operation left.toClosedRat right.toClosedRat third.toClosedRat) mode saturation

/-- Negation followed by one projection, which also covers negative results in unsigned targets. -/
@[inline] def neg (value : ExecFloat.P3109 format) (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  unary Arithmetic.neg value target mode saturation

/-- Absolute value followed by one projection. -/
@[inline] def abs (value : ExecFloat.P3109 format) (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  unary Arithmetic.abs value target mode saturation

/-- Copy the sign of `sign`, propagating either NaN, and project once. -/
@[inline] def copySign (value sign : ExecFloat.P3109 format) (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  binary Arithmetic.copySign value sign target mode saturation

/-- Add the exact decoded operands and project once. -/
@[inline] def add (left right : ExecFloat.P3109 format) (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  binary Arithmetic.add left right target mode saturation

/-- Subtract the exact decoded operands and project once. -/
@[inline] def sub (left right : ExecFloat.P3109 format) (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  binary Arithmetic.sub left right target mode saturation

/-- Multiply the exact decoded operands and project once. -/
@[inline] def mul (left right : ExecFloat.P3109 format) (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  binary Arithmetic.mul left right target mode saturation

/-- Divide the exact decoded operands and project once. A zero denominator gives NaN. -/
@[inline] def div (left right : ExecFloat.P3109 format) (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  binary Arithmetic.div left right target mode saturation

/-- Take the exact reciprocal and project once. Zero gives NaN. -/
@[inline] def recip (value : ExecFloat.P3109 format) (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  unary Arithmetic.recip value target mode saturation

/-- Fused multiply-add: the exact `left * right + addend`, projected once. -/
@[inline] def fma (left right addend : ExecFloat.P3109 format) (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  ternary Arithmetic.fma left right addend target mode saturation

/-- Fused add-add: the exact `left + middle + right`, projected once. -/
@[inline] def faa (left middle right : ExecFloat.P3109 format) (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  ternary Arithmetic.faa left middle right target mode saturation

end FloatLib.Floats.ExecFloat.P3109
