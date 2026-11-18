/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.ExtendedRat.Runtime
public import FloatLib.Floats.Formats.P3109.Projection.Rational.Runtime

/-!
# Exact rational arithmetic for P3109

The closed operations in `Arithmetic` evaluate finite operands in `Rat` and keep infinities and
the report's single NaN. So division by zero returns NaN, even infinity divided by zero. FMA and
fused add-add form the complete exact expression before projecting.

Each `ExecFloat.P3109` operation projects into `(target := ...)`, which defaults to the format of
its operands, with `(mode := ...)` and `(saturation := ...)` options that default to nearest-even
rounding and no saturation request. `unary`, `binary`, and `ternary` apply any exact closed
operation to operands of independent descriptors. There are no IEEE exception flags and no
floating-point environment.

With a wide exponent range, exact rational intermediates can need large integers, and we don't
promise a fixed workspace bound for arbitrary descriptors.

## Reference

IEEE Working Group P3109, *Interim Report on Arithmetic Formats for Machine Learning*,
version 4.1 (14 September 2026), §§4.10.1–4.10.8, revision `2d45cf2`.
This is an unapproved working-group report, not an approved IEEE standard.
<https://github.com/P3109/Public/tree/2d45cf2fe0314d32251f5439d9d3ed078f93fbb9>.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.ExecFloat.P3109

open Formats.P3109

variable {source leftFormat rightFormat thirdFormat format : Format}

/-- Exact closed rational value of a P3109 operand.

Reference: P3109 Interim Report v4.1 (unapproved draft), §§4.7 and 4.10.3–4.10.8.
-/
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

/-- Negation followed by one projection, which also covers negative results in unsigned targets.

P3109 interim report v4.1 (14 September 2026), §4.10.1; unapproved draft.
-/
@[inline] def Negate (value : ExecFloat.P3109 format) (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  unary Arithmetic.Negate value target mode saturation

/-- Absolute value followed by one projection.

P3109 interim report v4.1 (14 September 2026), §4.10.1; unapproved draft.
-/
@[inline] def Abs (value : ExecFloat.P3109 format) (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  unary Arithmetic.Abs value target mode saturation

/-- Copy the sign of `sign`, propagating either NaN, and project once.

P3109 interim report v4.1 (14 September 2026), §4.10.2; unapproved draft.
-/
@[inline] def CopySign (value : ExecFloat.P3109 format) (sign : ExecFloat.P3109 rightFormat)
    (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  binary Arithmetic.CopySign value sign target mode saturation

/-- Add the exact decoded operands and project once.

P3109 interim report v4.1 (14 September 2026), §4.10.3; unapproved draft.
-/
@[inline] def Add (left : ExecFloat.P3109 format) (right : ExecFloat.P3109 rightFormat) (target
    : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  binary Arithmetic.Add left right target mode saturation

/-- Subtract the exact decoded operands and project once.

P3109 interim report v4.1 (14 September 2026), §4.10.3; unapproved draft.
-/
@[inline] def Subtract (left : ExecFloat.P3109 format) (right : ExecFloat.P3109 rightFormat)
    (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  binary Arithmetic.Subtract left right target mode saturation

/-- Multiply the exact decoded operands and project once.

P3109 interim report v4.1 (14 September 2026), §4.10.4; unapproved draft.
-/
@[inline] def Multiply (left : ExecFloat.P3109 format) (right : ExecFloat.P3109 rightFormat)
    (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  binary Arithmetic.Multiply left right target mode saturation

/-- Divide the exact decoded operands and project once. A zero denominator gives NaN.

P3109 interim report v4.1 (14 September 2026), §4.10.5; unapproved draft.
-/
@[inline] def Divide (left : ExecFloat.P3109 format) (right : ExecFloat.P3109 rightFormat)
    (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  binary Arithmetic.Divide left right target mode saturation

/-- Take the exact reciprocal and project once. Zero gives NaN.

P3109 interim report v4.1 (14 September 2026), §4.10.8; unapproved draft.
-/
@[inline] def Recip (value : ExecFloat.P3109 format) (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  unary Arithmetic.Recip value target mode saturation

/-- Fused multiply-add: the exact `left * right + addend`, projected once.

P3109 interim report v4.1 (14 September 2026), §4.10.6; unapproved draft.
-/
@[inline] def FMA (left : ExecFloat.P3109 format) (right : ExecFloat.P3109 rightFormat)
    (addend : ExecFloat.P3109 thirdFormat) (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  ternary Arithmetic.FMA left right addend target mode saturation

/-- Fused add-add: the exact `left + middle + right`, projected once.

P3109 interim report v4.1 (14 September 2026), §4.10.7; unapproved draft.
-/
@[inline] def FAA (left : ExecFloat.P3109 format) (middle : ExecFloat.P3109 rightFormat)
    (right : ExecFloat.P3109 thirdFormat) (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  ternary Arithmetic.FAA left middle right target mode saturation

end FloatLib.Floats.ExecFloat.P3109
