/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Rounding.SqrtRuntime
public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Decode
public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Rational
public import FloatLib.Floats.ExecFloat.Backends.Generic.Sqrt.Runtime

/-!
# Single-round binary algebraic operations

These operations evaluate exact expressions and round only the final result. The norm forms an
exact dyadic sum of squares. Square roots use integer square root after exact target scaling;
other roots compare integer powers of rational boundaries without a refinement budget.
All widths and complete descriptors use the same algorithms. Specialization on the descriptor
lets compiled calls share format constants and remove inapplicable encoding branches. Integer
powers can materialize large exact integers; the exponent is not capped.

Signed zero, infinities and invalid arguments are handled before exact evaluation. A zero
integer exponent returns one, including for a quiet NaN base; signaling NaNs are quieted first.
Degree zero is invalid for `rootN`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

/-- Round an exact rational value once, using the complete format descriptor. -/
@[inline] def roundAlgebraicRat (fmt : FloatFormat) (value : Rat) : Model fmt :=
  roundRat fmt (decide (value < 0)) value.num.natAbs value.den

namespace Algebraic

/-- Square root of an exact dyadic sum of squares, with no intermediate format rounding. -/
@[inline] def hypotDyadic (fmt : FloatFormat) (left right : Numerics.Dyadic) : Model fmt :=
  let sum := left.sumSquares right
  FiniteSqrt.sqrtPositiveDyadic fmt sum.significand sum.exponent

end Algebraic

/--
Reciprocal square root, rounded once from the exact reciprocal radicand.

Positive infinity gives positive zero. Signed zero gives the correspondingly signed overflow
value. Negative nonzero inputs are invalid; NaNs retain the unary propagation policy.
-/
@[specialize fmt] def rsqrt {fmt : FloatFormat} (value : Model fmt) : Model fmt :=
  match chooseNaN1 value with
  | some nan => nan
  | none =>
    if isZero value then nativeOverflow fmt (signBit value)
    else if signBit value then invalidResult fmt
    else if isInf value then posZero fmt
    else
      match toRat? value with
      | none => invalidResult fmt
      | some q => AlgebraicRounding.sqrtRat fmt false q⁻¹

/--
Euclidean norm, rounded once from the exact sum of squares.

An infinite operand gives positive overflow, including when the other operand is a quiet NaN.
A signaling NaN takes precedence. Two zeros give positive zero, independently of their signs.
-/
@[specialize fmt] def hypot {fmt : FloatFormat} (left right : Model fmt) : Model fmt :=
  if isSNaN left || isSNaN right then
    (chooseNaN2 left right).getD (invalidResult fmt)
  else if isInf left || isInf right then nativeOverflow fmt false
  else
    match chooseNaN2 left right with
    | some nan => nan
    | none =>
      match toDyadic? left, toDyadic? right with
      | some a, some b => Algebraic.hypotDyadic fmt a b
      | _, _ => invalidResult fmt

/--
Integer-exponent power with one final rounding.

For nonzero finite bases, exponentiation takes place in the exact rationals, including negative
exponents. Zero and infinity retain a negative sign exactly for an odd exponent. A signaling
NaN is quieted before the zero-exponent rule; otherwise the zero exponent returns one.
-/
@[specialize fmt] def powInt {fmt : FloatFormat} (value : Model fmt) (exponent : Int) : Model fmt :=
  if isSNaN value then (chooseNaN1 value).getD (invalidResult fmt)
  else if exponent = 0 then posOne fmt
  else
    match chooseNaN1 value with
    | some nan => nan
    | none =>
      let sign := signBit value && exponent % 2 != 0
      if isZero value then
        if exponent < 0 then nativeOverflow fmt sign else zero fmt sign
      else if isInf value then
        if exponent < 0 then zero fmt sign else nativeOverflow fmt sign
      else
        match toRat? value with
        | none => invalidResult fmt
        | some q => roundAlgebraicRat fmt (q ^ exponent)

/--
Integer root with one final rounding, including reciprocal roots for negative degrees.

Even degrees require a nonnegative input; odd degrees use the signed real root.
For positive degrees, negative zero gives negative zero for odd degrees and positive zero
for even degrees. For negative degrees, either zero gives overflow with a negative sign
exactly when the input is negative zero and the degree is odd. Negative nonzero inputs with
even degree and all inputs with degree zero are invalid.
-/
@[specialize fmt] def rootN {fmt : FloatFormat} (value : Model fmt) (degree : Int) : Model fmt :=
  if degree = 0 then invalidResult fmt
  else
    match chooseNaN1 value with
    | some nan => nan
    | none =>
      let sign := signBit value && degree % 2 != 0
      if isZero value then
        if degree < 0 then nativeOverflow fmt sign else zero fmt sign
      else if signBit value && degree % 2 == 0 then invalidResult fmt
      else if isInf value then
        if degree < 0 then zero fmt sign else nativeOverflow fmt sign
      else
        match toRat? value with
        | none => invalidResult fmt
        | some q =>
          let radicand := if degree < 0 then |q|⁻¹ else |q|
          AlgebraicRounding.rootWithSqrt fmt sign radicand degree.natAbs

end FloatLib.Floats.Formats.BinaryInterchange.Model
