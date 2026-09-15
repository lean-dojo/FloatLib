/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Capabilities.Radix
public import Mathlib.Data.Rat.Defs

/-!
# Exact fixed-point representation and execution

The code stores an unbounded integer coefficient with its radix and fractional precision in the
type. Its exact rational decoder and coefficient operations are defined together here: addition,
subtraction, and negation keep the scale; multiplication composes the two operand scales.

No operation rounds or overflows. `Exact.Proof` defines the rational numerical system and proves
these operations refine exact arithmetic. Bounded coefficient policies live in `FixedPoint.Bounded`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.FixedPoint

open FloatLib.Numerics

/-- Natural denominator of a fixed-point grid with the given radix and fractional precision. -/
@[inline] def scale (radix : Radix) (fractionalDigits : Nat) : Nat :=
  radix.base ^ fractionalDigits

/-- An integer coefficient interpreted with `fractionalDigits` radix digits after the point. -/
structure Code (radix : Radix) (fractionalDigits : Nat) where
  /-- Signed integer numerator before division by `radix.base ^ fractionalDigits`. -/
  coefficient : Int
  deriving DecidableEq, Repr

end FloatLib.Floats.Formats.FixedPoint

/-! ## Executable operations -/

namespace FloatLib.Floats.Formats.FixedPoint.Code

open FloatLib.Numerics

/-- Exact rational value of a fixed-point code. -/
@[inline] def toRat {radix : Radix} {fractionalDigits : Nat}
    (value : Code radix fractionalDigits) : ℚ :=
  value.coefficient / (scale radix fractionalDigits : Nat)

/-- Encode an integer coefficient directly. -/
@[inline] def ofInt (radix : Radix) (fractionalDigits : Nat) (coefficient : Int) :
    Code radix fractionalDigits :=
  ⟨coefficient⟩

/-- Exact addition of fixed-point values with a common scale. -/
@[inline] def add {radix : Radix} {fractionalDigits : Nat}
    (left right : Code radix fractionalDigits) : Code radix fractionalDigits :=
  ⟨left.coefficient + right.coefficient⟩

/-- Exact additive inverse at the same scale. -/
@[inline] def neg {radix : Radix} {fractionalDigits : Nat}
    (value : Code radix fractionalDigits) : Code radix fractionalDigits :=
  ⟨-value.coefficient⟩

/-- Exact subtraction at a common scale. -/
@[inline] def sub {radix : Radix} {fractionalDigits : Nat}
    (left right : Code radix fractionalDigits) : Code radix fractionalDigits :=
  add left (neg right)

/--
Exact multiplication. Multiplying scales `p` and `q` produces scale `p + q`; no hidden rescaling
or rounding occurs.
-/
@[inline] def mul {radix : Radix} {p q : Nat}
    (left : Code radix p) (right : Code radix q) : Code radix (p + q) :=
  ⟨left.coefficient * right.coefficient⟩

end FloatLib.Floats.Formats.FixedPoint.Code
