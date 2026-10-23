/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Mode
public import FloatLib.Numerics.Exact.DecimalText.Precision
public import FloatLib.Numerics.Exact.HexText.Runtime
public import FloatLib.Numerics.IEEEStatus
public import FloatLib.Numerics.Quantization.Deterministic.Rational

/-!
# Exact and significant-digit text of binary values

Exact decimal and hexadecimal output preserve every finite value. Requested precision is an
arbitrary positive digit count. Both radices use the shared digit-grid and carry calculation.
Exponents are unbounded integers, so output can raise inexact but cannot overflow or underflow.
`Model.format` selects these digits through its `style` option.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

/-- Radix of the external significand. Hexadecimal output writes its binary exponent in decimal. -/
inductive TextRadix where
  /-- Decimal digits and an optional e exponent. -/
  | decimal
  /-- Hexadecimal digits with a 0x prefix and mandatory p exponent. -/
  | hexadecimal
  deriving DecidableEq, Repr

/-- A generated external character sequence and the exceptions raised while producing it. -/
structure TextOutcome where
  /-- Decimal, hexadecimal, infinity or diagnostic NaN text. -/
  text : String
  /-- Output rounding can raise inexact, and every other exception indicator stays clear. -/
  status : Numerics.IEEEStatus := {}
  deriving DecidableEq, Repr

/--
Integer magnitude rounding for an external digit grid, using the exact integer rounders.

The magnitude `x` is nonnegative. Nearest-away rounding is `Numerics.roundQuotient .nearestAway`
on its numerator and denominator, and rounding away from zero is the ceiling.
-/
def roundTextMagnitude (mode : IEEERoundingMode) (negative : Bool) (x : Rat) : Nat :=
  match mode with
  | .nearest => (Numerics.roundRatEven x).natAbs
  | .nearestAway => Numerics.roundQuotient .nearestAway x.num.natAbs x.den
  | .towardZero => ⌊x⌋₊
  | .up => if negative then ⌊x⌋₊ else ⌈x⌉₊
  | .down => if negative then ⌈x⌉₊ else ⌊x⌋₊
  | .away => ⌈x⌉₊

/-- Exact or significant-digit output for an unrounded dyadic, with numerical inexactness. -/
@[inline] def formatDyadicText (mode : IEEERoundingMode) (radix : TextRadix)
    (precision : Numerics.DecimalText.Precision) (value : Numerics.Dyadic) : TextOutcome :=
  match radix, precision with
  | .decimal, .exact => { text := Numerics.DecimalText.formatDyadic value }
  | .hexadecimal, .exact => { text := Numerics.HexText.format value }
  | .decimal, .significant digits =>
      let original := Numerics.DecimalText.ofDyadic value
      let result := Numerics.DecimalText.significantDecimal (roundTextMagnitude mode)
        original digits
      { text := result.format, status := { inexact := decide (result.toRat ≠ original.toRat) } }
  | .hexadecimal, .significant digits =>
      let result := Numerics.HexText.significant (roundTextMagnitude mode) value digits
      { text := Numerics.HexText.format result,
        status := { inexact := decide (result.toRat ≠ value.toRat) } }

end FloatLib.Floats.Formats.BinaryInterchange.Model
