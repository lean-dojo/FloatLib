/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Model.ExactValue
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Mode
public import FloatLib.Numerics.Exact.DecimalText.Precision
public import FloatLib.Numerics.Exact.DecimalText.Special
public import FloatLib.Numerics.Exact.HexText.Runtime
public import FloatLib.Numerics.Exact.Dyadic.Format
public import FloatLib.Numerics.IEEEStatus
public import FloatLib.Numerics.Quantization.Deterministic.Rational

/-!
# Binary external character output

Exact decimal and hexadecimal output preserve finite values, signed zeros,
infinities and NaN diagnostics. Requested precision is an arbitrary positive
digit count. Both radices use the shared digit-grid and carry calculation.
Exponents are unbounded integers, so output can raise inexact but cannot overflow
or underflow. Signaling NaNs retain their signaling state without invalid.

External conversion is explicit through `formatDecimal`, `formatHex`, or
`formatWithStatus`. The existing `format` and `ToString` retain the compact dyadic
diagnostic display, which omits NaN metadata.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

/-- Radix of the external significand; hexadecimal output still has a decimal binary exponent. -/
inductive TextRadix where
  /-- Decimal digits and an optional e exponent. -/
  | decimal
  /-- Hexadecimal digits with a 0x prefix and mandatory p exponent. -/
  | hexadecimal
  deriving DecidableEq, Repr

/-- Exact output or an arbitrary positive significant-digit count, shared with decimal formats. -/
abbrev TextPrecision := Numerics.DecimalText.Precision

/-- A generated external character sequence and the exceptions raised while producing it. -/
structure TextOutcome where
  /-- Decimal, hexadecimal, infinity or diagnostic NaN text. -/
  text : String
  /-- Output rounding can raise inexact; all other exception indicators remain clear. -/
  status : Numerics.IEEEStatus := {}
  deriving DecidableEq, Repr

/-- Integer magnitude rounding for an external digit grid, using existing exact integer rounders. -/
def roundTextMagnitude (mode : IEEERoundingMode) (negative : Bool) (x : Rat) : Nat :=
  match mode with
  | .nearestEven => (Numerics.roundRatEven x).natAbs
  | .towardZero => ⌊x⌋₊
  | .towardPositiveInfinity => if negative then ⌊x⌋₊ else ⌈x⌉₊
  | .towardNegativeInfinity => if negative then ⌈x⌉₊ else ⌊x⌋₊

/-- Exact or significant-digit output for an unrounded dyadic, with numerical inexactness. -/
def formatDyadicText (mode : IEEERoundingMode) (radix : TextRadix)
    (precision : TextPrecision) (value : Numerics.Dyadic) : TextOutcome :=
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

/-- Format any binary descriptor at exact or requested precision, preserving special metadata. -/
def formatWithStatus {fmt : FloatFormat} (mode : IEEERoundingMode) (radix : TextRadix)
    (precision : TextPrecision) (value : Model fmt) : TextOutcome :=
  match exactValue value with
  | .finite exact => formatDyadicText mode radix precision exact
  | .infinity negative =>
      { text := String.ofList (Numerics.SpecialText.infinityCharacters negative) }
  | .nan negative signaling payload =>
      { text := String.ofList (Numerics.SpecialText.nanCharacters negative signaling payload) }

/-- Exact decimal external output, preserving signed zero and complete NaN metadata. -/
def formatDecimal {fmt : FloatFormat} (value : Model fmt) : String :=
  (formatWithStatus .nearestEven .decimal .exact value).text

/-- Exact hexadecimal display, including the complete diagnostic spelling for a NaN. -/
def formatHex {fmt : FloatFormat} (value : Model fmt) : String :=
  (formatWithStatus .nearestEven .hexadecimal .exact value).text

/-- Host-independent diagnostic display, using compact dyadic text for finite values.
Use `formatDecimal` or `formatHex` for external conversion with NaN metadata. -/
def format {fmt : FloatFormat} (value : Model fmt) : String :=
  match exactValue value with
  | .finite exact => exact.format
  | .infinity true => "-inf"
  | .infinity false => "inf"
  | .nan _ _ _ => "nan"

instance {fmt : FloatFormat} : ToString (Model fmt) where
  toString := format

end FloatLib.Floats.Formats.BinaryInterchange.Model
