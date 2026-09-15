/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.Formatting
public import FloatLib.Numerics.Exact.DecimalText.Notation

/-!
# Fixed and scientific decimal output

Both styles take a number of digits after the decimal point. Fixed output rounds on the grid
`10^(-places)`; scientific output keeps `places + 1` significant digits. Rounding happens once
on the exact decimal value, before inserting the point and exponent. Trailing zeros express the
requested precision, and a negative value that rounds to zero retains its sign.

These operations use exact integer arithmetic for any binary descriptor. They do not call the
host floating-point printer. Infinities and NaNs use the same diagnostic spelling as
`formatDecimal`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Numerics

/-- Conventional decimal notation, with precision measured after the decimal point. -/
inductive DecimalStyle where
  /-- Ordinary decimal notation with exactly this many fractional digits. -/
  | fixed (places : Nat)
  /-- One digit before the decimal point and this many after it, followed by an `e` exponent. -/
  | scientific (places : Nat)
  deriving DecidableEq, Repr

/-- Round an exact decimal once at the precision required by the selected notation. -/
def roundDecimalForStyle (mode : IEEERoundingMode) (style : DecimalStyle)
    (value : DecimalText.Decimal) : DecimalText.Decimal :=
  match style with
  | .fixed places => DecimalText.roundDecimal (roundTextMagnitude mode) value (-(places : Int))
  | .scientific places =>
      DecimalText.significantDecimal (roundTextMagnitude mode) value ⟨places + 1, by omega⟩

/-- Render a decimal already rounded by `roundDecimalForStyle` with this same style.
The decimal record supplies the fractional places; this step only inserts notation. -/
def renderDecimalStyle (style : DecimalStyle) (value : DecimalText.Decimal) : String :=
  match style with
  | .fixed _ => value.formatFixed
  | .scientific _ => value.formatScientific

/-- Fixed or scientific output of an exact dyadic, including numerical rounding status. -/
def formatDyadicDecimal (mode : IEEERoundingMode) (style : DecimalStyle)
    (value : Numerics.Dyadic) : TextOutcome :=
  let original := DecimalText.ofDyadic value
  let rounded := roundDecimalForStyle mode style original
  { text := renderDecimalStyle style rounded
    status := { inexact := decide (rounded.toRat ≠ original.toRat) } }

/-- Decimal output with an explicit notation, rounding direction, and inexact indicator. -/
def formatDecimalWithStatus {fmt : FloatFormat} (mode : IEEERoundingMode)
    (style : DecimalStyle) (value : Model fmt) : TextOutcome :=
  match exactValue value with
  | .finite exact => formatDyadicDecimal mode style exact
  | .infinity negative =>
      { text := String.ofList (SpecialText.infinityCharacters negative) }
  | .nan negative signaling payload =>
      { text := String.ofList (SpecialText.nanCharacters negative signaling payload) }

/-- Nearest-even decimal output with exactly `places` digits after the decimal point. -/
def formatFixed {fmt : FloatFormat} (value : Model fmt) (places : Nat) : String :=
  (formatDecimalWithStatus .nearestEven (.fixed places) value).text

/-- Nearest-even scientific output with `places + 1` significant digits and an `e` exponent. -/
def formatScientific {fmt : FloatFormat} (value : Model fmt) (places : Nat) : String :=
  (formatDecimalWithStatus .nearestEven (.scientific places) value).text

end FloatLib.Floats.Formats.BinaryInterchange.Model
