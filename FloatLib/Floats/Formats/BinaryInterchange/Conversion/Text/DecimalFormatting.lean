/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.Digits
public import FloatLib.Numerics.Exact.DecimalText.Notation

/-!
# Fixed and scientific decimal output

Both notations take a number of digits after the decimal point. Fixed output rounds on the grid
`10^(-places)`, and scientific output keeps `places + 1` significant digits. Rounding happens once
on the exact decimal value, before inserting the point and exponent. Trailing zeros express the
requested precision, and a negative value that rounds to zero retains its sign.

These operations use exact integer arithmetic for any binary descriptor. They do not call the
host floating-point printer. `Model.format` selects them with `style := .fixed places` and
`style := .scientific places`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Numerics

/-- Round an exact decimal once on the grid `10^(-places)`. -/
def roundFixed (mode : IEEERoundingMode) (places : Nat) (value : DecimalText.Decimal) :
    DecimalText.Decimal :=
  DecimalText.roundDecimal (roundTextMagnitude mode) value (-(places : Int))

/-- Round an exact decimal once to `places + 1` significant digits. -/
def roundScientific (mode : IEEERoundingMode) (places : Nat) (value : DecimalText.Decimal) :
    DecimalText.Decimal :=
  DecimalText.significantDecimal (roundTextMagnitude mode) value ⟨places + 1, by omega⟩

/-- Fixed output of an exact dyadic with `places` fractional digits and its rounding status. -/
@[inline] def fixedText (mode : IEEERoundingMode) (places : Nat) (value : Numerics.Dyadic) :
    TextOutcome :=
  let original := DecimalText.ofDyadic value
  let rounded := roundFixed mode places original
  { text := rounded.formatFixed
    status := { inexact := decide (rounded.toRat ≠ original.toRat) } }

/-- Scientific output of an exact dyadic with `places + 1` significant digits and its status. -/
@[inline] def scientificText (mode : IEEERoundingMode) (places : Nat) (value : Numerics.Dyadic) :
    TextOutcome :=
  let original := DecimalText.ofDyadic value
  let rounded := roundScientific mode places original
  { text := rounded.formatScientific
    status := { inexact := decide (rounded.toRat ≠ original.toRat) } }

end FloatLib.Floats.Formats.BinaryInterchange.Model
