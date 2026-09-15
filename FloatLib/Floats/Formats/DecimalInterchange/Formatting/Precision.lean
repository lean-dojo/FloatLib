/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Formatting.Runtime
public import FloatLib.Numerics.Exact.DecimalText.Precision

/-!
# Selecting decimal output precision

IEEE 754 §5.12.2 distinguishes preserving the source quantum from requesting a
number of significant digits. `Precision` makes this choice explicit. Requested
precision has no format-width cap: the coefficient is rounded once on the
requested decimal grid, and extra requested digits are supplied by exact zeros.
The text exponent is an unbounded integer, so output has no exponent overflow.

Zero at precision `p` is written with quantum `1-p`. Special values keep their
exact spellings and fields. Only inexact can be raised during finite output.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Formatting

open FloatLib.Numerics.DecimalText

/-- Preserving the original quantum and requesting a digit count are separate operations. -/
abbrev Precision := FloatLib.Numerics.DecimalText.Precision

/-- Correctly rounded significant-digit output, with an unbounded requested precision. -/
abbrev significantDecimal (mode : RoundingMode) :=
  FloatLib.Numerics.DecimalText.significantDecimal mode.roundMagnitude

/-- The external string together with the conversion's IEEE status flags. -/
structure TextOutcome where
  /-- The generated external decimal character sequence. -/
  text : String
  /-- Exceptions raised by this conversion; output rounding can raise only inexact. -/
  status : Status := {}
  deriving DecidableEq, Repr

/-- Format a datum either exactly or to a requested significant-digit count.
The inexact flag records numerical rounding, rather than a change of quantum. -/
def format (mode : RoundingMode) (precision : Precision) (value : Datum) : TextOutcome :=
  match precision, value with
  | .significant digits, .finite negative coefficient quantum =>
      let original : Decimal := ⟨negative, coefficient, quantum⟩
      let result := significantDecimal mode original digits
      { text := result.format, status := { inexact := decide (result.toRat ≠ original.toRat) } }
  | _, _ => { text := formatExact value }

end FloatLib.Floats.Formats.DecimalInterchange.Formatting
