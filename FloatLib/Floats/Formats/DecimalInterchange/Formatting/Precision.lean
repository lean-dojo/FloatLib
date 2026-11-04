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

When you print a decimal you can keep its quantum or ask for a number of significant digits, and
IEEE 754 §5.12.2 treats those as two different requests. `Precision` names the choice. A requested
precision has no cap from the format width. The coefficient is rounded once on the requested
decimal grid, and any extra digits you ask for are exact zeros, so `1.5` at four digits gets the
coefficient `1500`. The text exponent is an unbounded integer, so output never overflows its
exponent.

Zero at precision `p` is written with quantum `1-p`. Special values keep their spellings and
fields, and finite output can raise only inexact.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Formatting

open FloatLib.Numerics.DecimalText

/-- Output precision: keep the source quantum or request a significant-digit count. -/
abbrev Precision := FloatLib.Numerics.DecimalText.Precision

/-- Correctly rounded significant-digit output, with an unbounded requested precision. -/
abbrev significantDecimal (mode : RoundingMode) :=
  FloatLib.Numerics.DecimalText.significantDecimal mode.roundMagnitude

/-- The external string together with the conversion's IEEE status flags. -/
structure TextOutcome where
  /-- The generated external decimal character sequence. -/
  text : String
  /-- Exceptions raised by this conversion. Output rounding can raise only inexact. -/
  status : Numerics.IEEEStatus := {}
  deriving DecidableEq, Repr

/-- Format a datum either exactly or to a requested significant-digit count.
The inexact flag records a change of value, and a change of quantum alone doesn't raise it. -/
def format (mode : RoundingMode) (precision : Precision) (value : Datum) : TextOutcome :=
  match precision, value with
  | .significant digits, .finite negative coefficient quantum =>
      let original : Decimal := ⟨negative, coefficient, quantum⟩
      let result := significantDecimal mode original digits
      { text := result.format, status := { inexact := decide (result.toRat ≠ original.toRat) } }
  | _, _ => { text := formatExact value }

end FloatLib.Floats.Formats.DecimalInterchange.Formatting
