/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.DecimalText.Runtime
public import FloatLib.Floats.Formats.Posit.Rounding.Runtime

/-!
# Posit decimal input

A string such as `-0.125` or `+25e-3` denotes an exact rational, and the parser rounds it once,
following Posit Standard (2022), §4.1. Decimal integers, fractions, and decimal exponents all work
this way, and `NaR` names the unique exceptional value. Empty or malformed input returns an error.
Whitespace and radix-two notation aren't part of the grammar.

Together with decimal display, this implements the value-preserving decimal character conversion
of §6.3. You'll find the character and posit round-trip proofs in `Formatting.Proof`.

## References

* Posit Working Group, *Standard for Posit Arithmetic (2022)*, March 2, 2022, §§4.1, 6.3,
  <https://posithub.org/docs/posit_standard-2.pdf>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

/-- A decimal-input failure, which is never confused with a written `NaR`. -/
inductive ParseError where
  /-- The supplied string has no characters. -/
  | emptyInput
  /-- The string is neither decimal syntax nor `NaR`. -/
  | invalidSyntax (input : String)
  deriving DecidableEq, Repr

/-- Human-readable explanation of a decimal-input failure. -/
def ParseError.message : ParseError → String
  | .emptyInput => "empty posit input"
  | .invalidSyntax input => s!"invalid posit decimal input: {input}"

instance : ToString ParseError where
  toString := ParseError.message

/--
A decimal exponent at which every nonzero significand already reaches maxPos.

It is the bit length of the numerator of maxPos (`log2 + 1`). That numerator is below two to this
power, so ten to this power exceeds maxPos, and so does any nonzero significand scaled by it.
-/
def decimalSaturationExponent (format : Format) : Int :=
  ((nonnegativeRatAt format (format.signMaskNat - 1)).num.natAbs.log2 : Int) + 1

/--
A decimal exponent at which the given significand, scaled by ten to this power, lies below minPos.

The bound adds the bit lengths of the significand and of the denominator of minPos.
-/
def decimalVanishingExponent (format : Format) (significand : Nat) : Int :=
  -(((significand.log2 + 1 : Nat) : Int) + (((minPositiveRat format).den.log2 + 1 : Nat) : Int))

/--
Move a decimal exponent into the range where it can affect posit rounding.

Posits saturate: every positive value at or above maxPos rounds to maxPos, and every positive value
below minPos rounds to minPos. Exponents beyond these points are replaced by the nearest endpoint,
and the exponent of a zero significand becomes zero. `roundRat_clampDecimal` proves that rounding
the clamped decimal gives the same posit, so the parser never builds a huge power of ten.
-/
def clampDecimal (format : Format) (value : FloatLib.Numerics.DecimalText.Decimal) :
    FloatLib.Numerics.DecimalText.Decimal :=
  if value.significand = 0 then { value with exponent := 0 }
  else
    { value with
      exponent := max (decimalVanishingExponent format value.significand)
        (min (decimalSaturationExponent format) value.exponent) }

/--
Read a decimal rational and round it once to the requested posit width.

Accepted finite syntax includes `12`, `-0.125`, `.5`, `1.`, and `+25e-3`. Only `NaR` requests the
exceptional value, and invalid syntax never silently becomes zero or NaR. Written exponents far
outside the posit range are clamped first (see `clampDecimal`), which leaves the rounded result
unchanged and keeps inputs such as `1e1000000000` cheap.
-/
def parse (format : Format) (input : String) : Except ParseError (Model format) :=
  if input = "NaR" then .ok (nar format)
  else
    match FloatLib.Numerics.DecimalText.parseCharacters input.toList with
    | some value => .ok (roundRat format (clampDecimal format value).toRat)
    | none => .error (if input = "" then .emptyInput else .invalidSyntax input)

end FloatLib.Floats.Formats.Posit.Model
