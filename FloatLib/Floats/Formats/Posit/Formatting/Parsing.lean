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

Decimal integers, fractions, and decimal exponents denote exact rationals, rounded once according
to Posit Standard (2022), §4.1. `NaR` names the unique exceptional value. Empty or malformed input
returns an explicit error. The decimal grammar does not accept whitespace or radix-two notation.

Together with decimal display, this implements the value-preserving decimal character conversion
described in §6.3. The character and posit round-trip proofs are in `Formatting.Proof`.

## References

* Posit Working Group, *Standard for Posit Arithmetic (2022)*, March 2, 2022, §§4.1, 6.3,
  <https://posithub.org/docs/posit_standard-2.pdf>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

/-- A decimal-input failure, distinct from the explicit `NaR` spelling. -/
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
Read a decimal rational and round it once to the requested posit width.

Accepted finite syntax includes `12`, `-0.125`, `.5`, `1.`, and `+25e-3`. Only `NaR` requests the
exceptional value; invalid syntax never silently becomes zero or NaR.
-/
def parse (format : Format) (input : String) : Except ParseError (Model format) :=
  if input = "NaR" then .ok (nar format)
  else
    match FloatLib.Numerics.DecimalText.parse input with
    | some value => .ok (roundRat format value)
    | none => .error (if input = "" then .emptyInput else .invalidSyntax input)

end FloatLib.Floats.Formats.Posit.Model
