/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Runtime
public import FloatLib.Numerics.Exact.DecimalText.Special

/-!
# Decimal character conversion

Finite text uses the shared exact decimal scanner. The coefficient and quantum
are kept separately until one destination rounding, with the written quantum as
the preferred exponent. Exact output uses coefficient/exponent notation:
`120e-2` and `12e-1` have equal values but preserve different representations.

This binding accepts ASCII decimal syntax without whitespace, and case-insensitive
`Inf`, `Infinity`, `NaN`, and `sNaN`, with an optional sign. NaN names may have
decimal payload digits. Output preserves NaN sign, signaling state, and payload;
reading an `sNaN` spelling creates a signaling NaN without raising invalid.
Malformed text or an unrepresentable NaN payload produces positive quiet NaN
with payload zero and the invalid flag. Finite conversion uses all five rounding
modes and the projection layer's tininess-before-rounding policy.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Formatting

open FloatLib.Numerics.DecimalText

/-- Interpret the shared special spellings as decimal datums. -/
abbrev parseSpecial := FloatLib.Numerics.SpecialText.parseSpecial Datum.infinity Datum.nan

/-- Parse an unbounded decimal datum, before applying a destination format. -/
def readCharacters (characters : List Char) : Option Datum :=
  match parseCharacters characters with
  | some value => some (.finite value.negative value.significand value.exponent)
  | none =>
      let (negative, rest) := splitSign characters
      parseSpecial negative rest

/-- Exact character decoding, including the written quantum and the sign of zero. -/
def read (text : String) : Option Datum := readCharacters text.toList

/-- The default result for a syntax error or an oversized diagnostic payload. -/
def invalidText : Outcome :=
  { value := .nan false false 0, status := { invalid := true } }

/-- Round a decoded datum into a destination format. Special spellings do not perform arithmetic. -/
def convert (f : Format) (mode : RoundingMode) : Datum → Outcome
  | .finite negative coefficient quantum =>
      projectScaled f mode negative coefficient quantum quantum
  | .infinity negative => { value := .infinity negative }
  | .nan negative signaling payload =>
      if payload < f.payloadBound then { value := .nan negative signaling payload }
      else invalidText

/-- Convert a complete string, reporting IEEE status flags for finite rounding and invalid text. -/
def parse (f : Format) (mode : RoundingMode) (text : String) : Outcome :=
  match read text with
  | some value => convert f mode value
  | none => invalidText

/-- An exact spelling preserves every component of a datum, including zero's quantum. -/
def characters : Datum → List Char
  | .finite negative coefficient quantum =>
      Decimal.characters ⟨negative, coefficient, quantum⟩
  | .infinity negative =>
      Numerics.SpecialText.infinityCharacters negative
  | .nan negative signaling payload =>
      Numerics.SpecialText.nanCharacters negative signaling payload

/-- Exact coefficient/quantum output; no rounding or floating-point exceptions occur. -/
def formatExact (value : Datum) : String := String.ofList (characters value)

end FloatLib.Floats.Formats.DecimalInterchange.Formatting
