/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Status.Runtime
public import FloatLib.Numerics.Exact.DecimalText.Special
public import FloatLib.Numerics.Exact.HexText.Runtime

/-!
# Binary external character conversion

Decimal integers, fractions and e/E exponents use the shared exact scanner.
Hexadecimal input follows IEEE 754 §5.12.3, including its mandatory p/P exponent.
The older `m * 2^e` spelling remains accepted. ASCII edge whitespace is ignored.
Finite conversion rounds once and reports the existing binary exception policy,
including tininess after rounding. Syntax errors remain explicit `ParseError`s.

Inf/Infinity/NaN/sNaN accept either case and an optional sign. A NaN's decimal
suffix denotes its complete fraction field, including the quiet bit. Zero or
an absent suffix chooses a default payload. Valid explicit payloads preserve
sign and signaling state without invalid. A descriptor unable to encode a
signaling NaN may quiet the default sNaN and raise invalid.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

/-- Why exact character input could not produce a value in the requested format. -/
inductive ParseError where
  /-- The input contains no non-whitespace characters. -/
  | emptyInput
  /-- The input is not a supported decimal, radix-two, infinity, or NaN spelling. -/
  | invalidSyntax (input : String)
  /-- The input requests an infinity from a finite-only encoding. -/
  | unsupportedInfinity (negative : Bool)
  /-- The input requests a NaN from an encoding with no NaN representation. -/
  | unsupportedNaN
  /-- The input exceeds the caller's byte limit before character scanning. -/
  | inputTooLong (actual maximum : Nat)
  /-- The adjusted decimal or binary exponent exceeds the caller's magnitude limit. -/
  | exponentTooLarge (actual maximum : Nat)
  deriving Repr, DecidableEq

/-- Concise human-readable explanation of a character-input failure. -/
def ParseError.message : ParseError → String
  | .emptyInput => "empty floating-point input"
  | .invalidSyntax input => s!"invalid floating-point input: {input}"
  | .unsupportedInfinity false => "the destination format has no positive infinity"
  | .unsupportedInfinity true => "the destination format has no negative infinity"
  | .unsupportedNaN => "the destination format has no NaN representation"
  | .inputTooLong actual maximum =>
      s!"floating-point input has {actual} bytes; limit is {maximum}"
  | .exponentTooLarge actual maximum =>
      s!"floating-point exponent magnitude is {actual}; limit is {maximum}"

instance : ToString ParseError where
  toString := ParseError.message

/-- Unrounded external text, retaining a decimal scale or binary scale and signed zero. -/
inductive TextValue where
  /-- An exact decimal coefficient and written decimal exponent. -/
  | decimal (value : Numerics.DecimalText.Decimal)
  /-- An exact dyadic from hexadecimal or legacy radix-two syntax. -/
  | dyadic (value : Numerics.Dyadic)
  /-- A signed infinity. -/
  | infinity (negative : Bool)
  /-- A signed NaN with signaling state and complete-fraction diagnostic suffix. -/
  | nan (negative signaling : Bool) (payload : Nat)
  deriving DecidableEq, Repr

/-- Decode the legacy exact radix-two spelling, using the common integer scanner. -/
def readLegacyDyadic (text : String) : Option Numerics.Dyadic := do
  let parts := (text.replace " " "").splitOn "*2^"
  let (coefficient, exponent) ← match parts with
    | [coefficient, exponent] => some (coefficient, exponent)
    | _ => none
  let (negative, rest) := Numerics.DecimalText.splitSign coefficient.toList
  let (significand, count, tail) := Numerics.RadixText.scanDigits rest 0 10
    Numerics.DecimalText.digitValue?
  if count = 0 ∨ tail ≠ [] then none
  else
    let exponent ← Numerics.DecimalText.parseInteger exponent.toList
    some { negative, significand, exponent }

/-- Decode one complete trimmed string before choosing a destination format or rounding. -/
def readText (text : String) : Option TextValue :=
  match Numerics.DecimalText.parseCharacters text.toList with
  | some value => some (.decimal value)
  | none =>
      match Numerics.HexText.parse text with
      | some value => some (.dyadic value)
      | none =>
          match readLegacyDyadic text with
          | some value => some (.dyadic value)
          | none =>
              let (negative, rest) := Numerics.DecimalText.splitSign text.toList
              Numerics.SpecialText.parseSpecial TextValue.infinity TextValue.nan negative rest

/-- One exact decimal-to-binary rounding, paired with the shared binary status calculation. -/
def convertDecimalText (fmt : FloatFormat) (mode : IEEERoundingMode)
    (exact : Numerics.DecimalText.Decimal) : IEEEOutcome fmt :=
  let magnitude := (exact.significand : Rat) * (10 : Rat) ^ exact.exponent
  let value := roundRatWithRounding fmt mode exact.negative magnitude.num.natAbs magnitude.den
  { value, status := rationalRoundingStatus fmt mode exact.negative
      magnitude.num.natAbs magnitude.den value }

/-- One hexadecimal or legacy dyadic conversion with binary rounding status. -/
def convertDyadicText (fmt : FloatFormat) (mode : IEEERoundingMode)
    (exact : Numerics.Dyadic) : IEEEOutcome fmt :=
  let value := roundDyadicWithRounding fmt mode exact
  { value, status := dyadicRoundingStatus fmt mode exact value }

/-- Interpret a NaN diagnostic according to the descriptor, rejecting unrepresentable payloads. -/
def convertNaNText (fmt : FloatFormat) (negative signaling : Bool) (payload : Nat) :
    Except ParseError (IEEEOutcome fmt) :=
  match canonicalNaN? fmt with
  | none => .error .unsupportedNaN
  | some canonical =>
      let defaultValue := if negative != signBit canonical then neg canonical else canonical
      let fraction := if payload = 0 then
          if signaling then 1 else fracField defaultValue
        else payload
      let candidate := match fmt.encoding with
        | .finiteUnsignedZero => defaultValue
        | _ => ofFields fmt negative fmt.expAllOnesNat fraction
      if isNaN candidate && isSNaN candidate == signaling &&
          fracField candidate == fraction then
        .ok { value := candidate, status := {} }
      else if payload = 0 then
        .ok { value := defaultValue, status := { invalid := signaling } }
      else .error (.invalidSyntax "unrepresentable NaN diagnostic")

/-- Convert a decoded text value. Unsupported specials and invalid diagnostics are explicit errors. -/
def convertText (fmt : FloatFormat) (mode : IEEERoundingMode) :
    TextValue → Except ParseError (IEEEOutcome fmt)
  | .decimal value => .ok (convertDecimalText fmt mode value)
  | .dyadic value => .ok (convertDyadicText fmt mode value)
  | .infinity negative =>
      match infinity? fmt negative with
      | some value => .ok { value, status := {} }
      | none => .error (.unsupportedInfinity negative)
  | .nan negative signaling payload => convertNaNText fmt negative signaling payload

namespace TextParser

/--
Implementation core for character input, reporting all five IEEE exceptions.
Finite input is converted from its complete exact value without resource limits.
The caller-facing entrypoint is `Model.parse` in `BoundedParsing`.
-/
def run (fmt : FloatFormat) (mode : IEEERoundingMode) (input : String) :
    Except ParseError (IEEEOutcome fmt) :=
  match readText input with
  | some value => convertText fmt mode value
  | none =>
      let trimmed := input.trimAscii.toString
      if trimmed.isEmpty then .error .emptyInput
      else match readText trimmed with
        | some value => convertText fmt mode value
        | none => .error (.invalidSyntax input)

end TextParser

end FloatLib.Floats.Formats.BinaryInterchange.Model
