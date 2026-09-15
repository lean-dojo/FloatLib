/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Dyadic.Basic
public import FloatLib.Numerics.Exact.RadixText.Runtime

/-!
# Exact decimal character conversion

The reusable decimal carrier denotes an integer times an integral power of ten. Parsing accepts
ASCII decimal integers, fractions, and `e`/`E` exponents with optional signs. Each successful parse
denotes an exact rational, without host floating-point conversion.

Every dyadic has a terminating decimal expansion: `m / 2^k = (m * 5^k) / 10^k`. The formatter
uses that identity, with decimal exponent notation for fractional values. Output size and
exact-integer work grow with the magnitude of the binary exponent.
-/

@[expose] public section

namespace FloatLib.Numerics.DecimalText

/-- An exact signed decimal significand and integral decimal scale. -/
structure Decimal where
  /-- Sign of the decimal significand; signed zeros denote the same rational. -/
  negative : Bool
  /-- Magnitude of the integer significand. -/
  significand : Nat
  /-- Power of ten multiplying the significand. -/
  exponent : Int
  deriving DecidableEq, Repr

/-- Exact rational meaning of a decimal record. -/
def Decimal.toRat (value : Decimal) : Rat :=
  (if value.negative then -(value.significand : Rat) else value.significand) *
    (10 : Rat) ^ value.exponent

/-- Recognize precisely the ten ASCII decimal digits. -/
def digitValue? (character : Char) : Option Nat :=
  if '0' ≤ character ∧ character ≤ '9' then some (character.toNat - '0'.toNat) else none

/-- Remove at most one leading sign; an absent sign is positive. -/
def splitSign : List Char → Bool × List Char
  | '-' :: rest => (true, rest)
  | '+' :: rest => (false, rest)
  | rest => (false, rest)

/-- Read a signed decimal integer, requiring at least one digit and complete consumption. -/
def parseInteger (characters : List Char) : Option Int :=
  let (negative, rest) := splitSign characters
  let (value, count, tail) := RadixText.scanDigits rest 0 10 digitValue?
  if count = 0 ∨ tail ≠ [] then none
  else some (if negative then -(value : Int) else value)

/-- Read an optional decimal exponent, rejecting incomplete or trailing input. -/
def parseExponent : List Char → Option Int
  | [] => some 0
  | 'e' :: rest | 'E' :: rest => parseInteger rest
  | _ => none

/-- Parse decimal characters with an optional leading sign. -/
def parseCharacters (characters : List Char) : Option Decimal := do
  let (negative, rest) := splitSign characters
  let (significand, exponent) ← RadixText.parseMagnitude rest 10 digitValue? parseExponent 1
  some { negative, significand, exponent }

/-- Parse an exact decimal rational. Whitespace and nondecimal notation are rejected. -/
def parse (text : String) : Option Rat :=
  (parseCharacters text.toList).map Decimal.toRat

/-- Print an integral exponent with an explicit minus sign only when negative. -/
def integerDigits : Int → List Char
  | .ofNat value => RadixText.naturalDigits value 10
  | .negSucc value => '-' :: RadixText.naturalDigits (value + 1) 10

/-- Print a decimal record as a decimal significand with an optional `e` exponent. -/
def Decimal.characters (value : Decimal) : List Char :=
  (if value.negative then ['-'] else []) ++ RadixText.naturalDigits value.significand 10 ++
    (if value.exponent = 0 then [] else 'e' :: integerDigits value.exponent)

/-- Character-string representation of the exact decimal record. -/
def Decimal.format (value : Decimal) : String :=
  String.ofList value.characters

/-- Convert a dyadic to an equal decimal using powers of five for negative binary exponents. -/
def ofDyadic (value : Dyadic) : Decimal :=
  match value.exponent with
  | .ofNat exponent =>
      { negative := value.negative, significand := value.significand * 2 ^ exponent, exponent := 0 }
  | .negSucc exponent =>
      { negative := value.negative
        significand := value.significand * 5 ^ (exponent + 1)
        exponent := .negSucc exponent }

/-- Exact decimal formatting of a dyadic; every finite input has decimal output. -/
def formatDyadic (value : Dyadic) : String :=
  (ofDyadic value).format

end FloatLib.Numerics.DecimalText
