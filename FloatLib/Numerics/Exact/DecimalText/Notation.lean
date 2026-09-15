/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Numerics.Exact.DecimalText.Runtime

/-!
# Fixed and scientific decimal presentation

These renderers place the decimal point in the digits of an exact decimal record. They perform
no rounding and retain coefficient trailing zeros. Scientific notation keeps one digit before
the point and always prints an exponent, including for signed zero.
-/

@[expose] public section

namespace FloatLib.Numerics.DecimalText

/-- Join whole and fractional digits, omitting the point when there are no fractional digits. -/
def pointCharacters (whole fraction : List Char) : List Char :=
  whole ++ if fraction = [] then [] else '.' :: fraction

/-- Place exactly `places` digits after the point, padding on the left when necessary. -/
def fractionalCharacters (coefficient places : Nat) : List Char :=
  let digits := RadixText.naturalDigits coefficient 10
  if places < digits.length then
    pointCharacters (digits.take (digits.length - places)) (digits.drop (digits.length - places))
  else
    pointCharacters ['0'] (List.replicate (places - digits.length) '0' ++ digits)

/-- The record recovered from fixed notation: positive powers of ten become integer digits. -/
def Decimal.fixedRepresentation (value : Decimal) : Decimal :=
  match value.exponent with
  | .ofNat exponent =>
      { negative := value.negative
        significand := value.significand * 10 ^ exponent
        exponent := 0 }
  | .negSucc _ => value

/-- Fixed notation with the original sign and all fractional places specified by the exponent. -/
def Decimal.fixedCharacters (value : Decimal) : List Char :=
  (if value.negative then ['-'] else []) ++
    match value.exponent with
    | .ofNat exponent => RadixText.naturalDigits (value.significand * 10 ^ exponent) 10
    | .negSucc exponent => fractionalCharacters value.significand (exponent + 1)

/-- Fixed decimal text, with no precision limit or additional rounding. -/
def Decimal.formatFixed (value : Decimal) : String :=
  String.ofList value.fixedCharacters

/-- Scientific notation with one leading digit and the original coefficient's trailing zeros.
For zero with exponent `-places`, print `places` fractional zeros and exponent zero.
Every output determines the original decimal record, including its sign and zero precision. -/
def Decimal.scientificCharacters (value : Decimal) : List Char :=
  let digits := RadixText.naturalDigits value.significand 10
  let fraction := digits.drop 1
  (if value.negative then ['-'] else []) ++
    if value.significand = 0 ∧ value.exponent ≤ 0 then
      fractionalCharacters 0 value.exponent.natAbs ++ ['e', '0']
    else
      pointCharacters (digits.take 1) fraction ++
      'e' :: integerDigits (value.exponent + (fraction.length : Int))

/-- Scientific decimal text, with no precision limit or additional rounding. -/
def Decimal.formatScientific (value : Decimal) : String :=
  String.ofList value.scientificCharacters

end FloatLib.Numerics.DecimalText
