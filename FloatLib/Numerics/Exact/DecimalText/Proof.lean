/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.DecimalText.Runtime
public import FloatLib.Numerics.Exact.RadixText.ScannerProof
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FieldSimp
import all Init.Data.Repr

/-!
# Decimal character preservation

The digit scanner recovers the base-ten positional value of every digit list. This connects actual
character strings to exact rationals, rather than assuming an abstract parser/formatter inverse.
The dyadic conversion then preserves value by the identity `10^k = 2^k * 5^k`.
-/

@[expose] public section

namespace FloatLib.Numerics.DecimalText

/-- Printing any decimal digit and reading it recovers that digit. -/
@[simp] theorem digitValue?_digitChar {digit : Nat} (hdigit : digit < 10) :
    digitValue? (Nat.digitChar digit) = some digit := by
  interval_cases digit <;> decide

/-- Every character printed for a natural is an ASCII decimal digit. -/
theorem digitValue?_mem_naturalDigits {value : Nat} {character : Char}
    (hcharacter : character ∈ RadixText.naturalDigits value 10) :
    ∃ digit, digit < 10 ∧ digitValue? character = some digit := by
  by_cases hzero : value = 0
  · simp [RadixText.naturalDigits, hzero] at hcharacter
    subst character
    exact ⟨0, by decide, by decide⟩
  · simp only [RadixText.naturalDigits, ite_eq_right hzero, List.mem_map,
    List.mem_reverse] at hcharacter
    obtain ⟨digit, hdigit, rfl⟩ := hcharacter
    have hlt := Nat.digits_lt_base (by decide : 1 < 10) hdigit
    exact ⟨digit, hlt, digitValue?_digitChar hlt⟩

/-- Decimal printing followed by scanning recovers any natural, without a width bound. -/
theorem scanDigits_naturalDigits (value : Nat) (tail : List Char)
    (htail : ∀ character ∈ tail.head?, digitValue? character = none) :
    RadixText.scanDigits (RadixText.naturalDigits value 10 ++ tail) 0 10 digitValue? =
      (value, (RadixText.naturalDigits value 10).length, tail) :=
  RadixText.scanDigits_naturalDigits 10 (by decide) digitValue?
    (fun _ h => digitValue?_digitChar h) value tail htail

/-- A printed natural is consumed completely. -/
@[simp] theorem scanDigits_naturalDigits_nil (value : Nat) :
    RadixText.scanDigits (RadixText.naturalDigits value 10) 0 10 digitValue? =
      (value, (RadixText.naturalDigits value 10).length, []) := by
  simpa using scanDigits_naturalDigits value [] (by simp)

/-- A printed natural cannot be mistaken for a leading sign. -/
theorem splitSign_naturalDigits (value : Nat) (tail : List Char) :
    splitSign (RadixText.naturalDigits value 10 ++ tail) =
      (false, RadixText.naturalDigits value 10 ++ tail) := by
  cases hdigits : RadixText.naturalDigits value 10 with
  | nil => simp at hdigits
  | cons character rest =>
      obtain ⟨digit, _, hdigit⟩ :=
        digitValue?_mem_naturalDigits
          (by simp [hdigits] : character ∈ RadixText.naturalDigits value 10)
      simp only [List.cons_append, splitSign]
      split <;> simp_all [digitValue?]

/-- A printed natural alone has no leading sign. -/
@[simp] theorem splitSign_naturalDigits_nil (value : Nat) :
    splitSign (RadixText.naturalDigits value 10) = (false, RadixText.naturalDigits value 10) := by
  simpa using splitSign_naturalDigits value []

/-- Integral exponent printing preserves every integer, including negative exponents. -/
@[simp] theorem parseInteger_integerDigits (value : Int) :
    parseInteger (integerDigits value) = some value := by
  cases value with
  | ofNat n =>
      simp [integerDigits, parseInteger]
  | negSucc n =>
      simp only [integerDigits, parseInteger, splitSign, scanDigits_naturalDigits_nil]
      simp [Int.negSucc_eq]

/-- Parsing the printed magnitude recovers its significand and decimal exponent. -/
theorem parseMagnitude_decimal (significand : Nat) (exponent : Int) :
    RadixText.parseMagnitude (RadixText.naturalDigits significand 10 ++
      (if exponent = 0 then [] else 'e' :: integerDigits exponent)) 10 digitValue? parseExponent 1 =
        some (significand, exponent) := by
  by_cases hexponent : exponent = 0
  · subst exponent
    simp [RadixText.parseMagnitude, parseExponent]
  · rw [ite_eq_right hexponent, RadixText.parseMagnitude,
      scanDigits_naturalDigits significand ('e' :: integerDigits exponent)
        (by simp [digitValue?])]
    simp [parseExponent]

/-- Parsing an actual printed decimal character list recovers the complete decimal record. -/
@[simp] theorem parseCharacters_characters (value : Decimal) :
    parseCharacters value.characters = some value := by
  rcases value with ⟨negative, significand, exponent⟩
  cases negative with
  | false =>
      simp only [Decimal.characters, Bool.false_eq_true, ite_false, List.nil_append,
        parseCharacters, splitSign_naturalDigits]
      simp [parseMagnitude_decimal]
  | true =>
      simp [Decimal.characters, parseCharacters, splitSign, parseMagnitude_decimal]

/-- Printing and parsing preserves the exact rational denoted by every decimal record. -/
@[simp] theorem parse_format (value : Decimal) :
    parse value.format = some value.toRat := by
  simp [parse, Decimal.format]

/-- Conversion to decimal preserves the exact rational meaning of every dyadic. -/
@[simp] theorem toRat_ofDyadic (value : Dyadic) :
    (ofDyadic value).toRat = value.toRat := by
  rcases value with ⟨negative, significand, exponent⟩
  cases exponent with
  | ofNat exponent =>
      cases negative <;>
        simp [ofDyadic, Decimal.toRat, Dyadic.toRat, Dyadic.signedSignificand]
  | negSucc exponent =>
      have hten : (10 : Rat) ^ (exponent + 1) =
          (2 : Rat) ^ (exponent + 1) * (5 : Rat) ^ (exponent + 1) := by
        rw [← mul_pow]
        norm_num
      cases negative <;>
        simp [ofDyadic, Decimal.toRat, Dyadic.toRat, Dyadic.signedSignificand,
          zpow_negSucc, hten] <;> field_simp

/-- The complete dyadic-to-decimal string conversion has exact rational value preservation. -/
@[simp] theorem parse_formatDyadic (value : Dyadic) :
    parse (formatDyadic value) = some value.toRat := by
  simp [formatDyadic]

end FloatLib.Numerics.DecimalText
