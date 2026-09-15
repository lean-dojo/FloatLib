/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Numerics.Exact.HexText.Runtime
public import FloatLib.Numerics.Exact.DecimalText.Proof
public import FloatLib.Numerics.Exact.RadixText.PrecisionProof
import Mathlib.Tactic.IntervalCases
import all Init.Data.Repr

/-! # Hexadecimal character preservation

The shared positional scanner recovers the printed hexadecimal coefficient;
the decimal integer scanner recovers the binary exponent. The result preserves
the entire dyadic record, including the sign of zero.
-/

@[expose] public section

namespace FloatLib.Numerics.HexText

/-- A printed hexadecimal digit decodes to its original value. -/
@[simp] theorem digitValue?_digitChar {digit : Nat} (hdigit : digit < 16) :
    digitValue? (Nat.digitChar digit) = some digit := by
  interval_cases digit <;> decide

/-- Scanning a printed hexadecimal coefficient recovers the coefficient and its suffix. -/
theorem scanDigits_naturalDigits (value : Nat) (tail : List Char)
    (htail : ∀ character ∈ tail.head?, digitValue? character = none) :
    RadixText.scanDigits (RadixText.naturalDigits value 16 ++ tail) 0 16 digitValue? =
      (value, (RadixText.naturalDigits value 16).length, tail) :=
  RadixText.scanDigits_naturalDigits 16 (by decide) digitValue?
    (fun _ h => digitValue?_digitChar h) value tail htail

/-- The complete hexadecimal magnitude, including its mandatory exponent, parses exactly. -/
theorem parseMagnitude_hexadecimal (significand : Nat) (exponent : Int) :
    RadixText.parseMagnitude
      (RadixText.naturalDigits significand 16 ++ 'p' :: DecimalText.integerDigits exponent)
      16 digitValue? parseExponent 4 = some (significand, exponent) := by
  rw [RadixText.parseMagnitude,
    scanDigits_naturalDigits significand ('p' :: DecimalText.integerDigits exponent)
      (by simp [digitValue?, DecimalText.digitValue?])]
  simp [parseExponent]

/-- Reading the printed characters preserves every dyadic field, with no width assumption. -/
@[simp] theorem parseCharacters_characters (value : Dyadic) :
    parseCharacters (characters value) = some value := by
  rcases value with ⟨negative, significand, exponent⟩
  cases negative <;>
    simp [characters, parseCharacters, DecimalText.splitSign,
      parseMagnitude_hexadecimal]

/-- Exact hexadecimal string output and input preserve the full dyadic representation. -/
@[simp] theorem parse_format (value : Dyadic) :
    parse (format value) = some value := by
  simp [parse, format]

/-- A hexadecimal power is a binary power at four times the exponent. -/
theorem sixteen_zpow (exponent : Int) :
    (16 : ℚ) ^ exponent = (2 : ℚ) ^ (4 * exponent) := by
  rw [zpow_mul]
  norm_num

/-- Moving a dyadic to a hexadecimal grid does not change its magnitude. -/
theorem radixPair_value (value : Dyadic) :
    ((radixPair value).1 : ℚ) * (16 : ℚ) ^ (radixPair value).2 =
      (value.significand : ℚ) * (2 : ℚ) ^ value.exponent := by
  have he : (value.exponent % 4 : Int) + 4 * (value.exponent / 4) = value.exponent := by omega
  have hr : 0 ≤ value.exponent % 4 := Int.emod_nonneg _ (by decide)
  simp only [radixPair, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [sixteen_zpow, mul_assoc, ← zpow_natCast, Int.toNat_of_nonneg hr,
    ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), he]

/-- Hexadecimal precision output preserves the sign, even if the coefficient is zero. -/
@[simp] theorem significant_negative (roundMagnitude : Bool → ℚ → Nat)
    (value : Dyadic) (digits : ℕ+) :
    (significant roundMagnitude value digits).negative = value.negative := rfl

/-- The hexadecimal output value is one integer rounding on the requested hexadecimal grid. -/
theorem significant_value (roundMagnitude : Bool → ℚ → Nat)
    (value : Dyadic) (digits : ℕ+) :
    (significant roundMagnitude value digits).toRat =
      (if value.negative then (-1 : ℚ) else 1) *
        (RadixText.roundCoefficient 16 roundMagnitude value.negative
          (radixPair value).1 (radixPair value).2
          (RadixText.significantQuantum 16 (radixPair value).1 (radixPair value).2 digits) : ℚ) *
        (16 : ℚ) ^
          RadixText.significantQuantum 16 (radixPair value).1 (radixPair value).2 digits := by
  have h := RadixText.significant_value 16 (by decide) roundMagnitude value.negative
    (radixPair value).1 (radixPair value).2 digits
  cases hs : value.negative <;>
    simp only [significant, Dyadic.toRat, Dyadic.signedSignificand, hs,
      Bool.false_eq_true, ite_false, ite_true,
      ← sixteen_zpow]
  · simpa [hs] using h
  · simpa [hs, neg_mul] using congrArg Neg.neg h

/-- Enough requested hexadecimal digits preserve the exact value in every integer-exact rounder. -/
theorem significant_exact (roundMagnitude : Bool → ℚ → Nat)
    (hexact : ∀ sign (n : Nat), roundMagnitude sign (n : ℚ) = n)
    (value : Dyadic) (digits : ℕ+)
    (hc : (radixPair value).1 < 16 ^ (digits : Nat)) :
    (significant roundMagnitude value digits).toRat = value.toRat := by
  have h := (RadixText.significant_exact 16 (by decide) roundMagnitude hexact
    value.negative (radixPair value).1 (radixPair value).2 digits hc).trans
    (radixPair_value value)
  cases hs : value.negative <;>
    simp only [significant, Dyadic.toRat, Dyadic.signedSignificand, hs,
      Bool.false_eq_true, ite_false, ite_true,
      ← sixteen_zpow]
  · simpa [hs] using h
  · simpa [hs, neg_mul] using congrArg Neg.neg h

end FloatLib.Numerics.HexText
