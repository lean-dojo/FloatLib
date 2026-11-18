/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Embedded.Error
public import FloatLib.Floats.Formats.FixedPoint.Embedded.Grammar
public import FloatLib.Numerics.Exact.DecimalText.NotationProof

/-!
# Numeric and consumption laws for fixed formatted conversions

WG14 N1169 (2006 TR 18037 draft), C clause 7.19.6.1–2, with inherited N1256 C99 requirements.
Printing rounds once on the decimal grid and satisfies the selected rounder's
error bound. Input selection consumes a maximal prefix of the numeric
subject grammar: the one-zero recognizer is both sound and complete.
Successful conversion refines the common DEFAULT nonsaturating conversion.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.FixedPoint.Embedded.Formatted

open FloatLib.Numerics

/-- The output decimal is the chosen integer divided by the decimal precision scale. -/
theorem decimal_toRat (rounding : Rounding) (value : ℚ) (places : Nat) :
    (decimal rounding value places).toRat =
      (rounding.run (value * (10 : ℚ) ^ places) : ℚ) / (10 : ℚ) ^ places := by
  simp [decimal, zpow_neg, div_eq_mul_inv]

/-- The shared fixed formatter preserves the exact rounded decimal value. -/
theorem parse_decimal_fixed (rounding : Rounding) (value : ℚ) (places : Nat) :
    DecimalText.parse (decimal rounding value places).formatFixed =
      some ((rounding.run (value * (10 : ℚ) ^ places) : ℚ) / (10 : ℚ) ^ places) := by
  rw [DecimalText.parse_formatFixed, decimal_toRat]

/-- The caller's integer rounding error scales by the requested decimal precision. -/
theorem decimal_error_le (rounding : Rounding) (value ε : ℚ) (places : Nat)
    (hround : |(rounding.run (value * (10 : ℚ) ^ places) : ℚ) -
      value * (10 : ℚ) ^ places| ≤ ε) :
    |(decimal rounding value places).toRat - value| ≤ ε / (10 : ℚ) ^ places := by
  rw [decimal_toRat, div_sub' (pow_ne_zero _ (by decide)), abs_div,
    abs_of_pos (pow_pos (show (0 : ℚ) < 10 by decide) places)]
  simpa only [mul_comm] using
    div_le_div_of_nonneg_right hround (pow_pos (show (0 : ℚ) < 10 by decide) places).le

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.19.6.1: any adjacent decimal rounding mode
    costs at most one decimal step. -/
theorem decimal_error_le_one (rounding : Rounding) (value : ℚ) (places : Nat) :
    |(decimal rounding value places).toRat - value| ≤ 1 / (10 : ℚ) ^ places :=
  decimal_error_le rounding value 1 places (rounding.error_le_one _)

/-- Nearest decimal presentation has the sharper half-decimal-step bound. -/
theorem decimal_error_le_half (rounding : NearestRounding) (value : ℚ) (places : Nat) :
    |(decimal rounding.toRounding value places).toRat - value| ≤
      (1 / 2) / (10 : ℚ) ^ places :=
  decimal_error_le rounding.toRounding value (1 / 2) places (rounding.error_le_half _)

/-- Every padded field meets its width, including negative dynamic width and zero padding. -/
theorem fieldCharacters_length (signed : Bool) (options : PrintOptions)
    (value : DecimalText.Decimal) :
    options.width.natAbs ≤ (fieldCharacters signed options value).length := by
  unfold fieldCharacters
  dsimp only
  split_ifs <;>
    simp only [List.length_append, List.length_replicate] <;> omega

/-- The item recognizer accepts a complete subject or its explicit one-zero completion. -/
theorem item_eq_some_iff (characters : List Char) :
    item characters = some () ↔
      (Text.subject characters).isSome ∨ (Text.subject (characters ++ ['0'])).isSome := by
  cases hs : Text.subject characters <;>
    cases hc : Text.subject (characters ++ ['0']) <;> simp [item, hs, hc]

/-- Every recognized input item has a complete numeric continuation. -/
theorem item_has_completion (characters : List Char) (h : item characters = some ()) :
    ∃ suffix : List Char, (Text.subject (characters ++ suffix)).isSome :=
  (Text.subject_has_completion_iff characters).mpr ((item_eq_some_iff characters).mp h)

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.19.6.2: the recognizer accepts exactly the
    prefixes of complete numeric subjects. -/
theorem item_eq_some_iff_has_completion (characters : List Char) :
    item characters = some () ↔
      ∃ suffix : List Char, (Text.subject (characters ++ suffix)).isSome :=
  (item_eq_some_iff characters).trans (Text.subject_has_completion_iff characters).symm

/-- Maximal item consumption holds for every prefix accepted by the item recognizer. -/
theorem le_item_length (width : Option ℕ+) (text : String) (length : Nat)
    (hbound : length ≤ (input width text).length)
    (hitem : item ((input width text).take length) = some ()) :
    length ≤ RadixText.prefixLength item (input width text) :=
  RadixText.le_prefixLength item (input width text) length () hbound hitem

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.19.6.2: consumption is maximal among all
    completable numeric prefixes. -/
theorem le_item_length_of_completion (width : Option ℕ+) (text : String) (length : Nat)
    (hbound : length ≤ (input width text).length)
    (hcomplete : ∃ suffix, (Text.subject ((input width text).take length ++ suffix)).isSome) :
    length ≤ RadixText.prefixLength item (input width text) :=
  le_item_length width text length hbound
    ((item_eq_some_iff_has_completion _).mpr hcomplete)

/-- The position includes skipped whitespace and the whole selected item, even on failure. -/
theorem scan_consumed (format : Format) (rounding : Rounding)
    (width : Option ℕ+) (text : String) :
    (scan format rounding width text).consumed =
      text.toList.length - (Text.subjectInput text).length +
        RadixText.prefixLength item (input width text) := by
  unfold scan
  dsimp only
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

/-- A nonempty incomplete item fails after consumption; no shorter subject is retried. -/
theorem scan_incomplete (format : Format) (rounding : Rounding)
    (width : Option ℕ+) (text : String)
    (hpos : RadixText.prefixLength item (input width text) ≠ 0)
    (hparse : Text.subject ((input width text).take
      (RadixText.prefixLength item (input width text))) = none) :
    (scan format rounding width text).status = .matchingFailure ∧
      (scan format rounding width text).value = none := by
  simp [scan, hpos, hparse]

/-- Successful input conversion has exactly the selected rounded coefficient. -/
theorem scanValue_eq_some_iff (format : Format) (rounding : Rounding)
    (value : ℚ) (result : format.Code) :
    scanValue format rounding value = some result ↔
      bitsfx result = rounding.run (value / format.quantizer.scale) :=
  fxbits_eq_some_iff format _ result

/-- Input overflow is undefined exactly when its rounded coefficient does not fit. -/
theorem scanValue_eq_none_iff (format : Format) (rounding : Rounding) (value : ℚ) :
    scanValue format rounding value = none ↔
      ¬ format.integerFormat.InRange (rounding.run (value / format.quantizer.scale)) := by
  simp [scanValue, fxbits]

/-- Numeric input conversion agrees with shared DEFAULT conversion on a primary destination. -/
theorem scanValue_eq_convert (format : Format) (rounding : Rounding) (value : ℚ)
    (hprimary : format.saturating = false) :
    scanValue format rounding value = Embedded.convert format rounding .DEFAULT value := by
  by_cases h : format.integerFormat.InRange (rounding.run (value / format.quantizer.scale))
  · simp only [scanValue, fxbits, h, ↓reduceDIte, Embedded.convert, Format.finish,
      Format.Saturates, hprimary, Bool.false_eq_true, false_or, reduceCtorEq, or_true, ↓reduceIte]
    apply congrArg some
    apply Subtype.ext
    exact (format.quantizer.clampCode_eq_self h.1 h.2).symm
  · simp [scanValue, fxbits, Embedded.convert, Format.finish, Format.Saturates, hprimary, h]

/-- The scan's numeric result comes from its entire nonempty selected input item. -/
theorem scan_value_eq_some_iff (format : Format) (rounding : Rounding)
    (width : Option ℕ+) (text : String) (result : format.Code) :
    (scan format rounding width text).value = some result ↔
      RadixText.prefixLength item (input width text) ≠ 0 ∧
        ∃ exact, Text.subject ((input width text).take
          (RadixText.prefixLength item (input width text))) = some exact ∧
            scanValue format rounding exact = some result := by
  unfold scan
  dsimp only
  split
  · simp_all
  · split
    · simp_all
    · split <;> simp_all

end FloatLib.Floats.Formats.FixedPoint.Embedded.Formatted
