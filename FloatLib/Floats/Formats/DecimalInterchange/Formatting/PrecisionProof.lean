/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Formatting.Precision
public import FloatLib.Floats.Formats.DecimalInterchange.Formatting.Proof
public import FloatLib.Numerics.Exact.DecimalText.PrecisionProof
public import FloatLib.Numerics.Exact.RadixText.PrecisionProof

/-!
# Guarantees for significant-digit output

The carry adjustment preserves value. The emitted characters therefore denote
the result of the existing exact integer-grid rounder, with its nearest and
directed error guarantees. The inexact flag detects a numerical change even when
the requested precision changes the output quantum.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Formatting

open FloatLib.Numerics.DecimalText

/-- Every nonzero output coefficient has exactly the requested number of decimal digits. -/
theorem significantDecimal_coefficient_bounds (mode : RoundingMode)
    (value : Decimal) (digits : ℕ+) (hc : value.significand ≠ 0) :
    10 ^ ((digits : Nat) - 1) ≤ (significantDecimal mode value digits).significand ∧
      (significantDecimal mode value digits).significand < 10 ^ (digits : Nat) :=
  FloatLib.Numerics.RadixText.significant_coefficient_bounds 10 (by decide)
    mode.roundMagnitude (mode.floor_le_roundMagnitude)
    (fun sign x n hx hn => mode.roundMagnitude_le_nat sign hx n hn)
    value.negative value.significand value.exponent digits hc

/-- The significant-digit result is one integer-grid rounding of the exact input. -/
theorem significantDecimal_value (mode : RoundingMode) (value : Decimal) (digits : ℕ+) :
    (significantDecimal mode value digits).toRat =
      (if value.negative then (-1 : ℚ) else 1) *
        (mode.roundAt value.negative
          ((value.significand : ℚ) * (10 : ℚ) ^ value.exponent)
          (significantQuantum value.significand value.exponent digits) : ℚ) *
        (10 : ℚ) ^ significantQuantum value.significand value.exponent digits := by
  exact FloatLib.Numerics.DecimalText.significantDecimal_value mode.roundMagnitude value digits

/-- Output retains the sign, including for zero. -/
theorem significantDecimal_negative (mode : RoundingMode)
    (value : Decimal) (digits : ℕ+) :
    (significantDecimal mode value digits).negative = value.negative := by
  exact FloatLib.Numerics.DecimalText.significantDecimal_negative mode.roundMagnitude value digits

private theorem significantDecimal_scaled (mode : RoundingMode)
    (value : Decimal) (digits : ℕ+) :
    (significantDecimal mode value digits).toRat =
      mode.roundSigned value.negative
        ((value.significand : ℚ) * (10 : ℚ) ^ value.exponent /
          (10 : ℚ) ^ significantQuantum value.significand value.exponent digits) *
        (10 : ℚ) ^ significantQuantum value.significand value.exponent digits := by
  rw [significantDecimal_value]
  cases value.negative <;> simp [RoundingMode.roundSigned, RoundingMode.roundAt]

private theorem decimal_scaled (value : Decimal) (quantum : Int) :
    value.toRat =
      (if value.negative then
        -((value.significand : ℚ) * (10 : ℚ) ^ value.exponent / (10 : ℚ) ^ quantum)
      else (value.significand : ℚ) * (10 : ℚ) ^ value.exponent / (10 : ℚ) ^ quantum) *
        (10 : ℚ) ^ quantum := by
  cases hs : value.negative <;>
    simp [Decimal.toRat, hs, div_mul_cancel₀ _ (zpow_ne_zero quantum
      (by norm_num : (10 : ℚ) ≠ 0))]

private theorem decimal_scaled_nonneg (value : Decimal) (quantum : Int) :
    0 ≤ (value.significand : ℚ) * (10 : ℚ) ^ value.exponent / (10 : ℚ) ^ quantum :=
  div_nonneg (mul_nonneg (Nat.cast_nonneg _) (zpow_pos (by norm_num) _).le)
    (zpow_pos (by norm_num) _).le

/-- Upward decimal output is an upper enclosure at every requested precision. -/
theorem le_significantDecimal_towardPositive (value : Decimal) (digits : ℕ+) :
    value.toRat ≤ (significantDecimal .towardPositive value digits).toRat := by
  rw [significantDecimal_scaled, decimal_scaled value
    (significantQuantum value.significand value.exponent digits)]
  apply mul_le_mul_of_nonneg_right _ (zpow_pos (by norm_num) _).le
  exact RoundingMode.le_roundSigned_towardPositive _ (decimal_scaled_nonneg value _)

/-- Downward decimal output is a lower enclosure at every requested precision. -/
theorem significantDecimal_towardNegative_le (value : Decimal) (digits : ℕ+) :
    (significantDecimal .towardNegative value digits).toRat ≤ value.toRat := by
  rw [significantDecimal_scaled, decimal_scaled value
    (significantQuantum value.significand value.exponent digits)]
  apply mul_le_mul_of_nonneg_right _ (zpow_pos (by norm_num) _).le
  exact RoundingMode.roundSigned_towardNegative_le _ (decimal_scaled_nonneg value _)

/-- Toward-zero decimal output does not increase magnitude. -/
theorem abs_significantDecimal_towardZero_le (value : Decimal) (digits : ℕ+) :
    |(significantDecimal .towardZero value digits).toRat| ≤ |value.toRat| := by
  rw [significantDecimal_value]
  have h := mul_le_mul_of_nonneg_right
    (RoundingMode.roundMagnitude_towardZero_le value.negative
      (decimal_scaled_nonneg value
        (significantQuantum value.significand value.exponent digits)))
    (zpow_pos (by norm_num : (0 : ℚ) < 10)
      (significantQuantum value.significand value.exponent digits)).le
  simp only [div_mul_cancel₀ _ (zpow_ne_zero _ (by norm_num : (10 : ℚ) ≠ 0))] at h
  cases hs : value.negative <;>
    simpa [Decimal.toRat, hs, RoundingMode.roundAt, abs_mul,
      abs_of_pos (zpow_pos (by norm_num : (0 : ℚ) < 10) _)] using h

/-- At a midpoint, nearest-even output selects the even adjacent grid coefficient. -/
theorem significantDecimal_nearestEven_midpoint (value : Decimal) (digits : ℕ+) (n : Nat)
    (hmid : (value.significand : ℚ) * (10 : ℚ) ^ value.exponent /
      (10 : ℚ) ^ significantQuantum value.significand value.exponent digits =
        (n : ℚ) + 1 / 2) :
    (significantDecimal .nearestEven value digits).toRat =
      (if value.negative then (-1 : ℚ) else 1) *
        ((if n % 2 = 1 then n + 1 else n : Nat) : ℚ) *
        (10 : ℚ) ^ significantQuantum value.significand value.exponent digits := by
  rw [significantDecimal_value, RoundingMode.roundAt, hmid,
    RoundingMode.roundMagnitude_nearestEven_midpoint]

/-- At a midpoint, nearest-away output selects the larger magnitude. -/
theorem significantDecimal_nearestAway_midpoint (value : Decimal) (digits : ℕ+) (n : Nat)
    (hmid : (value.significand : ℚ) * (10 : ℚ) ^ value.exponent /
      (10 : ℚ) ^ significantQuantum value.significand value.exponent digits =
        (n : ℚ) + 1 / 2) :
    (significantDecimal .nearestAway value digits).toRat =
      (if value.negative then (-1 : ℚ) else 1) * (n + 1 : Nat) *
        (10 : ℚ) ^ significantQuantum value.significand value.exponent digits := by
  rw [significantDecimal_value, RoundingMode.roundAt, hmid,
    RoundingMode.roundMagnitude_nearestAway_midpoint]

/-- Enough requested digits preserve the exact numerical value in every rounding mode. -/
theorem significantDecimal_exact (mode : RoundingMode) (value : Decimal) (digits : ℕ+)
    (hc : value.significand < 10 ^ (digits : Nat)) :
    (significantDecimal mode value digits).toRat = value.toRat := by
  by_cases hz : value.significand = 0
  · rw [significantDecimal_value]
    simp [hz, RoundingMode.roundAt, Decimal.toRat,
      show mode.roundMagnitude value.negative 0 = 0 from
        mode.roundMagnitude_natCast value.negative 0]
  · have hlog := Nat.log_lt_of_lt_pow hz hc
    have hq : significantQuantum value.significand value.exponent digits ≤
        value.exponent := by
      simp only [significantQuantum, FloatLib.Numerics.RadixText.significantQuantum, if_neg hz]
      omega
    rw [significantDecimal_value, mul_assoc,
      RoundingMode.roundAt_exact_value mode value.negative value.significand hq]
    cases hs : value.negative <;> simp [Decimal.toRat, hs]

/-- The descriptor precision suffices for every valid datum, with no restriction on exponent bias. -/
theorem significantDecimal_exact_of_valid (f : Format) (mode : RoundingMode)
    (value : Decimal) (digits : ℕ+)
    (hvalid : (Datum.finite value.negative value.significand value.exponent).Valid f)
    (hp : f.precision ≤ (digits : Nat)) :
    (significantDecimal mode value digits).toRat = value.toRat := by
  apply significantDecimal_exact
  exact (hvalid.1.trans_eq f.coefficientBound_eq).trans_le
    (Nat.pow_le_pow_right (by decide : 0 < 10) hp)

/-- Both nearest modes have at most half a requested grid unit of error. -/
theorem significantDecimal_error_le_half (mode : RoundingMode)
    (hm : mode = .nearestEven ∨ mode = .nearestAway) (value : Decimal) (digits : ℕ+) :
    |(significantDecimal mode value digits).toRat - value.toRat| ≤
      (10 : ℚ) ^ significantQuantum value.significand value.exponent digits / 2 := by
  have hx : 0 ≤ (value.significand : ℚ) * (10 : ℚ) ^ value.exponent :=
    mul_nonneg (Nat.cast_nonneg _) (zpow_pos (by norm_num) _).le
  have h := mode.roundAt_error_le_half hm value.negative hx
    (significantQuantum value.significand value.exponent digits)
  rw [significantDecimal_value]
  cases hs : value.negative
  · simpa [Decimal.toRat, hs] using h
  · simp only [hs, if_true, neg_one_mul, Decimal.toRat]
    have he : -((mode.roundAt true
        ((value.significand : ℚ) * (10 : ℚ) ^ value.exponent)
        (significantQuantum value.significand value.exponent digits) : ℚ)) *
        (10 : ℚ) ^ significantQuantum value.significand value.exponent digits -
        -(value.significand : ℚ) * (10 : ℚ) ^ value.exponent =
        -((mode.roundAt true
          ((value.significand : ℚ) * (10 : ℚ) ^ value.exponent)
          (significantQuantum value.significand value.exponent digits) : ℚ) *
          (10 : ℚ) ^ significantQuantum value.significand value.exponent digits -
          (value.significand : ℚ) * (10 : ℚ) ^ value.exponent) := by ring
    rw [he, abs_neg]
    simpa [hs] using h

/-- Actual output characters decode to the computed significant-digit record. -/
theorem read_format_significant (mode : RoundingMode) (digits : ℕ+) (value : Decimal) :
    read (format mode (.significant digits)
      (.finite value.negative value.significand value.exponent)).text =
      some (.finite (significantDecimal mode value digits).negative
        (significantDecimal mode value digits).significand
        (significantDecimal mode value digits).exponent) := by
  simp [format, Decimal.format, read, readCharacters]

/-- Requested-precision output sets inexact exactly when its character value differs from the input. -/
theorem format_significant_inexact_iff (mode : RoundingMode) (digits : ℕ+) (value : Decimal) :
    (format mode (.significant digits)
      (.finite value.negative value.significand value.exponent)).status.inexact = true ↔
      (significantDecimal mode value digits).toRat ≠ value.toRat := by
  simp [format]

private theorem significantDecimal_magnitude_of_valid (f : Format) (mode : RoundingMode)
    (value : Decimal) (digits : ℕ+)
    (hvalid : (Datum.finite value.negative value.significand value.exponent).Valid f)
    (hp : f.precision ≤ (digits : Nat)) :
    ((significantDecimal mode value digits).significand : ℚ) *
        (10 : ℚ) ^ (significantDecimal mode value digits).exponent =
      (value.significand : ℚ) * (10 : ℚ) ^ value.exponent := by
  have h := significantDecimal_exact_of_valid f mode value digits hvalid hp
  simp only [Decimal.toRat, significantDecimal_negative] at h
  cases hs : value.negative <;> simpa [hs] using h

/-- At least the format precision preserves numerical value through actual output and input.
The two conversions may use different rounding modes; the quantum need not be recovered. -/
theorem parse_format_significant_value (f : Format) (outputMode inputMode : RoundingMode)
    (value : Decimal) (digits : ℕ+)
    (hvalid : (Datum.finite value.negative value.significand value.exponent).Valid f)
    (hp : f.precision ≤ (digits : Nat)) :
    (parse f inputMode (format outputMode (.significant digits)
      (.finite value.negative value.significand value.exponent)).text).value.toRat? =
        (Datum.finite value.negative value.significand value.exponent).toRat? := by
  simp only [parse, read_format_significant, convert, significantDecimal_negative,
    significantDecimal_magnitude_of_valid f outputMode value digits hvalid hp]
  exact projectMagnitude_exact f inputMode value.negative value.significand value.exponent
    _ hvalid

/-- Sufficient-precision output raises none of the five IEEE flags. -/
theorem format_significant_status_of_valid (f : Format) (mode : RoundingMode)
    (value : Decimal) (digits : ℕ+)
    (hvalid : (Datum.finite value.negative value.significand value.exponent).Valid f)
    (hp : f.precision ≤ (digits : Nat)) :
    (format mode (.significant digits)
      (.finite value.negative value.significand value.exponent)).status = {} := by
  simp [format, significantDecimal_exact_of_valid f mode value digits hvalid hp]

/-- Parsing sufficient-precision output raises no flags, even if its written quantum cannot fit. -/
theorem parse_format_significant_status (f : Format) (outputMode inputMode : RoundingMode)
    (value : Decimal) (digits : ℕ+)
    (hvalid : (Datum.finite value.negative value.significand value.exponent).Valid f)
    (hp : f.precision ≤ (digits : Nat)) :
    (parse f inputMode (format outputMode (.significant digits)
      (.finite value.negative value.significand value.exponent)).text).status = {} := by
  simp only [parse, read_format_significant, convert, significantDecimal_negative,
    significantDecimal_magnitude_of_valid f outputMode value digits hvalid hp]
  exact projectMagnitude_exact_status f inputMode value.negative value.significand value.exponent
    _ hvalid

/-- Exact precision returns the representation-preserving spelling without flags. -/
@[simp] theorem format_exact (mode : RoundingMode) (value : Datum) :
    format mode .exact value = { text := formatExact value } := by
  cases value <;> rfl

end FloatLib.Floats.Formats.DecimalInterchange.Formatting
