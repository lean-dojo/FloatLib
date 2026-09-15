/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Conversion.Integer.FromInt
public import FloatLib.Floats.Formats.DecimalInterchange.Conversion.Integer.Rounding
public import FloatLib.Numerics.Quantization.Integer.Proof

/-!
# Decimal-to-integer numerical and exception contracts

Successful conversions deliver the specified rounded integer. Failure is
characterized by non-finiteness or a rounded value outside the destination range.
The integer-grid theorems give error and tie guarantees, and the packing
theorems show that the checked result survives fixed-width storage exactly.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Conversion.Integer

open FloatLib.Numerics FloatLib.Numerics.Representations

private theorem convertToInteger_cases (destination : IntegerFormat) (mode : RoundingMode)
    (signalInexact : Bool) (source : Datum) :
    convertToInteger destination mode signalInexact source =
      match source.toRat? with
      | none => invalidOutcome
      | some value =>
          if destination.InRange (roundInteger mode value) then
            { value := roundInteger mode value
              status := { inexact :=
                signalInexact && decide ((roundInteger mode value : ℚ) ≠ value) } }
          else invalidOutcome := by
  cases hs : source.toRat? with
  | none => simp [convertToInteger, hs]
  | some value =>
      by_cases hr : destination.InRange (roundInteger mode value) <;>
        simp [convertToInteger, hs, IntegerRange.round?, hr]

/-- Every delivered integer, including the invalid default, fits in the chosen destination. -/
theorem convertToInteger_inRange (destination : IntegerFormat) (mode : RoundingMode)
    (signalInexact : Bool) (source : Datum) :
    destination.InRange (convertToInteger destination mode signalInexact source).value := by
  simp only [convertToInteger_cases]
  split
  · exact destination.zero_inRange
  · split
    · assumption
    · exact destination.zero_inRange

/-- Range is tested after rounding the exact numerical operand. -/
theorem convertToInteger_invalid_iff (destination : IntegerFormat) (mode : RoundingMode)
    (signalInexact : Bool) (source : Datum) :
    (convertToInteger destination mode signalInexact source).status.invalid = true ↔
      ¬ ∃ value, source.toRat? = some value ∧
        destination.InRange (roundInteger mode value) := by
  cases hs : source.toRat? with
  | none => simp [convertToInteger_cases, hs, invalidOutcome]
  | some value =>
      by_cases hr : destination.InRange (roundInteger mode value) <;>
        simp [convertToInteger_cases, hs, hr, invalidOutcome]

theorem convertToInteger_of_inRange (destination : IntegerFormat) (mode : RoundingMode)
    (signalInexact : Bool) (source : Datum) (value : ℚ)
    (hs : source.toRat? = some value) (hr : destination.InRange (roundInteger mode value)) :
    convertToInteger destination mode signalInexact source =
      { value := roundInteger mode value
        status := { inexact :=
          signalInexact && decide ((roundInteger mode value : ℚ) ≠ value) } } := by
  simp [convertToInteger_cases, hs, hr]

/-- A successful result denotes the rounded integer exactly. -/
theorem convertToInteger_value (destination : IntegerFormat) (mode : RoundingMode)
    (signalInexact : Bool) (source : Datum) (value : ℚ)
    (hs : source.toRat? = some value)
    (hv : (convertToInteger destination mode signalInexact source).status.invalid = false) :
    (convertToInteger destination mode signalInexact source).value = roundInteger mode value := by
  by_cases hr : destination.InRange (roundInteger mode value)
  · rw [convertToInteger_of_inRange destination mode signalInexact source value hs hr]
  · simp [convertToInteger_cases, hs, hr, invalidOutcome] at hv

/-- An integer representable in both source and destination is unchanged with no flags. -/
theorem convertToInteger_exact (destination : IntegerFormat) (mode : RoundingMode)
    (signalInexact : Bool) (source : Datum) (value : Int)
    (hs : source.toRat? = some (value : ℚ)) (hr : destination.InRange value) :
    convertToInteger destination mode signalInexact source = { value := value } := by
  simp [convertToInteger_cases, hs, roundInteger_intCast, hr]

/-- Suppression of inexact does not affect the delivered integer. -/
theorem convertToInteger_value_independent (destination : IntegerFormat) (mode : RoundingMode)
    (signalInexact : Bool) (source : Datum) :
    (convertToInteger destination mode signalInexact source).value =
      (convertToInteger destination mode false source).value := by
  simp only [convertToInteger_cases]
  split <;> first | rfl | split <;> rfl

@[simp] theorem convertToInteger_quiet_inexact (destination : IntegerFormat)
    (mode : RoundingMode) (source : Datum) :
    (convertToInteger destination mode false source).status.inexact = false := by
  simp only [convertToInteger_cases]
  split <;> first | rfl | split <;> rfl

/-- Inexact is precisely a numerical change on a successful exact-variant conversion. -/
theorem convertToInteger_inexact_iff (destination : IntegerFormat) (mode : RoundingMode)
    (source : Datum) (value : ℚ) (hs : source.toRat? = some value)
    (hv : (convertToInteger destination mode true source).status.invalid = false) :
    (convertToInteger destination mode true source).status.inexact = true ↔
      ((convertToInteger destination mode true source).value : ℚ) ≠ value := by
  by_cases hr : destination.InRange (roundInteger mode value)
  · simp [convertToInteger_cases, hs, hr]
  · simp [convertToInteger_cases, hs, hr, invalidOutcome] at hv

/-- Invalid integer conversion delivers the documented default, with no simultaneous inexact. -/
theorem convertToInteger_of_invalid (destination : IntegerFormat) (mode : RoundingMode)
    (signalInexact : Bool) (source : Datum)
    (hv : (convertToInteger destination mode signalInexact source).status.invalid = true) :
    convertToInteger destination mode signalInexact source = invalidOutcome := by
  simp only [convertToInteger_cases] at *
  split at * <;> first | rfl | split at * <;> simp_all

/-- Integer destination conversion never raises floating-point range or division exceptions. -/
theorem convertToInteger_range_flags (destination : IntegerFormat) (mode : RoundingMode)
    (signalInexact : Bool) (source : Datum) :
    (convertToInteger destination mode signalInexact source).status.overflow = false ∧
      (convertToInteger destination mode signalInexact source).status.underflow = false ∧
      (convertToInteger destination mode signalInexact source).status.divideByZero = false := by
  simp only [convertToInteger_cases]
  split <;> first | exact ⟨rfl, rfl, rfl⟩ | split <;> exact ⟨rfl, rfl, rfl⟩

theorem convertToInteger_error_le_half (destination : IntegerFormat) (mode : RoundingMode)
    (hm : mode = .nearestEven ∨ mode = .nearestAway)
    (signalInexact : Bool) (source : Datum) (value : ℚ)
    (hs : source.toRat? = some value)
    (hv : (convertToInteger destination mode signalInexact source).status.invalid = false) :
    |((convertToInteger destination mode signalInexact source).value : ℚ) - value| ≤ 1 / 2 := by
  rw [convertToInteger_value destination mode signalInexact source value hs hv]
  exact roundInteger_error_le_half mode hm value

theorem convertToInteger_error_lt_one (destination : IntegerFormat) (mode : RoundingMode)
    (signalInexact : Bool) (source : Datum) (value : ℚ)
    (hs : source.toRat? = some value)
    (hv : (convertToInteger destination mode signalInexact source).status.invalid = false) :
    |((convertToInteger destination mode signalInexact source).value : ℚ) - value| < 1 := by
  rw [convertToInteger_value destination mode signalInexact source value hs hv]
  exact roundInteger_error_lt_one mode value

theorem le_convertToInteger_towardPositive (destination : IntegerFormat)
    (signalInexact : Bool) (source : Datum) (value : ℚ)
    (hs : source.toRat? = some value)
    (hv : (convertToInteger destination .towardPositive signalInexact source).status.invalid =
      false) :
    value ≤ ((convertToInteger destination .towardPositive signalInexact source).value : ℚ) := by
  rw [convertToInteger_value destination .towardPositive signalInexact source value hs hv]
  exact le_roundInteger_towardPositive value

theorem convertToInteger_towardNegative_le (destination : IntegerFormat)
    (signalInexact : Bool) (source : Datum) (value : ℚ)
    (hs : source.toRat? = some value)
    (hv : (convertToInteger destination .towardNegative signalInexact source).status.invalid =
      false) :
    ((convertToInteger destination .towardNegative signalInexact source).value : ℚ) ≤ value := by
  rw [convertToInteger_value destination .towardNegative signalInexact source value hs hv]
  exact roundInteger_towardNegative_le value

theorem abs_convertToInteger_towardZero_le (destination : IntegerFormat)
    (signalInexact : Bool) (source : Datum) (value : ℚ)
    (hs : source.toRat? = some value)
    (hv : (convertToInteger destination .towardZero signalInexact source).status.invalid = false) :
    |((convertToInteger destination .towardZero signalInexact source).value : ℚ)| ≤ |value| := by
  rw [convertToInteger_value destination .towardZero signalInexact source value hs hv]
  exact abs_roundInteger_towardZero_le value

/-- Fixed-width packing preserves the checked integer, including invalid delivery. -/
theorem convertToFixedInt_toInt (width : Nat) (mode : RoundingMode)
    (signalInexact : Bool) (source : Datum) :
    (convertToFixedInt width mode signalInexact source).1.toInt =
      (convertToInteger (.signed width) mode signalInexact source).value := by
  cases width with
  | zero =>
      have hr := convertToInteger_inRange (.signed 0) mode signalInexact source
      have hz : (convertToInteger (.signed 0) mode signalInexact source).value = 0 := by
        change 0 ≤ _ ∧ _ ≤ 0 at hr
        omega
      simp [convertToFixedInt, hz, FixedInt.toInt, FixedInt.ofInt]
  | succ width =>
      exact FixedInt.toInt_ofInt_eq_self (Nat.succ_pos width)
        (convertToInteger_inRange (.signed (width + 1)) mode signalInexact source)

/-- Unsigned packing preserves the checked integer exactly, including invalid delivery as zero. -/
theorem convertToUnsigned_toNat (width : Nat) (mode : RoundingMode)
    (signalInexact : Bool) (source : Datum) :
    ((convertToUnsigned width mode signalInexact source).1.toNat : Int) =
      (convertToInteger (.unsigned width) mode signalInexact source).value := by
  exact FloatLib.Numerics.IntegerFormat.toNat_ofNat_of_inRange
    (convertToInteger_inRange (.unsigned width) mode signalInexact source)

end FloatLib.Floats.Formats.DecimalInterchange.Conversion.Integer
