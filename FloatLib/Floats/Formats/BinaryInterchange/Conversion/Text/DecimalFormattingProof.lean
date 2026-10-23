/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.Formatting
public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.PrecisionProof
public import FloatLib.Numerics.Exact.DecimalText.NotationProof

/-!
# Correctness of fixed and scientific decimal output

The notation scanner recovers the decimal value selected by rounding in the `fixed` and
`scientific` styles of `format`. Fixed output has at most half a decimal place of nearest-even
error, and scientific output inherits the significant-digit bound. Neither decimal-point placement
nor exponent notation introduces additional rounding. Every style raises at most inexact, and the
exact styles raise nothing.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Numerics

/-- Nearest-even rounding on any decimal grid changes the value by at most half a grid unit. -/
theorem roundDecimal_nearest_error (value : DecimalText.Decimal) (quantum : Int) :
    |(DecimalText.roundDecimal (roundTextMagnitude .nearest) value quantum).toRat -
        value.toRat| ≤ (10 : Rat) ^ quantum / 2 := by
  let unit : Rat := (10 : Rat) ^ quantum
  let magnitude : Rat := (value.significand : Rat) * (10 : Rat) ^ value.exponent
  have hu : 0 < unit := zpow_pos (by norm_num) _
  have hm : 0 ≤ magnitude := mul_nonneg (Nat.cast_nonneg _) (zpow_pos (by norm_num) _).le
  have he := mul_le_mul_of_nonneg_right
    (roundTextMagnitude_nearest_error value.negative (magnitude / unit)
      (div_nonneg hm hu.le)) hu.le
  have heq : |(roundTextMagnitude .nearest value.negative (magnitude / unit) : Rat) * unit -
      magnitude| =
      |(roundTextMagnitude .nearest value.negative (magnitude / unit) : Rat) -
        magnitude / unit| * unit := by
    calc
      _ = |((roundTextMagnitude .nearest value.negative (magnitude / unit) : Rat) -
          magnitude / unit) * unit| := by
        rw [sub_mul, div_mul_cancel₀ _ hu.ne']
      _ = _ := by rw [abs_mul, abs_of_pos hu]
  rw [← heq] at he
  cases hs : value.negative <;>
    simpa [DecimalText.roundDecimal, RadixText.roundCoefficient, DecimalText.Decimal.toRat,
      hs, magnitude, unit, neg_mul, neg_sub_neg, neg_add_eq_sub, abs_sub_comm, div_eq_mul_inv,
      mul_comm] using he

/-- Fixed output denotes the decimal selected by rounding, without an extra rounding step. -/
@[simp] theorem parse_fixedText (mode : IEEERoundingMode) (places : Nat)
    (value : Numerics.Dyadic) :
    DecimalText.parse (fixedText mode places value).text =
      some (roundFixed mode places (DecimalText.ofDyadic value)).toRat := by
  simp [fixedText]

/-- Scientific output denotes the decimal selected by rounding, without an extra rounding step. -/
@[simp] theorem parse_scientificText (mode : IEEERoundingMode) (places : Nat)
    (value : Numerics.Dyadic) :
    DecimalText.parse (scientificText mode places value).text =
      some (roundScientific mode places (DecimalText.ofDyadic value)).toRat := by
  simp [scientificText]

/-- Fixed rounding preserves the sign, including when the result is zero. -/
@[simp] theorem roundFixed_negative (mode : IEEERoundingMode) (places : Nat)
    (value : DecimalText.Decimal) : (roundFixed mode places value).negative = value.negative :=
  rfl

/-- Scientific rounding preserves the sign, including when the result is zero. -/
@[simp] theorem roundScientific_negative (mode : IEEERoundingMode) (places : Nat)
    (value : DecimalText.Decimal) :
    (roundScientific mode places value).negative = value.negative :=
  rfl

/-- Fixed output raises inexact exactly when the rounding changes the numerical value. -/
theorem fixedText_inexact_iff (mode : IEEERoundingMode) (places : Nat)
    (value : Numerics.Dyadic) :
    (fixedText mode places value).status.inexact = true ↔
      (roundFixed mode places (DecimalText.ofDyadic value)).toRat ≠ value.toRat := by
  simp [fixedText]

/-- Scientific output raises inexact exactly when the rounding changes the numerical value. -/
theorem scientificText_inexact_iff (mode : IEEERoundingMode) (places : Nat)
    (value : Numerics.Dyadic) :
    (scientificText mode places value).status.inexact = true ↔
      (roundScientific mode places (DecimalText.ofDyadic value)).toRat ≠ value.toRat := by
  simp [scientificText]

/-- Text output can raise only inexact, so the other four exception indicators stay clear. -/
theorem format_status {fmt : FloatFormat} (value : Model fmt) (style : TextStyle)
    (mode : IEEERoundingMode) :
    (format value style mode (status := true)).status =
      { inexact := (format value style mode (status := true)).status.inexact } := by
  simp only [format, Internal.Status.format]
  cases exactValue value with
  | finite exact =>
      cases style with
      | hex precision =>
          cases precision <;> simp [Internal.Status.formatFinite, formatDyadicText]
      | significant digits => simp [Internal.Status.formatFinite, formatDyadicText]
      | _ => simp [Internal.Status.formatFinite, formatDyadicText, fixedText, scientificText]
  | infinity negative => cases style <;> rfl
  | nan negative signaling payload => cases style <;> rfl

/-- Exact decimal output raises none of the five exception indicators. -/
@[simp] theorem format_exact_status {fmt : FloatFormat} (value : Model fmt)
    (mode : IEEERoundingMode) :
    (format value (style := .exact) (mode := mode) (status := true)).status = {} := by
  simp only [format, Internal.Status.format]
  cases exactValue value <;> simp [Internal.Status.formatFinite, formatDyadicText]

/-- Exact hexadecimal output raises none of the five exception indicators. -/
@[simp] theorem format_hex_status {fmt : FloatFormat} (value : Model fmt)
    (mode : IEEERoundingMode) :
    (format value (style := .hex) (mode := mode) (status := true)).status = {} := by
  simp only [format, Internal.Status.format]
  cases exactValue value <;> simp [Internal.Status.formatFinite, formatDyadicText]

/-- A finite model's fixed output denotes its exact dyadic value rounded to `places` places. -/
theorem parse_format_fixed_of_toDyadic? {fmt : FloatFormat}
    (mode : IEEERoundingMode) (places : Nat) (value : Model fmt) (d : Numerics.Dyadic)
    (h : toDyadic? value = some d) :
    DecimalText.parse (format value (style := .fixed places) (mode := mode)) =
      some (roundFixed mode places (DecimalText.ofDyadic d)).toRat := by
  simp [format, Internal.Status.format, Internal.Status.formatFinite, exactValue, h]

/-- A finite model's scientific output denotes its exact dyadic value rounded to `places + 1`
significant digits. -/
theorem parse_format_scientific_of_toDyadic? {fmt : FloatFormat}
    (mode : IEEERoundingMode) (places : Nat) (value : Model fmt) (d : Numerics.Dyadic)
    (h : toDyadic? value = some d) :
    DecimalText.parse (format value (style := .scientific places) (mode := mode)) =
      some (roundScientific mode places (DecimalText.ofDyadic d)).toRat := by
  simp [format, Internal.Status.format, Internal.Status.formatFinite, exactValue, h]

/-- The fixed-point string has at most half a last-place unit of nearest-even error. -/
theorem format_fixed_error {fmt : FloatFormat} (value : Model fmt)
    (d : Numerics.Dyadic) (h : toDyadic? value = some d) (places : Nat) :
    ∃ result : Rat, DecimalText.parse (format value (style := .fixed places)) = some result ∧
      |result - d.toRat| ≤ (10 : Rat) ^ (-(places : Int)) / 2 := by
  refine ⟨_, parse_format_fixed_of_toDyadic? .nearest places value d h, ?_⟩
  simpa [roundFixed] using
    roundDecimal_nearest_error (DecimalText.ofDyadic d) (-(places : Int))

/-- The scientific string inherits the nearest-even significant-digit error bound. -/
theorem format_scientific_error {fmt : FloatFormat} (value : Model fmt)
    (d : Numerics.Dyadic) (h : toDyadic? value = some d) (places : Nat) :
    ∃ result : Rat, DecimalText.parse (format value (style := .scientific places)) = some result ∧
      |result - d.toRat| ≤
        (10 : Rat) ^ DecimalText.significantQuantum (DecimalText.ofDyadic d).significand
          (DecimalText.ofDyadic d).exponent ⟨places + 1, by omega⟩ / 2 := by
  refine ⟨_, parse_format_scientific_of_toDyadic? .nearest places value d h, ?_⟩
  simpa [roundScientific] using
    significantDecimal_nearest_error (DecimalText.ofDyadic d) ⟨places + 1, by omega⟩

end FloatLib.Floats.Formats.BinaryInterchange.Model
