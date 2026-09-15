/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.DecimalFormatting
public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.PrecisionProof
public import FloatLib.Numerics.Exact.DecimalText.NotationProof

/-!
# Correctness of fixed and scientific decimal output

The notation scanner recovers the decimal value selected by rounding. Fixed output has at most
half a decimal place of nearest-even error; scientific output inherits the significant-digit
bound. Neither decimal-point placement nor exponent notation introduces additional rounding.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Numerics

/-- Nearest-even rounding on any decimal grid changes the value by at most half a grid unit. -/
theorem roundDecimal_nearestEven_error (value : DecimalText.Decimal) (quantum : Int) :
    |(DecimalText.roundDecimal (roundTextMagnitude .nearestEven) value quantum).toRat -
        value.toRat| ≤ (10 : Rat) ^ quantum / 2 := by
  let unit : Rat := (10 : Rat) ^ quantum
  let magnitude : Rat := (value.significand : Rat) * (10 : Rat) ^ value.exponent
  have hu : 0 < unit := zpow_pos (by norm_num) _
  have hm : 0 ≤ magnitude := mul_nonneg (Nat.cast_nonneg _) (zpow_pos (by norm_num) _).le
  have he := mul_le_mul_of_nonneg_right
    (roundTextMagnitude_nearestEven_error value.negative (magnitude / unit)
      (div_nonneg hm hu.le)) hu.le
  have heq : |(roundTextMagnitude .nearestEven value.negative (magnitude / unit) : Rat) * unit -
      magnitude| =
      |(roundTextMagnitude .nearestEven value.negative (magnitude / unit) : Rat) -
        magnitude / unit| * unit := by
    calc
      _ = |((roundTextMagnitude .nearestEven value.negative (magnitude / unit) : Rat) -
          magnitude / unit) * unit| := by
        rw [sub_mul, div_mul_cancel₀ _ hu.ne']
      _ = _ := by rw [abs_mul, abs_of_pos hu]
  rw [← heq] at he
  cases hs : value.negative <;>
    simpa [DecimalText.roundDecimal, RadixText.roundCoefficient, DecimalText.Decimal.toRat,
      hs, magnitude, unit, neg_mul, neg_sub_neg, neg_add_eq_sub, abs_sub_comm, div_eq_mul_inv,
      mul_comm] using he

/-- Either decimal notation denotes the original decimal, without an extra rounding step. -/
@[simp] theorem parse_renderDecimalStyle (style : DecimalStyle) (value : DecimalText.Decimal) :
    DecimalText.parse (renderDecimalStyle style value) = some value.toRat := by
  cases style <;> simp [renderDecimalStyle]

/-- The characters denote precisely the value selected by decimal rounding. -/
theorem parse_formatDyadicDecimal (mode : IEEERoundingMode) (style : DecimalStyle)
    (value : Numerics.Dyadic) :
    DecimalText.parse (formatDyadicDecimal mode style value).text =
      some (roundDecimalForStyle mode style (DecimalText.ofDyadic value)).toRat := by
  simp [formatDyadicDecimal]

/-- Choosing notation and precision preserves the sign, including when the result is zero. -/
@[simp] theorem roundDecimalForStyle_negative (mode : IEEERoundingMode) (style : DecimalStyle)
    (value : DecimalText.Decimal) :
    (roundDecimalForStyle mode style value).negative = value.negative := by
  cases style <;> rfl

/-- Inexact is set exactly when the decimal rounding changes the numerical value. -/
theorem formatDyadicDecimal_inexact_iff (mode : IEEERoundingMode) (style : DecimalStyle)
    (value : Numerics.Dyadic) :
    (formatDyadicDecimal mode style value).status.inexact = true ↔
      (roundDecimalForStyle mode style (DecimalText.ofDyadic value)).toRat ≠ value.toRat := by
  simp [formatDyadicDecimal]

/-- Decimal text has unbounded exponents; output rounding can raise only inexact. -/
theorem formatDecimalWithStatus_status {fmt : FloatFormat} (mode : IEEERoundingMode)
    (style : DecimalStyle) (value : Model fmt) :
    (formatDecimalWithStatus mode style value).status =
      { inexact := (formatDecimalWithStatus mode style value).status.inexact } := by
  cases h : exactValue value <;> simp [formatDecimalWithStatus, h, formatDyadicDecimal]

/-- A finite model's output denotes its exact dyadic value rounded to the selected decimal grid. -/
theorem parse_formatDecimalWithStatus_of_toDyadic? {fmt : FloatFormat}
    (mode : IEEERoundingMode) (style : DecimalStyle) (value : Model fmt) (d : Numerics.Dyadic)
    (h : toDyadic? value = some d) :
    DecimalText.parse (formatDecimalWithStatus mode style value).text =
      some (roundDecimalForStyle mode style (DecimalText.ofDyadic d)).toRat := by
  simpa [formatDecimalWithStatus, exactValue, h] using parse_formatDyadicDecimal mode style d

/-- The actual fixed-point string has at most half a last-place unit of nearest-even error. -/
theorem formatFixed_nearestEven_error {fmt : FloatFormat} (value : Model fmt)
    (d : Numerics.Dyadic) (h : toDyadic? value = some d) (places : Nat) :
    ∃ result : Rat, DecimalText.parse (formatFixed value places) = some result ∧
      |result - d.toRat| ≤ (10 : Rat) ^ (-(places : Int)) / 2 := by
  refine ⟨_, parse_formatDecimalWithStatus_of_toDyadic? .nearestEven (.fixed places) value d h, ?_⟩
  simpa [roundDecimalForStyle] using
    roundDecimal_nearestEven_error (DecimalText.ofDyadic d) (-(places : Int))

/-- The actual scientific string inherits the nearest-even significant-digit error bound. -/
theorem formatScientific_nearestEven_error {fmt : FloatFormat} (value : Model fmt)
    (d : Numerics.Dyadic) (h : toDyadic? value = some d) (places : Nat) :
    ∃ result : Rat, DecimalText.parse (formatScientific value places) = some result ∧
      |result - d.toRat| ≤
        (10 : Rat) ^ DecimalText.significantQuantum (DecimalText.ofDyadic d).significand
          (DecimalText.ofDyadic d).exponent ⟨places + 1, by omega⟩ / 2 := by
  refine ⟨_,
    parse_formatDecimalWithStatus_of_toDyadic? .nearestEven (.scientific places) value d h, ?_⟩
  simpa [roundDecimalForStyle] using
    significantDecimal_nearestEven_error (DecimalText.ofDyadic d) ⟨places + 1, by omega⟩

end FloatLib.Floats.Formats.BinaryInterchange.Model
