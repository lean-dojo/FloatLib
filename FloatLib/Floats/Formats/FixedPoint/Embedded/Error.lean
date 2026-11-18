/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Embedded.Proof

/-!
# N1169 fixed-point error bounds

N1169, ISO/IEC TR 18037:2006(E), §4.1.3 and C 7.18a.6.3.
Successful conversions have a rounding term and an explicit saturation term.
On an in-range source the latter vanishes. The result covers every adjacent
rounder; nearest rounding gives the sharper half-step bound. Coarse `roundfx`
rounding retains its half-step error even when saturation changes the low bits.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.FixedPoint.Embedded

open FloatLib.Numerics.Quantization

/-- WG14 N1169 (2006 TR 18037 draft), §4.1.3: every adjacent choice has error at most one
    coefficient unit. -/
theorem Rounding.error_le_one (rounding : Rounding) (x : ℚ) :
    |(rounding.run x : ℚ) - x| ≤ 1 := by
  rcases rounding.adjacent x with h | h
  · rw [h, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Rat.floor_le x))]
    exact (sub_lt_iff_lt_add'.mpr
      (by simpa only [Int.cast_add, Int.cast_one] using Rat.lt_floor_add_one x)).le
  · rw [h, abs_of_nonneg (sub_nonneg.mpr (Rat.le_ceil (x := x)))]
    exact (sub_lt_iff_lt_add'.mpr (Rat.ceil_lt (x := x))).le

/-- Rational clipping error in coefficient units, including arbitrary source overflow. -/
def Format.clippingError (format : Format) (x : ℚ) : ℚ :=
  |Saturating.clamp (format.quantizer.qmin : ℚ) (format.quantizer.qmax : ℚ)
    (x / format.quantizer.scale) - x / format.quantizer.scale|

/-- The clipping term is zero on every source that fits before rounding. -/
theorem Format.clippingError_eq_zero (format : Format) (x : ℚ)
    (h : format.SourceInRange x) : format.clippingError x = 0 := by
  simp [Format.clippingError, Saturating.clamp_eq_self h.1 h.2]

/-- A coefficient approximation scales to the value grid, with explicit source clipping. -/
theorem Format.clamp_error_le (format : Format) (coefficient : Int) (x ε : ℚ)
    (hround : |(coefficient : ℚ) - x / format.quantizer.scale| ≤ ε) :
    |Format.decode (format.clamp coefficient) - x| ≤
      format.quantizer.scale * (ε + format.clippingError x) := by
  have hrewrite : Format.decode (format.clamp coefficient) - x =
      format.quantizer.scale *
        (Saturating.clamp (format.quantizer.qmin : ℚ) (format.quantizer.qmax : ℚ)
          (coefficient : ℚ) - x / format.quantizer.scale) := by
    change format.quantizer.scale * ((format.quantizer.clampCode coefficient - 0 : Int) : ℚ) -
      x = _
    rw [Int.sub_zero]
    simp only [AffineQuantizer.clampCode, Saturating.clamp, Int.cast_max, Int.cast_min]
    rw [mul_sub, mul_div_cancel₀ _ (ne_of_gt format.quantizer.scale_pos)]
  rw [hrewrite, abs_mul, abs_of_pos format.quantizer.scale_pos]
  apply mul_le_mul_of_nonneg_left _ format.quantizer.scale_pos.le
  exact (Saturating.abs_clamp_sub_le (format.quantizer.qmin : ℚ)
    (format.quantizer.qmax : ℚ) (coefficient : ℚ)
    (x / format.quantizer.scale)).trans (add_le_add hround le_rfl)

/-- Every successful conversion inherits the coefficient bound of its selected rounder. -/
theorem convert_error_le (format : Format) (rounding : Rounding)
    (overflow : Overflow) (x ε : ℚ) (result : format.Code)
    (hround : |(rounding.run (x / format.quantizer.scale) : ℚ) -
      x / format.quantizer.scale| ≤ ε)
    (hresult : convert format rounding overflow x = some result) :
    |Format.decode result - x| ≤
      format.quantizer.scale * (ε + format.clippingError x) := by
  have hcode := ((convert_eq_some_iff format rounding overflow x result).mp hresult).2
  have heq : result = format.clamp (rounding.run (x / format.quantizer.scale)) :=
    Subtype.ext hcode
  rw [heq]
  exact format.clamp_error_le _ x ε hround

/-- WG14 N1169 (2006 TR 18037 draft), §4.1.3: one grid unit plus clipping bounds every
    successful adjacent conversion. -/
theorem convert_error_le_one (format : Format) (rounding : Rounding)
    (overflow : Overflow) (x : ℚ) (result : format.Code)
    (hresult : convert format rounding overflow x = some result) :
    |Format.decode result - x| ≤
      format.quantizer.scale * (1 + format.clippingError x) :=
  convert_error_le format rounding overflow x 1 result (rounding.error_le_one _) hresult

/-- Nearest conversion has half a grid unit of rounding error, separately from clipping. -/
theorem convert_nearest_error_le_half (format : Format) (rounding : NearestRounding)
    (overflow : Overflow) (x : ℚ) (result : format.Code)
    (hresult : convert format rounding.toRounding overflow x = some result) :
    |Format.decode result - x| ≤
      format.quantizer.scale * (1 / 2 + format.clippingError x) :=
  convert_error_le format rounding.toRounding overflow x (1 / 2) result
    (rounding.error_le_half _) hresult

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.6.3: saturation preserves the coarse
    rounding half-step error bound. -/
theorem roundfx_error_le_half {format : Format} (rounding : NearestRounding)
    (value result : format.Code) (count : Int)
    (hresult : roundfx rounding value count = some result) :
    |Format.decode result - Format.decode value| ≤
      format.quantizer.scale * ((2 : ℚ) ^ (format.fractionalBits - count.toNat) / 2) := by
  unfold roundfx at hresult
  split at hresult
  · simp only [Option.some.injEq] at hresult
    have hclamp := Saturating.abs_clamp_sub_clamp_le
      (format.quantizer.qmin : ℚ) (format.quantizer.qmax : ℚ)
      (roundCoefficient rounding format.fractionalBits (bitsfx value) count : ℚ)
      (bitsfx value : ℚ)
    have hlo : (format.quantizer.qmin : ℚ) ≤ (bitsfx value : ℚ) := by
      exact_mod_cast value.2.1
    have hhi : (bitsfx value : ℚ) ≤ (format.quantizer.qmax : ℚ) := by
      exact_mod_cast value.2.2
    rw [Saturating.clamp_eq_self hlo hhi] at hclamp
    rw [← hresult]
    change |format.quantizer.scale * ((format.quantizer.clampCode
      (roundCoefficient rounding format.fractionalBits (bitsfx value) count) - 0 : Int) : ℚ) -
      format.quantizer.scale * ((bitsfx value - 0 : Int) : ℚ)| ≤ _
    simp only [Int.sub_zero, AffineQuantizer.clampCode, Saturating.clamp,
      Int.cast_max, Int.cast_min]
    rw [← mul_sub, abs_mul, abs_of_pos format.quantizer.scale_pos]
    exact mul_le_mul_of_nonneg_left
      (hclamp.trans (roundCoefficient_error_le_half _ _ _ _)) format.quantizer.scale_pos.le
  · simp at hresult

/-- A coefficient distance scales exactly to a distance on the fixed-point value grid. -/
theorem Format.decode_distance_le {format : Format} (left right : format.Code)
    (ε : Int) (h : |bitsfx left - bitsfx right| ≤ ε) :
    |Format.decode left - Format.decode right| ≤ format.quantizer.scale * (ε : ℚ) := by
  change |format.quantizer.scale * ((bitsfx left - 0 : Int) : ℚ) -
    format.quantizer.scale * ((bitsfx right - 0 : Int) : ℚ)| ≤ _
  simp only [Int.sub_zero]
  rw [← mul_sub, abs_mul, abs_of_pos format.quantizer.scale_pos]
  apply mul_le_mul_of_nonneg_left _ format.quantizer.scale_pos.le
  exact_mod_cast h

/-- The draft's inward unit-product exception incurs one grid step plus source clipping. -/
theorem Format.unitProduct_error_le (format : Format) (positive : Bool) :
    |Format.decode (format.unitProduct positive) - (if positive then 1 else -1)| ≤
      format.quantizer.scale *
        (1 + format.clippingError (if positive then 1 else -1)) := by
  apply format.clamp_error_le
  cases positive <;> norm_num [Format.quantizer, div_div, Int.cast_sub, Int.cast_pow]

/-- WG14 N1169 (2006 TR 18037 draft), §4.1.6.2.1: every admitted arithmetic result has at most
    two steps plus clipping. -/
theorem Arithmetic.Allowed.error_le (operation : Arithmetic) (precision : Precision)
    (format : Format) (rounding : Rounding) (overflow : Overflow)
    (x y exact : ℚ) (result : format.Code)
    (hexact : operation.exact x y = some exact)
    (hresult : operation.Allowed precision format rounding overflow x y result) :
    |Format.decode result - exact| ≤
      format.quantizer.scale * (2 + format.clippingError exact) := by
  obtain ⟨value, hvalue, ordinary | neighbor | unit⟩ := hresult
  all_goals have heq : value = exact := Option.some.inj (hvalue.symm.trans hexact)
  all_goals subst value
  · apply (convert_error_le_one format rounding overflow exact result ordinary).trans
    apply mul_le_mul_of_nonneg_left _ format.quantizer.scale_pos.le
    exact add_le_add (by norm_num : (1 : ℚ) ≤ 2) le_rfl
  · obtain ⟨_, _, original, horiginal, hdistance⟩ := neighbor
    have hm := Format.decode_distance_le result original 1 hdistance
    have ho := convert_error_le_one format rounding overflow exact original horiginal
    calc
      |Format.decode result - exact| ≤
          |Format.decode result - Format.decode original| +
            |Format.decode original - exact| := abs_sub_le _ _ _
      _ ≤ format.quantizer.scale * 1 +
          format.quantizer.scale * (1 + format.clippingError exact) := add_le_add hm ho
      _ = format.quantizer.scale * (2 + format.clippingError exact) := by ring
  · obtain ⟨_, hu, hr⟩ := unit
    rw [hr]
    have hunit : (if decide (exact = 1) then (1 : ℚ) else -1) = exact := by
      rcases hu with rfl | rfl <;> decide
    have hbound := format.unitProduct_error_le (exact = 1)
    rw [hunit] at hbound
    apply hbound.trans
    apply mul_le_mul_of_nonneg_left _ format.quantizer.scale_pos.le
    exact add_le_add (by norm_num : (1 : ℚ) ≤ 2) le_rfl

/-- The whole implementation-selected arithmetic family satisfies the common error budget. -/
theorem Arithmetic.applyWith_error_le (operation : Arithmetic) (policy : ArithmeticPolicy)
    (format : Format) (rounding : Rounding) (overflow : Overflow)
    (x y exact : ℚ) (result : format.Code)
    (hexact : operation.exact x y = some exact)
    (hresult : operation.applyWith policy format rounding overflow x y = some result) :
    |Format.decode result - exact| ≤
      format.quantizer.scale * (2 + format.clippingError exact) :=
  Arithmetic.Allowed.error_le operation policy.FX_FULL_PRECISION format rounding overflow
    x y exact result hexact
    (operation.applyWith_allowed policy format rounding overflow x y result hresult)

/-- WG14 N1169 (2006 TR 18037 draft), C clause 6.4.4.2a: decimal neighboring-value freedom costs
    at most one extra grid step. -/
theorem Constant.rounded_error_le (layout : Layout) (policy : Constant.Policy)
    (literal : Constant.Literal) :
    |Format.decode (Constant.rounded layout policy literal) - literal.value| ≤
      (layout.format literal.type).quantizer.scale *
        (3 / 2 + (layout.format literal.type).clippingError literal.value) := by
  let format := layout.format literal.type
  by_cases hhex : literal.hexadecimal
  · simp only [Constant.rounded, hhex, ↓reduceIte]
    apply (format.clamp_error_le _ literal.value 1
      (policy.hexadecimal.error_le_one _)).trans
    apply mul_le_mul_of_nonneg_left _ format.quantizer.scale_pos.le
    exact add_le_add (by norm_num : (1 : ℚ) ≤ 3 / 2) le_rfl
  · let base := format.clamp (policy.nearest.run (literal.value / format.quantizer.scale))
    have hmove := (Format.move_distance base (policy.decimalStep format literal)).trans
      (policy.decimalStep_bound format literal)
    have hm := Format.decode_distance_le _ _ 1 hmove
    have hb := format.clamp_error_le _ literal.value (1 / 2)
      (policy.nearest.error_le_half _)
    simp only [Constant.rounded, hhex]
    calc
      |Format.decode (Format.move base (policy.decimalStep format literal)) -
          literal.value| ≤
          |Format.decode (Format.move base (policy.decimalStep format literal)) -
            Format.decode base| + |Format.decode base - literal.value| := abs_sub_le _ _ _
      _ ≤ format.quantizer.scale * 1 +
          format.quantizer.scale * (1 / 2 + format.clippingError literal.value) :=
        add_le_add hm hb
      _ = _ := by ring

/-- The maximum of any fract grid is one minus its spacing, including zero-bit extensions. -/
theorem Format.decode_maximum_fract (format : Format) (h : format.integralBits = 0) :
    Format.decode format.maximum = 1 - format.quantizer.scale := by
  rw [decode_eq]
  change (format.integerFormat.maxValue : ℚ) / 2 ^ format.fractionalBits = _
  rw [format.maxValue_eq]
  simp only [Format.precision, h, Nat.zero_add, Int.cast_sub, Int.cast_pow, Int.cast_ofNat,
    Int.cast_one, Format.quantizer]
  field_simp

/-- WG14 N1169 (2006 TR 18037 draft), C clause 6.4.4.2a: every accepted constant lies within
    three halves of a grid step. -/
theorem Constant.translate_error_le (layout : Layout) (policy : Constant.Policy)
    (literal : Constant.Literal) (result : (layout.format literal.type).Code)
    (hresult : Constant.translate layout policy literal = some result) :
    |Format.decode result - literal.value| ≤
      (layout.format literal.type).quantizer.scale * (3 / 2) := by
  unfold Constant.translate at hresult
  split at hresult
  · rename_i hunit
    obtain ⟨hkind, hvalue⟩ := hunit
    have hi : (layout.format literal.type).integralBits = 0 := by
      simp [Layout.format, hkind]
    have heq := Option.some.inj hresult
    rw [← heq, (layout.format literal.type).decode_maximum_fract hi, hvalue]
    rw [sub_sub_cancel_left, abs_neg,
      abs_of_pos (layout.format literal.type).quantizer.scale_pos]
    exact le_mul_of_one_le_right
      (layout.format literal.type).quantizer.scale_pos.le (by norm_num)
  · split at hresult
    · rename_i hrange
      have heq := Option.some.inj hresult
      have hbound := Constant.rounded_error_le layout policy literal
      rw [heq, (layout.format literal.type).clippingError_eq_zero _ hrange, add_zero] at hbound
      exact hbound
    · simp at hresult

end FloatLib.Floats.Formats.FixedPoint.Embedded
