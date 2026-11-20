/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Functions.Recommended.Runtime
public import FloatLib.Floats.Formats.P3109.Functions.Proof

/-!
# The functions of clause 9.2 on P3109 formats round the real function once

Each function of `Functions.Recommended.Runtime` decodes to `Functions.referenceValue` of its
closed expression, for independent source and target formats, every rounding mode and every
saturation mode (`decode_Exp10`, `decode_Log10`, `decode_Rootn`, `decode_Pown`, `decode_Pow`
and their siblings): the real value of a finite expression is rounded once by the report's
rule and then saturated.

The second group of theorems says which real number a finite expression denotes:
`exponential_finite` (`base ^ x`, less one with `minusOne`), `logarithmIn_of_pos`
(`logb base (x + offset)`), `root_of_pos` and `root_of_neg` (`x ^ (1 / degree)` and its negative
for an odd degree), `integerPower_of_ne_zero` (`x ^ n`), `power_of_pos`, `power_of_neg`
(`x ^ y`, and `x ^ n` for a negative base and an integer exponent), `positivePower_of_pos` and
`compound_of_gt` (`(1 + x) ^ n`).
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109.Functions

/-- At a finite operand the exponential in a base is `base ^ x`, less one with `minusOne`. -/
theorem exponential_finite (base : Rat) (hbase : 1 < base) (minusOne : Bool) (x : Rat) :
    ∃ expression, exponential base hbase minusOne (.finite x) = .finite expression ∧
      expression.toReal = (base : ℝ) ^ (x : ℝ) - (if minusOne then 1 else 0) := by
  cases minusOne
  · exact ⟨_, rfl, by simp [FunctionExpr.toReal]⟩
  · refine ⟨_, rfl, ?_⟩
    simp only [↓reduceIte, FunctionExpr.toReal]
    push_cast
    ring

/-- At a finite operand above the zero of its argument, the logarithm in a base is
`logb base (x + offset)`. -/
theorem logarithmIn_of_pos (base : Rat) (hbase : 1 < base) (offset : Rat) {x : Rat}
    (hpositive : 0 < x + offset) :
    ∃ expression, logarithmIn base hbase offset (.finite x) = .finite expression ∧
      expression.toReal = Real.logb base ((x : ℝ) + offset) := by
  refine ⟨.logb base (x + offset) hbase hpositive, ?_, ?_⟩
  · simp only [logarithmIn, hpositive, ↓reduceDIte]
  · simp [FunctionExpr.toReal]

/-- At a positive operand and a nonzero degree the root is `x ^ (1 / degree)`. -/
theorem root_of_pos {degree : Int} (hdegree : degree ≠ 0) {x : Rat} (hpositive : 0 < x) :
    ∃ expression, root degree (.finite x) = .finite expression ∧
      expression.toReal = (x : ℝ) ^ ((degree : ℝ)⁻¹) := by
  refine ⟨.power x (1 / (degree : Rat)) hpositive.le, ?_, ?_⟩
  · simp only [root, hdegree, hpositive.ne', hpositive, ↓reduceIte, ↓reduceDIte]
  · simp [FunctionExpr.toReal]

/-- At a negative operand and an odd degree the root is the negative of `(-x) ^ (1 / degree)`. -/
theorem root_of_neg {degree : Int} (hodd : degree % 2 ≠ 0) {x : Rat} (hnegative : x < 0) :
    ∃ expression, root degree (.finite x) = .finite expression ∧
      expression.toReal = -((-x : ℝ) ^ ((degree : ℝ)⁻¹)) := by
  have hdegree : degree ≠ 0 := by
    rintro rfl
    exact hodd rfl
  refine ⟨.affine (-1) 0 (.power (-x) (1 / (degree : Rat)) (neg_nonneg.mpr hnegative.le)),
    ?_, ?_⟩
  · simp only [root, hdegree, hnegative.ne, not_lt.mpr hnegative.le, hodd, ↓reduceIte,
      ↓reduceDIte]
  · simp [FunctionExpr.toReal]

/-- At a nonzero finite operand the integer power is `x ^ exponent`. -/
theorem integerPower_of_ne_zero (exponent : Int) {x : Rat} (hx : x ≠ 0) :
    ∃ expression, integerPower exponent (.finite x) = .finite expression ∧
      expression.toReal = (x : ℝ) ^ exponent := by
  by_cases hexponent : exponent = 0
  · refine ⟨.rational 1, ?_, ?_⟩
    · simp only [integerPower, hexponent, ↓reduceIte]
    · simp [FunctionExpr.toReal, hexponent]
  · refine ⟨.rational (x ^ exponent), ?_, ?_⟩
    · simp only [integerPower, hexponent, hx, ↓reduceIte]
    · simp [FunctionExpr.toReal]

/-- At a positive base and a finite exponent the power is `x ^ y`. -/
theorem power_of_pos {x : Rat} (hpositive : 0 < x) (y : Rat) :
    ∃ expression, power (.finite x) (.finite y) = .finite expression ∧
      expression.toReal = (x : ℝ) ^ (y : ℝ) := by
  by_cases hy : y = 0
  · refine ⟨.rational 1, ?_, ?_⟩
    · simp only [power, hy, ↓reduceIte]
    · simp [FunctionExpr.toReal, hy]
  · refine ⟨.power x y hpositive.le, ?_, ?_⟩
    · simp only [power, hy, hpositive.ne', hpositive, ↓reduceIte, ↓reduceDIte]
    · simp [FunctionExpr.toReal]

/-- At a negative base and an integer exponent the power is `x ^ n`. -/
theorem power_of_neg {x : Rat} (hnegative : x < 0) (n : Int) :
    ∃ expression, power (.finite x) (.finite (n : Rat)) = .finite expression ∧
      expression.toReal = (x : ℝ) ^ n := by
  by_cases hn : n = 0
  · refine ⟨.rational 1, ?_, ?_⟩
    · simp only [power, hn, Int.cast_zero, ↓reduceIte]
    · simp [FunctionExpr.toReal, hn]
  · have hcast : (n : Rat) ≠ 0 := by exact_mod_cast hn
    have hmagnitude : ((-x : Rat) : ℝ) ^ ((n : Rat) : ℝ) = (-(x : ℝ)) ^ n := by
      push_cast
      exact Real.rpow_intCast _ n
    by_cases heven : n % 2 = 0
    · refine ⟨.power (-x) n (neg_nonneg.mpr hnegative.le), ?_, ?_⟩
      · simp only [power, hcast, hnegative.ne, not_lt.mpr hnegative.le, Rat.den_intCast,
          Rat.num_intCast, heven, ↓reduceIte, ↓reduceDIte]
      · simp only [FunctionExpr.toReal]
        rw [hmagnitude, (Int.even_iff.mpr heven).neg_zpow]
    · refine ⟨.affine (-1) 0 (.power (-x) n (neg_nonneg.mpr hnegative.le)), ?_, ?_⟩
      · simp only [power, hcast, hnegative.ne, not_lt.mpr hnegative.le, Rat.den_intCast,
          Rat.num_intCast, heven, ↓reduceIte, ↓reduceDIte]
      · simp only [FunctionExpr.toReal]
        rw [hmagnitude, (Int.not_even_iff_odd.mp (mt Int.even_iff.mp heven)).neg_zpow]
        push_cast
        ring

/-- At a positive base and a finite exponent `powr` is `x ^ y`. -/
theorem positivePower_of_pos {x : Rat} (hpositive : 0 < x) (y : Rat) :
    ∃ expression, positivePower (.finite x) (.finite y) = .finite expression ∧
      expression.toReal = (x : ℝ) ^ (y : ℝ) := by
  refine ⟨.power x y hpositive.le, ?_, ?_⟩
  · simp only [positivePower, hpositive, ↓reduceDIte]
  · simp [FunctionExpr.toReal]

/-- At a finite operand above -1 the compound is `(1 + x) ^ exponent`. -/
theorem compound_of_gt (exponent : Int) {x : Rat} (hx : -1 < x) :
    ∃ expression, compound exponent (.finite x) = .finite expression ∧
      expression.toReal = (1 + (x : ℝ)) ^ exponent := by
  refine ⟨.rational ((1 + x) ^ exponent), ?_, ?_⟩
  · simp only [compound, not_lt.mpr hx.le, hx.ne', ↓reduceIte]
  · simp [FunctionExpr.toReal]

end FloatLib.Floats.Formats.P3109.Functions

namespace FloatLib.Floats.ExecFloat.P3109

open Formats.P3109

variable {format : Format}

/-- `Exp10` decodes to the reference of `10 ^ x`, rounded once and saturated. -/
theorem decode_Exp10 (input : ExecFloat.P3109 format) (target : Format) (mode : RoundingMode)
    (saturation : SaturationMode) :
    Format.SameDatum (decode (Exp10 input target mode saturation))
      (Functions.referenceValue target { rounding := mode, saturation }
        (Functions.exponential 10 (by decide) false input.toClosedRat)) :=
  decode_projectFunction _ _ _

/-- `Exp2MinusOne` decodes to the reference of `2 ^ x - 1`, rounded once and saturated. -/
theorem decode_Exp2MinusOne (input : ExecFloat.P3109 format) (target : Format)
    (mode : RoundingMode) (saturation : SaturationMode) :
    Format.SameDatum (decode (Exp2MinusOne input target mode saturation))
      (Functions.referenceValue target { rounding := mode, saturation }
        (Functions.exponential 2 (by decide) true input.toClosedRat)) :=
  decode_projectFunction _ _ _

/-- `Exp10MinusOne` decodes to the reference of `10 ^ x - 1`, rounded once and saturated. -/
theorem decode_Exp10MinusOne (input : ExecFloat.P3109 format) (target : Format)
    (mode : RoundingMode) (saturation : SaturationMode) :
    Format.SameDatum (decode (Exp10MinusOne input target mode saturation))
      (Functions.referenceValue target { rounding := mode, saturation }
        (Functions.exponential 10 (by decide) true input.toClosedRat)) :=
  decode_projectFunction _ _ _

/-- `Log10` decodes to the reference of the base-ten logarithm, rounded once and saturated. -/
theorem decode_Log10 (input : ExecFloat.P3109 format) (target : Format) (mode : RoundingMode)
    (saturation : SaturationMode) :
    Format.SameDatum (decode (Log10 input target mode saturation))
      (Functions.referenceValue target { rounding := mode, saturation }
        (Functions.logarithmIn 10 (by decide) 0 input.toClosedRat)) :=
  decode_projectFunction _ _ _

/-- `Log2OnePlus` decodes to the reference of `logb 2 (1 + x)`, rounded once and saturated. -/
theorem decode_Log2OnePlus (input : ExecFloat.P3109 format) (target : Format)
    (mode : RoundingMode) (saturation : SaturationMode) :
    Format.SameDatum (decode (Log2OnePlus input target mode saturation))
      (Functions.referenceValue target { rounding := mode, saturation }
        (Functions.logarithmIn 2 (by decide) 1 input.toClosedRat)) :=
  decode_projectFunction _ _ _

/-- `Log10OnePlus` decodes to the reference of `logb 10 (1 + x)`, rounded once and saturated. -/
theorem decode_Log10OnePlus (input : ExecFloat.P3109 format) (target : Format)
    (mode : RoundingMode) (saturation : SaturationMode) :
    Format.SameDatum (decode (Log10OnePlus input target mode saturation))
      (Functions.referenceValue target { rounding := mode, saturation }
        (Functions.logarithmIn 10 (by decide) 1 input.toClosedRat)) :=
  decode_projectFunction _ _ _

/-- `Rootn` decodes to the reference of the real root, rounded once and saturated. -/
theorem decode_Rootn (input : ExecFloat.P3109 format) (degree : Int) (target : Format)
    (mode : RoundingMode) (saturation : SaturationMode) :
    Format.SameDatum (decode (Rootn input degree target mode saturation))
      (Functions.referenceValue target { rounding := mode, saturation }
        (Functions.root degree input.toClosedRat)) :=
  decode_projectFunction _ _ _

/-- `Cbrt` decodes to the reference of the real cube root, rounded once and saturated. -/
theorem decode_Cbrt (input : ExecFloat.P3109 format) (target : Format) (mode : RoundingMode)
    (saturation : SaturationMode) :
    Format.SameDatum (decode (Cbrt input target mode saturation))
      (Functions.referenceValue target { rounding := mode, saturation }
        (Functions.root 3 input.toClosedRat)) :=
  decode_Rootn input 3 target mode saturation

/-- `Pown` decodes to the reference of the exact integer power, rounded once and saturated. -/
theorem decode_Pown (input : ExecFloat.P3109 format) (exponent : Int) (target : Format)
    (mode : RoundingMode) (saturation : SaturationMode) :
    Format.SameDatum (decode (Pown input exponent target mode saturation))
      (Functions.referenceValue target { rounding := mode, saturation }
        (Functions.integerPower exponent input.toClosedRat)) :=
  decode_projectFunction _ _ _

/-- `Pow` decodes to the reference of `x ^ y`, rounded once and saturated, for independent
formats of the base, the exponent and the result. -/
theorem decode_Pow {exponentFormat : Format} (base : ExecFloat.P3109 format)
    (exponent : ExecFloat.P3109 exponentFormat) (target : Format) (mode : RoundingMode)
    (saturation : SaturationMode) :
    Format.SameDatum (decode (Pow base exponent target mode saturation))
      (Functions.referenceValue target { rounding := mode, saturation }
        (Functions.power base.toClosedRat exponent.toClosedRat)) :=
  decode_projectFunction _ _ _

/-- `Powr` decodes to the reference of `x ^ y` for a nonnegative base, rounded once and
saturated. -/
theorem decode_Powr {exponentFormat : Format} (base : ExecFloat.P3109 format)
    (exponent : ExecFloat.P3109 exponentFormat) (target : Format) (mode : RoundingMode)
    (saturation : SaturationMode) :
    Format.SameDatum (decode (Powr base exponent target mode saturation))
      (Functions.referenceValue target { rounding := mode, saturation }
        (Functions.positivePower base.toClosedRat exponent.toClosedRat)) :=
  decode_projectFunction _ _ _

/-- `Compound` decodes to the reference of `(1 + x) ^ exponent`, rounded once and saturated. -/
theorem decode_Compound (input : ExecFloat.P3109 format) (exponent : Int) (target : Format)
    (mode : RoundingMode) (saturation : SaturationMode) :
    Format.SameDatum (decode (Compound input exponent target mode saturation))
      (Functions.referenceValue target { rounding := mode, saturation }
        (Functions.compound exponent input.toClosedRat)) :=
  decode_projectFunction _ _ _

end FloatLib.Floats.ExecFloat.P3109
