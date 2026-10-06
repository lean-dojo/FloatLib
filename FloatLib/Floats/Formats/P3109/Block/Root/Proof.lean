/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Block.Root.Runtime
public import FloatLib.Floats.Formats.P3109.Arithmetic.Sqrt.Proof

/-!
# Refinement of P3109 block roots

Finite nonzero result scales normalize the exact real root before precision rounding. The
executable square comparisons refine the existing real-root reference in every rounding mode.
The final encoder preserves the signed, rounded, and saturated datum.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.P3109

open FloatLib.Numerics Arithmetic

namespace BlockRoot

/-- Exact normalization of a valid finite root by a finite nonzero scale. -/
@[simp] theorem normalize_finite (scale radicand : Rat) (hscale : scale ≠ 0)
    (hrad : 0 ≤ radicand) :
    normalize (.finite scale) (.finite radicand) =
      ⟨decide (scale < 0), .finite (radicand / (scale * scale))⟩ := by
  simp [normalize, not_lt.mpr hrad, hscale]

/-- The exact normalized root denotes `sqrt(q) / s`, including negative scales. -/
theorem normalize_finite_real (scale radicand : Rat) (hscale : scale ≠ 0)
    (hrad : 0 ≤ radicand) :
    (if scale < 0 then (-1 : Real) else 1) *
      Real.sqrt ((radicand / (scale * scale) : Rat) : Real) =
        Real.sqrt (radicand : Real) / (scale : Real) := by
  have hq : (0 : Real) ≤ radicand := by exact_mod_cast hrad
  push_cast
  rw [Real.sqrt_div hq, Real.sqrt_mul_self_eq_abs]
  by_cases hnegative : scale < 0
  · have hsneg : (scale : Real) < 0 := by exact_mod_cast hnegative
    simp [hnegative, abs_of_neg hsneg, div_neg]
  · have hspos : (0 : Real) < scale := by
      exact_mod_cast (lt_of_le_of_ne (not_lt.mp hnegative) (Ne.symm hscale))
    simp [hnegative, abs_of_pos hspos]

/-- Reference signed-root rounding uses the actual real square root and exact thresholds. -/
noncomputable def roundedReal (format : Format) (mode : RoundingMode) (root : BlockRoot) :
    NumericalValue Numerics.Dyadic :=
  applySign root.negative (match root.radicand with
    | .exceptional _ | .infinity true => .exceptional .nan
    | .infinity false => .infinity false
    | .finite value =>
        if value < 0 then .exceptional .nan
        else .finite (Arithmetic.roundSqrtRealToPrecision format
          (magnitudeMode root.negative mode) value))

/-- Executable signed-root rounding agrees with the real-root reference for every policy. -/
theorem rounded_eq_real (format : Format) (mode : RoundingMode) (root : BlockRoot) :
    rounded format mode root = roundedReal format mode root := by
  cases hrad : root.radicand with
  | finite value =>
      simp [rounded, roundedReal, Arithmetic.sqrtRounded, hrad,
        Arithmetic.roundSqrtRatToPrecision_eq_real]
  | infinity negative =>
      cases negative <;> simp [rounded, roundedReal, Arithmetic.sqrtRounded, hrad]
  | exceptional _ => simp [rounded, roundedReal, Arithmetic.sqrtRounded, hrad]

private theorem fitsPrecisionGrid_neg (format : Format) (value : Numerics.Dyadic)
    (hgrid : format.FitsPrecisionGrid value) : format.FitsPrecisionGrid value.neg := by
  simpa [Format.FitsPrecisionGrid, Numerics.Dyadic.neg] using hgrid

/-- Signed-root precision rounding always lands on the destination's precision grid. -/
theorem rounded_fitsPrecisionGrid (format : Format) (mode : RoundingMode) (root : BlockRoot) :
    match rounded format mode root with
    | .finite value => format.FitsPrecisionGrid value
    | _ => True := by
  cases hrad : root.radicand with
  | finite radicand =>
      by_cases hnegative : radicand < 0
      · simp [rounded, Arithmetic.sqrtRounded, hrad, hnegative, applySign]
      · have hgrid := Arithmetic.roundSqrtRatToPrecision_fitsPrecisionGrid format
          (magnitudeMode root.negative mode) radicand
        cases hsign : root.negative
        · simpa [rounded, Arithmetic.sqrtRounded, hrad, hnegative, applySign, hsign] using hgrid
        · simpa [rounded, Arithmetic.sqrtRounded, hrad, hnegative, applySign, hsign] using
            fitsPrecisionGrid_neg format _ hgrid
  | infinity negative => cases negative <;> simp [rounded, Arithmetic.sqrtRounded, hrad, applySign]
  | exceptional _ => simp [rounded, Arithmetic.sqrtRounded, hrad, applySign]

/-- Final P3109 encoding preserves the root's single rounded and saturated result. -/
theorem decode_project (format : Format) (policy : ProjectionPolicy) (root : BlockRoot) :
    Format.SameDatum (ExecFloat.P3109.decode (project format policy root))
      (value format policy root) := by
  change Format.SameDatum (format.decode (BitVec.ofNat format.bitWidth
    (Format.Internal.encodeDatumNat format (value format policy root)))) _
  exact format.sameDatum_decode_encodeSaturate policy.saturation policy.rounding _
    (rounded_fitsPrecisionGrid format policy.rounding root)

end BlockRoot
end FloatLib.Floats.Formats.P3109
