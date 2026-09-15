/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Conversion.Posit.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Conversion.Format.Proof
public import FloatLib.Floats.Formats.Posit.Rounding.Real
public import FloatLib.Floats.Formats.Posit.Semantics.Exact.Proof

/-!
# Posit and decimal conversion semantics

Decimal destinations inherit the shared projection's validity, error and directed
enclosure guarantees. Posit destinations equal the standard signed real-rounding
specification for every finite decimal input, including saturation and nonzero
underflow. No intermediate binary format is involved.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Conversion

open FloatLib.Floats.Formats

/-- A finite posit is converted by decimal projection of its exact rational value. -/
theorem fromPosit_eq_project {fmt : Posit.Format} (f : Format) (mode : RoundingMode)
    (x : Posit.Model fmt) {a : ℚ} (hx : Posit.Model.toRat? x = some a) :
    fromPosit f mode x = project f mode a 0 false := by
  simp [fromPosit, hx]

/-- Every posit conversion produces a valid destination datum. -/
theorem fromPosit_valid {fmt : Posit.Format} (f : Format) (mode : RoundingMode)
    (x : Posit.Model fmt) :
    (fromPosit f mode x).value.Valid f := by
  unfold fromPosit
  split
  · exact project_valid ..
  · change 0 < f.payloadBound
    exact f.payloadBound_pos

/-- Posit zero becomes positive decimal zero, with preferred quantum zero clamped
to the destination quantum range. -/
theorem fromPosit_zero_clamped (fmt : Posit.Format) (f : Format) (mode : RoundingMode) :
    fromPosit f mode (Posit.Model.zero fmt) =
      { value := .finite false 0 (max f.minQuantum (min 0 f.maxQuantum)) } := by
  simp [fromPosit, project_zero]

/-- When quantum zero is available, posit zero converts to positive decimal zero there. -/
@[simp] theorem fromPosit_zero (fmt : Posit.Format) (f : Format) [f.HasQuantumZero]
    (mode : RoundingMode) :
    fromPosit f mode (Posit.Model.zero fmt) = { value := .finite false 0 0 } := by
  simp [fromPosit_zero_clamped, min_eq_left f.maxQuantum_nonneg,
    max_eq_right f.minQuantum_nonpos]

/-- NaR becomes a quiet, zero-payload decimal NaN, with no IEEE exception raised. -/
@[simp] theorem fromPosit_nar (fmt : Posit.Format) (f : Format) (mode : RoundingMode) :
    fromPosit f mode (Posit.Model.nar fmt) = { value := .nan false false 0 } := by
  simp [fromPosit]

/-- A nonoverflowing nearest decimal conversion has at most half a grid unit of error. -/
theorem fromPosit_error_le_half {fmt : Posit.Format} (f : Format) (mode : RoundingMode)
    (hm : mode = .nearestEven ∨ mode = .nearestAway) (x : Posit.Model fmt)
    {a : ℚ} (hx : Posit.Model.toRat? x = some a)
    (hfinite : (fromPosit f mode x).status.overflow = false) :
    ∃ value, (fromPosit f mode x).value.toRat? = some value ∧
      |value - a| ≤ (10 : ℚ) ^ roundingQuantum f |a| / 2 := by
  rw [fromPosit_eq_project f mode x hx] at hfinite ⊢
  exact project_error_le_half f mode hm a 0 false hfinite

/-- In any rounding direction a nonoverflowing conversion changes the value by less
than one decimal grid unit. -/
theorem fromPosit_error_lt_one {fmt : Posit.Format} (f : Format) (mode : RoundingMode)
    (x : Posit.Model fmt) {a : ℚ} (hx : Posit.Model.toRat? x = some a)
    (hfinite : (fromPosit f mode x).status.overflow = false) :
    ∃ value, (fromPosit f mode x).value.toRat? = some value ∧
      |value - a| < (10 : ℚ) ^ roundingQuantum f |a| := by
  rw [fromPosit_eq_project f mode x hx] at hfinite ⊢
  exact project_error_lt_one f mode a 0 false hfinite

/-- Upward posit-to-decimal conversion encloses the exact posit value. -/
theorem le_fromPosit_towardPositive {fmt : Posit.Format} (f : Format)
    (x : Posit.Model fmt) {a : ℚ} (hx : Posit.Model.toRat? x = some a)
    (hfinite : (fromPosit f .towardPositive x).status.overflow = false) :
    ∃ value, (fromPosit f .towardPositive x).value.toRat? = some value ∧ a ≤ value := by
  rw [fromPosit_eq_project f .towardPositive x hx] at hfinite ⊢
  exact le_project_towardPositive f a 0 false hfinite

/-- Downward posit-to-decimal conversion encloses the exact posit value. -/
theorem fromPosit_towardNegative_le {fmt : Posit.Format} (f : Format)
    (x : Posit.Model fmt) {a : ℚ} (hx : Posit.Model.toRat? x = some a)
    (hfinite : (fromPosit f .towardNegative x).status.overflow = false) :
    ∃ value, (fromPosit f .towardNegative x).value.toRat? = some value ∧ value ≤ a := by
  rw [fromPosit_eq_project f .towardNegative x hx] at hfinite ⊢
  exact project_towardNegative_le f a 0 false hfinite

/-- Without overflow, inexact is exactly a changed rational value. -/
theorem fromPosit_inexact_iff {fmt : Posit.Format} (f : Format) (mode : RoundingMode)
    (x : Posit.Model fmt) {a value : ℚ} (hx : Posit.Model.toRat? x = some a)
    (hfinite : (fromPosit f mode x).status.overflow = false)
    (hout : (fromPosit f mode x).value.toRat? = some value) :
    (fromPosit f mode x).status.inexact = true ↔ value ≠ a := by
  rw [fromPosit_eq_project f mode x hx] at hfinite hout ⊢
  exact project_inexact_iff f mode a value 0 false hfinite hout

/-- Decimal underflow is precisely an inexact tiny input when overflow is absent. -/
theorem fromPosit_underflow_iff {fmt : Posit.Format} (f : Format) (mode : RoundingMode)
    (x : Posit.Model fmt) {a : ℚ} (hx : Posit.Model.toRat? x = some a)
    (hfinite : (fromPosit f mode x).status.overflow = false) :
    (fromPosit f mode x).status.underflow = true ↔
      |a| < f.minNormal ∧ (fromPosit f mode x).status.inexact = true := by
  rw [fromPosit_eq_project f mode x hx] at hfinite ⊢
  exact project_underflow_iff f mode a 0 false hfinite

/-- Decimal NaNs, whether signaling or quiet, convert to NaR. -/
@[simp] theorem toPosit_nan (fmt : Posit.Format) (s signaling : Bool) (p : Nat) :
    toPosit fmt (.nan s signaling p) = Posit.Model.nar fmt := rfl

/-- Either signed decimal infinity converts to NaR. -/
@[simp] theorem toPosit_infinity (fmt : Posit.Format) (s : Bool) :
    toPosit fmt (.infinity s) = Posit.Model.nar fmt := rfl

/-- Both decimal zero signs and every zero cohort convert to the unique posit zero. -/
@[simp] theorem toPosit_zero (fmt : Posit.Format) (s : Bool) (q : Int) :
    toPosit fmt (.finite s 0 q) = Posit.Model.zero fmt := by
  simp [toPosit, Datum.toRat?_eq]

/-- Every finite decimal datum has exact single-rounding posit semantics. This includes
range saturation and the standard nonzero-underflow rule without additional hypotheses. -/
theorem toPosit_eq_real (fmt : Posit.Format) (x : Datum) {a : ℚ}
    (hx : x.toRat? = some a) :
    toPosit fmt x = Posit.Model.RealRounding.round fmt (a : ℝ) := by
  simp only [toPosit, hx]
  exact (Posit.Model.RealRounding.round_ratCast fmt a).symm

/-- Changing a decimal cohort does not change its posit conversion. -/
theorem toPosit_eq_of_toRat?_eq (fmt : Posit.Format) {x y : Datum}
    (h : x.toRat? = y.toRat?) : toPosit fmt x = toPosit fmt y := by
  simp only [toPosit, h]

end FloatLib.Floats.Formats.DecimalInterchange.Conversion
