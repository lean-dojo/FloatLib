/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Arithmetic.External.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Exact
public import FloatLib.Floats.Formats.P3109.Projection.Rational.Semantics
public import FloatLib.Numerics.Exact.Dyadic.Order
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Precision and range of external P3109 results

The quotient floor is strictly below `2^P`; every report mode chooses it or its successor.
Consequently precision rounding produces an exact binary grid value, even at a carry. Saturation
then places each finite result in the external format's finite range. These two facts justify
using an ordinary binary encoder without introducing a second rounding error.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109.Arithmetic.External

open BinaryInterchange

/-- The external subnormal quantum is nonpositive. -/
theorem minSubnormalExponent_nonpos (format : FloatFormat) :
    format.minSubnormalExponent ≤ 0 := by
  have := format.exponentBias_pos
  simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
    Int.ofNat_eq_natCast]
  omega

/-- Grid sufficient for exact external encoding, allowing a carry to the next binade. -/
def FitsGrid (format : FloatFormat) (value : Numerics.Dyadic) : Prop :=
  value.significand ≤ 2 ^ (format.fracWidth + 1) ∧
    format.minSubnormalExponent ≤ value.exponent

/-- Every rounding mode, for every explicit stochastic word, lands on the external grid. -/
theorem roundFinite_fitsGrid (format : FloatFormat) (mode : P3109.RoundingMode) (exact : Rat) :
    FitsGrid format (roundFinite format mode exact) := by
  unfold roundFinite
  simp only [beq_iff_eq]
  split
  · exact ⟨by simp [Numerics.Dyadic.zero], minSubnormalExponent_nonpos format⟩
  next hzero =>
    have hlower := RationalRounding.quotientFloor_lt_precision (format.fracWidth + 1)
      format.minNormalExponent exact.num.natAbs exact.den hzero exact.den_nz
    simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one,
      sub_add_eq_sub_sub, sub_add_cancel] at hlower
    have hquantum :
        format.minSubnormalExponent ≤
          max (RationalBinary.floorLog2 exact.num.natAbs exact.den) format.minNormalExponent -
            Int.ofNat format.fracWidth := by
      exact sub_le_sub_right (le_max_right _ _) _
    split <;> split
    · exact ⟨by simp [Numerics.Dyadic.zero], minSubnormalExponent_nonpos format⟩
    · exact ⟨Nat.succ_le_of_lt hlower, hquantum⟩
    · exact ⟨by simp [Numerics.Dyadic.zero], minSubnormalExponent_nonpos format⟩
    · exact ⟨Nat.le_of_lt hlower, hquantum⟩

/-- Each finite external endpoint lies on the precision grid. -/
theorem endpoint_fitsGrid (format : FloatFormat) (negative : Bool) :
    FitsGrid format (endpoint format negative) := by
  refine ⟨Nat.sub_le _ _, ?_⟩
  exact sub_le_sub_right (Model.minNormalExponent_le_maxNormalExponent format) _

/-- The positive endpoint is exactly the existing binary model's largest finite dyadic. -/
theorem endpoint_eq_maxFiniteDyadic (format : FloatFormat) (hformat : format.isIEEE = true) :
    endpoint format false = Model.maxFiniteDyadic format := by
  have hencoding := FloatFormat.encoding_eq_ieee_of_isIEEE format hformat
  have hpow := Nat.two_pow_pos format.fracWidth
  simp [endpoint, Model.maxFiniteDyadic, FloatFormat.maxFiniteFracField, hencoding,
    FloatFormat.fracMaskNat, Model.pow2_eq_two_pow, pow_succ]
  omega

/-- The absolute endpoint value is the positive maximum, for either sign. -/
theorem abs_endpoint_toReal (format : FloatFormat) (hformat : format.isIEEE = true)
    (negative : Bool) :
    |(endpoint format negative).toReal| = Model.toReal (Model.posMaxFinite format) := by
  rw [← Model.Dyadic.toReal_maxFiniteDyadic, ← endpoint_eq_maxFiniteDyadic format hformat]
  have hp : 0 ≤ (endpoint format false).toReal := by
    unfold endpoint Numerics.Dyadic.toReal Numerics.Dyadic.signedSignificand
    simp only [Bool.false_eq_true, if_false]
    exact mul_nonneg (Nat.cast_nonneg _) (le_of_lt (Model.bpow_pos _))
  cases negative
  · exact abs_of_nonneg hp
  · have hneg : (endpoint format true).toReal = -(endpoint format false).toReal := by
      simp [endpoint, Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand]
      ring
    rw [hneg, abs_neg, abs_of_nonneg hp]

/-- Scalable comparison tests exactly the real-valued magnitude bound used by encoding. -/
theorem magnitude_bound_of_not_overflow (format : FloatFormat)
    (hformat : format.isIEEE = true) (value : Numerics.Dyadic)
    (h : (Numerics.Dyadic.Internal.compareScalable
      (endpoint format false) { value with negative := false } == .lt) = false) :
    |value.toReal| ≤ Model.toReal (Model.posMaxFinite format) := by
  rw [Numerics.Dyadic.Internal.compareScalable_eq_compare] at h
  have hrat : ({ value with negative := false } : Numerics.Dyadic).toRat ≤
      (endpoint format false).toRat := by
    apply le_of_not_gt
    intro hlt
    have hcmp := (Numerics.Dyadic.compare_eq_lt_iff _ _).2 hlt
    simp [hcmp] at h
  have hreal :
      ({ value with negative := false } : Numerics.Dyadic).toReal ≤
        (endpoint format false).toReal := by
    have hcast : (({ value with negative := false } : Numerics.Dyadic).toRat : Real) ≤
        ((endpoint format false).toRat : Real) := by exact_mod_cast hrat
    simpa only [Numerics.Dyadic.cast_toRat] using hcast
  have habs : ({ value with negative := false } : Numerics.Dyadic).toReal = |value.toReal| := by
    cases value with
    | mk negative significand exponent =>
      cases negative <;>
        simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, abs_mul]
  rw [habs, endpoint_eq_maxFiniteDyadic format hformat,
    Model.Dyadic.toReal_maxFiniteDyadic] at hreal
  exact hreal

/-- Saturation preserves the grid and bounds every finite result by the external endpoints. -/
theorem saturate_finite (format : FloatFormat) (hformat : format.isIEEE = true)
    (policy : ProjectionPolicy) (input : NumericalValue Numerics.Dyadic)
    (hgrid : ∀ value, input = .finite value → FitsGrid format value)
    (result : Numerics.Dyadic) (hresult : saturate format policy input = .finite result) :
    FitsGrid format result ∧ |result.toReal| ≤ Model.toReal (Model.posMaxFinite format) := by
  have hendpoint (negative : Bool) :
      FitsGrid format (endpoint format negative) ∧
        |(endpoint format negative).toReal| ≤ Model.toReal (Model.posMaxFinite format) :=
    ⟨endpoint_fitsGrid format negative, (abs_endpoint_toReal format hformat negative).le⟩
  cases input with
  | exceptional value => simp [saturate] at hresult
  | infinity negative =>
      simp only [saturate] at hresult
      split at hresult
      · cases hresult; exact hendpoint negative
      · cases hresult
  | finite value =>
      simp only [saturate] at hresult
      split at hresult
      next hoverflow =>
        cases hs : policy.saturation <;> cases hr : policy.rounding <;>
          cases hn : value.negative <;>
          simp [finiteOverflow, hs, hr, hn] at hresult <;>
          (subst result; exact hendpoint _)
      next hnot =>
        rw [← NumericalValue.finite.inj hresult]
        exact ⟨hgrid value rfl,
          magnitude_bound_of_not_overflow format hformat value (Bool.eq_false_iff.mpr hnot)⟩

end FloatLib.Floats.Formats.P3109.Arithmetic.External
