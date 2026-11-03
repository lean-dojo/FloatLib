/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Generic.Sqrt.Proof
import FloatLib.Floats.Formats.BinaryInterchange.Model.ERealSemantics

/-!
# Square-root specification

The reference operation is descriptor-aware for every validated `FloatFormat`. The model bridge
below is intentionally restricted to conventional IEEE descriptors.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.Spec

/-- Descriptor-aware square root rounded to nearest with ties to even. -/
@[inline] def sqrt {fmt : FloatFormat} (x : Model fmt) : Model fmt :=
  match chooseNaN1 x with
  | some nan => nan
  | none =>
      if isInf x then
        if signBit x then invalidResult fmt else nativeOverflow fmt false
      else if isZero x then
        x
      else if signBit x then
        invalidResult fmt
      else
        match toDyadic? x with
        | some value =>
            FiniteSqrt.sqrtPositiveDyadic fmt value.significand value.exponent
        | none => invalidResult fmt

/--
For a zero of either sign in a conventional-IEEE format, the descriptor-aware square root agrees
with the unpacked-model result: both return the zero unchanged, so `sqrt (-0) = -0`.
-/
theorem sqrt_eq_model_of_isZero
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true) (x : Model fmt)
    (hzero : isZero x = true) :
    sqrt x =
      ofModel fmt
        (Float.Model.UnpackedFloat.sqrt (FloatFormat.toModel fmt) (toModel x)) := by
  have hfinite := isFinite_eq_true_of_isZero_eq_true x hzero
  have hnan := isNaN_eq_false_of_isFinite_eq_true x hfinite
  have hinf := isInf_eq_false_of_isFinite_eq_true x hfinite
  have hencoding := ((FloatFormat.isIEEE_eq_true_iff fmt).mp hfmt).1
  have hfields : expField x = 0 ∧ fracField x = 0 := by
    simpa [isZero, hencoding, IEEE.isZero] using hzero
  have hmodel : toModel x = .zero (modelSign (signBit x)) := by
    apply toModel_eq_zero_of_ieeeToDyadic?_eq_some x (signBit x) 0
    simpa [toDyadic?, hfmt] using toDyadic?_eq_zero_of_isZero_eq_true x hzero
  simp only [sqrt, chooseNaN1, hnan, hinf, hzero, Bool.false_eq_true, ite_false, ite_true,
    hmodel]
  conv_lhs => rw [← ofFields_signBit_expField_fracField x, hfields.1, hfields.2]
  cases signBit x
  · rw [ofFields_false_zero_zero, posZero_eq_ofModel_zero]
    rfl
  · rw [ofFields_true_zero_zero, negZero_eq_ofModel_zero]
    rfl

/--
For a finite conventional-IEEE value with a clear sign bit, `+0` included, the descriptor-aware
square root agrees with the established unpacked-model result used by the binary32 and binary64
refinements. `sqrt_eq_model_of_isZero` covers `-0`.
-/
theorem sqrt_eq_model
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true) (x : Model fmt)
    (hfinite : isFinite x = true) (hnonnegative : signBit x = false) :
    sqrt x =
      ofModel fmt
        (Float.Model.UnpackedFloat.sqrt (FloatFormat.toModel fmt) (toModel x)) := by
  by_cases hzero : isZero x = true
  · exact sqrt_eq_model_of_isZero hfmt x hzero
  have hnan := isNaN_eq_false_of_isFinite_eq_true x hfinite
  have hinf := isInf_eq_false_of_isFinite_eq_true x hfinite
  have hnonzero : isZero x = false := Bool.eq_false_iff.mpr hzero
  obtain ⟨value, hdecode⟩ := exists_toDyadic?_of_isFinite hfinite
  have hsign : value.negative = false :=
    (sign_eq_signBit_of_toDyadic?_some hdecode).trans hnonnegative
  have hbridge :=
    FiniteSqrt.sqrtPositiveDyadic_eq_model_of_ieee
      hfmt x value hdecode hsign
  simp [sqrt, chooseNaN1, hnan, hinf, hnonzero, hnonnegative,
    hdecode, hbridge]

end Model.Spec
end FloatLib.Floats.Formats.BinaryInterchange
