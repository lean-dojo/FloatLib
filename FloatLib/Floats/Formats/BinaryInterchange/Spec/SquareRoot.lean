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
For a positive finite conventional-IEEE value, the descriptor-aware square root agrees with the
established unpacked-model result used by the binary32 and binary64 refinements.
-/
theorem sqrt_eq_model
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true) (x : Model fmt)
    (hfinite : isFinite x = true) (hnonzero : isZero x = false)
    (hnonnegative : signBit x = false) :
    sqrt x =
      ofModel fmt
        (Float.Model.UnpackedFloat.sqrt (FloatFormat.toModel fmt) (toModel x)) := by
  obtain ⟨value, hdecode⟩ := exists_toDyadic?_of_isFinite hfinite
  have hsign : value.negative = false :=
    (sign_eq_signBit_of_toDyadic?_some hdecode).trans hnonnegative
  have hmantissa : value.significand ≠ 0 := by
    intro hzero
    have hzeroSource :=
      isZero_eq_true_of_toDyadic?_some_of_mant_eq_zero hdecode hzero
    rw [hnonzero] at hzeroSource
    contradiction
  have hbridge :=
    FiniteSqrt.sqrtPositiveDyadic_eq_model_of_ieee
      hfmt x value hdecode hsign hmantissa
  have hnan := isNaN_eq_false_of_isFinite_eq_true x hfinite
  have hinf := isInf_eq_false_of_isFinite_eq_true x hfinite
  simp [sqrt, chooseNaN1, hnan, hinf, hnonzero, hnonnegative,
    hdecode, hbridge]

end Model.Spec
end FloatLib.Floats.Formats.BinaryInterchange
