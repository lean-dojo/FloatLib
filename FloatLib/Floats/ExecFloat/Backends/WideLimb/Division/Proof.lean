/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.WideLimb.Division.Runtime
public import FloatLib.Floats.ExecFloat.Backends.WideLimb.Core.Proof
public import FloatLib.Floats.ExecFloat.Backends.Generic.Kernel.Proof
public import FloatLib.Floats.ExecFloat.Backends.Generic.QuotientRound.GeneralProof
public import FloatLib.Floats.ExecFloat.Backends.Dispatch.Div.Proof

/-!
# Refinement of wide-limb division

The limb decoder supplies the exact significands and their relative scale. The format's common
scale offset cancels in division. Normal significands supply a proved comparison-based ratio
exponent; all other finite cases use the exact rational exponent directly.

The single-quotient rounder agrees with the reference in every IEEE rounding direction. Finite
zero operands follow the same invalid-operation and signed-overflow rules. For non-finite inputs,
division's value result is independent of the rounding direction.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb

open FloatLib.Numerics

variable {fmt : FloatFormat}

private theorem expWord_eq_zero_iff (x : Value fmt) :
    expWord x = 0 ↔ expField x = 0 := by
  rw [← UInt32.toNat_inj]
  rfl

private theorem expWord_eq_all_iff (h : fmt.expWidth ≤ 32) (x : Value fmt) :
    expWord x = expAllOnes fmt ↔ expField x = fmt.expAllOnesNat := by
  rw [← UInt32.toNat_inj, expAllOnes_toNat h]
  rfl

/-- The division significand is exactly the compact finite decoder's significand. -/
theorem divisionMantissa_eq (x : Value fmt) :
    divisionMantissa x =
      FiniteKernel.decodeMantissa fmt (expField x) (fraction x).toNat := by
  by_cases hx : expWord x = 0
  · have hexp := (expWord_eq_zero_iff x).mp hx
    simp [divisionMantissa, FiniteKernel.decodeMantissa, hx, hexp]
  · have hexp : expField x ≠ 0 := by simpa only [expWord_eq_zero_iff] using hx
    simp [divisionMantissa, hx, decodeMantissa_eq_normalMantissa x hexp]

/-- The fast normal comparison and the general subnormal path give the exact ratio exponent. -/
theorem divisionRatioExponent_eq (x y : Value fmt) :
    divisionRatioExponent x y (divisionMantissa x) (divisionMantissa y) =
      RationalBinary.floorLog2 (divisionMantissa x) (divisionMantissa y) := by
  unfold divisionRatioExponent
  split
  · rfl
  · rename_i hnormal
    simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hnormal
    simp only [divisionMantissa, hnormal.1, hnormal.2, beq_iff_eq, ite_false]
    exact (FiniteQuotientRound.floorLog2_eq_of_normal fmt.fracWidth _ _
      (normalMantissa_bounds x) (normalMantissa_bounds y)).symm

private theorem scale_eq_sub_one (exponent : Nat) :
    FiniteKernel.scale exponent = exponent - 1 := by
  by_cases h : exponent = 0 <;> simp [FiniteKernel.scale, h]

private theorem model_divWithRounding_of_finite (mode : IEEERoundingMode)
    {x y : Model fmt} {dx dy : Numerics.Dyadic}
    (hdx : toDyadic? x = some dx) (hdy : toDyadic? y = some dy) :
    Model.divWithRounding mode x y =
      let sign := Bool.xor dx.negative dy.negative
      if dy.significand == 0 then
        if dx.significand == 0 then invalidResult fmt else nativeOverflow fmt sign
      else if dx.significand == 0 then zero fmt sign
      else roundRatWithRoundingScaled fmt mode sign dx.significand dy.significand
        (dx.exponent - dy.exponent) := by
  have hxFinite := isFinite_eq_true_of_toDyadic?_some hdx
  have hyFinite := isFinite_eq_true_of_toDyadic?_some hdy
  have hchoose := (chooseNaN2_eq_none_iff x y).mpr
    ⟨isNaN_eq_false_of_isFinite_eq_true x hxFinite,
      isNaN_eq_false_of_isFinite_eq_true y hyFinite⟩
  have hxInf := isInf_eq_false_of_toDyadic?_some hdx
  have hyInf := isInf_eq_false_of_toDyadic?_some hdy
  have hxZero := isZero_eq_beq_zero_of_toDyadic?_some hdx
  have hyZero := isZero_eq_beq_zero_of_toDyadic?_some hdy
  have hxSign := sign_eq_signBit_of_toDyadic?_some hdx
  have hySign := sign_eq_signBit_of_toDyadic?_some hdy
  cases mode with
  | nearestEven =>
      simp [Model.divWithRounding, Model.div, DivBackend.word_eq_spec, Spec.div,
        hdx, hdy, roundRatWithRoundingScaled]
  | towardZero | towardPositiveInfinity | towardNegativeInfinity =>
      simp [Model.divWithRounding, hchoose, hxInf, hyInf, hxZero, hyZero, hdx, hdy,
        ← hxSign, ← hySign, Bool.xor]

/-- Every accepted finite quotient has the exact public result in the requested rounding mode. -/
theorem divFiniteWithRounding?_refines (h : Eligible fmt) (mode : IEEERoundingMode)
    (x y r : Value fmt) (hr : divFiniteWithRounding? fmt mode x y = some r) :
    toModel r = Model.divWithRounding mode (toModel x) (toModel y) := by
  unfold divFiniteWithRounding? at hr
  split at hr
  · cases hr
  · rename_i hfinite
    have hfields := hfinite
    simp only [Bool.or_eq_true, beq_iff_eq, not_or, expWord_eq_all_iff h.exp_le] at hfields
    let dx : FiniteKernel.Components := ⟨signBit x, expField x, divisionMantissa x⟩
    let dy : FiniteKernel.Components := ⟨signBit y, expField y, divisionMantissa y⟩
    have hxDecode : FiniteKernel.decode? (toModel x) = some dx := by
      dsimp only [dx]
      rw [divisionMantissa_eq]
      exact decode?_toModel x h.isIEEE h.exp_le hfields.1
    have hyDecode : FiniteKernel.decode? (toModel y) = some dy := by
      dsimp only [dy]
      rw [divisionMantissa_eq]
      exact decode?_toModel y h.isIEEE h.exp_le hfields.2
    have hdx : toDyadic? (toModel x) = some (dx.toDyadic fmt) := by
      rw [FiniteKernel.toDyadic_eq_decode, hxDecode]
      rfl
    have hdy : toDyadic? (toModel y) = some (dy.toDyadic fmt) := by
      rw [FiniteKernel.toDyadic_eq_decode, hyDecode]
      rfl
    rw [← Option.some.inj hr, toModel_ofModel, model_divWithRounding_of_finite mode hdx hdy]
    simp only [FiniteKernel.Components.toDyadic_negative, FiniteKernel.Components.toDyadic_mant]
    by_cases hyZero : divisionMantissa y = 0
    · simp [dx, dy, hyZero]
    by_cases hxZero : divisionMantissa x = 0
    · simp [dx, dy, hxZero, hyZero]
    · have hxMant : dx.mantissa ≠ 0 := hxZero
      have hyMant : dy.mantissa ≠ 0 := hyZero
      simp only [dx, dy, hxZero, hyZero, beq_iff_eq, ite_false]
      rw [FiniteQuotientRound.roundAtExponent_eq _ _ _ _ _ _ _ (divisionRatioExponent_eq x y)]
      congr 1
      rw [FiniteKernel.Components.toDyadic_exp_of_mantissa_ne_zero fmt dx hxMant,
        FiniteKernel.Components.toDyadic_exp_of_mantissa_ne_zero fmt dy hyMant,
        FiniteKernel.exponent_eq_scale, FiniteKernel.exponent_eq_scale,
        scale_eq_sub_one, scale_eq_sub_one]
      dsimp only [dx, dy, expField]
      omega

private theorem model_divWithRounding_eq_spec_of_nonfinite
    (mode : IEEERoundingMode) (x y : Model fmt)
    (hfinite : Model.isFinite x = false ∨ Model.isFinite y = false) :
    Model.divWithRounding mode x y = Spec.div x y := by
  have hspecial : Spec.div x y = Spec.divSpecial x y := by
    unfold Spec.div
    cases hdx : toDyadic? x with
    | none => rfl
    | some dx =>
        cases hdy : toDyadic? y with
        | none => rfl
        | some dy =>
            have hx := isFinite_eq_true_of_toDyadic?_some hdx
            have hy := isFinite_eq_true_of_toDyadic?_some hdy
            rcases hfinite with h | h <;> simp_all
  cases mode with
  | nearestEven =>
      exact DivBackend.word_eq_spec x y
  | towardZero | towardPositiveInfinity | towardNegativeInfinity =>
      rw [hspecial]
      cases hnan : chooseNaN2 x y with
      | some nan =>
          simp [Model.divWithRounding, Spec.divSpecial, hnan]
      | none =>
          have hnotNaN := (chooseNaN2_eq_none_iff x y).mp hnan
          by_cases hxInf : Model.isInf x = true
          · simp [Model.divWithRounding, Spec.divSpecial, hnan, hxInf]
          by_cases hyInf : Model.isInf y = true
          · simp [Model.divWithRounding, Spec.divSpecial, hnan, hxInf, hyInf]
          · have hx := isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x
              hnotNaN.1 (Bool.eq_false_of_not_eq_true hxInf)
            have hy := isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false y
              hnotNaN.2 (Bool.eq_false_of_not_eq_true hyInf)
            rcases hfinite with h | h <;> simp_all

/-- Total wide-limb division refines the public operation in every IEEE rounding direction. -/
theorem toModel_divWithRounding (h : Eligible fmt) (mode : IEEERoundingMode) (x y : Value fmt) :
    toModel (divWithRounding fmt mode x y) =
      Model.divWithRounding mode (toModel x) (toModel y) := by
  unfold divWithRounding
  cases hfast : divFiniteWithRounding? fmt mode x y with
  | some r => exact divFiniteWithRounding?_refines h mode x y r hfast
  | none =>
      rw [toModel_ofModel]
      apply (model_divWithRounding_eq_spec_of_nonfinite mode _ _ ?_).symm
      unfold divFiniteWithRounding? at hfast
      split at hfast
      · rename_i hspecial
        simp only [Bool.or_eq_true, beq_iff_eq, expWord_eq_all_iff h.exp_le] at hspecial
        rcases hspecial with hx | hy
        · left
          simp [isFinite_toModel x h.isIEEE h.exp_le, hx]
        · right
          simp [isFinite_toModel y h.isIEEE h.exp_le, hy]
      · cases hfast

/-- Configured nearest-even wide-limb division preserves `Spec.div` exactly. -/
theorem toModel_div (h : Eligible fmt) (x y : Value fmt) :
    toModel (div fmt x y) = Spec.div (toModel x) (toModel y) := by
  rw [div, toModel_divWithRounding h]
  exact DivBackend.word_eq_spec _ _

end FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb
