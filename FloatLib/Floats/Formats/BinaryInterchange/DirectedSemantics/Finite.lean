/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Floats.ExecFloat.Backends.Dispatch.Sqrt.Proof
import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Model.ERealSemantics

/-!
# Finite-operand helpers for directed arithmetic

Finite-operand classification facts support the format-generic directed arithmetic proofs.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-- Unary NaN selection is inactive for a finite operand. -/
theorem chooseNaN1_none_of_isFinite
    {fmt : FloatFormat} (x : Model fmt) (hx : isFinite x = true) :
    chooseNaN1 x = none := by
  simp [chooseNaN1, isNaN_eq_false_of_isFinite_eq_true x hx]

/-- NaN selection is inactive when both operands are finite. -/
theorem chooseNaN2_none_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    chooseNaN2 x y = none :=
  chooseNaN2_none_of_not_isNaN x y
    (isNaN_eq_false_of_isFinite_eq_true x hx)
    (isNaN_eq_false_of_isFinite_eq_true y hy)

/-- A finite nonzero value decodes to a dyadic with nonzero significand. -/
theorem significand_ne_zero_of_toDyadic?_some_of_isZero_eq_false
    {fmt : FloatFormat} {x : Model fmt} {d : Numerics.Dyadic}
    (hd : toDyadic? x = some d) (hzero : isZero x = false) :
    d.significand ≠ 0 := by
  intro hmant
  have := isZero_eq_true_of_toDyadic?_some_of_mant_eq_zero hd hmant
  simp [hzero] at this

/-! ## Exact intermediates of finite operands -/

/-- The exact dyadic sum of two finite values denotes their real sum. -/
theorem toReal_addDyadic_of_toDyadic?_some
    {fmt : FloatFormat} {x y : Model fmt} {dx dy : Numerics.Dyadic}
    (hdx : toDyadic? x = some dx) (hdy : toDyadic? y = some dy) :
    (addDyadic dx dy).toReal = toReal x + toReal y := by
  rw [Dyadic.toReal_addDyadic]
  simp [toReal_eq, hdx, hdy]

/-- The exact dyadic product of two finite values denotes their real product. -/
theorem toReal_mulDyadic_of_toDyadic?_some
    {fmt : FloatFormat} {x y : Model fmt} {dx dy : Numerics.Dyadic}
    (hdx : toDyadic? x = some dx) (hdy : toDyadic? y = some dy) :
    ({ negative := Bool.xor dx.negative dy.negative
       significand := dx.significand * dy.significand
       exponent := dx.exponent + dy.exponent } : Numerics.Dyadic).toReal =
      toReal x * toReal y := by
  rw [Dyadic.toReal_mul]
  simp [toReal_eq, hdx, hdy]

/-! ## Signed zero of an exactly cancelling sum -/

/-- The signed zero chosen for an exactly cancelling sum denotes zero. -/
@[simp] theorem toReal_zeroForExactSum
    (fmt : FloatFormat) (mode : IEEERoundingMode) (leftSign rightSign : Bool) :
    toReal (zeroForExactSum fmt mode leftSign rightSign) = 0 := by
  cases mode <;> simp [zeroForExactSum]

/-- The signed zero chosen for an exactly cancelling sum is not a NaN. -/
@[simp] theorem isNaN_zeroForExactSum_eq_false
    (fmt : FloatFormat) (mode : IEEERoundingMode) (leftSign rightSign : Bool) :
    isNaN (zeroForExactSum fmt mode leftSign rightSign) = false := by
  cases mode <;> simp [zeroForExactSum]

/-- The signed zero chosen for an exactly cancelling sum denotes zero in the extended reals. -/
@[simp] theorem toEReal_zeroForExactSum
    (fmt : FloatFormat) (mode : IEEERoundingMode) (leftSign rightSign : Bool) :
    toEReal (zeroForExactSum fmt mode leftSign rightSign) = 0 := by
  cases mode <;> simp [zeroForExactSum]

/-! ## Directed operations on finite operands

For modes other than nearest-even, finite addition and multiplication reduce to rounding an exact
dyadic intermediate, and finite division with a nonzero divisor rounds an exact scaled rational.
Exact cancellation has its own signed-zero rule. Square root in a directed mode instead rounds
the appropriate endpoint of a dyadic bracket around the exact root, and both nearest modes use the
nearest-even `sqrt`. These characterisations are shared by the enclosure, non-NaN, and
finite-format proofs.
-/

/--
For finite operands, a directed addition is the directed rounding of the exact dyadic sum, or the
rounding direction's signed zero when the sum cancels exactly.
-/
theorem add_eq_of_toDyadic?_some
    {fmt : FloatFormat} (mode : IEEERoundingMode) (hmode : mode ≠ .nearest)
    {x y : Model fmt} {dx dy : Numerics.Dyadic}
    (hdx : toDyadic? x = some dx) (hdy : toDyadic? y = some dy) :
    add x y (mode := mode) =
      if (addDyadic dx dy).significand = 0 then
        zeroForExactSum fmt mode dx.negative dy.negative
      else
        Internal.Directed.roundDyadic fmt mode (addDyadic dx dy) := by
  have hx := isFinite_eq_true_of_toDyadic?_some hdx
  have hy := isFinite_eq_true_of_toDyadic?_some hdy
  have hchoose := chooseNaN2_none_of_isFinite x y hx hy
  have hxInf := isInf_eq_false_of_isFinite_eq_true x hx
  have hyInf := isInf_eq_false_of_isFinite_eq_true y hy
  cases mode <;> first
    | exact absurd rfl hmode
    | simp [add, Internal.Directed.add, hchoose, hxInf, hyInf, hdx, hdy]

/-- For finite operands, a directed multiplication rounds the exact dyadic product. -/
theorem mul_eq_of_toDyadic?_some
    {fmt : FloatFormat} (mode : IEEERoundingMode) (hmode : mode ≠ .nearest)
    {x y : Model fmt} {dx dy : Numerics.Dyadic}
    (hdx : toDyadic? x = some dx) (hdy : toDyadic? y = some dy) :
    mul x y (mode := mode) =
      Internal.Directed.roundDyadic fmt mode
        { negative := Bool.xor dx.negative dy.negative
          significand := dx.significand * dy.significand
          exponent := dx.exponent + dy.exponent } := by
  have hx := isFinite_eq_true_of_toDyadic?_some hdx
  have hy := isFinite_eq_true_of_toDyadic?_some hdy
  have hchoose := chooseNaN2_none_of_isFinite x y hx hy
  have hxInf := isInf_eq_false_of_isFinite_eq_true x hx
  have hyInf := isInf_eq_false_of_isFinite_eq_true y hy
  cases mode <;> first
    | exact absurd rfl hmode
    | simp [mul, Internal.Directed.mul, hchoose, hxInf, hyInf, hdx, hdy]

/--
For a finite dividend and a finite nonzero divisor, a directed division rounds the exact scaled
rational quotient.
-/
theorem div_eq_of_toDyadic?_some
    {fmt : FloatFormat} (mode : IEEERoundingMode) (hmode : mode ≠ .nearest)
    {x y : Model fmt} {dx dy : Numerics.Dyadic}
    (hdx : toDyadic? x = some dx) (hdy : toDyadic? y = some dy)
    (hy0 : isZero y = false) :
    div x y (mode := mode) =
      Internal.Directed.roundRatScaled fmt mode (Bool.xor dx.negative dy.negative)
        dx.significand dy.significand (dx.exponent - dy.exponent) := by
  have hx := isFinite_eq_true_of_toDyadic?_some hdx
  have hy := isFinite_eq_true_of_toDyadic?_some hdy
  have hchoose := chooseNaN2_none_of_isFinite x y hx hy
  have hxInf := isInf_eq_false_of_isFinite_eq_true x hx
  have hyInf := isInf_eq_false_of_isFinite_eq_true y hy
  have hdyMant := significand_ne_zero_of_toDyadic?_some_of_isZero_eq_false hdy hy0
  by_cases hdxMant : dx.significand = 0
  · cases mode <;> first
      | exact absurd rfl hmode
      | simp [div, Internal.Directed.div, hchoose, hxInf, hyInf, hy0, hdx, hdy, hdxMant, hdyMant,
          Internal.Directed.roundRatScaled, roundRatMagnitudeDirectedScaled,
            roundRatNearestAwayScaled,
          rationalIsGridTieScaled, roundRatScaled_num_zero fmt _ _ _ hdyMant]
  · cases mode <;> first
      | exact absurd rfl hmode
      | simp [div, Internal.Directed.div, hchoose, hxInf, hyInf, hy0, hdx, hdy, hdxMant]

/--
Square root fixes a finite zero of either sign in every rounding direction, for every descriptor.
-/
theorem sqrt_of_isZero {fmt : FloatFormat} {mode : IEEERoundingMode} {x : Model fmt}
    (hfinite : isFinite x = true) (hzero : isZero x = true) :
    sqrt x (mode := mode) = x := by
  have hchoose := chooseNaN1_none_of_isFinite x hfinite
  have hinf := isInf_eq_false_of_isFinite_eq_true x hfinite
  cases mode
  case nearest | nearestAway =>
    change Internal.Nearest.sqrt x = x
    rw [show Internal.Nearest.sqrt x = Spec.sqrt x from SqrtBackend.dispatch_eq_spec x]
    simp [Spec.sqrt, hchoose, hinf, hzero]
  all_goals simp [sqrt, Internal.Directed.sqrt, hchoose, hinf, hzero]

/-- On a finite positive operand, downward square root rounds the lower bracket downward. -/
theorem sqrt_down_eq_roundDyadicDown_of_toDyadic?_some
    {fmt : FloatFormat} {x : Model fmt} {d : Numerics.Dyadic}
    (hd : toDyadic? x = some d) (hsign : signBit x = false) (hzero : isZero x = false) :
    sqrt x (mode := .down) = roundDyadicDown fmt (sqrtDyadicBracket fmt d).lower := by
  have hfinite := isFinite_eq_true_of_toDyadic?_some hd
  simp [sqrt, Internal.Directed.sqrt, chooseNaN1_none_of_isFinite x hfinite,
    isInf_eq_false_of_isFinite_eq_true x hfinite, hzero, hsign, hd]

/-- On a finite positive operand, upward square root rounds the upper bracket upward. -/
theorem sqrt_up_eq_roundDyadicUp_of_toDyadic?_some
    {fmt : FloatFormat} {x : Model fmt} {d : Numerics.Dyadic}
    (hd : toDyadic? x = some d) (hsign : signBit x = false) (hzero : isZero x = false) :
    sqrt x (mode := .up) = roundDyadicUp fmt (sqrtDyadicBracket fmt d).upper := by
  have hfinite := isFinite_eq_true_of_toDyadic?_some hd
  simp [sqrt, Internal.Directed.sqrt, chooseNaN1_none_of_isFinite x hfinite,
    isInf_eq_false_of_isFinite_eq_true x hfinite, hzero, hsign, hd]

end Model
end FloatLib.Floats.Formats.BinaryInterchange
