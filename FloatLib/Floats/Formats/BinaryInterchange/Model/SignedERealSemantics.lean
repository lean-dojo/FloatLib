/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Model.ERealSemantics
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.SignedSemantics.Core

/-!
# Signed extended-real interpretation of binary models

Executable, policy-aware negation reverses the extended-real interpretation of every non-NaN
value. The result applies uniformly to finite values and infinities; only NaNs are excluded.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

noncomputable section

/-- Executable float negation distributes over a conditional choice. -/
theorem neg_ite {fmt : FloatFormat} {p : Prop} [Decidable p]
    (x y : Model fmt) :
    neg (if p then x else y) = if p then neg x else neg y := by
  by_cases hp : p <;> simp [hp]

/-- Negating any non-NaN executable float negates its extended-real interpretation. -/
theorem toEReal_neg_of_isNaN_eq_false
    {fmt : FloatFormat} (x : Model fmt) (hnan : isNaN x = false) :
    toEReal (neg x) = -toEReal x := by
  rw [toEReal_eq_ite (neg x), toEReal_eq_ite x]
  rw [isNaN_neg, hnan, isInf_neg]
  simp only [Bool.false_eq_true, ite_false]
  cases hinf : isInf x
  · have hfinite :
        isFinite x = true :=
      isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x hnan hinf
    rw [toReal_neg x hfinite]
    simp
  · have hzero := isZero_eq_false_of_isInf_eq_true x hinf
    rw [signBit_neg]
    simp [hnan, hzero]
    cases hsign : signBit x <;> simp

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
