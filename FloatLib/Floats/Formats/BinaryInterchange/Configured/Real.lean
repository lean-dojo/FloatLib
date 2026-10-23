/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.PowerProof
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.Error
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Rounding.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.Core
public import FloatLib.Floats.Formats.BinaryInterchange.Model.RealSemantics
import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Classification

/-!
# Real values of configured binary values

`toReal?` reads a configured binary value as the real number it denotes, through its proof model,
and returns `none` for NaNs and infinities, which have no real value. `toReal` is the total
version, which maps them to zero as `Model.toReal` does.

The theorems `toReal_add` through `toReal_sqrt` state the IEEE rounding contract on the configured
carrier: a finite result of `x + y`, `x - y`, `x * y`, `x / y`, or `sqrt x` is the nearest-even
rounding `Model.roundAt` of the exact real result. `abs_toReal_add_sub_le` and its siblings turn
that into an absolute error of at most half an ulp, `Model.epsilonAt format`. They need an IEEE
descriptor, finite operands, a finite result (square root always has one), a nonzero divisor for
division, a nonnegative operand for square root, and, like `toModel_hAdd`, the instance argument
that the selected capability computes the configured model operation. Instance search proves that
argument for every capability the library declares.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Floats.Formats.BinaryInterchange

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  ExecFloat.Binary format.expWidth format.fracWidth format.encoding format.exponentBias
    format.expWidth_ge_two format.fracWidth_pos format.exponentBias_pos
    format.exponentBias_le_maxFinite plan code

/-- Exact real value of a finite configured binary value, or `none` for a NaN or an infinity. -/
noncomputable def toReal? (value : Value) : Option ℝ :=
  Model.toReal? (toModel value)

/--
Real value of a configured binary value. A NaN or an infinity, which has no real value, gives
zero. Theorems about it carry finiteness hypotheses, and `toReal?` is the partial version.
-/
noncomputable def toReal (value : Value) : ℝ :=
  Model.toReal (toModel value)

/-- The optional real value is absent exactly for the values that are not finite. -/
@[simp, grind =] theorem toReal?_eq_none_iff (value : Value) :
    toReal? value = none ↔ isFinite value = false := by
  have hdecode := Model.toDyadic?_isSome_eq_isFinite (toModel value)
  unfold toReal? Model.toReal? isFinite
  cases hd : Model.toDyadic? (toModel value) <;> simp_all

/-- A value whose exact rational value is `q` has real value `q`. -/
theorem toReal_of_toRat?_eq_some {value : Value} {q : ℚ} (hvalue : toRat? value = some q) :
    toReal value = q :=
  Model.Algebraic.toReal_of_toRat?_eq_some hvalue

/-- A finite value's optional real value is its real value. -/
theorem toReal?_eq_some_toReal {value : Value} (hvalue : isFinite value = true) :
    toReal? value = some (toReal value) := by
  have hdecode := Model.toDyadic?_isSome_eq_isFinite (toModel value)
  unfold toReal? toReal Model.toReal Model.toReal? isFinite at *
  cases hd : Model.toDyadic? (toModel value) <;> simp_all

section Rounding

variable [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]

/-- A finite configured sum is the nearest-even rounding of the exact real sum. -/
theorem toReal_add {left right : Value}
    [cap : ExecFloat.Add (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.add]
    (hformat : format.isIEEE = true) (hleft : isFinite left = true)
    (hright : isFinite right = true) (hresult : isFinite (left + right) = true) :
    toReal (left + right) = Model.roundAt format (toReal left + toReal right) := by
  unfold toReal isFinite at *
  rw [toModel_hAdd] at hresult ⊢
  exact Model.toReal_add_eq_roundAt _ _ hformat hleft hright hresult

/-- A finite configured difference is the nearest-even rounding of the exact real difference. -/
theorem toReal_sub {left right : Value}
    [cap : ExecFloat.Sub (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.sub]
    (hformat : format.isIEEE = true) (hleft : isFinite left = true)
    (hright : isFinite right = true) (hresult : isFinite (left - right) = true) :
    toReal (left - right) = Model.roundAt format (toReal left - toReal right) := by
  unfold toReal isFinite at *
  rw [toModel_hSub] at hresult ⊢
  exact Model.toReal_sub_eq_roundAt _ _ hformat hleft hright hresult

/-- A finite configured product is the nearest-even rounding of the exact real product. -/
theorem toReal_mul {left right : Value}
    [cap : ExecFloat.Mul (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.mul]
    (hformat : format.isIEEE = true) (hleft : isFinite left = true)
    (hright : isFinite right = true) (hresult : isFinite (left * right) = true) :
    toReal (left * right) = Model.roundAt format (toReal left * toReal right) := by
  unfold toReal isFinite at *
  rw [toModel_hMul] at hresult ⊢
  exact Model.toReal_mul_eq_roundAt _ _ hformat hleft hright hresult

/--
A finite configured quotient by a nonzero divisor is the nearest-even rounding of the exact real
quotient.
-/
theorem toReal_div {left right : Value}
    [cap : ExecFloat.Div (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.div]
    (hformat : format.isIEEE = true) (hleft : isFinite left = true)
    (hright : isFinite right = true) (hzero : isZero right = false)
    (hresult : isFinite (left / right) = true) :
    toReal (left / right) = Model.roundAt format (toReal left / toReal right) := by
  unfold toReal isFinite isZero at *
  rw [toModel_hDiv] at hresult ⊢
  exact Model.toReal_div_eq_roundAt _ _ hformat hleft hright hzero hresult

/--
The configured square root of a finite zero or positive value is the nearest-even rounding of the
exact real square root. The result is always finite.
-/
theorem toReal_sqrt {value : Value}
    [cap : ExecFloat.Sqrt (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.sqrt]
    (hformat : format.isIEEE = true) (hvalue : isFinite value = true)
    (hdomain : isZero value = true ∨ signBit value = false) :
    toReal (sqrt value) = Model.roundAt format (Real.sqrt (toReal value)) := by
  unfold toReal isFinite isZero signBit at *
  rw [toModel_sqrt]
  exact Model.toReal_sqrt_eq_roundAt _ hformat hvalue hdomain

/-- A finite configured sum is within half an ulp of the exact real sum. -/
theorem abs_toReal_add_sub_le {left right : Value}
    [cap : ExecFloat.Add (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.add]
    (hformat : format.isIEEE = true) (hleft : isFinite left = true)
    (hright : isFinite right = true) (hresult : isFinite (left + right) = true) :
    |toReal (left + right) - (toReal left + toReal right)| ≤
      Model.epsilonAt format (toReal left + toReal right) := by
  rw [toReal_add hformat hleft hright hresult]
  exact Model.abs_roundAt_sub_le format _

/-- A finite configured difference is within half an ulp of the exact real difference. -/
theorem abs_toReal_sub_sub_le {left right : Value}
    [cap : ExecFloat.Sub (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.sub]
    (hformat : format.isIEEE = true) (hleft : isFinite left = true)
    (hright : isFinite right = true) (hresult : isFinite (left - right) = true) :
    |toReal (left - right) - (toReal left - toReal right)| ≤
      Model.epsilonAt format (toReal left - toReal right) := by
  rw [toReal_sub hformat hleft hright hresult]
  exact Model.abs_roundAt_sub_le format _

/-- A finite configured product is within half an ulp of the exact real product. -/
theorem abs_toReal_mul_sub_le {left right : Value}
    [cap : ExecFloat.Mul (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.mul]
    (hformat : format.isIEEE = true) (hleft : isFinite left = true)
    (hright : isFinite right = true) (hresult : isFinite (left * right) = true) :
    |toReal (left * right) - toReal left * toReal right| ≤
      Model.epsilonAt format (toReal left * toReal right) := by
  rw [toReal_mul hformat hleft hright hresult]
  exact Model.abs_roundAt_sub_le format _

/--
A finite configured quotient by a nonzero divisor is within half an ulp of the exact real
quotient.
-/
theorem abs_toReal_div_sub_le {left right : Value}
    [cap : ExecFloat.Div (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.div]
    (hformat : format.isIEEE = true) (hleft : isFinite left = true)
    (hright : isFinite right = true) (hzero : isZero right = false)
    (hresult : isFinite (left / right) = true) :
    |toReal (left / right) - toReal left / toReal right| ≤
      Model.epsilonAt format (toReal left / toReal right) := by
  rw [toReal_div hformat hleft hright hzero hresult]
  exact Model.abs_roundAt_sub_le format _

/--
The configured square root of a finite zero or positive value is within half an ulp of the exact
real square root.
-/
theorem abs_toReal_sqrt_sub_le {value : Value}
    [cap : ExecFloat.Sqrt (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.sqrt]
    (hformat : format.isIEEE = true) (hvalue : isFinite value = true)
    (hdomain : isZero value = true ∨ signBit value = false) :
    |toReal (sqrt value) - Real.sqrt (toReal value)| ≤
      Model.epsilonAt format (Real.sqrt (toReal value)) := by
  rw [toReal_sqrt hformat hvalue hdomain]
  exact Model.abs_roundAt_sub_le format _

end Rounding

end FloatLib.Floats.ExecFloat.Binary
