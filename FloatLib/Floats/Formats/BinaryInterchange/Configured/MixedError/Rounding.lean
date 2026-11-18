/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.MixedError.Attribute
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.Rational
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.MixedError
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Operations.Proof

/-!
# Local rounding of configured operations

FloatLib states each rounded configured operation together with the propagation of its operands'
errors. An error analysis that chooses the propagation rule itself needs the rounding alone, and
this module states it. For an IEEE descriptor, under the selected capability's specification
(`HasSpec`), a finite result has relative error `u` against the exact operation on the computed
operands. Sums and differences have no absolute part, while products, quotients and square roots
carry the underflow error. A quotient keeps a finite divisor and a square root a finite operand in
its domain.

Next to those local steps sit finiteness from a range condition on an enclosure of the exact
result, the finiteness of FloatLib's exact operations, which needs no range condition, and the
converse for sums, differences and products: a finite result has finite operands. A
finite conversion of a rational is its rounding. So C's `(float) n` of an integer or a natural
number has relative error `u`, and none when its magnitude is at most `2 ^ p`, with
`p = fracWidth + 1`.

A range condition bounds the enclosure `(1 + r) * |x₀| + a` of the exact operation on the
computed operands by the largest finite value. It is an inequality on inputs and budgets, never
the assumption that the result is finite.

A sum, a difference, a product or a fused multiply-add with a rounding attribute,
`add left right (mode := mode)` and the three others, has the unit roundoff of that attribute,
`Model.unitRoundoffIn format mode`, in each of the six attributes. A fused multiply-add with the
default attribute has its own rule too (`fma_rounding`). A directed rounding saturates on
overflow, so these rules ask that the exact result be within the largest finite magnitude and
not only that the result be finite.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [ExecFloat.ModelCodec plan (Model format) code]
    {x₀ r a : ℝ}

local notation "Value" =>
  ExecFloat.Binary format.expWidth format.fracWidth format.encoding format.exponentBias
    format.expWidth_ge_two format.fracWidth_pos format.exponentBias_pos
    format.exponentBias_le_maxFinite plan code

/-- An executable zero is finite and has real value zero. -/
private theorem isFinite_and_toReal_eq_zero_of_isZero {value : Value}
    (hzero : isZero value = true) : isFinite value = true ∧ toReal value = 0 :=
  ⟨Model.isFinite_eq_true_of_isZero_eq_true _ hzero, Model.toReal_eq_zero_of_isZero _ hzero⟩

section Rounding

variable [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]

/-- For an IEEE descriptor, a finite configured sum has relative error `u` against the exact sum of
its operands. -/
theorem add_rounding {left right : Value}
    [cap : ExecFloat.Add (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.add]
    (hresult : isFinite (left + right) = true) (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal (left + right)) (toReal left + toReal right)
      (Model.unitRoundoffAt format) 0 :=
  (mixedError_toReal_add hresult (.refl _) (.refl _)).mono le_rfl
    (by simp)

/-- For an IEEE descriptor, a finite configured difference has relative error `u` against the exact
difference. -/
theorem sub_rounding {left right : Value}
    [cap : ExecFloat.Sub (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.sub]
    (hresult : isFinite (left - right) = true) (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal (left - right)) (toReal left - toReal right)
      (Model.unitRoundoffAt format) 0 :=
  (mixedError_toReal_sub hresult (.refl _) (.refl _)).mono le_rfl
    (by simp)

/-- For an IEEE descriptor, a finite configured product has the mixed error of one rounding. -/
theorem mul_rounding {left right : Value}
    [cap : ExecFloat.Mul (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.mul]
    (hresult : isFinite (left * right) = true) (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal (left * right)) (toReal left * toReal right)
      (Model.unitRoundoffAt format) (Model.underflowErrorAt format) :=
  mixedError_toReal_of_eq_roundAt (toReal_mul_eq_roundAt hresult)

/-- For an IEEE descriptor, a finite configured fused multiply-add has the mixed error of one
rounding against the exact `left * right + addend`. -/
theorem fma_rounding {left right addend : Value}
    [cap : ExecFloat.Fma (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.fma]
    (hresult : isFinite (fma left right addend) = true)
    (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal (fma left right addend)) (toReal left * toReal right + toReal addend)
      (Model.unitRoundoffAt format) (Model.underflowErrorAt format) :=
  mixedError_toReal_of_eq_roundAt (toReal_fma_eq_roundAt hresult)

/-- For an IEEE descriptor, a finite configured quotient by a finite divisor has the mixed error of
one rounding. -/
theorem div_rounding {left right : Value}
    [cap : ExecFloat.Div (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.div]
    (hright : isFinite right = true) (hresult : isFinite (left / right) = true)
    (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal (left / right)) (toReal left / toReal right)
      (Model.unitRoundoffAt format) (Model.underflowErrorAt format) :=
  mixedError_toReal_of_eq_roundAt (toReal_div_eq_roundAt hright hresult)

/-- For an IEEE descriptor, the configured square root of a finite zero or positive value has the
mixed error of one rounding. -/
theorem sqrt_rounding {value : Value}
    [cap : ExecFloat.Sqrt (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.sqrt]
    (hvalue : isFinite value = true) (hdomain : isZero value = true ∨ signBit value = false)
    (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal (sqrt value)) (Real.sqrt (toReal value))
      (Model.unitRoundoffAt format) (Model.underflowErrorAt format) :=
  mixedError_toReal_of_eq_roundAt (toReal_sqrt_eq_roundAt hvalue hdomain)

/-- `sqrt_rounding` for the format-generic call `ExecFloat.sqrt`. -/
theorem execFloat_sqrt_rounding {value : Value}
    [cap : ExecFloat.Sqrt (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.sqrt]
    (hvalue : isFinite value = true) (hdomain : isZero value = true ∨ signBit value = false)
    (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal (ExecFloat.sqrt value)) (Real.sqrt (toReal value))
      (Model.unitRoundoffAt format) (Model.underflowErrorAt format) :=
  sqrt_rounding hvalue hdomain

/-- For an IEEE descriptor, finite operands whose exact sum has an enclosure at most the largest
finite value have a finite configured sum. -/
theorem isFinite_add_of_mixedError {left right : Value}
    [cap : ExecFloat.Add (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.add]
    (hleft : isFinite left = true) (hright : isFinite right = true)
    (bound : MixedError (toReal left + toReal right) x₀ r a)
    (range : (1 + r) * |x₀| + a ≤ Model.toReal (Model.posMaxFinite format))
    (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (left + right) = true := by
  unfold isFinite toReal at *
  rw [toModel_hAdd]
  exact Model.isFinite_add_of_abs_toReal_add_le_posMaxFinite _ _ hformat hleft hright
    (bound.abs_le.trans range)

/-- For an IEEE descriptor, finite operands whose exact difference has an enclosure at most the
largest finite value have a finite configured difference. -/
theorem isFinite_sub_of_mixedError {left right : Value}
    [cap : ExecFloat.Sub (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.sub]
    (hleft : isFinite left = true) (hright : isFinite right = true)
    (bound : MixedError (toReal left - toReal right) x₀ r a)
    (range : (1 + r) * |x₀| + a ≤ Model.toReal (Model.posMaxFinite format))
    (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (left - right) = true := by
  unfold isFinite toReal at *
  rw [toModel_hSub]
  exact Model.isFinite_sub_of_abs_toReal_sub_le_posMaxFinite _ _ hformat hleft hright
    (bound.abs_le.trans range)

/-- For an IEEE descriptor, finite operands whose exact product has an enclosure at most the largest
finite value have a finite configured product. -/
theorem isFinite_mul_of_mixedError {left right : Value}
    [cap : ExecFloat.Mul (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.mul]
    (hleft : isFinite left = true) (hright : isFinite right = true)
    (bound : MixedError (toReal left * toReal right) x₀ r a)
    (range : (1 + r) * |x₀| + a ≤ Model.toReal (Model.posMaxFinite format))
    (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (left * right) = true := by
  unfold isFinite toReal at *
  rw [toModel_hMul]
  refine Model.isFinite_mul_of_abs_mul_le_posMaxFinite _ _ hformat hleft hright ?_
  rw [← abs_mul]
  exact bound.abs_le.trans range

/-- For an IEEE descriptor, finite operands, the divisor nonzero, whose exact quotient has an
enclosure at most the largest finite value have a finite configured quotient. -/
theorem isFinite_div_of_mixedError {left right : Value}
    [cap : ExecFloat.Div (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.div]
    (hleft : isFinite left = true) (hright : isFinite right = true) (hzero : isZero right = false)
    (bound : MixedError (toReal left / toReal right) x₀ r a)
    (range : (1 + r) * |x₀| + a ≤ Model.toReal (Model.posMaxFinite format))
    (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (left / right) = true := by
  unfold isFinite isZero toReal at *
  rw [toModel_hDiv]
  exact Model.isFinite_div_of_abs_div_le_posMaxFinite _ _ hformat hleft hright hzero
    (bound.abs_le.trans range)

/-! ### Operations in a rounding attribute

`add left right (mode := mode)` rounds the exact sum once in the attribute `mode`. A directed
attribute saturates: a sum above the largest finite value rounds downward to that value, which is
finite and far from the exact sum. So each rule below asks that the exact result be within the
largest finite magnitude, which also makes the result finite.
-/

/-- For an IEEE descriptor and every rounding attribute, the configured sum of finite
operands whose exact sum is within the largest finite magnitude has the relative error of that
attribute against the exact sum, and no absolute part. -/
theorem add_rounding_mode {left right : Value} {mode : Model.IEEERoundingMode}
    [cap : ExecFloat.Add (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.add]
    (hleft : isFinite left = true) (hright : isFinite right = true)
    (hrange : |toReal left + toReal right| ≤ Model.toReal (Model.posMaxFinite format))
    (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal (add left right (mode := mode))) (toReal left + toReal right)
      (Model.unitRoundoffIn format mode) 0 := by
  unfold isFinite toReal at *
  rw [toModel_add]
  exact Model.add_rounding_mode hformat hleft hright hrange

/-- For an IEEE descriptor and every rounding attribute, the configured difference of
finite operands whose exact difference is within the largest finite magnitude has the relative
error of that attribute against the exact difference, and no absolute part. -/
theorem sub_rounding_mode {left right : Value} {mode : Model.IEEERoundingMode}
    [cap : ExecFloat.Sub (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.sub]
    (hleft : isFinite left = true) (hright : isFinite right = true)
    (hrange : |toReal left - toReal right| ≤ Model.toReal (Model.posMaxFinite format))
    (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal (sub left right (mode := mode))) (toReal left - toReal right)
      (Model.unitRoundoffIn format mode) 0 := by
  unfold isFinite toReal at *
  rw [toModel_sub]
  exact Model.sub_rounding_mode hformat hleft hright hrange

/-- For an IEEE descriptor and every rounding attribute, the configured product of
finite operands whose exact product is within the largest finite magnitude has the mixed error of
one rounding in that attribute. -/
theorem mul_rounding_mode {left right : Value} {mode : Model.IEEERoundingMode}
    [cap : ExecFloat.Mul (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.mul]
    (hleft : isFinite left = true) (hright : isFinite right = true)
    (hrange : |toReal left * toReal right| ≤ Model.toReal (Model.posMaxFinite format))
    (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal (mul left right (mode := mode))) (toReal left * toReal right)
      (Model.unitRoundoffIn format mode) (Model.underflowErrorIn format mode) := by
  unfold isFinite toReal at *
  rw [toModel_mul]
  exact Model.mul_rounding_mode hformat hleft hright hrange

/-- For an IEEE descriptor and every rounding attribute, the configured sum of finite
operands whose exact sum is within the largest finite magnitude is within the relative error of
that attribute of the exact sum. -/
theorem abs_toReal_add_sub_le_mode {left right : Value} {mode : Model.IEEERoundingMode}
    [cap : ExecFloat.Add (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.add]
    (hleft : isFinite left = true) (hright : isFinite right = true)
    (hrange : |toReal left + toReal right| ≤ Model.toReal (Model.posMaxFinite format))
    (hformat : format.isIEEE = true := by ieee_format) :
    |toReal (add left right (mode := mode)) - (toReal left + toReal right)| ≤
      Model.unitRoundoffIn format mode * |toReal left + toReal right| := by
  simpa using (add_rounding_mode hleft hright hrange hformat).bound

/-- For an IEEE descriptor and every rounding attribute, the configured difference of
finite operands whose exact difference is within the largest finite magnitude is within the
relative error of that attribute of the exact difference. -/
theorem abs_toReal_sub_sub_le_mode {left right : Value} {mode : Model.IEEERoundingMode}
    [cap : ExecFloat.Sub (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.sub]
    (hleft : isFinite left = true) (hright : isFinite right = true)
    (hrange : |toReal left - toReal right| ≤ Model.toReal (Model.posMaxFinite format))
    (hformat : format.isIEEE = true := by ieee_format) :
    |toReal (sub left right (mode := mode)) - (toReal left - toReal right)| ≤
      Model.unitRoundoffIn format mode * |toReal left - toReal right| := by
  simpa using (sub_rounding_mode hleft hright hrange hformat).bound

/-- For an IEEE descriptor and every rounding attribute, the configured product of
finite operands whose exact product is within the largest finite magnitude is within the relative
and the absolute error of that attribute of the exact product. -/
theorem abs_toReal_mul_sub_le_mode {left right : Value} {mode : Model.IEEERoundingMode}
    [cap : ExecFloat.Mul (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.mul]
    (hleft : isFinite left = true) (hright : isFinite right = true)
    (hrange : |toReal left * toReal right| ≤ Model.toReal (Model.posMaxFinite format))
    (hformat : format.isIEEE = true := by ieee_format) :
    |toReal (mul left right (mode := mode)) - toReal left * toReal right| ≤
      Model.unitRoundoffIn format mode * |toReal left * toReal right| +
        Model.underflowErrorIn format mode :=
  (mul_rounding_mode hleft hright hrange hformat).bound

/-- For an IEEE descriptor and every rounding attribute, the configured fused multiply-add of
finite operands whose exact `left * right + addend` is within the largest finite magnitude has
the mixed error of one rounding in that attribute. -/
theorem fma_rounding_mode {left right addend : Value} {mode : Model.IEEERoundingMode}
    [cap : ExecFloat.Fma (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.fma]
    (hleft : isFinite left = true) (hright : isFinite right = true)
    (haddend : isFinite addend = true)
    (hrange : |toReal left * toReal right + toReal addend| ≤
      Model.toReal (Model.posMaxFinite format))
    (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal (fma left right addend (mode := mode)))
      (toReal left * toReal right + toReal addend)
      (Model.unitRoundoffIn format mode) (Model.underflowErrorIn format mode) := by
  unfold isFinite toReal at *
  rw [toModel_fma]
  exact Model.fma_rounding_mode hformat hleft hright haddend hrange

/-- For an IEEE descriptor and every rounding attribute, the configured fused multiply-add of
finite operands whose exact `left * right + addend` is within the largest finite magnitude is
within the relative and the absolute error of that attribute of the exact value. -/
theorem abs_toReal_fma_sub_le_mode {left right addend : Value} {mode : Model.IEEERoundingMode}
    [cap : ExecFloat.Fma (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.fma]
    (hleft : isFinite left = true) (hright : isFinite right = true)
    (haddend : isFinite addend = true)
    (hrange : |toReal left * toReal right + toReal addend| ≤
      Model.toReal (Model.posMaxFinite format))
    (hformat : format.isIEEE = true := by ieee_format) :
    |toReal (fma left right addend (mode := mode)) -
        (toReal left * toReal right + toReal addend)| ≤
      Model.unitRoundoffIn format mode * |toReal left * toReal right + toReal addend| +
        Model.underflowErrorIn format mode :=
  (fma_rounding_mode hleft hright haddend hrange hformat).bound

/-- A sum, a difference or a product with the default attribute written out is the operation
that `+`, `-` or `*` runs. -/
theorem toReal_add_nearest {left right : Value}
    [ExecFloat.Add (Configured.Family format code plan)] :
    toReal (add left right (mode := .nearest)) = toReal (left + right) := rfl

@[inherit_doc toReal_add_nearest]
theorem toReal_sub_nearest {left right : Value}
    [ExecFloat.Sub (Configured.Family format code plan)] :
    toReal (sub left right (mode := .nearest)) = toReal (left - right) := rfl

@[inherit_doc toReal_add_nearest]
theorem toReal_mul_nearest {left right : Value}
    [ExecFloat.Mul (Configured.Family format code plan)] :
    toReal (mul left right (mode := .nearest)) = toReal (left * right) := rfl

/-- For an IEEE descriptor and every rounding attribute, finite operands whose exact sum
has an enclosure at most the largest finite value have a finite configured sum in that
attribute. -/
theorem isFinite_add_of_mixedError_mode {left right : Value} {mode : Model.IEEERoundingMode}
    [cap : ExecFloat.Add (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.add]
    (hleft : isFinite left = true) (hright : isFinite right = true)
    (bound : MixedError (toReal left + toReal right) x₀ r a)
    (range : (1 + r) * |x₀| + a ≤ Model.toReal (Model.posMaxFinite format))
    (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (add left right (mode := mode)) = true := by
  unfold isFinite toReal at *
  rw [toModel_add]
  exact (Model.add_finite_roundAt hformat hleft hright (bound.abs_le.trans range)).1

/-- For an IEEE descriptor and every rounding attribute, finite operands whose exact
difference has an enclosure at most the largest finite value have a finite configured difference
in that attribute. -/
theorem isFinite_sub_of_mixedError_mode {left right : Value} {mode : Model.IEEERoundingMode}
    [cap : ExecFloat.Sub (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.sub]
    (hleft : isFinite left = true) (hright : isFinite right = true)
    (bound : MixedError (toReal left - toReal right) x₀ r a)
    (range : (1 + r) * |x₀| + a ≤ Model.toReal (Model.posMaxFinite format))
    (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (sub left right (mode := mode)) = true := by
  unfold isFinite toReal at *
  rw [toModel_sub]
  exact (Model.sub_finite_roundAt hformat hleft hright (bound.abs_le.trans range)).1

/-- For an IEEE descriptor and every rounding attribute, finite operands whose exact
product has an enclosure at most the largest finite value have a finite configured product in
that attribute. -/
theorem isFinite_mul_of_mixedError_mode {left right : Value} {mode : Model.IEEERoundingMode}
    [cap : ExecFloat.Mul (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.mul]
    (hleft : isFinite left = true) (hright : isFinite right = true)
    (bound : MixedError (toReal left * toReal right) x₀ r a)
    (range : (1 + r) * |x₀| + a ≤ Model.toReal (Model.posMaxFinite format))
    (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (mul left right (mode := mode)) = true := by
  unfold isFinite toReal at *
  rw [toModel_mul]
  exact (Model.mul_finite_roundAt hformat hleft hright (bound.abs_le.trans range)).1

/-- For an IEEE descriptor and every rounding attribute, finite operands whose exact
`left * right + addend` has an enclosure at most the largest finite value have a finite configured
fused multiply-add in that attribute. -/
theorem isFinite_fma_of_mixedError_mode {left right addend : Value}
    {mode : Model.IEEERoundingMode}
    [cap : ExecFloat.Fma (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.fma]
    (hleft : isFinite left = true) (hright : isFinite right = true)
    (haddend : isFinite addend = true)
    (bound : MixedError (toReal left * toReal right + toReal addend) x₀ r a)
    (range : (1 + r) * |x₀| + a ≤ Model.toReal (Model.posMaxFinite format))
    (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (fma left right addend (mode := mode)) = true := by
  unfold isFinite toReal at *
  rw [toModel_fma]
  exact (Model.fma_finite_roundAt hformat hleft hright haddend (bound.abs_le.trans range)).1

/-! ### Exact operations

FloatLib's exact operations, such as `toReal_add_of_isZero_right`, give the real value of their
result. Under the same hypotheses, an IEEE descriptor and the zero, unit-magnitude or finiteness
facts each states, the result is finite, with no range condition. -/

/-- For an IEEE descriptor, a finite configured value minus itself is finite. -/
theorem isFinite_sub_self {left : Value}
    [cap : ExecFloat.Sub (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.sub]
    (hleft : isFinite left = true) (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (left - left) = true :=
  Model.Algebraic.isFinite_of_toRat?_eq_some (toRat?_sub_self hleft)

/-- A zero plus a finite configured value is finite. -/
theorem isFinite_add_of_isZero_left {left right : Value}
    [cap : ExecFloat.Add (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.add]
    (hleft : isZero left = true) (hright : isFinite right = true)
    (hformat : format.isIEEE = true := by ieee_format) : isFinite (left + right) = true := by
  obtain ⟨hfinite, hzero⟩ := isFinite_and_toReal_eq_zero_of_isZero hleft
  exact isFinite_add_of_mixedError hfinite hright (.refl _) (by
    simpa [hzero] using abs_toReal_le_posMaxFinite_of_isFinite hright)

/-- For an IEEE descriptor, a finite configured value plus a zero is finite. -/
theorem isFinite_add_of_isZero_right {left right : Value}
    [cap : ExecFloat.Add (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.add]
    (hleft : isFinite left = true) (hright : isZero right = true)
    (hformat : format.isIEEE = true := by ieee_format) : isFinite (left + right) = true := by
  obtain ⟨hfinite, hzero⟩ := isFinite_and_toReal_eq_zero_of_isZero hright
  exact isFinite_add_of_mixedError hleft hfinite (.refl _) (by
    simpa [hzero] using abs_toReal_le_posMaxFinite_of_isFinite hleft)

/-- A zero minus a finite configured value is finite. -/
theorem isFinite_sub_of_isZero_left {left right : Value}
    [cap : ExecFloat.Sub (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.sub]
    (hleft : isZero left = true) (hright : isFinite right = true)
    (hformat : format.isIEEE = true := by ieee_format) : isFinite (left - right) = true := by
  obtain ⟨hfinite, hzero⟩ := isFinite_and_toReal_eq_zero_of_isZero hleft
  exact isFinite_sub_of_mixedError hfinite hright (.refl _) (by
    simpa [hzero] using abs_toReal_le_posMaxFinite_of_isFinite hright)

/-- For an IEEE descriptor, a finite configured value minus a zero is finite. -/
theorem isFinite_sub_of_isZero_right {left right : Value}
    [cap : ExecFloat.Sub (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.sub]
    (hleft : isFinite left = true) (hright : isZero right = true)
    (hformat : format.isIEEE = true := by ieee_format) : isFinite (left - right) = true := by
  obtain ⟨hfinite, hzero⟩ := isFinite_and_toReal_eq_zero_of_isZero hright
  exact isFinite_sub_of_mixedError hleft hfinite (.refl _) (by
    simpa [hzero] using abs_toReal_le_posMaxFinite_of_isFinite hleft)

/-- A zero times a finite configured value is finite. -/
theorem isFinite_mul_of_isZero_left {left right : Value}
    [cap : ExecFloat.Mul (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.mul]
    (hleft : isZero left = true) (hright : isFinite right = true)
    (hformat : format.isIEEE = true := by ieee_format) : isFinite (left * right) = true := by
  obtain ⟨hfinite, hzero⟩ := isFinite_and_toReal_eq_zero_of_isZero hleft
  exact isFinite_mul_of_mixedError hfinite hright (.refl _) (by
    simpa [hzero] using Model.toReal_posMaxFinite_nonneg format)

/-- For an IEEE descriptor, a finite configured value times a zero is finite. -/
theorem isFinite_mul_of_isZero_right {left right : Value}
    [cap : ExecFloat.Mul (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.mul]
    (hleft : isFinite left = true) (hright : isZero right = true)
    (hformat : format.isIEEE = true := by ieee_format) : isFinite (left * right) = true := by
  obtain ⟨hfinite, hzero⟩ := isFinite_and_toReal_eq_zero_of_isZero hright
  exact isFinite_mul_of_mixedError hleft hfinite (.refl _) (by
    simpa [hzero] using Model.toReal_posMaxFinite_nonneg format)

/-- A configured value of magnitude one times a finite configured value is finite. -/
theorem isFinite_mul_of_abs_toReal_eq_one_left {left right : Value}
    [cap : ExecFloat.Mul (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.mul]
    (hleft : isFinite left = true) (hright : isFinite right = true) (hone : |toReal left| = 1)
    (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (left * right) = true :=
  isFinite_mul_of_mixedError hleft hright (.refl _) (by
    simpa [abs_mul, hone] using abs_toReal_le_posMaxFinite_of_isFinite hright)

/-- For an IEEE descriptor, a finite configured value times one of magnitude one is finite. -/
theorem isFinite_mul_of_abs_toReal_eq_one_right {left right : Value}
    [cap : ExecFloat.Mul (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.mul]
    (hleft : isFinite left = true) (hright : isFinite right = true) (hone : |toReal right| = 1)
    (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (left * right) = true :=
  isFinite_mul_of_mixedError hleft hright (.refl _) (by
    simpa [abs_mul, hone] using abs_toReal_le_posMaxFinite_of_isFinite hleft)

/-- For an IEEE descriptor, a finite configured value divided by one of magnitude one is finite. -/
theorem isFinite_div_of_abs_toReal_eq_one_right {left right : Value}
    [cap : ExecFloat.Div (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.div]
    (hleft : isFinite left = true) (hright : isFinite right = true) (hone : |toReal right| = 1)
    (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (left / right) = true := by
  have hzero : isZero right = false := Bool.eq_false_iff.mpr fun hzero => by
    simp [(isFinite_and_toReal_eq_zero_of_isZero hzero).2] at hone
  exact isFinite_div_of_mixedError hleft hright hzero (.refl _) (by
    simpa [abs_div, hone] using abs_toReal_le_posMaxFinite_of_isFinite hleft)

/-- For an IEEE descriptor, a finite configured sum has finite operands. -/
theorem isFinite_of_isFinite_add {left right : Value}
    [cap : ExecFloat.Add (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.add]
    (hresult : isFinite (left + right) = true) (hformat : format.isIEEE = true := by ieee_format) :
    isFinite left = true ∧ isFinite right = true := by
  unfold isFinite at *
  rw [toModel_hAdd] at hresult
  exact Model.isFinite_of_isFinite_add hformat hresult

/-- For an IEEE descriptor, a finite configured difference has finite operands. -/
theorem isFinite_of_isFinite_sub {left right : Value}
    [cap : ExecFloat.Sub (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.sub]
    (hresult : isFinite (left - right) = true) (hformat : format.isIEEE = true := by ieee_format) :
    isFinite left = true ∧ isFinite right = true := by
  unfold isFinite at *
  rw [toModel_hSub] at hresult
  exact Model.isFinite_of_isFinite_sub hformat hresult

/-- For an IEEE descriptor, a finite configured product has finite operands. -/
theorem isFinite_of_isFinite_mul {left right : Value}
    [cap : ExecFloat.Mul (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.mul]
    (hresult : isFinite (left * right) = true) (hformat : format.isIEEE = true := by ieee_format) :
    isFinite left = true ∧ isFinite right = true := by
  unfold isFinite at *
  rw [toModel_hMul] at hresult
  exact Model.isFinite_of_isFinite_mul hformat hresult

/-- For an IEEE descriptor, a finite configured quotient has a finite dividend. The divisor may
be an infinity. -/
theorem isFinite_left_of_isFinite_div {left right : Value}
    [cap : ExecFloat.Div (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.div]
    (hresult : isFinite (left / right) = true) (hformat : format.isIEEE = true := by ieee_format) :
    isFinite left = true := by
  unfold isFinite at *
  rw [toModel_hDiv] at hresult
  exact Model.isFinite_left_of_isFinite_div hformat hresult

end Rounding

/-- A scientific literal has a nonnegative real value. -/
theorem toReal_ofScientific_nonneg (mantissa : Nat) (exponentSign : Bool) (decimalExponent : Nat)
    (hformat : format.isIEEE = true := by ieee_format) :
    0 ≤ toReal (OfScientific.ofScientific mantissa exponentSign decimalExponent :
      ExecFloat (Configured.Family format code plan)) := by
  refine toReal_nonneg_of_isFinite_imp fun hfinite => ?_
  change Model.isFinite (Configured.Family.toModel (Configured.Family.ofModel
    (Model.ofRat format (OfScientific.ofScientific mantissa exponentSign decimalExponent : ℚ)))) =
      true at hfinite
  change 0 ≤ Model.toReal (Configured.Family.toModel (Configured.Family.ofModel
    (Model.ofRat format (OfScientific.ofScientific mantissa exponentSign decimalExponent : ℚ))))
  rw [Configured.Family.toModel_ofModel] at hfinite ⊢
  rw [Model.toReal_ofRat_eq_roundAt _ hformat hfinite]
  refine Model.roundAt_nonneg _ (Rat.cast_nonneg.mpr ?_)
  rw [← Rat.ofScientific_eq_ofScientific, Rat.ofScientific_def]
  split
  · rw [Rat.mkRat_eq_div]
    positivity
  · positivity

/-- A scientific literal no larger in magnitude than the largest finite value is finite. -/
theorem isFinite_ofScientific (mantissa : Nat) (exponentSign : Bool) (decimalExponent : Nat)
    (hrange : |((OfScientific.ofScientific mantissa exponentSign decimalExponent : ℚ) : ℝ)| ≤
      Model.toReal (Model.posMaxFinite format))
    (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (OfScientific.ofScientific mantissa exponentSign decimalExponent :
      ExecFloat (Configured.Family format code plan)) = true := by
  change Model.isFinite (Configured.Family.toModel (Configured.Family.ofModel
    (Model.ofRat format (OfScientific.ofScientific mantissa exponentSign decimalExponent : ℚ)))) =
      true
  rw [Configured.Family.toModel_ofModel]
  exact Model.isFinite_ofRat _ hformat hrange

/-- A rational no larger in magnitude than the largest finite value converts to a finite
configured value. -/
theorem isFinite_ofRat (q : ℚ) (hrange : |(q : ℝ)| ≤ Model.toReal (Model.posMaxFinite format))
    (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (ofRat q : Value) = true := by
  unfold isFinite
  rw [toModel_ofRat]
  exact Model.isFinite_ofRat q hformat hrange

/-- A finite conversion of a rational is its nearest-even rounding to the format. -/
theorem toReal_ofRat_eq_roundAt (q : ℚ) (hresult : isFinite (ofRat q : Value) = true)
    (hformat : format.isIEEE = true := by ieee_format) :
    toReal (ofRat q : Value) = Model.roundAt format (q : ℝ) := by
  have hfinite : Model.isFinite (Model.ofRat format q) = true := by
    simpa [isFinite] using hresult
  unfold toReal
  rw [toModel_ofRat, Model.toReal_ofRat_eq_roundAt _ hformat hfinite]

/-- A finite conversion of an integer, C's `(float) n`, has relative error `u` and no absolute
error: the integer is zero or at least the least positive normal magnitude. -/
theorem ofRat_intCast_rounding (n : ℤ) (hresult : isFinite (ofRat (n : ℚ) : Value) = true)
    (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal (ofRat (n : ℚ) : Value)) n (Model.unitRoundoffAt format) 0 := by
  rw [toReal_ofRat_eq_roundAt _ hresult, Rat.cast_intCast]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Int.cast_zero, Model.roundAt_zero]
    exact (MixedError.refl 0).mono (Model.unitRoundoffAt_pos format).le le_rfl
  · refine Model.mixedError_roundAt_of_minNormalAt_le format
      ((Model.minNormalAt_le_one format).trans ?_)
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hn

/-- A finite conversion of a natural number, C's `(float) n`, has relative error `u` and no
absolute error. -/
theorem ofRat_natCast_rounding (n : ℕ) (hresult : isFinite (ofRat (n : ℚ) : Value) = true)
    (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal (ofRat (n : ℚ) : Value)) n (Model.unitRoundoffAt format) 0 := by
  have h := ofRat_intCast_rounding (plan := plan) (code := code) (n : ℤ)
    (by simpa using hresult)
  simpa using h

/-- C's `(float) n` of an integer of magnitude at most `2 ^ p`, with `p = fracWidth + 1`, is
exact when it is finite. -/
theorem toReal_ofRat_intCast_of_abs_le (n : ℤ) (hresult : isFinite (ofRat (n : ℚ) : Value) = true)
    (hn : |(n : ℝ)| ≤ 2 ^ (format.fracWidth + 1))
    (hformat : format.isIEEE = true := by ieee_format) :
    toReal (ofRat (n : ℚ) : Value) = n := by
  rw [toReal_ofRat_eq_roundAt _ hresult, Rat.cast_intCast,
    Model.roundAt_intCast_of_abs_le format hn]

/-- C's `(float) n` of a natural number at most `2 ^ p`, with `p = fracWidth + 1`, is exact when
it is finite. -/
theorem toReal_ofRat_natCast_of_le (n : ℕ) (hresult : isFinite (ofRat (n : ℚ) : Value) = true)
    (hn : (n : ℝ) ≤ 2 ^ (format.fracWidth + 1)) (hformat : format.isIEEE = true := by ieee_format) :
    toReal (ofRat (n : ℚ) : Value) = n := by
  have h := toReal_ofRat_intCast_of_abs_le (plan := plan) (code := code) (n : ℤ)
    (by simpa using hresult) (by simpa using hn)
  simpa using h

/-- The integer of a finite value in `mode`, as a C cast computes it, is the real value of the
value's integral rounding in `mode`. -/
theorem cast_toInt?_getD {value : Value} {mode : Model.IEEERoundingMode} (default : Int)
    (hrange : (format.fracWidth : Int) ≤ format.maxNormalExponent) (hvalue : isFinite value = true)
    (hformat : format.isIEEE = true := by ieee_format) :
    (((toInt? value mode).getD default : Int) : ℝ) = toReal (roundToIntegral value mode) := by
  obtain ⟨exact, hd⟩ := Model.exists_toDyadic?_of_isFinite hvalue
  unfold toInt? toReal
  rw [hd, toModel_roundToIntegral, Model.toReal_roundToIntegral hformat hrange _ mode exact hd]
  rfl

/-- The maximum of finite configured values is finite. -/
theorem isFinite_max {left right : ExecFloat (Configured.Family format code plan)}
    (hleft : isFinite left = true) (hright : isFinite right = true) :
    isFinite (max left right) = true := by
  change Model.isFinite (toModel (max left right)) = true
  rw [toModel_max]
  exact Model.isFinite_maximum _ _ hleft hright

end FloatLib.Floats.ExecFloat.Binary
