/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.MixedError
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Real
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Bounds

/-!
# Mixed error of configured binary arithmetic

This module states the theorems of `Analysis.MixedError` for configured binary values, with
`u = Model.unitRoundoffAt format` and `η = Model.underflowErrorAt format`: `+`, `-`, `*`, `/`,
fused multiply-add, square root, negation, `max`, `min`, casts, and left-to-right sums over a list
or with `Fin.foldl`, together with the exact results stated with `toRat?`. Each theorem decodes
its operands and applies the corresponding descriptor-model theorem, so the constants are the
same. As in `Configured.Real`, each theorem about a rounded operation asks, as an instance
argument, that the selected capability compute the configured model operation, and instance
search proves this for every capability the library declares.

A cast theorem applies to every finite configured value that decodes to `Model.cast` of a
configured value, such as `ofModel (Model.cast source format (toModel value))`.

A sum of values with nonnegative real values is nonnegative, finite or not, since a value that is
not finite has real value zero (`toReal_add_nonneg`). A finite left-to-right sum of such values
is at least each of them (`le_toReal_foldl_add`). A product keeps the weak sign of its exact
product (`toReal_mul_nonneg`, `toReal_mul_nonpos`), and a product of finite values is negative
when its exact product is in range and below `-η` (`toReal_mul_lt_zero`).
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Numerics
open FloatLib.Floats.Formats.BinaryInterchange

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  ExecFloat.Binary format.expWidth format.fracWidth format.encoding format.exponentBias
    format.expWidth_ge_two format.fracWidth_pos format.exponentBias_pos
    format.exponentBias_le_maxFinite plan code

variable {x₀ y₀ z₀ r a rx ax ry ay rz az m : ℝ}

/--
A configured value equal to the nearest-even rounding of `t` has the mixed error of rounding.
Applied to a correctly rounded function, this gives its implementation contract.
-/
theorem mixedError_toReal_of_eq_roundAt {value : Value} {t : ℝ}
    (h : toReal value = Model.roundAt format t) :
    MixedError (toReal value) t (Model.unitRoundoffAt format) (Model.underflowErrorAt format) :=
  Model.mixedError_toReal_of_eq_roundAt h

/-! ## Negation, `max` and `min` -/

/-- Configured negation of a finite value is exact and keeps its error. -/
theorem mixedError_toReal_neg {value : Value} (hvalue : isFinite value = true)
    (evalue : MixedError (toReal value) x₀ r a) :
    MixedError (toReal (-value)) (-x₀) r a := by
  unfold toReal isFinite at *
  rw [toModel_neg]
  exact Model.mixedError_toReal_neg hvalue evalue

/-- The configured `max` of finite values is exact and carries the larger operand error. -/
theorem mixedError_toReal_max {left right : Value} (hleft : isFinite left = true)
    (hright : isFinite right = true) (eleft : MixedError (toReal left) x₀ rx ax)
    (eright : MixedError (toReal right) y₀ ry ay) :
    MixedError (toReal (max left right)) (max x₀ y₀) 0
      (max (rx * |x₀| + ax) (ry * |y₀| + ay)) := by
  unfold toReal isFinite at *
  rw [toModel_max]
  exact Model.mixedError_toReal_maximum hleft hright eleft eright

/--
The configured `max` of finite values with nonnegative exact values has relative error `max rx ry`
and absolute error `max ax ay`.
-/
theorem mixedError_toReal_max_of_nonneg {left right : Value} (hleft : isFinite left = true)
    (hright : isFinite right = true) (eleft : MixedError (toReal left) x₀ rx ax)
    (eright : MixedError (toReal right) y₀ ry ay) (hx₀ : 0 ≤ x₀) (hy₀ : 0 ≤ y₀) :
    MixedError (toReal (max left right)) (max x₀ y₀) (max rx ry) (max ax ay) := by
  unfold toReal isFinite at *
  rw [toModel_max]
  exact Model.mixedError_toReal_maximum_of_nonneg hleft hright eleft eright hx₀ hy₀

/-- The configured `min` of finite values is exact and carries the larger operand error. -/
theorem mixedError_toReal_min {left right : Value} (hleft : isFinite left = true)
    (hright : isFinite right = true) (eleft : MixedError (toReal left) x₀ rx ax)
    (eright : MixedError (toReal right) y₀ ry ay) :
    MixedError (toReal (min left right)) (min x₀ y₀) 0
      (max (rx * |x₀| + ax) (ry * |y₀| + ay)) := by
  unfold toReal isFinite at *
  rw [toModel_min]
  exact Model.mixedError_toReal_minimum hleft hright eleft eright

/--
The configured `min` of finite values with nonpositive exact values has relative error `max rx ry`
and absolute error `max ax ay`.
-/
theorem mixedError_toReal_min_of_nonpos {left right : Value} (hleft : isFinite left = true)
    (hright : isFinite right = true) (eleft : MixedError (toReal left) x₀ rx ax)
    (eright : MixedError (toReal right) y₀ ry ay) (hx₀ : x₀ ≤ 0) (hy₀ : y₀ ≤ 0) :
    MixedError (toReal (min left right)) (min x₀ y₀) (max rx ry) (max ax ay) := by
  unfold toReal isFinite at *
  rw [toModel_min]
  exact Model.mixedError_toReal_minimum_of_nonpos hleft hright eleft eright hx₀ hy₀

/-! ## Conversion -/

section Conversion

variable {source : FloatFormat} {sourcePlan : Configured.StoragePlan source} {sourceCode : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec sourcePlan (Model source) sourceCode]

local notation "Source" =>
  ExecFloat.Binary source.expWidth source.fracWidth source.encoding source.exponentBias
    source.expWidth_ge_two source.fracWidth_pos source.exponentBias_pos
    source.exponentBias_le_maxFinite sourcePlan sourceCode

/--
A finite configured value that decodes to the cast of a configured value into an IEEE format has
relative error `(1 + u) * r + u` and absolute error `(1 + u) * a + η`, with
`u = Model.unitRoundoffAt format` and `η = Model.underflowErrorAt format`.
-/
theorem mixedError_toReal_of_toModel_eq_cast {value : Source} {result : Value}
    (hresult : isFinite result = true)
    (hcast : toModel result = Model.cast source format (toModel value))
    (evalue : MixedError (toReal value) x₀ r a) (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal result) x₀
      ((1 + Model.unitRoundoffAt format) * r + Model.unitRoundoffAt format)
      ((1 + Model.unitRoundoffAt format) * a + Model.underflowErrorAt format) := by
  unfold toReal isFinite at *
  rw [hcast] at hresult ⊢
  exact Model.mixedError_toReal_cast hformat hresult evalue

/--
A finite configured value that decodes to the cast of a configured value into an IEEE format whose
grid contains the source's, with at least the source's fraction width and a least subnormal
exponent no larger, is exact and keeps the error of its operand. The finite result is a premise:
a finer grid can still have a smaller finite range.
-/
theorem mixedError_toReal_of_toModel_eq_cast_of_gridExtension {value : Source} {result : Value}
    (hfrac : source.fracWidth ≤ format.fracWidth)
    (hmin : format.minSubnormalExponent ≤ source.minSubnormalExponent)
    (hresult : isFinite result = true)
    (hcast : toModel result = Model.cast source format (toModel value))
    (evalue : MixedError (toReal value) x₀ r a) (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal result) x₀ r a := by
  unfold toReal isFinite at *
  rw [hcast] at hresult ⊢
  exact Model.mixedError_toReal_cast_of_gridExtension hformat hfrac hmin hresult evalue

/--
A configured widening cast of a finite value, with the same exponent width, bias and encoding and
at least the source's fraction width, is exact and keeps the error of its operand.
-/
theorem mixedError_toReal_of_toModel_eq_cast_of_compatibleWidening {value : Source}
    {result : Value} (hexp : source.expWidth = format.expWidth)
    (hbias : source.exponentBias = format.exponentBias)
    (hencoding : source.encoding = format.encoding) (hfrac : source.fracWidth ≤ format.fracWidth)
    (hvalue : isFinite value = true)
    (hcast : toModel result = Model.cast source format (toModel value))
    (evalue : MixedError (toReal value) x₀ r a) :
    MixedError (toReal result) x₀ r a := by
  unfold toReal isFinite at *
  rw [hcast]
  exact Model.mixedError_toReal_cast_of_compatibleWidening hexp hbias hencoding hfrac hvalue
    evalue

end Conversion

/-- A value whose real value is nonnegative when it is finite has a nonnegative real value: a NaN
or an infinity has real value zero. -/
theorem toReal_nonneg_of_isFinite_imp {value : Value}
    (h : isFinite value = true → 0 ≤ toReal value) : 0 ≤ toReal value := by
  cases hfinite : isFinite value
  · unfold isFinite toReal at *
    rw [Model.toReal_eq_zero_of_isFinite_eq_false hfinite]
  · exact h hfinite

/-- A value whose real value is nonpositive when it is finite has a nonpositive real value. -/
theorem toReal_nonpos_of_isFinite_imp {value : Value}
    (h : isFinite value = true → toReal value ≤ 0) : toReal value ≤ 0 := by
  cases hfinite : isFinite value
  · unfold isFinite toReal at *
    rw [Model.toReal_eq_zero_of_isFinite_eq_false hfinite]
  · exact h hfinite

section Rounding

variable [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]

section Add

variable [cap : ExecFloat.Add (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.add]

/--
With `u = Model.unitRoundoffAt format`, a finite configured sum has relative error `u` and absolute
error `(1 + u) * (rx * |x₀| + ax + (ry * |y₀| + ay))`.
-/
theorem mixedError_toReal_add {left right : Value} (hresult : isFinite (left + right) = true)
    (eleft : MixedError (toReal left) x₀ rx ax) (eright : MixedError (toReal right) y₀ ry ay)
    (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal (left + right)) (x₀ + y₀) (Model.unitRoundoffAt format)
      ((1 + Model.unitRoundoffAt format) * (rx * |x₀| + ax + (ry * |y₀| + ay))) := by
  unfold toReal isFinite at *
  rw [toModel_hAdd] at hresult ⊢
  exact Model.mixedError_toReal_add hformat hresult eleft eright

/--
A finite configured sum of two values whose exact values have the same sign has relative error
`(1 + u) * max rx ry + u` and absolute error `(1 + u) * (ax + ay)`, with
`u = Model.unitRoundoffAt format`.
-/
theorem mixedError_toReal_add_of_mul_nonneg {left right : Value}
    (hresult : isFinite (left + right) = true) (eleft : MixedError (toReal left) x₀ rx ax)
    (eright : MixedError (toReal right) y₀ ry ay) (hsign : 0 ≤ x₀ * y₀)
    (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal (left + right)) (x₀ + y₀)
      ((1 + Model.unitRoundoffAt format) * max rx ry + Model.unitRoundoffAt format)
      ((1 + Model.unitRoundoffAt format) * (ax + ay)) := by
  unfold toReal isFinite at *
  rw [toModel_hAdd] at hresult ⊢
  exact Model.mixedError_toReal_add_of_mul_nonneg hformat hresult eleft eright hsign

/--
If the exact sum of two decoded configured values is the decoded value of some `result`, the
configured sum decodes to that exact sum.
-/
theorem toRat?_add_of_representable {left right result : Value} {p q : ℚ}
    (hleft : toRat? left = some p) (hright : toRat? right = some q)
    (hresult : toRat? result = some (p + q)) (hformat : format.isIEEE = true := by ieee_format) :
    toRat? (left + right) = some (p + q) := by
  unfold toRat? at *
  rw [toModel_hAdd]
  exact Model.toRat?_add_of_representable hformat hleft hright hresult

/-- Adding a configured value to one that decodes to zero is exact. -/
theorem toRat?_add_of_toRat?_eq_some_zero_left {left right : Value}
    {q : ℚ} (hleft : toRat? left = some 0) (hright : toRat? right = some q)
    (hformat : format.isIEEE = true := by ieee_format) : toRat? (left + right) = some q := by
  unfold toRat? at *
  rw [toModel_hAdd]
  exact Model.toRat?_add_of_toRat?_eq_some_zero_left hformat hleft hright

/-- Adding a configured value that decodes to zero is exact. -/
theorem toRat?_add_of_toRat?_eq_some_zero_right {left right : Value}
    {q : ℚ} (hleft : toRat? left = some q) (hright : toRat? right = some 0)
    (hformat : format.isIEEE = true := by ieee_format) : toRat? (left + right) = some q := by
  unfold toRat? at *
  rw [toModel_hAdd]
  exact Model.toRat?_add_of_toRat?_eq_some_zero_right hformat hleft hright

/-- A sum of values with nonnegative real values has a nonnegative real value. A sum that is not
finite has real value zero, so no finiteness is needed. -/
theorem toReal_add_nonneg {left right : Value} (hleft : 0 ≤ toReal left) (hright : 0 ≤ toReal right)
    (hformat : format.isIEEE = true := by ieee_format) :
    0 ≤ toReal (left + right) := by
  cases hresult : isFinite (left + right)
  · unfold isFinite toReal at *
    rw [Model.toReal_eq_zero_of_isFinite_eq_false hresult]
  · rw [toReal_add_eq_roundAt hresult]
    exact Model.roundAt_nonneg format (add_nonneg hleft hright)

/-- A sum of values with nonpositive real values has a nonpositive real value. -/
theorem toReal_add_nonpos {left right : Value} (hleft : toReal left ≤ 0) (hright : toReal right ≤ 0)
    (hformat : format.isIEEE = true := by ieee_format) :
    toReal (left + right) ≤ 0 := by
  cases hresult : isFinite (left + right)
  · unfold isFinite toReal at *
    rw [Model.toReal_eq_zero_of_isFinite_eq_false hresult]
  · rw [toReal_add_eq_roundAt hresult]
    exact Model.roundAt_nonpos format (add_nonpos hleft hright)

end Add

section Sub

variable [cap : ExecFloat.Sub (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.sub]

/--
With `u = Model.unitRoundoffAt format`, a finite configured difference has relative error `u` and
absolute error `(1 + u) * (rx * |x₀| + ax + (ry * |y₀| + ay))`.
-/
theorem mixedError_toReal_sub {left right : Value} (hresult : isFinite (left - right) = true)
    (eleft : MixedError (toReal left) x₀ rx ax) (eright : MixedError (toReal right) y₀ ry ay)
    (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal (left - right)) (x₀ - y₀) (Model.unitRoundoffAt format)
      ((1 + Model.unitRoundoffAt format) * (rx * |x₀| + ax + (ry * |y₀| + ay))) := by
  unfold toReal isFinite at *
  rw [toModel_hSub] at hresult ⊢
  exact Model.mixedError_toReal_sub hformat hresult eleft eright

/--
A finite configured difference of two values whose exact values have opposite signs has relative
error `(1 + u) * max rx ry + u` and absolute error `(1 + u) * (ax + ay)`, with
`u = Model.unitRoundoffAt format`.
-/
theorem mixedError_toReal_sub_of_mul_nonpos {left right : Value}
    (hresult : isFinite (left - right) = true) (eleft : MixedError (toReal left) x₀ rx ax)
    (eright : MixedError (toReal right) y₀ ry ay) (hsign : x₀ * y₀ ≤ 0)
    (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal (left - right)) (x₀ - y₀)
      ((1 + Model.unitRoundoffAt format) * max rx ry + Model.unitRoundoffAt format)
      ((1 + Model.unitRoundoffAt format) * (ax + ay)) := by
  unfold toReal isFinite at *
  rw [toModel_hSub] at hresult ⊢
  exact Model.mixedError_toReal_sub_of_mul_nonpos hformat hresult eleft eright hsign

/--
Subtraction of finite configured values of the same sign within a factor of two does not round:
the difference adds no rounding error and has the pure absolute bound
`rx * |x₀| + ax + (ry * |y₀| + ay)`.
-/
theorem mixedError_toReal_sub_of_sterbenz {left right : Value}
    (hleft : isFinite left = true) (hright : isFinite right = true)
    (eleft : MixedError (toReal left) x₀ rx ax) (eright : MixedError (toReal right) y₀ ry ay)
    (hsign : 0 ≤ toReal left * toReal right) (hlr : |toReal left| ≤ 2 * |toReal right|)
    (hrl : |toReal right| ≤ 2 * |toReal left|) (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal (left - right)) (x₀ - y₀) 0 (rx * |x₀| + ax + (ry * |y₀| + ay)) := by
  unfold toReal isFinite at *
  rw [toModel_hSub]
  exact Model.mixedError_toReal_sub_of_sterbenz hformat hleft hright eleft eright hsign hlr hrl

/-- Subtracting a finite configured value from itself is exactly zero, whatever its error. -/
theorem mixedError_toReal_sub_self {left : Value} (hleft : isFinite left = true)
    (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal (left - left)) (x₀ - x₀) 0 0 :=
  MixedError.of_eq (by rw [toReal_sub_self hleft, sub_self])

/-- Subtracting a finite configured value from itself gives a value that decodes to zero. -/
theorem toRat?_sub_self {left : Value} (hleft : isFinite left = true)
    (hformat : format.isIEEE = true := by ieee_format) : toRat? (left - left) = some 0 := by
  unfold toRat? isFinite at *
  rw [toModel_hSub]
  exact Model.toRat?_sub_self hformat hleft

/--
If the exact difference of two decoded configured values is the decoded value of some `result`,
the configured difference decodes to that exact difference.
-/
theorem toRat?_sub_of_representable {left right result : Value} {p q : ℚ}
    (hleft : toRat? left = some p) (hright : toRat? right = some q)
    (hresult : toRat? result = some (p - q)) (hformat : format.isIEEE = true := by ieee_format) :
    toRat? (left - right) = some (p - q) := by
  unfold toRat? at *
  rw [toModel_hSub]
  exact Model.toRat?_sub_of_representable hformat hleft hright hresult

end Sub

/--
A finite configured product has relative error `(1 + u) * (rx + ry + rx * ry) + u` and absolute
error `(1 + u) * ((1 + ry) * ax * |y₀| + (1 + rx) * ay * |x₀| + ax * ay) + η`, with
`u = Model.unitRoundoffAt format` and `η = Model.underflowErrorAt format`.
-/
theorem mixedError_toReal_mul {left right : Value}
    [cap : ExecFloat.Mul (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.mul]
    (hresult : isFinite (left * right) = true) (eleft : MixedError (toReal left) x₀ rx ax)
    (eright : MixedError (toReal right) y₀ ry ay)
    (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal (left * right)) (x₀ * y₀)
      ((1 + Model.unitRoundoffAt format) * (rx + ry + rx * ry) + Model.unitRoundoffAt format)
      ((1 + Model.unitRoundoffAt format) * ((1 + ry) * ax * |y₀| + (1 + rx) * ay * |x₀| +
        ax * ay) + Model.underflowErrorAt format) := by
  unfold toReal isFinite at *
  rw [toModel_hMul] at hresult ⊢
  exact Model.mixedError_toReal_mul hformat hresult eleft eright

section Mul

variable [cap : ExecFloat.Mul (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.mul]

/--
If the exact product of two decoded configured values is the decoded value of some `result`, the
configured product decodes to that exact product.
-/
theorem toRat?_mul_of_representable {left right result : Value} {p q : ℚ}
    (hleft : toRat? left = some p) (hright : toRat? right = some q)
    (hresult : toRat? result = some (p * q)) (hformat : format.isIEEE = true := by ieee_format) :
    toRat? (left * right) = some (p * q) := by
  unfold toRat? at *
  rw [toModel_hMul]
  exact Model.toRat?_mul_of_representable hformat hleft hright hresult

/-- The configured product of a value that decodes to zero and a finite value decodes to zero. -/
theorem toRat?_mul_of_toRat?_eq_some_zero_left {left right : Value}
    (hleft : toRat? left = some 0) (hright : isFinite right = true)
    (hformat : format.isIEEE = true := by ieee_format) : toRat? (left * right) = some 0 := by
  unfold toRat? isFinite at *
  rw [toModel_hMul]
  exact Model.toRat?_mul_of_toRat?_eq_some_zero_left hformat hleft hright

/-- The configured product of a finite value and a value that decodes to zero decodes to zero. -/
theorem toRat?_mul_of_toRat?_eq_some_zero_right {left right : Value}
    (hleft : isFinite left = true) (hright : toRat? right = some 0)
    (hformat : format.isIEEE = true := by ieee_format) : toRat? (left * right) = some 0 := by
  unfold toRat? isFinite at *
  rw [toModel_hMul]
  exact Model.toRat?_mul_of_toRat?_eq_some_zero_right hformat hleft hright

/-- Multiplying by a configured value that decodes to `1` or `-1` on the left is exact. -/
theorem toRat?_mul_of_abs_eq_one_left {left right : Value} {p q : ℚ} (hleft : toRat? left = some p)
    (hp : |p| = 1) (hright : toRat? right = some q)
    (hformat : format.isIEEE = true := by ieee_format) :
    toRat? (left * right) = some (p * q) := by
  unfold toRat? at *
  rw [toModel_hMul]
  exact Model.toRat?_mul_of_abs_eq_one_left hformat hleft hp hright

/-- Multiplying by a configured value that decodes to `1` or `-1` on the right is exact. -/
theorem toRat?_mul_of_abs_eq_one_right {left right : Value} {p q : ℚ} (hleft : toRat? left = some p)
    (hright : toRat? right = some q) (hq : |q| = 1)
    (hformat : format.isIEEE = true := by ieee_format) :
    toRat? (left * right) = some (p * q) := by
  unfold toRat? at *
  rw [toModel_hMul]
  exact Model.toRat?_mul_of_abs_eq_one_right hformat hleft hright hq

/-- A product whose exact product is nonnegative has a nonnegative real value. A product that is
not finite has real value zero. -/
theorem toReal_mul_nonneg {left right : Value} (hsign : 0 ≤ toReal left * toReal right)
    (hformat : format.isIEEE = true := by ieee_format) : 0 ≤ toReal (left * right) := by
  cases hresult : isFinite (left * right)
  · exact (Model.toReal_eq_zero_of_isFinite_eq_false hresult).ge
  · rw [toReal_mul_eq_roundAt hresult]
    exact Model.roundAt_nonneg format hsign

/-- A product whose exact product is nonpositive has a nonpositive real value. -/
theorem toReal_mul_nonpos {left right : Value} (hsign : toReal left * toReal right ≤ 0)
    (hformat : format.isIEEE = true := by ieee_format) : toReal (left * right) ≤ 0 := by
  cases hresult : isFinite (left * right)
  · exact (Model.toReal_eq_zero_of_isFinite_eq_false hresult).le
  · rw [toReal_mul_eq_roundAt hresult]
    exact Model.roundAt_nonpos format hsign

/-- A product of finite values is negative when its exact product is at most the largest finite
value in magnitude and below `-underflowErrorAt`. -/
theorem toReal_mul_lt_zero {left right : Value} (hleft : isFinite left = true)
    (hright : isFinite right = true)
    (hrange : |toReal left * toReal right| ≤ Model.toReal (Model.posMaxFinite format))
    (hlarge : toReal left * toReal right < -Model.underflowErrorAt format)
    (hformat : format.isIEEE = true := by ieee_format) :
    toReal (left * right) < 0 := by
  have hresult : isFinite (left * right) = true := by
    unfold isFinite toReal at *
    rw [toModel_hMul]
    exact Model.isFinite_mul_of_abs_mul_le_posMaxFinite _ _ hformat hleft hright
      (by rwa [← abs_mul])
  rw [toReal_mul_eq_roundAt hresult]
  exact Model.roundAt_lt_zero format hlarge

end Mul

/--
A finite configured quotient by a finite divisor with pure relative error `ry < 1`, absolute part
zero, has relative error `(1 + u) * ((rx + ry) / (1 - ry)) + u` and absolute error
`(1 + u) * (ax / ((1 - ry) * |y₀|)) + η`, with `u = Model.unitRoundoffAt format` and
`η = Model.underflowErrorAt format`. A finite quotient alone does not make the divisor finite: a
finite value over an infinity is a zero.
-/
theorem mixedError_toReal_div {left right : Value}
    [cap : ExecFloat.Div (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.div]
    (hright : isFinite right = true) (hresult : isFinite (left / right) = true)
    (eleft : MixedError (toReal left) x₀ rx ax) (eright : MixedError (toReal right) y₀ ry 0)
    (hry : ry < 1) (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal (left / right)) (x₀ / y₀)
      ((1 + Model.unitRoundoffAt format) * ((rx + ry) / (1 - ry)) + Model.unitRoundoffAt format)
      ((1 + Model.unitRoundoffAt format) * (ax / ((1 - ry) * |y₀|)) +
        Model.underflowErrorAt format) := by
  unfold toReal isFinite at *
  rw [toModel_hDiv] at hresult ⊢
  exact Model.mixedError_toReal_div hformat hright hresult eleft eright hry

/--
A finite configured fused multiply-add rounds once. With `u = Model.unitRoundoffAt format` and
`η = Model.underflowErrorAt format`, it approximates the exact `x₀ * y₀ + z₀` with relative error
`u` and absolute error `(1 + u)` times the error bounds of the product, as in `MixedError.mul`, and
of the addend, plus `η`.
-/
theorem mixedError_toReal_fma {left right addend : Value}
    [cap : ExecFloat.Fma (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.fma]
    (hresult : isFinite (fma left right addend) = true) (eleft : MixedError (toReal left) x₀ rx ax)
    (eright : MixedError (toReal right) y₀ ry ay) (eaddend : MixedError (toReal addend) z₀ rz az)
    (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal (fma left right addend)) (x₀ * y₀ + z₀) (Model.unitRoundoffAt format)
      ((1 + Model.unitRoundoffAt format) * ((rx + ry + rx * ry) * |x₀ * y₀| +
        ((1 + ry) * ax * |y₀| + (1 + rx) * ay * |x₀| + ax * ay) + (rz * |z₀| + az)) +
        Model.underflowErrorAt format) := by
  unfold toReal isFinite at *
  rw [toModel_fma] at hresult ⊢
  exact Model.mixedError_toReal_fma hformat hresult eleft eright eaddend

/--
The configured square root of a finite value that is zero or has a clear sign bit, approximating a
nonnegative exact value, has relative error
`(1 + u) * r + u` and absolute error `(1 + u) * √a + η`, with `u = Model.unitRoundoffAt format` and
`η = Model.underflowErrorAt format`.
-/
theorem mixedError_toReal_sqrt {value : Value}
    [cap : ExecFloat.Sqrt (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.sqrt]
    (hvalue : isFinite value = true) (hdomain : isZero value = true ∨ signBit value = false)
    (evalue : MixedError (toReal value) x₀ r a) (hx₀ : 0 ≤ x₀)
    (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal (sqrt value)) (√x₀)
      ((1 + Model.unitRoundoffAt format) * r + Model.unitRoundoffAt format)
      ((1 + Model.unitRoundoffAt format) * √a + Model.underflowErrorAt format) := by
  unfold toReal isFinite isZero signBit at *
  rw [toModel_sqrt]
  exact Model.mixedError_toReal_sqrt hformat hvalue hdomain evalue hx₀

/--
The configured square root of a finite value that is zero or has a clear sign bit, approximating
an exact value at least `m > 0`, has relative error
`(1 + u) * r + u` and absolute error `(1 + u) * (a / √m) + η`, with
`u = Model.unitRoundoffAt format` and `η = Model.underflowErrorAt format`.
-/
theorem mixedError_toReal_sqrt_of_le {value : Value}
    [cap : ExecFloat.Sqrt (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.sqrt]
    (hvalue : isFinite value = true) (hdomain : isZero value = true ∨ signBit value = false)
    (evalue : MixedError (toReal value) x₀ r a) (hm : 0 < m) (hmx : m ≤ x₀)
    (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal (sqrt value)) (√x₀)
      ((1 + Model.unitRoundoffAt format) * r + Model.unitRoundoffAt format)
      ((1 + Model.unitRoundoffAt format) * (a / √m) + Model.underflowErrorAt format) := by
  unfold toReal isFinite isZero signBit at *
  rw [toModel_sqrt]
  exact Model.mixedError_toReal_sqrt_of_le hformat hvalue hdomain evalue hm hmx

section Sum

variable [cap : ExecFloat.Add (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.add]
    {ι : Type*} {l : List ι} {term₀ rel err : ι → ℝ} {seed₀ d : ℝ}

/-- Decoding the partial sums of a configured left-to-right sum gives the model partial sums. -/
private theorem map_toModel_scanl_add {term : ι → Value} (seed : Value) :
    (l.scanl (fun acc i => acc + term i) seed).map toModel =
      l.scanl (fun acc i => Model.add acc (toModel (term i))) (toModel seed) := by
  induction l generalizing seed with
  | nil => simp
  | cons i l ih => simp [ih]

/-- Decoding a configured left-to-right sum gives the model sum of the decoded terms. -/
private theorem toModel_foldl_add {term : ι → Value} (seed : Value) :
    toModel (l.foldl (fun acc i => acc + term i) seed) =
      l.foldl (fun acc i => Model.add acc (toModel (term i))) (toModel seed) :=
  (List.foldl_hom toModel fun acc i => by simp).symm

/-- Finite configured partial sums decode to finite model partial sums. -/
private theorem isFinite_of_mem_scanl_add_toModel {term : ι → Value} {seed : Value}
    (hfinite : ∀ v ∈ l.scanl (fun acc i => acc + term i) seed, isFinite v = true) :
    ∀ v ∈ l.scanl (fun acc i => Model.add acc (toModel (term i))) (toModel seed),
      Model.isFinite v = true := by
  rw [← map_toModel_scanl_add]
  intro v hv
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hv
  exact hfinite w hw

/-- Every partial sum of a finite configured left-to-right sum is finite. -/
theorem isFinite_of_mem_scanl_add {term : ι → Value} {seed : Value}
    (hsum : isFinite (l.foldl (fun acc i => acc + term i) seed) = true) {v : Value}
    (hv : v ∈ l.scanl (fun acc i => acc + term i) seed)
    (hformat : format.isIEEE = true := by ieee_format) : isFinite v = true := by
  unfold isFinite at *
  rw [toModel_foldl_add] at hsum
  exact Model.isFinite_of_mem_scanl_add hformat hsum
    (by rw [← map_toModel_scanl_add]; exact List.mem_map_of_mem hv)

/--
A finite configured left-to-right sum, from a nonnegative seed, of terms with nonnegative real
values is at least its seed and each of its terms.
-/
theorem le_toReal_foldl_add {term : ι → Value} {seed : Value}
    (hsum : isFinite (l.foldl (fun acc i => acc + term i) seed) = true)
    (hnonneg : ∀ i ∈ l, 0 ≤ toReal (term i)) (hseed : 0 ≤ toReal seed)
    (hformat : format.isIEEE = true := by ieee_format) :
    toReal seed ≤ toReal (l.foldl (fun acc i => acc + term i) seed) ∧
      ∀ i ∈ l, toReal (term i) ≤ toReal (l.foldl (fun acc i => acc + term i) seed) := by
  induction l generalizing seed with
  | nil => simp
  | cons i l ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at hnonneg
      simp only [List.foldl_cons] at hsum
      have hnext : isFinite (seed + term i) = true :=
        isFinite_of_mem_scanl_add (l := i :: l) hsum (by cases l <;> simp)
      have hmodel := hnext
      unfold isFinite at hmodel
      rw [toModel_hAdd] at hmodel
      obtain ⟨hseedFinite, htermFinite⟩ := Model.isFinite_of_isFinite_add hformat hmodel
      have hrounded := toReal_add_eq_roundAt hnext
      have hseedBound : toReal seed ≤ toReal (seed + term i) :=
        calc toReal seed = Model.roundAt format (toReal seed) :=
              (Model.roundAt_toReal_eq _ hseedFinite).symm
          _ ≤ _ := Model.roundAt_mono _ (by linarith [hnonneg.1])
          _ = _ := hrounded.symm
      have htermBound : toReal (term i) ≤ toReal (seed + term i) :=
        calc toReal (term i) = Model.roundAt format (toReal (term i)) :=
              (Model.roundAt_toReal_eq _ htermFinite).symm
          _ ≤ _ := Model.roundAt_mono _ (by linarith)
          _ = _ := hrounded.symm
      obtain ⟨hnextBound, htermsBound⟩ := ih hsum hnonneg.2 (hseed.trans hseedBound)
      simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
      exact ⟨hseedBound.trans hnextBound, htermBound.trans hnextBound, htermsBound⟩

/--
A configured left-to-right sum whose seed and terms have nonnegative exact values keeps relative
accuracy,
with relative error `(1 + u) ^ l.length * (1 + r) - 1` and absolute error
`(1 + u) ^ l.length * (d + Σ err i)` for `u = Model.unitRoundoffAt format`, as in
`Model.mixedError_toReal_foldl_add`.
-/
theorem mixedError_toReal_foldl_add {term : ι → Value} {seed : Value}
    (hfinite : ∀ v ∈ l.scanl (fun acc i => acc + term i) seed, isFinite v = true)
    (hterm : ∀ i ∈ l, isFinite (term i) = true) (eseed : MixedError (toReal seed) seed₀ r d)
    (eterm : ∀ i ∈ l, MixedError (toReal (term i)) (term₀ i) r (err i)) (hseed₀ : 0 ≤ seed₀)
    (hterm₀ : ∀ i ∈ l, 0 ≤ term₀ i) (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal (l.foldl (fun acc i => acc + term i) seed))
      (seed₀ + (l.map term₀).sum)
      ((1 + Model.unitRoundoffAt format) ^ l.length * (1 + r) - 1)
      ((1 + Model.unitRoundoffAt format) ^ l.length * (d + (l.map err).sum)) := by
  have hmodel := isFinite_of_mem_scanl_add_toModel hfinite
  unfold toReal at *
  rw [toModel_foldl_add]
  exact Model.mixedError_toReal_foldl_add hformat hmodel hterm eseed eterm hseed₀ hterm₀

/--
A configured left-to-right sum from a seed of real value zero, of terms with nonnegative exact
values, has relative error
`(1 + u) ^ (l.length - 1) * (1 + r) - 1` and absolute error `(1 + u) ^ (l.length - 1) * Σ err i`
for `u = Model.unitRoundoffAt format`, as in `Model.mixedError_toReal_foldl_add_of_toReal_eq_zero`:
`n` terms take `n - 1` roundings, with natural subtraction.
-/
theorem mixedError_toReal_foldl_add_of_toReal_eq_zero {term : ι → Value} {seed : Value}
    (hseed : toReal seed = 0)
    (hfinite : ∀ v ∈ l.scanl (fun acc i => acc + term i) seed, isFinite v = true)
    (hterm : ∀ i ∈ l, isFinite (term i) = true)
    (eterm : ∀ i ∈ l, MixedError (toReal (term i)) (term₀ i) r (err i)) (hr : 0 ≤ r)
    (hterm₀ : ∀ i ∈ l, 0 ≤ term₀ i) (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal (l.foldl (fun acc i => acc + term i) seed)) (l.map term₀).sum
      ((1 + Model.unitRoundoffAt format) ^ (l.length - 1) * (1 + r) - 1)
      ((1 + Model.unitRoundoffAt format) ^ (l.length - 1) * (l.map err).sum) := by
  have hmodel := isFinite_of_mem_scanl_add_toModel hfinite
  unfold toReal at *
  rw [toModel_foldl_add]
  exact Model.mixedError_toReal_foldl_add_of_toReal_eq_zero hformat hseed hmodel hterm eterm hr
    hterm₀

/--
A configured left-to-right sum, from a seed with nonnegative exact value and pure absolute error
`d`, of terms with nonnegative exact values and their own mixed errors
`(rel i, err i)` has relative error `(1 + u) ^ l.length - 1` and absolute error
`(1 + u) ^ l.length * (d + Σ (rel i * term₀ i + err i))` for `u = Model.unitRoundoffAt format`, as
in `Model.mixedError_toReal_foldl_add_weighted`.
-/
theorem mixedError_toReal_foldl_add_weighted {term : ι → Value} {seed : Value}
    (hfinite : ∀ v ∈ l.scanl (fun acc i => acc + term i) seed, isFinite v = true)
    (hterm : ∀ i ∈ l, isFinite (term i) = true) (eseed : MixedError (toReal seed) seed₀ 0 d)
    (eterm : ∀ i ∈ l, MixedError (toReal (term i)) (term₀ i) (rel i) (err i)) (hseed₀ : 0 ≤ seed₀)
    (hterm₀ : ∀ i ∈ l, 0 ≤ term₀ i) (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal (l.foldl (fun acc i => acc + term i) seed))
      (seed₀ + (l.map term₀).sum) ((1 + Model.unitRoundoffAt format) ^ l.length - 1)
      ((1 + Model.unitRoundoffAt format) ^ l.length *
        (d + (l.map fun i => rel i * term₀ i + err i).sum)) := by
  have hmodel := isFinite_of_mem_scanl_add_toModel hfinite
  unfold toReal at *
  rw [toModel_foldl_add]
  exact Model.mixedError_toReal_foldl_add_weighted hformat hmodel hterm eseed eterm hseed₀ hterm₀

/--
The bound of `mixedError_toReal_foldl_add_weighted` from a seed of real value zero, with no seed
error and `l.length - 1` in place of `l.length`, in natural subtraction, as in
`Model.mixedError_toReal_foldl_add_weighted_of_toReal_eq_zero`.
-/
theorem mixedError_toReal_foldl_add_weighted_of_toReal_eq_zero {term : ι → Value}
    {seed : Value} (hseed : toReal seed = 0)
    (hfinite : ∀ v ∈ l.scanl (fun acc i => acc + term i) seed, isFinite v = true)
    (hterm : ∀ i ∈ l, isFinite (term i) = true)
    (eterm : ∀ i ∈ l, MixedError (toReal (term i)) (term₀ i) (rel i) (err i))
    (hterm₀ : ∀ i ∈ l, 0 ≤ term₀ i) (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal (l.foldl (fun acc i => acc + term i) seed)) (l.map term₀).sum
      ((1 + Model.unitRoundoffAt format) ^ (l.length - 1) - 1)
      ((1 + Model.unitRoundoffAt format) ^ (l.length - 1) *
        (l.map fun i => rel i * term₀ i + err i).sum) := by
  have hmodel := isFinite_of_mem_scanl_add_toModel hfinite
  unfold toReal at *
  rw [toModel_foldl_add]
  exact Model.mixedError_toReal_foldl_add_weighted_of_toReal_eq_zero hformat hseed hmodel hterm
    eterm hterm₀

/--
A configured left-to-right sum of terms of any sign, from a seed with pure absolute error `d`,
has the pure absolute bound
`((1 + u) ^ n - 1) * (|seed₀| + Σ |term₀ i|) + (1 + u) ^ n * (d + Σ (rel i * |term₀ i| + err i))`
for `n = l.length` and `u = Model.unitRoundoffAt format`, as in
`Model.mixedError_toReal_foldl_add_absolute`.
-/
theorem mixedError_toReal_foldl_add_absolute {term : ι → Value} {seed : Value}
    (hfinite : ∀ v ∈ l.scanl (fun acc i => acc + term i) seed, isFinite v = true)
    (hterm : ∀ i ∈ l, isFinite (term i) = true) (eseed : MixedError (toReal seed) seed₀ 0 d)
    (eterm : ∀ i ∈ l, MixedError (toReal (term i)) (term₀ i) (rel i) (err i))
    (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal (l.foldl (fun acc i => acc + term i) seed))
      (seed₀ + (l.map term₀).sum) 0
      (((1 + Model.unitRoundoffAt format) ^ l.length - 1) *
          (|seed₀| + (l.map fun i => |term₀ i|).sum) +
        (1 + Model.unitRoundoffAt format) ^ l.length *
          (d + (l.map fun i => rel i * |term₀ i| + err i).sum)) := by
  have hmodel := isFinite_of_mem_scanl_add_toModel hfinite
  unfold toReal at *
  rw [toModel_foldl_add]
  exact Model.mixedError_toReal_foldl_add_absolute hformat hmodel hterm eseed eterm

/--
The bound of `mixedError_toReal_foldl_add_absolute` from a seed of real value zero, with no seed
terms and `l.length - 1` in place of `l.length`, in natural subtraction, as in
`Model.mixedError_toReal_foldl_add_absolute_of_toReal_eq_zero`.
-/
theorem mixedError_toReal_foldl_add_absolute_of_toReal_eq_zero {term : ι → Value}
    {seed : Value} (hseed : toReal seed = 0)
    (hfinite : ∀ v ∈ l.scanl (fun acc i => acc + term i) seed, isFinite v = true)
    (hterm : ∀ i ∈ l, isFinite (term i) = true)
    (eterm : ∀ i ∈ l, MixedError (toReal (term i)) (term₀ i) (rel i) (err i))
    (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal (l.foldl (fun acc i => acc + term i) seed)) (l.map term₀).sum 0
      (((1 + Model.unitRoundoffAt format) ^ (l.length - 1) - 1) *
          (l.map fun i => |term₀ i|).sum +
        (1 + Model.unitRoundoffAt format) ^ (l.length - 1) *
          (l.map fun i => rel i * |term₀ i| + err i).sum) := by
  have hmodel := isFinite_of_mem_scanl_add_toModel hfinite
  unfold toReal at *
  rw [toModel_foldl_add]
  exact Model.mixedError_toReal_foldl_add_absolute_of_toReal_eq_zero hformat hseed hmodel hterm
    eterm

/-- Adding configured terms that decode to zero leaves the decoded value of the seed unchanged. -/
theorem toRat?_foldl_add_of_eq_zero {term : ι → Value} {seed : Value}
    {q : ℚ} (hseed : toRat? seed = some q) (hterm : ∀ i ∈ l, toRat? (term i) = some 0)
    (hformat : format.isIEEE = true := by ieee_format) :
    toRat? (l.foldl (fun acc i => acc + term i) seed) = some q := by
  unfold toRat? at *
  rw [toModel_foldl_add]
  exact Model.toRat?_foldl_add_of_eq_zero hformat hseed hterm

/--
A configured left-to-right sum over a list `l` without repeated indices (`l.Nodup`) that contains
`j`, from a seed that decodes to zero, whose terms all decode to zero except the one at `j`,
decodes to that term's value, as `Model.toRat?_foldl_add_eq_single`.
-/
theorem toRat?_foldl_add_eq_single {term : ι → Value} {seed : Value}
    {j : ι} {q : ℚ} (hl : l.Nodup) (hj : j ∈ l) (hseed : toRat? seed = some 0)
    (hterm : toRat? (term j) = some q) (hzero : ∀ i ∈ l, i ≠ j → toRat? (term i) = some 0)
    (hformat : format.isIEEE = true := by ieee_format) :
    toRat? (l.foldl (fun acc i => acc + term i) seed) = some q := by
  unfold toRat? at *
  rw [toModel_foldl_add]
  exact Model.toRat?_foldl_add_eq_single hformat hl hj hseed hterm hzero

end Sum

section FinSum

variable [cap : ExecFloat.Add (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.add]
    {n : ℕ} {term₀ rel err : Fin n → ℝ} {seed₀ d : ℝ}

/-- Every partial sum of a finite configured sum computed by `Fin.foldl` is finite. -/
theorem isFinite_of_mem_finRange_scanl_add {term : Fin n → Value} {seed : Value}
    (hsum : isFinite (Fin.foldl n (fun acc i => acc + term i) seed) = true) {v : Value}
    (hv : v ∈ (List.finRange n).scanl (fun acc i => acc + term i) seed)
    (hformat : format.isIEEE = true := by ieee_format) :
    isFinite v = true :=
  isFinite_of_mem_scanl_add (by rwa [Fin.foldl_eq_finRange_foldl] at hsum) hv

/--
The bound of `mixedError_toReal_foldl_add` for a configured sum of `n` terms computed by
`Fin.foldl`.
-/
theorem mixedError_toReal_fin_foldl_add {term : Fin n → Value} {seed : Value}
    (hfinite : ∀ v ∈ (List.finRange n).scanl (fun acc i => acc + term i) seed,
      isFinite v = true)
    (hterm : ∀ i, isFinite (term i) = true) (eseed : MixedError (toReal seed) seed₀ r d)
    (eterm : ∀ i, MixedError (toReal (term i)) (term₀ i) r (err i)) (hseed₀ : 0 ≤ seed₀)
    (hterm₀ : ∀ i, 0 ≤ term₀ i) (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal (Fin.foldl n (fun acc i => acc + term i) seed)) (seed₀ + ∑ i, term₀ i)
      ((1 + Model.unitRoundoffAt format) ^ n * (1 + r) - 1)
      ((1 + Model.unitRoundoffAt format) ^ n * (d + ∑ i, err i)) := by
  rw [Fin.foldl_eq_finRange_foldl, Fin.sum_univ_def, Fin.sum_univ_def]
  simpa using mixedError_toReal_foldl_add hfinite (fun i _ => hterm i) eseed
    (fun i _ => eterm i) hseed₀ fun i _ => hterm₀ i

/--
The bound of `mixedError_toReal_foldl_add_of_toReal_eq_zero` for a configured sum of `n` terms
computed by `Fin.foldl`.
-/
theorem mixedError_toReal_fin_foldl_add_of_toReal_eq_zero {term : Fin n → Value} {seed : Value}
    (hseed : toReal seed = 0)
    (hfinite : ∀ v ∈ (List.finRange n).scanl (fun acc i => acc + term i) seed,
      isFinite v = true)
    (hterm : ∀ i, isFinite (term i) = true)
    (eterm : ∀ i, MixedError (toReal (term i)) (term₀ i) r (err i)) (hr : 0 ≤ r)
    (hterm₀ : ∀ i, 0 ≤ term₀ i) (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal (Fin.foldl n (fun acc i => acc + term i) seed)) (∑ i, term₀ i)
      ((1 + Model.unitRoundoffAt format) ^ (n - 1) * (1 + r) - 1)
      ((1 + Model.unitRoundoffAt format) ^ (n - 1) * ∑ i, err i) := by
  rw [Fin.foldl_eq_finRange_foldl, Fin.sum_univ_def, Fin.sum_univ_def]
  simpa using mixedError_toReal_foldl_add_of_toReal_eq_zero hseed hfinite
    (fun i _ => hterm i) (fun i _ => eterm i) hr fun i _ => hterm₀ i

/--
The bound of `mixedError_toReal_foldl_add_weighted` for a configured sum of `n` terms computed by
`Fin.foldl`.
-/
theorem mixedError_toReal_fin_foldl_add_weighted {term : Fin n → Value} {seed : Value}
    (hfinite : ∀ v ∈ (List.finRange n).scanl (fun acc i => acc + term i) seed,
      isFinite v = true)
    (hterm : ∀ i, isFinite (term i) = true) (eseed : MixedError (toReal seed) seed₀ 0 d)
    (eterm : ∀ i, MixedError (toReal (term i)) (term₀ i) (rel i) (err i)) (hseed₀ : 0 ≤ seed₀)
    (hterm₀ : ∀ i, 0 ≤ term₀ i) (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal (Fin.foldl n (fun acc i => acc + term i) seed)) (seed₀ + ∑ i, term₀ i)
      ((1 + Model.unitRoundoffAt format) ^ n - 1)
      ((1 + Model.unitRoundoffAt format) ^ n * (d + ∑ i, (rel i * term₀ i + err i))) := by
  rw [Fin.foldl_eq_finRange_foldl]
  simp only [Fin.sum_univ_def]
  simpa using mixedError_toReal_foldl_add_weighted hfinite (fun i _ => hterm i) eseed
    (fun i _ => eterm i) hseed₀ fun i _ => hterm₀ i

/--
The bound of `mixedError_toReal_foldl_add_weighted_of_toReal_eq_zero` for a configured sum of `n`
terms computed by `Fin.foldl`.
-/
theorem mixedError_toReal_fin_foldl_add_weighted_of_toReal_eq_zero {term : Fin n → Value}
    {seed : Value} (hseed : toReal seed = 0)
    (hfinite : ∀ v ∈ (List.finRange n).scanl (fun acc i => acc + term i) seed,
      isFinite v = true)
    (hterm : ∀ i, isFinite (term i) = true)
    (eterm : ∀ i, MixedError (toReal (term i)) (term₀ i) (rel i) (err i))
    (hterm₀ : ∀ i, 0 ≤ term₀ i) (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal (Fin.foldl n (fun acc i => acc + term i) seed)) (∑ i, term₀ i)
      ((1 + Model.unitRoundoffAt format) ^ (n - 1) - 1)
      ((1 + Model.unitRoundoffAt format) ^ (n - 1) * ∑ i, (rel i * term₀ i + err i)) := by
  rw [Fin.foldl_eq_finRange_foldl]
  simp only [Fin.sum_univ_def]
  simpa using mixedError_toReal_foldl_add_weighted_of_toReal_eq_zero hseed hfinite
    (fun i _ => hterm i) (fun i _ => eterm i) fun i _ => hterm₀ i

/--
The bound of `mixedError_toReal_foldl_add_absolute` for a configured sum of `n` terms computed by
`Fin.foldl`.
-/
theorem mixedError_toReal_fin_foldl_add_absolute {term : Fin n → Value} {seed : Value}
    (hfinite : ∀ v ∈ (List.finRange n).scanl (fun acc i => acc + term i) seed,
      isFinite v = true)
    (hterm : ∀ i, isFinite (term i) = true) (eseed : MixedError (toReal seed) seed₀ 0 d)
    (eterm : ∀ i, MixedError (toReal (term i)) (term₀ i) (rel i) (err i))
    (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal (Fin.foldl n (fun acc i => acc + term i) seed)) (seed₀ + ∑ i, term₀ i)
      0 (((1 + Model.unitRoundoffAt format) ^ n - 1) * (|seed₀| + ∑ i, |term₀ i|) +
        (1 + Model.unitRoundoffAt format) ^ n * (d + ∑ i, (rel i * |term₀ i| + err i))) := by
  rw [Fin.foldl_eq_finRange_foldl]
  simp only [Fin.sum_univ_def]
  simpa using mixedError_toReal_foldl_add_absolute hfinite (fun i _ => hterm i) eseed
    fun i _ => eterm i

/--
The bound of `mixedError_toReal_foldl_add_absolute_of_toReal_eq_zero` for a configured sum of `n`
terms computed by `Fin.foldl`.
-/
theorem mixedError_toReal_fin_foldl_add_absolute_of_toReal_eq_zero {term : Fin n → Value}
    {seed : Value} (hseed : toReal seed = 0)
    (hfinite : ∀ v ∈ (List.finRange n).scanl (fun acc i => acc + term i) seed,
      isFinite v = true)
    (hterm : ∀ i, isFinite (term i) = true)
    (eterm : ∀ i, MixedError (toReal (term i)) (term₀ i) (rel i) (err i))
    (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal (Fin.foldl n (fun acc i => acc + term i) seed)) (∑ i, term₀ i) 0
      (((1 + Model.unitRoundoffAt format) ^ (n - 1) - 1) * ∑ i, |term₀ i| +
        (1 + Model.unitRoundoffAt format) ^ (n - 1) * ∑ i, (rel i * |term₀ i| + err i)) := by
  rw [Fin.foldl_eq_finRange_foldl]
  simp only [Fin.sum_univ_def]
  simpa using mixedError_toReal_foldl_add_absolute_of_toReal_eq_zero hseed hfinite
    (fun i _ => hterm i) fun i _ => eterm i

/-- `toRat?_foldl_add_of_eq_zero` for a configured sum computed by `Fin.foldl`. -/
theorem toRat?_fin_foldl_add_of_eq_zero {term : Fin n → Value} {seed : Value}
    {q : ℚ} (hseed : toRat? seed = some q) (hterm : ∀ i, toRat? (term i) = some 0)
    (hformat : format.isIEEE = true := by ieee_format) :
    toRat? (Fin.foldl n (fun acc i => acc + term i) seed) = some q := by
  rw [Fin.foldl_eq_finRange_foldl]
  exact toRat?_foldl_add_of_eq_zero hseed fun i _ => hterm i

/--
`toRat?_foldl_add_eq_single` for a configured sum computed by `Fin.foldl`, which visits every
index once: a one-hot sum of any length is exact.
-/
theorem toRat?_fin_foldl_add_eq_single {term : Fin n → Value} {seed : Value}
    {j : Fin n} {q : ℚ} (hseed : toRat? seed = some 0) (hterm : toRat? (term j) = some q)
    (hzero : ∀ i, i ≠ j → toRat? (term i) = some 0)
    (hformat : format.isIEEE = true := by ieee_format) :
    toRat? (Fin.foldl n (fun acc i => acc + term i) seed) = some q := by
  rw [Fin.foldl_eq_finRange_foldl]
  exact toRat?_foldl_add_eq_single (List.nodup_finRange n) (List.mem_finRange j) hseed
    hterm fun i _ => hzero i

end FinSum

end Rounding

end FloatLib.Floats.ExecFloat.Binary
