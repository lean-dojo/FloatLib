/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.Rational
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.MixedError
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Operations.Proof

/-!
# Local rounding of configured operations

FloatLib states each rounded configured operation together with the propagation of its operands'
errors. An error analysis that chooses the propagation rule itself needs the rounding alone: for
an IEEE descriptor, under the selected capability's specification (`HasSpec`), a finite result has
relative error `u` against the exact operation on the computed operands, with no absolute part for
sums and differences and the underflow error for products, quotients and square roots. A quotient
keeps a finite divisor and a square root a finite operand in its domain. Here are those local
steps, finiteness from a range condition on an enclosure of the exact result, and the finiteness
of FloatLib's exact operations, which needs no range condition. A finite conversion of a rational
is its rounding, so C's `(float) n` of an integer or a natural number has relative error `u`, and
none when its magnitude is at most `2 ^ p`, with `p = fracWidth + 1`.

A range condition bounds the enclosure `(1 + r) * |x₀| + a` of the exact operation on the
computed operands by the largest finite value. It is an inequality on inputs and budgets, never
the assumption that the result is finite.
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
