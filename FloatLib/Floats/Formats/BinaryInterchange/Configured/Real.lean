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

/-!
# Real values of configured binary values

`toReal?` reads a configured binary value as the real number it denotes, through its proof model,
and returns `none` for NaNs and infinities, which have no real value. `toReal` is the total
version, which maps them to zero as `Model.toReal` does.

The theorems `toReal_add_eq_roundAt` through `toReal_sqrt_eq_roundAt` state the IEEE rounding
contract on the configured carrier: a finite result of `x + y`, `x - y`, `x * y`, `x / y`,
`fma x y z`, or `sqrt x` is the nearest-even rounding `Model.roundAt` of the exact real result.
`abs_toReal_add_sub_le` and its siblings turn that into an absolute error of at most half an ulp,
`Model.halfUlpAt format`. They need an IEEE descriptor, a finite result, which forces finite
operands and a nonzero divisor, a finite divisor for division (a finite value over an infinity is
a signed zero), a finite operand that is zero or nonnegative for square root (which never
overflows), and, like `toModel_hAdd`, the instance argument that the selected capability computes
the configured model operation. Instance search proves that argument for every capability the
library declares.

The descriptor proof `hformat : format.isIEEE = true` is the last argument of these theorems and
of every other configured theorem that needs it, with the tactic `ieee_format` as its default. It
takes the proof from a hypothesis in context, or decides it for a concrete IEEE-encoded format such
as binary32. A format with another encoding has no such proof, and a variable format without one
in context passes it as `(hformat := h)`.

`toReal_add_of_isZero_left` and its siblings state the cases that do not round: sums and
differences with a zero, `x - x`, products with a zero or with a value of magnitude one, quotients
by a value of magnitude one, and the square root of a zero. The literals `0` and `1` denote zero
and one, the encoding word `1` denotes the least positive subnormal, and a value compares equal to
zero with `==` exactly when it is a finite zero (`beq_zero_iff`).

Between finite values `<` and `≤` are the order of the real values (`lt_iff_toReal_lt`), so a
selection such as C's maximum step `if m < x then x else m` has the real value `max` of its
operands (`toReal_ite_lt_eq_max` and its siblings), and is finite when they are
(`isFinite_ite`). Between finite values `==` is the equality of the real values, so the two zeros
compare equal (`beq_eq_decide_toReal_eq`). `isFinite_sqrt` states that square root does not
overflow, and the `execFloat_sqrt` forms restate the square-root theorems for the format-generic
call `ExecFloat.sqrt`.
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

/-- A finite value whose real value is the rational `q` has exact rational value `q`. -/
theorem toRat?_eq_some_of_toReal_eq {value : Value} {q : ℚ} (hvalue : isFinite value = true)
    (hreal : toReal value = q) : toRat? value = some q :=
  Model.Algebraic.toRat?_eq_some_of_toReal_eq hvalue hreal

/-- A finite value's optional real value is its real value. -/
theorem toReal?_eq_some_toReal {value : Value} (hvalue : isFinite value = true) :
    toReal? value = some (toReal value) := by
  have hdecode := Model.toDyadic?_isSome_eq_isFinite (toModel value)
  unfold toReal? toReal Model.toReal Model.toReal? isFinite at *
  cases hd : Model.toDyadic? (toModel value) <;> simp_all

/-- A finite value is an executable zero exactly when its real value is zero. -/
theorem isZero_eq_true_iff_toReal_eq_zero {value : Value} (hvalue : isFinite value = true) :
    isZero value = true ↔ toReal value = 0 :=
  Model.isZero_eq_true_iff_toReal_eq_zero _ hvalue

/-- A finite value with a nonnegative real value is in the domain of square root: a zero of either
sign, or a value with a clear sign bit. -/
theorem isZero_or_signBit_eq_false_of_toReal_nonneg {value : Value}
    (hvalue : isFinite value = true) (hnonneg : 0 ≤ toReal value) :
    isZero value = true ∨ signBit value = false :=
  Model.isZero_or_signBit_eq_false_of_toReal_nonneg _ hvalue hnonneg

/-- A finite value is at most the largest finite value in magnitude. -/
theorem abs_toReal_le_posMaxFinite_of_isFinite {value : Value} (hvalue : isFinite value = true) :
    |toReal value| ≤ Model.toReal (Model.posMaxFinite format) :=
  Model.abs_toReal_le_posMaxFinite_of_isFinite _ hvalue

/-- Negation keeps finiteness. -/
@[simp] theorem isFinite_neg (value : Value) : isFinite (-value) = isFinite value := by
  unfold isFinite
  rw [toModel_neg, Model.isFinite_neg]

/-! ## Literals

The literals are stated for `ExecFloat (Configured.Family format code plan)`, the type that the
numeral instances elaborate at, so that they apply without unfolding the descriptor.
-/

/-- The zero literal denotes zero. -/
@[simp] theorem toReal_zero :
    toReal (0 : ExecFloat (Configured.Family format code plan)) = 0 := by
  change Model.toReal (Configured.Family.toModel
    (Configured.Family.ofModel (Model.ofRat format (0 : Rat)))) = 0
  rw [Configured.Family.toModel_ofModel]
  simp [Model.ofRat, Model.Internal.Directed.roundRat, Model.Internal.Directed.roundRatScaled]

/-- The zero literal is finite. -/
@[simp] theorem isFinite_zero :
    isFinite (0 : ExecFloat (Configured.Family format code plan)) = true := by
  change Model.isFinite (Configured.Family.toModel
    (Configured.Family.ofModel (Model.ofRat format (0 : Rat)))) = true
  rw [Configured.Family.toModel_ofModel]
  simpa [Model.ofRat, Model.Internal.Directed.roundRat, Model.Internal.Directed.roundRatScaled]
    using Model.isFinite_eq_true_of_isZero_eq_true _ (Model.isZero_zero format false)

/-- The zero literal is an executable zero. -/
@[simp] theorem isZero_zero :
    isZero (0 : ExecFloat (Configured.Family format code plan)) = true := by
  change Model.isZero (Configured.Family.toModel
    (Configured.Family.ofModel (Model.ofRat format (0 : Rat)))) = true
  rw [Configured.Family.toModel_ofModel]
  simp [Model.ofRat, Model.Internal.Directed.roundRat, Model.Internal.Directed.roundRatScaled]

/-- Rounding the rational one is finite in an IEEE format. -/
private theorem isFinite_ofRat_one (hformat : format.isIEEE = true) :
    Model.isFinite (Model.ofRat format (1 : Rat)) = true := by
  change Model.isFinite (Model.roundRat format false 1 1) = true
  rw [Model.roundRat]
  apply Model.isFinite_roundRatScaled_of_abs_le_posMaxFinite format false 1 1 0 hformat
    one_ne_zero
  simpa [Model.signedScaledRatToReal, Model.scaledRatToReal] using
    Model.abs_toReal_le_posMaxFinite_of_isFinite _ (Model.isFinite_posOne format)

/-- The one literal is finite in an IEEE format. -/
theorem isFinite_one (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (1 : ExecFloat (Configured.Family format code plan)) = true := by
  change Model.isFinite (Configured.Family.toModel
    (Configured.Family.ofModel (Model.ofRat format (1 : Rat)))) = true
  rw [Configured.Family.toModel_ofModel]
  exact isFinite_ofRat_one hformat

/-- The one literal denotes one in an IEEE format. -/
theorem toReal_one (hformat : format.isIEEE = true := by ieee_format) :
    toReal (1 : ExecFloat (Configured.Family format code plan)) = 1 := by
  change Model.toReal (Configured.Family.toModel
    (Configured.Family.ofModel (Model.ofRat format (1 : Rat)))) = 1
  have hfinite := isFinite_ofRat_one (format := format) hformat
  change Model.isFinite (Model.roundRat format false 1 1) = true at hfinite
  rw [Configured.Family.toModel_ofModel]
  change Model.toReal (Model.roundRat format false 1 1) = 1
  rw [Model.roundRat] at hfinite ⊢
  rw [Model.toReal_roundRatScaled_eq_roundAt format false 1 1 0 hformat hfinite]
  simp [Model.signedScaledRatToReal, Model.scaledRatToReal]

/-- The encoding word `1`, the least positive subnormal, is finite in every format. -/
@[simp] theorem isFinite_ofNatBits_one :
    isFinite (ofNatBits 1 : ExecFloat (Configured.Family format code plan)) = true := by
  change Model.isFinite (Configured.Family.toModel
    (Configured.Family.ofModel (Model.posMinSubnormal format))) = true
  rw [Configured.Family.toModel_ofModel, Model.isFinite_posMinSubnormal]

/-- The encoding word `1` denotes the least positive subnormal, `2 ^ minSubnormalExponent`. -/
@[simp] theorem toReal_ofNatBits_one :
    toReal (ofNatBits 1 : ExecFloat (Configured.Family format code plan)) =
      2 ^ format.minSubnormalExponent := by
  change Model.toReal (Configured.Family.toModel
    (Configured.Family.ofModel (Model.posMinSubnormal format))) = _
  rw [Configured.Family.toModel_ofModel, Model.toReal_posMinSubnormal, Model.bpow,
    FloatLib.Floats.Formats.Flocq.bpow_binaryRadix]

/-- A value compares equal to zero exactly when it is finite with real value zero. -/
theorem beq_zero_iff {value : ExecFloat (Configured.Family format code plan)} :
    (value == 0) = true ↔ isFinite value = true ∧ toReal value = 0 := by
  change (Model.compare (toModel value)
    (toModel (0 : ExecFloat (Configured.Family format code plan))) == some .eq) = true ↔ _
  rw [beq_iff_eq]
  constructor
  · intro compared
    have notNaN : Model.isNaN (toModel value) = false := by
      cases nan : Model.isNaN (toModel value)
      · rfl
      · rw [(Model.compare_eq_none_iff _ _).2 (.inl nan)] at compared
        cases compared
    obtain ⟨extended, decoded⟩ := Model.exists_toEReal?_of_isNaN_eq_false _ notNaN
    have equal := (Model.compare_eq_some_eq_iff_toEReal_eq decoded
      (Model.toEReal?_eq_some_toReal_of_isFinite_eq_true _ isFinite_zero)).1 compared
    rcases Model.toEReal?_cases _ decoded with ⟨-, infinite⟩ | ⟨finite, real⟩
    · rw [infinite] at equal
      split_ifs at equal <;> simp at equal
    · exact ⟨finite, (EReal.coe_eq_coe_iff.mp (real.symm.trans equal)).trans toReal_zero⟩
  · rintro ⟨finite, zero⟩
    exact (Model.compare_eq_some_eq_iff_toReal_eq_of_isFinite _ _ finite isFinite_zero).2
      (zero.trans toReal_zero.symm)

/-- Between finite values, `<` is the order of their real values. -/
theorem lt_iff_toReal_lt {left right : Value} (hleft : isFinite left = true)
    (hright : isFinite right = true) : left < right ↔ toReal left < toReal right := by
  rw [lt_iff_compare_eq_lt]
  exact Model.compare_eq_some_lt_iff_toReal_lt_of_isFinite _ _ hleft hright

/-- Between finite values, `≤` is the order of their real values. -/
theorem le_iff_toReal_le {left right : Value} (hleft : isFinite left = true)
    (hright : isFinite right = true) : left ≤ right ↔ toReal left ≤ toReal right := by
  rw [le_iff_compare_eq_lt_or_eq,
    Model.compare_eq_some_lt_iff_toReal_lt_of_isFinite _ _ hleft hright,
    Model.compare_eq_some_eq_iff_toReal_eq_of_isFinite _ _ hleft hright]
  exact le_iff_lt_or_eq.symm

/-- Between finite values, `==` is the equality of their real values, under which the two zeros
are equal. -/
theorem beq_eq_decide_toReal_eq {left right : Value} (hleft : isFinite left = true)
    (hright : isFinite right = true) : (left == right) = decide (toReal left = toReal right) := by
  change (Model.compare (toModel left) (toModel right) == some .eq) = _
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  exact Model.compare_eq_some_eq_iff_toReal_eq_of_isFinite _ _ hleft hright

/-- A selection between finite values is finite, such as the step of a C maximum loop. -/
theorem isFinite_ite {condition : Prop} [Decidable condition] {left right : Value}
    (hleft : isFinite left = true) (hright : isFinite right = true) :
    isFinite (if condition then left else right) = true := by
  split <;> assumption

/-- The selection `if left < right then right else left` of finite values has the real value
`max (toReal left) (toReal right)`, as in a C maximum loop. -/
theorem toReal_ite_lt_eq_max {left right : Value} (hleft : isFinite left = true)
    (hright : isFinite right = true) :
    toReal (if left < right then right else left) = max (toReal left) (toReal right) := by
  split_ifs with h
  · exact (max_eq_right ((lt_iff_toReal_lt hleft hright).1 h).le).symm
  · exact (max_eq_left (not_lt.1 (mt (lt_iff_toReal_lt hleft hright).2 h))).symm

/-- The selection `if left < right then left else right` of finite values has the real value
`min (toReal left) (toReal right)`. -/
theorem toReal_ite_lt_eq_min {left right : Value} (hleft : isFinite left = true)
    (hright : isFinite right = true) :
    toReal (if left < right then left else right) = min (toReal left) (toReal right) := by
  split_ifs with h
  · exact (min_eq_left ((lt_iff_toReal_lt hleft hright).1 h).le).symm
  · exact (min_eq_right (not_lt.1 (mt (lt_iff_toReal_lt hleft hright).2 h))).symm

/-- The selection `if left ≤ right then right else left` of finite values has the real value
`max (toReal left) (toReal right)`. -/
theorem toReal_ite_le_eq_max {left right : Value} (hleft : isFinite left = true)
    (hright : isFinite right = true) :
    toReal (if left ≤ right then right else left) = max (toReal left) (toReal right) := by
  split_ifs with h
  · exact (max_eq_right ((le_iff_toReal_le hleft hright).1 h)).symm
  · exact (max_eq_left (not_le.1 (mt (le_iff_toReal_le hleft hright).2 h)).le).symm

/-- The selection `if left ≤ right then left else right` of finite values has the real value
`min (toReal left) (toReal right)`. -/
theorem toReal_ite_le_eq_min {left right : Value} (hleft : isFinite left = true)
    (hright : isFinite right = true) :
    toReal (if left ≤ right then left else right) = min (toReal left) (toReal right) := by
  split_ifs with h
  · exact (min_eq_left ((le_iff_toReal_le hleft hright).1 h)).symm
  · exact (min_eq_right (not_le.1 (mt (le_iff_toReal_le hleft hright).2 h)).le).symm

section Rounding

variable [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]

/-- A finite configured sum is the nearest-even rounding of the exact real sum. -/
theorem toReal_add_eq_roundAt {left right : Value}
    [cap : ExecFloat.Add (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.add]
    (hresult : isFinite (left + right) = true) (hformat : format.isIEEE = true := by ieee_format) :
    toReal (left + right) = Model.roundAt format (toReal left + toReal right) := by
  unfold toReal isFinite at *
  rw [toModel_hAdd] at hresult ⊢
  exact Model.toReal_add_eq_roundAt _ _ hformat hresult

/-- A finite configured difference is the nearest-even rounding of the exact real difference. -/
theorem toReal_sub_eq_roundAt {left right : Value}
    [cap : ExecFloat.Sub (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.sub]
    (hresult : isFinite (left - right) = true) (hformat : format.isIEEE = true := by ieee_format) :
    toReal (left - right) = Model.roundAt format (toReal left - toReal right) := by
  unfold toReal isFinite at *
  rw [toModel_hSub] at hresult ⊢
  exact Model.toReal_sub_eq_roundAt _ _ hformat hresult

/-- A finite configured product is the nearest-even rounding of the exact real product. -/
theorem toReal_mul_eq_roundAt {left right : Value}
    [cap : ExecFloat.Mul (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.mul]
    (hresult : isFinite (left * right) = true) (hformat : format.isIEEE = true := by ieee_format) :
    toReal (left * right) = Model.roundAt format (toReal left * toReal right) := by
  unfold toReal isFinite at *
  rw [toModel_hMul] at hresult ⊢
  exact Model.toReal_mul_eq_roundAt _ _ hformat hresult

/--
A finite configured quotient by a finite divisor is the nearest-even rounding of the exact real
quotient. The finite result forces a nonzero divisor.
-/
theorem toReal_div_eq_roundAt {left right : Value}
    [cap : ExecFloat.Div (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.div]
    (hright : isFinite right = true) (hresult : isFinite (left / right) = true)
    (hformat : format.isIEEE = true := by ieee_format) :
    toReal (left / right) = Model.roundAt format (toReal left / toReal right) := by
  unfold toReal isFinite at *
  rw [toModel_hDiv] at hresult ⊢
  exact Model.toReal_div_eq_roundAt _ _ hformat hright hresult

/-- A finite configured fused multiply-add is the nearest-even rounding of the exact real
`left * right + addend`. -/
theorem toReal_fma_eq_roundAt {left right addend : Value}
    [cap : ExecFloat.Fma (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.fma]
    (hresult : isFinite (fma left right addend) = true)
    (hformat : format.isIEEE = true := by ieee_format) :
    toReal (fma left right addend) =
      Model.roundAt format (toReal left * toReal right + toReal addend) := by
  unfold toReal isFinite at *
  rw [toModel_fma] at hresult ⊢
  exact Model.toReal_fma_eq_roundAt _ _ _ hformat hresult

/--
The configured square root of a finite zero or positive value is the nearest-even rounding of the
exact real square root. The result is always finite.
-/
theorem toReal_sqrt_eq_roundAt {value : Value}
    [cap : ExecFloat.Sqrt (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.sqrt]
    (hvalue : isFinite value = true) (hdomain : isZero value = true ∨ signBit value = false)
    (hformat : format.isIEEE = true := by ieee_format) :
    toReal (sqrt value) = Model.roundAt format (Real.sqrt (toReal value)) := by
  unfold toReal isFinite isZero signBit at *
  rw [toModel_sqrt]
  exact Model.toReal_sqrt_eq_roundAt _ hformat hvalue hdomain

/-- A finite configured sum is within half an ulp of the exact real sum. -/
theorem abs_toReal_add_sub_le {left right : Value}
    [cap : ExecFloat.Add (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.add]
    (hresult : isFinite (left + right) = true) (hformat : format.isIEEE = true := by ieee_format) :
    |toReal (left + right) - (toReal left + toReal right)| ≤
      Model.halfUlpAt format (toReal left + toReal right) := by
  rw [toReal_add_eq_roundAt hresult]
  exact Model.abs_roundAt_sub_le format _

/-- A finite configured difference is within half an ulp of the exact real difference. -/
theorem abs_toReal_sub_sub_le {left right : Value}
    [cap : ExecFloat.Sub (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.sub]
    (hresult : isFinite (left - right) = true) (hformat : format.isIEEE = true := by ieee_format) :
    |toReal (left - right) - (toReal left - toReal right)| ≤
      Model.halfUlpAt format (toReal left - toReal right) := by
  rw [toReal_sub_eq_roundAt hresult]
  exact Model.abs_roundAt_sub_le format _

/-- A finite configured product is within half an ulp of the exact real product. -/
theorem abs_toReal_mul_sub_le {left right : Value}
    [cap : ExecFloat.Mul (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.mul]
    (hresult : isFinite (left * right) = true) (hformat : format.isIEEE = true := by ieee_format) :
    |toReal (left * right) - toReal left * toReal right| ≤
      Model.halfUlpAt format (toReal left * toReal right) := by
  rw [toReal_mul_eq_roundAt hresult]
  exact Model.abs_roundAt_sub_le format _

/--
A finite configured quotient by a finite divisor is within half an ulp of the exact real quotient.
-/
theorem abs_toReal_div_sub_le {left right : Value}
    [cap : ExecFloat.Div (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.div]
    (hright : isFinite right = true) (hresult : isFinite (left / right) = true)
    (hformat : format.isIEEE = true := by ieee_format) :
    |toReal (left / right) - toReal left / toReal right| ≤
      Model.halfUlpAt format (toReal left / toReal right) := by
  rw [toReal_div_eq_roundAt hright hresult]
  exact Model.abs_roundAt_sub_le format _

/-- A finite configured fused multiply-add is within half an ulp of the exact real
`left * right + addend`. -/
theorem abs_toReal_fma_sub_le {left right addend : Value}
    [cap : ExecFloat.Fma (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.fma]
    (hresult : isFinite (fma left right addend) = true)
    (hformat : format.isIEEE = true := by ieee_format) :
    |toReal (fma left right addend) - (toReal left * toReal right + toReal addend)| ≤
      Model.halfUlpAt format (toReal left * toReal right + toReal addend) := by
  rw [toReal_fma_eq_roundAt hresult]
  exact Model.abs_roundAt_sub_le format _

/--
The configured square root of a finite zero or positive value is within half an ulp of the exact
real square root.
-/
theorem abs_toReal_sqrt_sub_le {value : Value}
    [cap : ExecFloat.Sqrt (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.sqrt]
    (hvalue : isFinite value = true) (hdomain : isZero value = true ∨ signBit value = false)
    (hformat : format.isIEEE = true := by ieee_format) :
    |toReal (sqrt value) - Real.sqrt (toReal value)| ≤
      Model.halfUlpAt format (Real.sqrt (toReal value)) := by
  rw [toReal_sqrt_eq_roundAt hvalue hdomain]
  exact Model.abs_roundAt_sub_le format _

/-! ## Exact operations -/

/-- Adding a finite configured value to a zero is exact. -/
theorem toReal_add_of_isZero_left {left right : Value}
    [cap : ExecFloat.Add (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.add]
    (hleft : isZero left = true) (hright : isFinite right = true)
    (hformat : format.isIEEE = true := by ieee_format) :
    toReal (left + right) = toReal right := by
  unfold toReal isFinite isZero at *
  rw [toModel_hAdd]
  exact Model.toReal_add_of_isZero_left _ _ hformat hleft hright

/-- Adding a zero to a finite configured value is exact. -/
theorem toReal_add_of_isZero_right {left right : Value}
    [cap : ExecFloat.Add (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.add]
    (hleft : isFinite left = true) (hright : isZero right = true)
    (hformat : format.isIEEE = true := by ieee_format) :
    toReal (left + right) = toReal left := by
  unfold toReal isFinite isZero at *
  rw [toModel_hAdd]
  exact Model.toReal_add_of_isZero_right _ _ hformat hleft hright

/-- Subtracting a finite configured value from a zero is exact negation. -/
theorem toReal_sub_of_isZero_left {left right : Value}
    [cap : ExecFloat.Sub (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.sub]
    (hleft : isZero left = true) (hright : isFinite right = true)
    (hformat : format.isIEEE = true := by ieee_format) :
    toReal (left - right) = -toReal right := by
  unfold toReal isFinite isZero at *
  rw [toModel_hSub]
  exact Model.toReal_sub_of_isZero_left _ _ hformat hleft hright

/-- Subtracting a zero from a finite configured value is exact. -/
theorem toReal_sub_of_isZero_right {left right : Value}
    [cap : ExecFloat.Sub (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.sub]
    (hleft : isFinite left = true) (hright : isZero right = true)
    (hformat : format.isIEEE = true := by ieee_format) :
    toReal (left - right) = toReal left := by
  unfold toReal isFinite isZero at *
  rw [toModel_hSub]
  exact Model.toReal_sub_of_isZero_right _ _ hformat hleft hright

/-- Subtracting a finite configured value from itself gives exactly zero. -/
theorem toReal_sub_self {left : Value}
    [cap : ExecFloat.Sub (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.sub]
    (hleft : isFinite left = true) (hformat : format.isIEEE = true := by ieee_format) :
    toReal (left - left) = 0 := by
  unfold toReal isFinite at *
  rw [toModel_hSub]
  exact Model.toReal_sub_self hformat hleft

/-- Multiplying a configured zero by a finite configured value gives exactly zero. -/
theorem toReal_mul_of_isZero_left {left right : Value}
    [cap : ExecFloat.Mul (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.mul]
    (hleft : isZero left = true) (hright : isFinite right = true)
    (hformat : format.isIEEE = true := by ieee_format) :
    toReal (left * right) = 0 := by
  unfold toReal isFinite isZero at *
  rw [toModel_hMul]
  exact Model.toReal_mul_of_isZero_left _ _ hformat hleft hright

/-- Multiplying a finite configured value by a zero gives exactly zero. -/
theorem toReal_mul_of_isZero_right {left right : Value}
    [cap : ExecFloat.Mul (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.mul]
    (hleft : isFinite left = true) (hright : isZero right = true)
    (hformat : format.isIEEE = true := by ieee_format) :
    toReal (left * right) = 0 := by
  unfold toReal isFinite isZero at *
  rw [toModel_hMul]
  exact Model.toReal_mul_of_isZero_right _ _ hformat hleft hright

/-- Multiplying a configured value of magnitude one by a finite configured value is exact. -/
theorem toReal_mul_of_abs_toReal_eq_one_left {left right : Value}
    [cap : ExecFloat.Mul (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.mul]
    (hleft : isFinite left = true) (hright : isFinite right = true) (hone : |toReal left| = 1)
    (hformat : format.isIEEE = true := by ieee_format) :
    toReal (left * right) = toReal left * toReal right := by
  unfold toReal isFinite at *
  rw [toModel_hMul]
  exact Model.toReal_mul_of_abs_toReal_eq_one_left _ _ hformat hleft hright hone

/-- Multiplying a finite configured value by a configured value of magnitude one is exact. -/
theorem toReal_mul_of_abs_toReal_eq_one_right {left right : Value}
    [cap : ExecFloat.Mul (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.mul]
    (hleft : isFinite left = true) (hright : isFinite right = true) (hone : |toReal right| = 1)
    (hformat : format.isIEEE = true := by ieee_format) :
    toReal (left * right) = toReal left * toReal right := by
  unfold toReal isFinite at *
  rw [toModel_hMul]
  exact Model.toReal_mul_of_abs_toReal_eq_one_right _ _ hformat hleft hright hone

/-- Dividing a finite configured value by a configured value of magnitude one is exact. -/
theorem toReal_div_of_abs_toReal_eq_one_right {left right : Value}
    [cap : ExecFloat.Div (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.div]
    (hleft : isFinite left = true) (hright : isFinite right = true) (hone : |toReal right| = 1)
    (hformat : format.isIEEE = true := by ieee_format) :
    toReal (left / right) = toReal left / toReal right := by
  unfold toReal isFinite at *
  rw [toModel_hDiv]
  exact Model.toReal_div_of_abs_toReal_eq_one_right _ _ hformat hleft hright hone

/-- The configured square root of a zero is exactly zero. -/
theorem toReal_sqrt_of_isZero {value : Value}
    [cap : ExecFloat.Sqrt (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.sqrt]
    (hzero : isZero value = true) :
    toReal (sqrt value) = 0 := by
  unfold toReal isZero at *
  rw [toModel_sqrt]
  exact Model.toReal_sqrt_of_isZero _ hzero

/-- The configured square root of a finite zero or positive value is finite. -/
theorem isFinite_sqrt {value : Value}
    [cap : ExecFloat.Sqrt (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.sqrt]
    (hvalue : isFinite value = true) (hdomain : isZero value = true ∨ signBit value = false)
    (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (sqrt value) = true := by
  unfold isFinite isZero signBit at *
  rw [toModel_sqrt]
  exact Model.isFinite_sqrt_of_isFinite _ hformat hvalue hdomain

/-! The format-generic call `ExecFloat.sqrt value` is `sqrt value` at its default arguments, so
the theorems above restate for it. -/

/-- `toReal_sqrt_eq_roundAt` for the format-generic call `ExecFloat.sqrt`. -/
theorem toReal_execFloat_sqrt_eq_roundAt {value : Value}
    [cap : ExecFloat.Sqrt (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.sqrt]
    (hvalue : isFinite value = true) (hdomain : isZero value = true ∨ signBit value = false)
    (hformat : format.isIEEE = true := by ieee_format) :
    toReal (ExecFloat.sqrt value) = Model.roundAt format (Real.sqrt (toReal value)) :=
  toReal_sqrt_eq_roundAt hvalue hdomain

/-- `abs_toReal_sqrt_sub_le` for the format-generic call `ExecFloat.sqrt`. -/
theorem abs_toReal_execFloat_sqrt_sub_le {value : Value}
    [cap : ExecFloat.Sqrt (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.sqrt]
    (hvalue : isFinite value = true) (hdomain : isZero value = true ∨ signBit value = false)
    (hformat : format.isIEEE = true := by ieee_format) :
    |toReal (ExecFloat.sqrt value) - Real.sqrt (toReal value)| ≤
      Model.halfUlpAt format (Real.sqrt (toReal value)) :=
  abs_toReal_sqrt_sub_le hvalue hdomain

/-- `toReal_sqrt_of_isZero` for the format-generic call `ExecFloat.sqrt`. -/
theorem toReal_execFloat_sqrt_of_isZero {value : Value}
    [cap : ExecFloat.Sqrt (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.sqrt]
    (hzero : isZero value = true) :
    toReal (ExecFloat.sqrt value) = 0 :=
  toReal_sqrt_of_isZero hzero

/-- `isFinite_sqrt` for the format-generic call `ExecFloat.sqrt`. -/
theorem isFinite_execFloat_sqrt {value : Value}
    [cap : ExecFloat.Sqrt (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.sqrt]
    (hvalue : isFinite value = true) (hdomain : isZero value = true ∨ signBit value = false)
    (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (ExecFloat.sqrt value) = true :=
  isFinite_sqrt hvalue hdomain

end Rounding

end FloatLib.Floats.ExecFloat.Binary
