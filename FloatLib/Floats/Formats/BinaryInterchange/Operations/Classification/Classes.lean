/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Classification.Predicates

/-!
# The ten binary classes

`classify_eq_iff` characterizes every result by the existing descriptor predicates.
The signed numerical classes retain the stored sign; the two NaN classes deliberately
ignore sign and payload. The result type is shared with decimal classification.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

variable {fmt : FloatFormat}

/-- Complete characterization of all ten mutually exclusive classification results. -/
theorem classify_eq_iff (x : Model fmt) (c : Numerics.IEEEClass) :
    classify x = c ↔
      match c with
      | .signalingNaN => isSNaN x = true
      | .quietNaN => isQNaN x = true
      | .negativeInfinity => isInf x = true ∧ signBit x = true
      | .positiveInfinity => isInf x = true ∧ signBit x = false
      | .negativeZero => isZero x = true ∧ signBit x = true
      | .positiveZero => isZero x = true ∧ signBit x = false
      | .negativeSubnormal => isSubnormal x = true ∧ signBit x = true
      | .positiveSubnormal => isSubnormal x = true ∧ signBit x = false
      | .negativeNormal => isNormal x = true ∧ signBit x = true
      | .positiveNormal => isNormal x = true ∧ signBit x = false := by
  have hfinite := isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x
  have hnan := isNaN_eq_false_of_isFinite_eq_true x
  have hinf := isInf_eq_false_of_isFinite_eq_true x
  have hzero := isFinite_eq_true_of_isZero_eq_true x
  have hsub := isFinite_of_isSubnormal (x := x)
  have hnormal := isNormal_iff x
  have hsignaling := isNaN_of_isSNaN (x := x)
  have hquiet := isQNaN_eq_nan_and_not_signaling x
  have hinfNaN := isNaN_eq_false_of_isInf_eq_true x
  have hzeroSub := isSubnormal_eq_false_of_isZero (x := x)
  unfold classify
  split_ifs <;> cases c <;> simp_all

/-- Classification as signaling NaN is exactly the existing signaling predicate. -/
@[simp] theorem classify_eq_signalingNaN_iff (x : Model fmt) :
    classify x = .signalingNaN ↔ isSNaN x = true :=
  classify_eq_iff x _

/-- Classification as quiet NaN is exactly the existing quiet-NaN predicate. -/
@[simp] theorem classify_eq_quietNaN_iff (x : Model fmt) :
    classify x = .quietNaN ↔ isQNaN x = true :=
  classify_eq_iff x _

/-- Negative infinity is infinity with the sign bit set. -/
@[simp] theorem classify_eq_negativeInfinity_iff (x : Model fmt) :
    classify x = .negativeInfinity ↔ isInf x = true ∧ signBit x = true :=
  classify_eq_iff x _

/-- Positive infinity is infinity with the sign bit clear. -/
@[simp] theorem classify_eq_positiveInfinity_iff (x : Model fmt) :
    classify x = .positiveInfinity ↔ isInf x = true ∧ signBit x = false :=
  classify_eq_iff x _

/-- Negative zero is a policy zero with the sign bit set; FNUZ has no such value. -/
@[simp] theorem classify_eq_negativeZero_iff (x : Model fmt) :
    classify x = .negativeZero ↔ isZero x = true ∧ signBit x = true :=
  classify_eq_iff x _

/-- Positive zero is a policy zero with the sign bit clear. -/
@[simp] theorem classify_eq_positiveZero_iff (x : Model fmt) :
    classify x = .positiveZero ↔ isZero x = true ∧ signBit x = false :=
  classify_eq_iff x _

/-- Negative subnormal classification retains the stored negative sign. -/
@[simp] theorem classify_eq_negativeSubnormal_iff (x : Model fmt) :
    classify x = .negativeSubnormal ↔ isSubnormal x = true ∧ signBit x = true :=
  classify_eq_iff x _

/-- Positive subnormal classification retains the stored positive sign. -/
@[simp] theorem classify_eq_positiveSubnormal_iff (x : Model fmt) :
    classify x = .positiveSubnormal ↔ isSubnormal x = true ∧ signBit x = false :=
  classify_eq_iff x _

/-- Negative normal classification uses policy-aware normality and the stored negative sign. -/
@[simp] theorem classify_eq_negativeNormal_iff (x : Model fmt) :
    classify x = .negativeNormal ↔ isNormal x = true ∧ signBit x = true :=
  classify_eq_iff x _

/-- Positive normal classification uses policy-aware normality and the stored positive sign. -/
@[simp] theorem classify_eq_positiveNormal_iff (x : Model fmt) :
    classify x = .positiveNormal ↔ isNormal x = true ∧ signBit x = false :=
  classify_eq_iff x _

/-- The two NaN classes exhaust precisely the NaN encodings. -/
theorem isNaN_iff_classify (x : Model fmt) :
    isNaN x = true ↔ classify x = .signalingNaN ∨ classify x = .quietNaN := by
  rw [classify_eq_signalingNaN_iff, classify_eq_quietNaN_iff,
    isQNaN_eq_nan_and_not_signaling]
  have hs := isNaN_of_isSNaN (x := x)
  cases hn : isNaN x <;> cases hsn : isSNaN x <;> simp_all

/-- The finite classes exhaust precisely zero, subnormal, and normal encodings. -/
theorem isFinite_iff_classify (x : Model fmt) :
    isFinite x = true ↔
      classify x = .negativeZero ∨ classify x = .positiveZero ∨
      classify x = .negativeSubnormal ∨ classify x = .positiveSubnormal ∨
      classify x = .negativeNormal ∨ classify x = .positiveNormal := by
  rw [isFinite_eq_zero_or_subnormal_or_normal]
  cases hs : signBit x <;> simp [hs, or_assoc]

end FloatLib.Floats.Formats.BinaryInterchange.Model
