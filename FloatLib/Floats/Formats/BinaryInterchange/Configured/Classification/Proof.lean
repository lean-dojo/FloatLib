/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Classification.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Classification.Proof
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.CoreProof

/-!
# Classification refinement for configured binary values

Every storage codec preserves classification. The ten class characterizations and the exact
numerical threshold theorems are transported from the descriptor model, with no assumptions on
storage width, bias, or exceptional-value policy beyond a valid descriptor.

Canonicality carries no information here. An implicit-leading-bit binary layout has no
non-canonical words, so `isCanonical` is the constant `true` predicate (`isCanonical_eq_true`),
and the canonicality lemmas below record that fact rather than an invariant a codec must keep.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Floats.Formats.BinaryInterchange

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" => ExecFloat (Configured.Family format code plan)

/-- Configured classification is the descriptor-model classification. -/
theorem classify_eq_model (x : Value) : classify x = Model.classify (toModel x) := rfl

/-- Configured normality is the descriptor-model normality predicate. -/
theorem isNormal_eq_model (x : Value) : isNormal x = Model.isNormal (toModel x) := rfl

/-- Configured canonicality is that of the descriptor model, which is always `true`. -/
theorem isCanonical_eq_model (x : Value) :
    isCanonical x = Model.isCanonical (toModel x) := rfl

/-- Packing any descriptor model preserves its class. -/
@[simp] theorem classify_ofModel (x : Model format) :
    classify (ofModel (plan := plan) (code := code) x) = Model.classify x := by
  simp [classify]

/-- Packing a descriptor model preserves its normality. -/
@[simp] theorem isNormal_ofModel (x : Model format) :
    isNormal (ofModel (plan := plan) (code := code) x) = Model.isNormal x := by
  simp [isNormal]

/-- Packing a descriptor model keeps its canonicality; both sides are `true`. -/
@[simp] theorem isCanonical_ofModel (x : Model format) :
    isCanonical (ofModel (plan := plan) (code := code) x) = Model.isCanonical x := by
  simp [isCanonical]

/-- All ten configured classification results agree with the existing configured predicates. -/
theorem classify_eq_iff (x : Value) (c : FloatLib.Numerics.IEEEClass) :
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
      | .positiveNormal => isNormal x = true ∧ signBit x = false :=
  Model.classify_eq_iff (toModel x) c

/-- The signaling class is exactly the configured signaling predicate. -/
@[simp] theorem classify_eq_signalingNaN_iff (x : Value) :
    classify x = .signalingNaN ↔ isSNaN x = true := classify_eq_iff x _

/-- The quiet class is exactly the configured quiet-NaN predicate. -/
@[simp] theorem classify_eq_quietNaN_iff (x : Value) :
    classify x = .quietNaN ↔ isQNaN x = true := classify_eq_iff x _

/-- Negative infinity retains its stored negative sign. -/
@[simp] theorem classify_eq_negativeInfinity_iff (x : Value) :
    classify x = .negativeInfinity ↔ isInf x = true ∧ signBit x = true :=
  classify_eq_iff x _

/-- Positive infinity retains its stored positive sign. -/
@[simp] theorem classify_eq_positiveInfinity_iff (x : Value) :
    classify x = .positiveInfinity ↔ isInf x = true ∧ signBit x = false :=
  classify_eq_iff x _

/-- Negative zero is a zero with a negative stored sign under the configured policy. -/
@[simp] theorem classify_eq_negativeZero_iff (x : Value) :
    classify x = .negativeZero ↔ isZero x = true ∧ signBit x = true :=
  classify_eq_iff x _

/-- Positive zero is a zero with a positive stored sign. -/
@[simp] theorem classify_eq_positiveZero_iff (x : Value) :
    classify x = .positiveZero ↔ isZero x = true ∧ signBit x = false :=
  classify_eq_iff x _

/-- Negative subnormal classification agrees with the configured predicates. -/
@[simp] theorem classify_eq_negativeSubnormal_iff (x : Value) :
    classify x = .negativeSubnormal ↔ isSubnormal x = true ∧ signBit x = true :=
  classify_eq_iff x _

/-- Positive subnormal classification agrees with the configured predicates. -/
@[simp] theorem classify_eq_positiveSubnormal_iff (x : Value) :
    classify x = .positiveSubnormal ↔ isSubnormal x = true ∧ signBit x = false :=
  classify_eq_iff x _

/-- Negative normal classification uses the configured policy and negative sign. -/
@[simp] theorem classify_eq_negativeNormal_iff (x : Value) :
    classify x = .negativeNormal ↔ isNormal x = true ∧ signBit x = true :=
  classify_eq_iff x _

/-- Positive normal classification uses the configured policy and positive sign. -/
@[simp] theorem classify_eq_positiveNormal_iff (x : Value) :
    classify x = .positiveNormal ↔ isNormal x = true ∧ signBit x = false :=
  classify_eq_iff x _

/-- Normality excludes zeros, subnormals, infinities, and NaNs for every storage codec. -/
theorem isNormal_iff (x : Value) :
    isNormal x = true ↔ isFinite x = true ∧ isZero x = false ∧ isSubnormal x = false :=
  Model.isNormal_iff (toModel x)

/-- Configured finiteness is the union of the three finite classes. -/
theorem isFinite_eq_zero_or_subnormal_or_normal (x : Value) :
    isFinite x = (isZero x || isSubnormal x || isNormal x) :=
  Model.isFinite_eq_zero_or_subnormal_or_normal (toModel x)

/-- Configured normality is an exact finite magnitude at or above the normal threshold. -/
theorem isNormal_iff_exactValue (x : Value) :
    isNormal x = true ↔ ∃ d, exactValue x = .finite d ∧
      (2 : ℚ) ^ format.minNormalExponent ≤ |d.toRat| := by
  simpa only [isNormal, exactValue, Model.exactValue_eq_finite_iff] using
    Model.isNormal_iff_exists_toDyadic (toModel x)

/-- Configured subnormality is an exact positive magnitude below the normal threshold. -/
theorem isSubnormal_iff_exactValue (x : Value) :
    isSubnormal x = true ↔ ∃ d, exactValue x = .finite d ∧
      0 < |d.toRat| ∧ |d.toRat| < (2 : ℚ) ^ format.minNormalExponent := by
  simpa only [isSubnormal, exactValue, Model.exactValue_eq_finite_iff] using
    Model.isSubnormal_iff_exists_toDyadic (toModel x)

/-- Every configured class is determined by its exact value and the descriptor threshold. -/
theorem classify_eq_match_exactValue (x : Value) :
    classify x =
      match exactValue x with
      | .nan _ signaling _ => if signaling then .signalingNaN else .quietNaN
      | .infinity sign => if sign then .negativeInfinity else .positiveInfinity
      | .finite d =>
          if d.toRat = 0 then
            if d.negative then .negativeZero else .positiveZero
          else if |d.toRat| < (2 : ℚ) ^ format.minNormalExponent then
            if d.negative then .negativeSubnormal else .positiveSubnormal
          else
            if d.negative then .negativeNormal else .positiveNormal :=
  Model.classify_eq_match_exactValue (toModel x)

/--
Every configured implicit-leading-bit binary word is canonical, including every NaN payload:
`isCanonical` is the constant `true` predicate.
-/
@[simp] theorem isCanonical_eq_true (x : Value) : isCanonical x = true := rfl

/--
Canonicality agrees with lossless reconstruction from the full interchange word.

Both sides hold for every value (`isCanonical_eq_true` and `ofNatBits_toNatBits`), so this
explains why the constant predicate is right; it excludes no word.
-/
theorem isCanonical_iff_word_roundtrip (x : Value) :
    isCanonical x = true ↔ ofNatBits (toNatBits x) = x := by
  simp [ofNatBits_toNatBits]

end FloatLib.Floats.ExecFloat.Binary
