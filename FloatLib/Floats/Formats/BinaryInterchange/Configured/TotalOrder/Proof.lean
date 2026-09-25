/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.TotalOrder.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.TotalOrder.Proof
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.CoreProof
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Storage.Family.Proof

/-!
# Configured total-order refinement

Packing and decoding preserve both predicates exactly. Order laws and numerical, zero, and NaN
rules are transported from the descriptor model, independently of the chosen runtime carrier.
Mutual magnitude comparison identifies absolute exact values, including NaN metadata; opposite
signs can tie.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Floats.Formats.BinaryInterchange

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" => ExecFloat (Configured.Family format code plan)

/-- Configured total ordering is exactly the descriptor-model predicate. -/
theorem totalOrder_eq_model (x y : Value) :
    totalOrder x y = Model.totalOrder (toModel x) (toModel y) := rfl

/-- Configured magnitude ordering is exactly the descriptor-model predicate. -/
theorem totalOrderMag_eq_model (x y : Value) :
    totalOrderMag x y = Model.totalOrderMag (toModel x) (toModel y) := rfl

/-- The configured predicate uses the shared complete exact-value order. -/
theorem totalOrder_eq_exactValue (x y : Value) :
    totalOrder x y = Model.ExactValue.totalOrder (exactValue x) (exactValue y) := rfl

/-- The configured magnitude predicate uses the shared exact magnitude order. -/
theorem totalOrderMag_eq_exactValue (x y : Value) :
    totalOrderMag x y = Model.ExactValue.totalOrderMag (exactValue x) (exactValue y) := rfl

/-- Packing two models preserves their total-order comparison. -/
@[simp] theorem totalOrder_ofModel (x y : Model format) :
    totalOrder (ofModel (plan := plan) (code := code) x) (ofModel y) =
      Model.totalOrder x y := by
  simp [totalOrder]

/-- Packing two models preserves their magnitude comparison. -/
@[simp] theorem totalOrderMag_ofModel (x y : Model format) :
    totalOrderMag (ofModel (plan := plan) (code := code) x) (ofModel y) =
      Model.totalOrderMag x y := by
  simp [totalOrderMag]

/-- Every configured datum precedes itself, including signaling NaNs. -/
@[simp] theorem totalOrder_refl (x : Value) : totalOrder x x = true :=
  Model.totalOrder_refl _

/-- Configured total ordering compares every pair of values. -/
theorem totalOrder_total (x y : Value) :
    totalOrder x y = true ∨ totalOrder y x = true := Model.totalOrder_total _ _

/-- Configured total ordering is transitive. -/
theorem totalOrder_trans {x y z : Value}
    (hxy : totalOrder x y = true) (hyz : totalOrder y z = true) :
    totalOrder x z = true := Model.totalOrder_trans hxy hyz

/-- Mutual total ordering identifies the configured value, including its complete encoding. -/
theorem totalOrder_antisymm {x y : Value}
    (hxy : totalOrder x y = true) (hyx : totalOrder y x = true) : x = y :=
  Configured.Family.toModel_injective (Model.totalOrder_antisymm hxy hyx)

/-- Mutual total comparison is equivalent to equality for every configured storage plan. -/
theorem totalOrder_both_iff (x y : Value) :
    totalOrder x y = true ∧ totalOrder y x = true ↔ x = y := by
  constructor
  · rintro ⟨hxy, hyx⟩
    exact totalOrder_antisymm hxy hyx
  · rintro rfl
    simp

/-- Strict model numerical comparison is respected by configured total order. -/
theorem totalOrder_of_compare_eq_lt {x y : Value}
    (h : Model.compare (toModel x) (toModel y) = some .lt) :
    totalOrder x y = true := Model.totalOrder_of_compare_eq_lt h

/-- Reversed strict numerical comparison fails configured total order. -/
theorem totalOrder_eq_false_of_compare_eq_gt {x y : Value}
    (h : Model.compare (toModel x) (toModel y) = some .gt) :
    totalOrder x y = false := Model.totalOrder_eq_false_of_compare_eq_gt h

/-- Configured zero ordering depends only on the stored sign flags. -/
theorem totalOrder_zero_iff {x y : Value} (hx : isZero x = true) (hy : isZero y = true) :
    totalOrder x y = (signBit x || !signBit y) := Model.totalOrder_zero_iff hx hy

/-- The configured NaN rule preserves sign, signaling class, and full fraction payload. -/
theorem totalOrder_nan_iff {x y : Value} (hx : isNaN x = true) (hy : isNaN y = true) :
    totalOrder x y = true ↔
      (signBit x = true ∧ signBit y = false) ∨ signBit x = signBit y ∧
        (if signBit x then
          (isSignalingNaN x = false ∧ isSignalingNaN y = true) ∨
            isSignalingNaN x = isSignalingNaN y ∧
              Model.fracField (toModel y) ≤ Model.fracField (toModel x)
        else
          (isSignalingNaN x = true ∧ isSignalingNaN y = false) ∨
            isSignalingNaN x = isSignalingNaN y ∧
              Model.fracField (toModel x) ≤ Model.fracField (toModel y)) :=
  Model.totalOrder_nan_iff hx hy

/-- Magnitude comparison is reflexive on every configured value. -/
@[simp] theorem totalOrderMag_refl (x : Value) : totalOrderMag x x = true :=
  Model.totalOrderMag_refl _

/-- Magnitude comparison is total on configured values, including NaNs. -/
theorem totalOrderMag_total (x y : Value) :
    totalOrderMag x y = true ∨ totalOrderMag y x = true := Model.totalOrderMag_total _ _

/-- Configured magnitude comparison is transitive. -/
theorem totalOrderMag_trans {x y z : Value}
    (hxy : totalOrderMag x y = true) (hyz : totalOrderMag y z = true) :
    totalOrderMag x z = true := Model.totalOrderMag_trans hxy hyz

/-- Mutual configured magnitude comparison identifies absolute exact data. -/
theorem totalOrderMag_both_iff_exactValue_abs_eq (x y : Value) :
    totalOrderMag x y = true ∧ totalOrderMag y x = true ↔
      Model.ExactValue.abs (exactValue x) = Model.ExactValue.abs (exactValue y) :=
  Model.totalOrderMag_both_iff_exactValue_abs_eq _ _

/-- In a signed-zero format, magnitude ordering agrees with model absolute-value ordering. -/
theorem totalOrderMag_eq_totalOrder_model_abs (x y : Value)
    (hformat : format.supportsSignedZero = true) :
    totalOrderMag x y = Model.totalOrder (Model.abs (toModel x)) (Model.abs (toModel y)) :=
  Model.totalOrderMag_eq_totalOrder_abs _ _ hformat

/-- All configured zeros tie under magnitude comparison. -/
theorem totalOrderMag_zero {x y : Value} (hx : isZero x = true) (hy : isZero y = true) :
    totalOrderMag x y = true := Model.totalOrderMag_zero hx hy

/-- Configured NaN magnitudes compare signaling class, then increasing fraction payload. -/
theorem totalOrderMag_nan_iff {x y : Value} (hx : isNaN x = true) (hy : isNaN y = true) :
    totalOrderMag x y = true ↔
      (isSignalingNaN x = true ∧ isSignalingNaN y = false) ∨
        isSignalingNaN x = isSignalingNaN y ∧
          Model.fracField (toModel x) ≤ Model.fracField (toModel y) :=
  Model.totalOrderMag_nan_iff hx hy

end FloatLib.Floats.ExecFloat.Binary
