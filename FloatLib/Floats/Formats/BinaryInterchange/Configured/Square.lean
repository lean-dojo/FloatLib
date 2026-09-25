/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Proof.Arithmetic
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.Instances
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.CoreProof
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Square

/-!
# Squaring configured binary values

Word and model carriers transport the unary square kernel through their lossless codec.
Byte tables and limb carriers retain their selected multiplication kernel. Both routes preserve
the complete configured multiplication result.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Floats.Formats.BinaryInterchange

variable {format : FloatFormat} {plan : Configured.StoragePlan format}
    [FloatLib.Floats.ExecFloat.Backend.PolicyFor
      (Configured.Family format (Configured.Code plan) plan)]

local notation "Value" =>
  ExecFloat.Binary format.expWidth format.fracWidth format.encoding format.exponentBias
    format.expWidth_ge_two format.fracWidth_pos format.exponentBias_pos
    format.exponentBias_le_maxFinite plan (Configured.Code plan)

/-- Square with one nearest-even rounding, retaining the descriptor's full encoding policy. -/
@[inline] def square (value : Value) : Value :=
  if (match plan with | .byte _ | .limbs _ => true | _ => false) then
    ExecFloat.mul value value
  else
    ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.square value

/-- Configured squaring agrees with the certified multiplication specification. -/
theorem square_eq_spec (value : Value) :
    square value = Configured.Spec.mul value value := by
  unfold square
  split_ifs
  · exact ExecFloat.Proof.mul_eq_spec value value
  · apply ModelCodec.decode_injective
      (F := Configured.Family format (Configured.Code plan) plan)
      (Model := Model format) (plan := plan)
    simp [Configured.Spec.mul, Model.square_eq_spec]

/-- Squaring preserves the complete result of the selected multiplication capability. -/
theorem square_eq_mul (value : Value) :
    square value = ExecFloat.mul value value :=
  (square_eq_spec value).trans (ExecFloat.Proof.mul_eq_spec value value).symm

/-- Decoding a configured square gives the exact encoded model square. -/
@[simp, grind =] theorem toModel_square (value : Value) :
    toModel (square value) = Model.square (toModel value) := by
  rw [square_eq_spec, Model.square_eq_spec]
  simp [Configured.Spec.mul, toModel, Configured.Family.toModel]

end FloatLib.Floats.ExecFloat.Binary
