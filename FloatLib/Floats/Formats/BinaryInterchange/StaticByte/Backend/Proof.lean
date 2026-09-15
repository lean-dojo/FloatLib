/-
Copyright (c) 2026 Robert Weller
Released under MIT license as described in the file LICENSE.
Authors: Robert Weller
-/
module

public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.Backend.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.Core.Proof

/-!
# Static-byte backend correctness

Each supplied byte operation decodes to the model-level reference result. The proofs use the
operation's certificate, so they apply to exhaustive tables and arithmetic kernels alike.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.StaticByte

universe u
/-- Static-byte addition agrees with the family's independent reference specification. -/
theorem Backend.add_eq_spec {F : Type u} [Family F]
    (left right : FloatLib.Floats.ExecFloat F) :
    Backend.add left right = Spec.add left right := by
  apply toModel_injective (F := F)
  simp only [Spec.add, toModel_ofModel]
  change byteCodeToModel ((Family.kernels (F := F)).add left.raw right.raw) =
    FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.add
      (byteCodeToModel left.raw) (byteCodeToModel right.raw)
  exact (Family.kernels (F := F)).add_eq_spec left.raw right.raw

/-- Static-byte subtraction agrees with the family's independent reference specification. -/
theorem Backend.sub_eq_spec {F : Type u} [Family F]
    (left right : FloatLib.Floats.ExecFloat F) :
    Backend.sub left right = Spec.sub left right := by
  apply toModel_injective (F := F)
  simp only [Spec.sub, toModel_ofModel]
  change byteCodeToModel ((Family.kernels (F := F)).sub left.raw right.raw) =
    FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.sub
      (byteCodeToModel left.raw) (byteCodeToModel right.raw)
  exact (Family.kernels (F := F)).sub_eq_spec left.raw right.raw

/-- Static-byte multiplication agrees with the family's independent reference specification. -/
theorem Backend.mul_eq_spec {F : Type u} [Family F]
    (left right : FloatLib.Floats.ExecFloat F) :
    Backend.mul left right = Spec.mul left right := by
  apply toModel_injective (F := F)
  simp only [Spec.mul, toModel_ofModel]
  change byteCodeToModel ((Family.kernels (F := F)).mul left.raw right.raw) =
    FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.mul
      (byteCodeToModel left.raw) (byteCodeToModel right.raw)
  exact (Family.kernels (F := F)).mul_eq_spec left.raw right.raw

/-- Static-byte division agrees with the family's independent reference specification. -/
theorem Backend.div_eq_spec {F : Type u} [Family F]
    (left right : FloatLib.Floats.ExecFloat F) :
    Backend.div left right = Spec.div left right := by
  apply toModel_injective (F := F)
  simp only [Spec.div, toModel_ofModel]
  change byteCodeToModel ((Family.kernels (F := F)).div left.raw right.raw) =
    FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.div
      (byteCodeToModel left.raw) (byteCodeToModel right.raw)
  exact (Family.kernels (F := F)).div_eq_spec left.raw right.raw

/-- Static-byte square root agrees with the family's independent reference specification. -/
theorem Backend.sqrt_eq_spec {F : Type u} [Family F]
    (value : FloatLib.Floats.ExecFloat F) :
    Backend.sqrt value = Spec.sqrt value := by
  apply toModel_injective (F := F)
  simp only [Spec.sqrt, toModel_ofModel]
  change byteCodeToModel ((Family.kernels (F := F)).sqrt value.raw) =
    FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.sqrt
      (byteCodeToModel value.raw)
  exact (Family.kernels (F := F)).sqrt_eq_spec value.raw

/-- Static-byte fused multiply-add agrees with the family's independent reference specification. -/
theorem Backend.fma_eq_spec {F : Type u} [Family F]
    (left right addend : FloatLib.Floats.ExecFloat F) :
    Backend.fma left right addend = Spec.fma left right addend := by
  apply toModel_injective (F := F)
  simp only [Spec.fma, toModel_ofModel]
  change byteCodeToModel
      ((Family.kernels (F := F)).fma left.raw right.raw addend.raw) =
    FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.fma
      (byteCodeToModel left.raw) (byteCodeToModel right.raw)
      (byteCodeToModel addend.raw)
  exact (Family.kernels (F := F)).fma_eq_spec left.raw right.raw addend.raw

namespace Backend.Table

/-- A direct binary table agrees with the model operation certified by that table. -/
theorem binary_eq_spec {F : Type u} [Family F]
    {modelSpec :
      ModelValue (Family.format (F := F)) →
        ModelValue (Family.format (F := F)) →
          ModelValue (Family.format (F := F))}
    (width_le_eight : (Family.format (F := F)).bitWidth ≤ 8)
    (table : FloatLib.Floats.ExecFloat.Backend.TinyTable.CertifiedBinary
      (encoding (Family.format (F := F)) width_le_eight) modelSpec)
    (left right : FloatLib.Floats.ExecFloat F) :
    binary width_le_eight table left right =
      ofModel (modelSpec (toModel left) (toModel right)) :=
  liftBinaryTable_eq_spec width_le_eight table left right

/-- A direct unary table agrees with the model operation certified by that table. -/
theorem unary_eq_spec {F : Type u} [Family F]
    {modelSpec :
      ModelValue (Family.format (F := F)) →
        ModelValue (Family.format (F := F))}
    (width_le_eight : (Family.format (F := F)).bitWidth ≤ 8)
    (table : FloatLib.Floats.ExecFloat.Backend.TinyTable.CertifiedUnary
      (encoding (Family.format (F := F)) width_le_eight) modelSpec)
    (value : FloatLib.Floats.ExecFloat F) :
    unary width_le_eight table value =
      ofModel (modelSpec (toModel value)) :=
  liftUnaryTable_eq_spec width_le_eight table value

/-- A direct ternary table agrees with the model operation certified by that table. -/
theorem ternary_eq_spec {F : Type u} [Family F]
    {modelSpec :
      ModelValue (Family.format (F := F)) →
        ModelValue (Family.format (F := F)) →
          ModelValue (Family.format (F := F)) →
            ModelValue (Family.format (F := F))}
    (width_le_eight : (Family.format (F := F)).bitWidth ≤ 8)
    (table : FloatLib.Floats.ExecFloat.Backend.TinyTable.CertifiedTernary
      (encoding (Family.format (F := F)) width_le_eight) modelSpec)
    (left right addend : FloatLib.Floats.ExecFloat F) :
    ternary width_le_eight table left right addend =
      ofModel (modelSpec (toModel left) (toModel right) (toModel addend)) :=
  liftTernaryTable_eq_spec width_le_eight table left right addend

end Backend.Table

namespace Backend.Model

/-- A direct model adapter preserves any proved ternary specification. -/
theorem ternary_eq_spec {F : Type u} [Family F]
    {modelSpec :
      ModelValue (Family.format (F := F)) →
        ModelValue (Family.format (F := F)) →
          ModelValue (Family.format (F := F)) →
            ModelValue (Family.format (F := F))}
    (width_le_eight : (Family.format (F := F)).bitWidth ≤ 8)
    (op :
      ModelValue (Family.format (F := F)) →
        ModelValue (Family.format (F := F)) →
          ModelValue (Family.format (F := F)) →
            ModelValue (Family.format (F := F)))
    (op_eq_spec : ∀ left right addend,
      op left right addend = modelSpec left right addend)
    (left right addend : FloatLib.Floats.ExecFloat F) :
    ternary width_le_eight op left right addend =
      ofModel (modelSpec (toModel left) (toModel right) (toModel addend)) :=
  liftModelTernary_eq_spec width_le_eight op op_eq_spec left right addend

end Backend.Model

end FloatLib.Floats.Formats.BinaryInterchange.StaticByte
