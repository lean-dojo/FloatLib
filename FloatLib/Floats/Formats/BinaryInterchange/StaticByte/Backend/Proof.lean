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
    Backend.add left right = Spec.add left right :=
  liftBinary_eq_spec (Family.kernels (F := F)).add
    FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.add
    (Family.kernels (F := F)).add_eq_spec left right

/-- Static-byte subtraction agrees with the family's independent reference specification. -/
theorem Backend.sub_eq_spec {F : Type u} [Family F]
    (left right : FloatLib.Floats.ExecFloat F) :
    Backend.sub left right = Spec.sub left right :=
  liftBinary_eq_spec (Family.kernels (F := F)).sub
    FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.sub
    (Family.kernels (F := F)).sub_eq_spec left right

/-- Static-byte multiplication agrees with the family's independent reference specification. -/
theorem Backend.mul_eq_spec {F : Type u} [Family F]
    (left right : FloatLib.Floats.ExecFloat F) :
    Backend.mul left right = Spec.mul left right :=
  liftBinary_eq_spec (Family.kernels (F := F)).mul
    FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.mul
    (Family.kernels (F := F)).mul_eq_spec left right

/-- Static-byte division agrees with the family's independent reference specification. -/
theorem Backend.div_eq_spec {F : Type u} [Family F]
    (left right : FloatLib.Floats.ExecFloat F) :
    Backend.div left right = Spec.div left right :=
  liftBinary_eq_spec (Family.kernels (F := F)).div
    FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.div
    (Family.kernels (F := F)).div_eq_spec left right

/-- Static-byte square root agrees with the family's independent reference specification. -/
theorem Backend.sqrt_eq_spec {F : Type u} [Family F]
    (value : FloatLib.Floats.ExecFloat F) :
    Backend.sqrt value = Spec.sqrt value :=
  liftUnary_eq_spec (Family.kernels (F := F)).sqrt
    FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.sqrt
    (Family.kernels (F := F)).sqrt_eq_spec value

/-- Static-byte fused multiply-add agrees with the family's independent reference specification. -/
theorem Backend.fma_eq_spec {F : Type u} [Family F]
    (left right addend : FloatLib.Floats.ExecFloat F) :
    Backend.fma left right addend = Spec.fma left right addend :=
  liftTernary_eq_spec (Family.kernels (F := F)).fma
    FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.fma
    (Family.kernels (F := F)).fma_eq_spec left right addend

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
