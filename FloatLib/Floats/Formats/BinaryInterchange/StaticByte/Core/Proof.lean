/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.Core.Runtime

/-!
# Static-byte representation and lifting proofs

Byte/model round trips, certified table execution equations, injectivity, and lifting theorems
justify nominal FP8 and other static-byte families.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.StaticByte

open FloatLib.Numerics
open FloatLib.Floats.ExecFloat.Backend

universe u

/-- Every model code selected by a static-byte family fits in `UInt8`. -/
theorem model_toNatBits_lt_byte {F : Type u} [Family F]
    (value : ModelValue (Family.format (F := F))) :
    value.toNatBits < 256 := by
  have hpow :
      2 ^ (Family.format (F := F)).bitWidth ≤ 2 ^ 8 :=
    Nat.pow_le_pow_right (by decide) (Family.width_le_eight (F := F))
  exact lt_of_lt_of_le
    (FloatLib.Floats.Formats.BinaryInterchange.Model.toNatBits_lt_two_pow value)
    (by simpa using hpow)

/-- Encoding a model value as a byte code and decoding it returns the value. -/
@[simp] theorem byteCodeToModel_modelToByteCode
    (format : FloatFormat) (width_le_eight : format.bitWidth ≤ 8)
    (value : ModelValue format) :
    byteCodeToModel (modelToByteCode format width_le_eight value) = value := by
  unfold byteCodeToModel modelToByteCode
  rw [FloatLib.Numerics.StaticStorage.ByteCode.toNat_ofNat]
  exact FloatLib.Floats.Formats.BinaryInterchange.Model.ofNatBits_toNatBits value

/-- Running a certified binary table on byte codes decodes to the specification applied to the
decoded operands. -/
@[simp] theorem byteCodeToModel_runBinary
    {format : FloatFormat} {spec : ModelValue format → ModelValue format → ModelValue format}
    (width_le_eight : format.bitWidth ≤ 8)
    (kernel : TinyTable.CertifiedBinary (encoding format width_le_eight) spec)
    (left right : ByteCode format) :
    byteCodeToModel (runBinary width_le_eight kernel left right) =
      spec (byteCodeToModel left) (byteCodeToModel right) := by
  exact kernel.decodeCode_run left right

/-- Running a certified unary table on a byte code decodes to the specification applied to the
decoded operand. -/
@[simp] theorem byteCodeToModel_runUnary
    {format : FloatFormat} {spec : ModelValue format → ModelValue format}
    (width_le_eight : format.bitWidth ≤ 8)
    (kernel : TinyTable.CertifiedUnary (encoding format width_le_eight) spec)
    (value : ByteCode format) :
    byteCodeToModel (runUnary width_le_eight kernel value) =
      spec (byteCodeToModel value) := by
  exact kernel.decodeCode_run value

/-- Running a certified ternary table on byte codes decodes to the specification applied to the
decoded operands. -/
@[simp] theorem byteCodeToModel_runTernary
    {format : FloatFormat}
    {spec : ModelValue format → ModelValue format → ModelValue format → ModelValue format}
    (width_le_eight : format.bitWidth ≤ 8)
    (kernel : TinyTable.CertifiedTernary (encoding format width_le_eight) spec)
    (left right addend : ByteCode format) :
    byteCodeToModel (runTernary width_le_eight kernel left right addend) =
      spec (byteCodeToModel left) (byteCodeToModel right) (byteCodeToModel addend) := by
  exact
    kernel.decodeCode_run left right addend

/-- Decoding the byte-level lift of a ternary model operation gives that operation on the
decoded operands. -/
@[simp] theorem byteCodeToModel_modelTernary
    (format : FloatFormat) (width_le_eight : format.bitWidth ≤ 8)
    (op : ModelValue format → ModelValue format → ModelValue format → ModelValue format)
    (left right addend : ByteCode format) :
    byteCodeToModel (modelTernary format width_le_eight op left right addend) =
      op (byteCodeToModel left) (byteCodeToModel right) (byteCodeToModel addend) := by
  exact byteCodeToModel_modelToByteCode format width_le_eight _
/-- Encoding a model value as a family code and decoding it returns the value. -/
@[simp] theorem codeToModel_modelToCode {F : Type u} [Family F]
    (value : ModelValue (Family.format (F := F))) :
    codeToModel (modelToCode value) = value := by
  exact byteCodeToModel_modelToByteCode
    (Family.format (F := F)) (Family.width_le_eight (F := F)) value

/-- `toModel` inverts `ofModel` on model values. -/
@[simp] theorem toModel_ofModel {F : Type u} [Family F]
    (value : ModelValue (Family.format (F := F))) :
    toModel (ofModel value) = value :=
  codeToModel_modelToCode value

/-- Decoding a stored code and encoding the result returns the same code. -/
@[simp] theorem modelToCode_codeToModel {F : Type u} [Family F]
    (code : Code F) :
    modelToCode (codeToModel code) = code := by
  apply Subtype.ext
  apply UInt8.toNat_inj.mp
  change
    (UInt8.ofNat
      ((FloatLib.Floats.Formats.BinaryInterchange.Model.ofNatBits
        code.1.toNat).toNatBits)).toNat =
      code.1.toNat
  rw [FloatLib.Floats.Formats.BinaryInterchange.Model.toNatBits_ofNatBits_of_lt
    code.1.toNat code.2]
  exact congrArg UInt8.toNat
    (@UInt8.ofNat_toNat code.1)

/-- `ofModel` inverts `toModel` on stored values. -/
@[simp] theorem ofModel_toModel {F : Type u} [Family F]
    (value : FloatLib.Floats.ExecFloat F) :
    ofModel (toModel value) = value := by
  apply FloatLib.Floats.ExecFloat.ext
  exact modelToCode_codeToModel value.raw

/-- The model conversion is injective because `ofModel` is its inverse. -/
theorem toModel_injective {F : Type u} [Family F]
    {left right : FloatLib.Floats.ExecFloat F}
    (equality : toModel left = toModel right) :
    left = right := by
  rw [← ofModel_toModel left, ← ofModel_toModel right, equality]

/--
Lift a direct binary byte-kernel refinement equation to the universal static-byte carrier.

The executable function is an explicit argument. A capability can name its byte kernel directly
and use this theorem to prove its refinement.
-/
theorem liftBinary_eq_spec {F : Type u} [Family F]
    (run : Code F → Code F → Code F)
    (modelSpec :
      ModelValue (Family.format (F := F)) →
        ModelValue (Family.format (F := F)) →
          ModelValue (Family.format (F := F)))
    (run_eq_spec : ∀ left right,
      byteCodeToModel (run left right) =
        modelSpec (byteCodeToModel left) (byteCodeToModel right))
    (left right : FloatLib.Floats.ExecFloat F) :
    FloatLib.Floats.ExecFloat.ofRaw (run left.raw right.raw) =
      ofModel (modelSpec (toModel left) (toModel right)) := by
  apply toModel_injective (F := F)
  rw [toModel_ofModel]
  exact run_eq_spec left.raw right.raw

/--
Lift a direct unary byte-kernel refinement equation to the universal static-byte carrier.

The theorem is proof-only; it does not add a conversion or dispatch layer to the executable
kernel.
-/
theorem liftUnary_eq_spec {F : Type u} [Family F]
    (run : Code F → Code F)
    (modelSpec :
      ModelValue (Family.format (F := F)) →
        ModelValue (Family.format (F := F)))
    (run_eq_spec : ∀ value,
      byteCodeToModel (run value) = modelSpec (byteCodeToModel value))
    (value : FloatLib.Floats.ExecFloat F) :
    FloatLib.Floats.ExecFloat.ofRaw (run value.raw) =
      ofModel (modelSpec (toModel value)) := by
  apply toModel_injective (F := F)
  rw [toModel_ofModel]
  exact run_eq_spec value.raw

/--
Lift a direct ternary byte-kernel refinement equation to the universal static-byte carrier.

This is the erased proof bridge used by monomorphic fused-multiply-add capabilities.
-/
theorem liftTernary_eq_spec {F : Type u} [Family F]
    (run : Code F → Code F → Code F → Code F)
    (modelSpec :
      ModelValue (Family.format (F := F)) →
        ModelValue (Family.format (F := F)) →
          ModelValue (Family.format (F := F)) →
            ModelValue (Family.format (F := F)))
    (run_eq_spec : ∀ left right addend,
      byteCodeToModel (run left right addend) =
        modelSpec
          (byteCodeToModel left) (byteCodeToModel right) (byteCodeToModel addend))
    (left right addend : FloatLib.Floats.ExecFloat F) :
    FloatLib.Floats.ExecFloat.ofRaw (run left.raw right.raw addend.raw) =
      ofModel (modelSpec (toModel left) (toModel right) (toModel addend)) := by
  apply toModel_injective (F := F)
  rw [toModel_ofModel]
  exact run_eq_spec left.raw right.raw addend.raw

/--
Lift a certified binary byte table directly to the universal static-byte carrier.

This proof-only wrapper packages the recurring composition of `liftBinary_eq_spec` with the
certificate carried by `TinyTable.CertifiedBinary`. Concrete format modules can therefore keep
their executable functions monomorphic while sharing the erased refinement argument.
-/
theorem liftBinaryTable_eq_spec {F : Type u} [Family F]
    {modelSpec :
      ModelValue (Family.format (F := F)) →
        ModelValue (Family.format (F := F)) →
          ModelValue (Family.format (F := F))}
    (width_le_eight : (Family.format (F := F)).bitWidth ≤ 8)
    (kernel : TinyTable.CertifiedBinary
      (encoding (Family.format (F := F)) width_le_eight) modelSpec)
    (left right : FloatLib.Floats.ExecFloat F) :
    FloatLib.Floats.ExecFloat.ofRaw
        (runBinary width_le_eight kernel left.raw right.raw) =
      ofModel (modelSpec (toModel left) (toModel right)) :=
  liftBinary_eq_spec
    (runBinary width_le_eight kernel) modelSpec
    (byteCodeToModel_runBinary width_le_eight kernel) left right

/--
Lift a certified unary byte table directly to the universal static-byte carrier.

The certificate is the same one used by `byteCodeToModel_runUnary`, lifted to `ExecFloat`.
-/
theorem liftUnaryTable_eq_spec {F : Type u} [Family F]
    {modelSpec :
      ModelValue (Family.format (F := F)) →
        ModelValue (Family.format (F := F))}
    (width_le_eight : (Family.format (F := F)).bitWidth ≤ 8)
    (kernel : TinyTable.CertifiedUnary
      (encoding (Family.format (F := F)) width_le_eight) modelSpec)
    (value : FloatLib.Floats.ExecFloat F) :
    FloatLib.Floats.ExecFloat.ofRaw
        (runUnary width_le_eight kernel value.raw) =
      ofModel (modelSpec (toModel value)) :=
  liftUnary_eq_spec
    (runUnary width_le_eight kernel) modelSpec
    (byteCodeToModel_runUnary width_le_eight kernel) value

/--
Lift a certified ternary byte table directly to the universal static-byte carrier.

The concrete table remains named in the monomorphic executable definition; only its refinement
proof is factored through this theorem.
-/
theorem liftTernaryTable_eq_spec {F : Type u} [Family F]
    {modelSpec :
      ModelValue (Family.format (F := F)) →
        ModelValue (Family.format (F := F)) →
          ModelValue (Family.format (F := F)) →
            ModelValue (Family.format (F := F))}
    (width_le_eight : (Family.format (F := F)).bitWidth ≤ 8)
    (kernel : TinyTable.CertifiedTernary
      (encoding (Family.format (F := F)) width_le_eight) modelSpec)
    (left right addend : FloatLib.Floats.ExecFloat F) :
    FloatLib.Floats.ExecFloat.ofRaw
        (runTernary width_le_eight kernel left.raw right.raw addend.raw) =
      ofModel (modelSpec (toModel left) (toModel right) (toModel addend)) :=
  liftTernary_eq_spec
    (runTernary width_le_eight kernel) modelSpec
    (byteCodeToModel_runTernary width_le_eight kernel) left right addend

/--
Lift a proved model-level ternary kernel through the direct-byte representation.

This gives a table-free FMA construction. The executable function is `modelTernary`;
`op_eq_spec` supplies its correctness proof.
-/
theorem liftModelTernary_eq_spec {F : Type u} [Family F]
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
    FloatLib.Floats.ExecFloat.ofRaw
        (modelTernary (Family.format (F := F)) width_le_eight op
          left.raw right.raw addend.raw) =
      ofModel (modelSpec (toModel left) (toModel right) (toModel addend)) := by
  apply liftTernary_eq_spec
  intro x y z
  rw [byteCodeToModel_modelTernary, op_eq_spec]

end FloatLib.Floats.Formats.BinaryInterchange.StaticByte
