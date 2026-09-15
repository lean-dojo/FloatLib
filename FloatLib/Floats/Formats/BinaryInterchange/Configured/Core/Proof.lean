/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Core.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Dispatch.Add.Proof
public import FloatLib.Floats.ExecFloat.Backends.Dispatch.Div.Proof
public import FloatLib.Floats.ExecFloat.Backends.Dispatch.Fma.Proof
public import FloatLib.Floats.ExecFloat.Backends.Dispatch.Mul.Proof
public import FloatLib.Floats.ExecFloat.Backends.Dispatch.Sqrt.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Storage.Family.Runtime

/-!
# Correctness of configured binary kernels

Every configured backend in `Configured.Core.Runtime` refines the same carrier-independent
specification. The proofs depend only on the codec laws and the shared model-kernel theorems,
not on the selected storage representation.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Configured

open FloatLib.Floats.ExecFloat

namespace Backend

variable {format : FloatFormat} {plan : StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

/-! ## Total generic kernels -/

/-- The width-generic addition backend implements the configured addition specification. -/
@[grind =]
theorem genericAdd_eq_spec
    (left right : FloatLib.Floats.ExecFloat (Family format code plan)) :
    genericAdd left right = Spec.add left right := by
  apply ModelCodec.decode_injective
    (F := Family format code plan) (Model := Model format) (plan := plan)
  simpa only [genericAdd, Spec.add, Family.toModel,
    ModelCodec.decode_liftBinary] using
    Model.AddBackend.generic_eq_spec (Family.toModel left) (Family.toModel right)

/-- The width-generic subtraction backend implements the configured subtraction specification. -/
@[grind =]
theorem genericSub_eq_spec
    (left right : FloatLib.Floats.ExecFloat (Family format code plan)) :
    genericSub left right = Spec.sub left right := by
  apply ModelCodec.decode_injective
    (F := Family format code plan) (Model := Model format) (plan := plan)
  simp only [genericSub, Spec.sub, ModelCodec.decode_liftBinary]
  simpa [Model.Spec.sub, Family.toModel] using
    Model.AddBackend.generic_eq_spec (Family.toModel left) (Model.neg (Family.toModel right))

/--
The width-generic multiplication backend implements the configured multiplication specification.
-/
@[grind =]
theorem genericMul_eq_spec
    (left right : FloatLib.Floats.ExecFloat (Family format code plan)) :
    genericMul left right = Spec.mul left right := by
  apply ModelCodec.decode_injective
    (F := Family format code plan) (Model := Model format) (plan := plan)
  simpa only [genericMul, Spec.mul, Family.toModel,
    ModelCodec.decode_liftBinary] using
    Model.MulBackend.generic_eq_spec (Family.toModel left) (Family.toModel right)

/-- The width-generic division backend implements the configured division specification. -/
@[grind =]
theorem genericDiv_eq_spec
    (left right : FloatLib.Floats.ExecFloat (Family format code plan)) :
    genericDiv left right = Spec.div left right := by
  apply ModelCodec.decode_injective
    (F := Family format code plan) (Model := Model format) (plan := plan)
  simpa only [genericDiv, Spec.div, Family.toModel,
    ModelCodec.decode_liftBinary] using
    Model.DivBackend.generic_eq_spec (Family.toModel left) (Family.toModel right)

/-- The width-generic square-root backend implements the configured square-root specification. -/
@[grind =]
theorem genericSqrt_eq_spec
    (value : FloatLib.Floats.ExecFloat (Family format code plan)) :
    genericSqrt value = Spec.sqrt value := by
  apply ModelCodec.decode_injective
    (F := Family format code plan) (Model := Model format) (plan := plan)
  simpa only [genericSqrt, Spec.sqrt, Family.toModel,
    ModelCodec.decode_liftUnary] using
    Model.SqrtBackend.generic_eq_spec (Family.toModel value)

/-- The width-generic fused multiply-add backend implements the configured FMA specification. -/
@[grind =]
theorem genericFma_eq_spec
    (left right addend : FloatLib.Floats.ExecFloat (Family format code plan)) :
    genericFma left right addend = Spec.fma left right addend := by
  apply ModelCodec.decode_injective
    (F := Family format code plan) (Model := Model format) (plan := plan)
  simpa only [genericFma, Spec.fma, Family.toModel,
    ModelCodec.decode_liftTernary] using
    Model.FmaBackend.generic_eq_spec
      (Family.toModel left) (Family.toModel right) (Family.toModel addend)

/-! ## Word and fixed-limb arithmetic -/

/-- The native-word addition backend implements the configured addition specification. -/
@[grind =]
theorem wordAdd_eq_spec
    (left right : FloatLib.Floats.ExecFloat (Family format code plan)) :
    wordAdd left right = Spec.add left right := by
  apply ModelCodec.decode_injective
    (F := Family format code plan) (Model := Model format) (plan := plan)
  simpa only [wordAdd, Spec.add, Family.toModel,
    ModelCodec.decode_liftBinary] using
    Model.AddBackend.word_eq_spec (Family.toModel left) (Family.toModel right)

/-- The native-word subtraction backend implements the configured subtraction specification. -/
@[grind =]
theorem wordSub_eq_spec
    (left right : FloatLib.Floats.ExecFloat (Family format code plan)) :
    wordSub left right = Spec.sub left right := by
  apply ModelCodec.decode_injective
    (F := Family format code plan) (Model := Model format) (plan := plan)
  simpa only [wordSub, Spec.sub, Family.toModel,
    ModelCodec.decode_liftBinary] using
    Model.AddBackend.subWord_eq_spec (Family.toModel left) (Family.toModel right)

/-- The word or fixed-limb multiplication backend implements the configured specification. -/
@[grind =]
theorem wordMul_eq_spec
    (left right : FloatLib.Floats.ExecFloat (Family format code plan)) :
    wordMul left right = Spec.mul left right := by
  apply ModelCodec.decode_injective
    (F := Family format code plan) (Model := Model format) (plan := plan)
  simpa only [wordMul, Spec.mul, Family.toModel,
    ModelCodec.decode_liftBinary] using
    Model.MulBackend.word_eq_spec (Family.toModel left) (Family.toModel right)

/-- The word or fixed-limb division backend implements the configured specification. -/
@[grind =]
theorem wordDiv_eq_spec
    (left right : FloatLib.Floats.ExecFloat (Family format code plan)) :
    wordDiv left right = Spec.div left right := by
  apply ModelCodec.decode_injective
    (F := Family format code plan) (Model := Model format) (plan := plan)
  simpa only [wordDiv, Spec.div, Family.toModel,
    ModelCodec.decode_liftBinary] using
    Model.DivBackend.word_eq_spec (Family.toModel left) (Family.toModel right)

/-- The native-word square-root backend implements the configured square-root specification. -/
@[grind =]
theorem wordSqrt_eq_spec
    (value : FloatLib.Floats.ExecFloat (Family format code plan)) :
    wordSqrt value = Spec.sqrt value := by
  apply ModelCodec.decode_injective
    (F := Family format code plan) (Model := Model format) (plan := plan)
  simpa only [wordSqrt, Spec.sqrt, Family.toModel,
    ModelCodec.decode_liftUnary] using
    Model.SqrtBackend.word_eq_spec (Family.toModel value)

/-- The native-word fused multiply-add backend implements the configured FMA specification. -/
@[grind =]
theorem wordFma_eq_spec
    (left right addend : FloatLib.Floats.ExecFloat (Family format code plan)) :
    wordFma left right addend = Spec.fma left right addend := by
  apply ModelCodec.decode_injective
    (F := Family format code plan) (Model := Model format) (plan := plan)
  simpa only [wordFma, Spec.fma, Family.toModel,
    ModelCodec.decode_liftTernary] using
    Model.FmaBackend.word_eq_spec
      (Family.toModel left) (Family.toModel right) (Family.toModel addend)

/-- The fixed-limb square-root route implements the configured square-root specification. -/
@[grind =]
theorem fixedLimbSqrt_eq_spec
    (value : FloatLib.Floats.ExecFloat (Family format code plan)) :
    fixedLimbSqrt value = Spec.sqrt value := by
  apply ModelCodec.decode_injective
    (F := Family format code plan) (Model := Model format) (plan := plan)
  simpa only [fixedLimbSqrt, Spec.sqrt, Family.toModel,
    ModelCodec.decode_liftUnary] using
    Model.SqrtBackend.dispatch_eq_spec (Family.toModel value)

/-- The fixed-limb fused multiply-add route implements the configured FMA specification. -/
@[grind =]
theorem fixedLimbFma_eq_spec
    (left right addend : FloatLib.Floats.ExecFloat (Family format code plan)) :
    fixedLimbFma left right addend = Spec.fma left right addend := by
  apply ModelCodec.decode_injective
    (F := Family format code plan) (Model := Model format) (plan := plan)
  simpa only [fixedLimbFma, Spec.fma, Family.toModel,
    ModelCodec.decode_liftTernary] using
    Model.FmaBackend.dispatch_eq_spec
      (Family.toModel left) (Family.toModel right) (Family.toModel addend)

end Backend

end FloatLib.Floats.Formats.BinaryInterchange.Configured
