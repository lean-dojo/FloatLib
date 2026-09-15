/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Dispatch.Add.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Dispatch.Div.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Dispatch.Fma.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Dispatch.Mul.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Dispatch.Sqrt.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Spec


/-!
# Certified execution backends for binary descriptors

Descriptor planning uses width-generic, native-word, and fixed-limb kernels with refinement
theorems. Backend choice is separate: `Descriptor.Plan` constructs the candidate set and the
universal selector makes that decision.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange

open FloatLib.Floats.ExecFloat

namespace Descriptor.Backend

/-! ## Width-generic kernels -/

/-- Width-generic proved addition. -/
@[inline] def genericAdd {format : FloatFormat} :=
  ModelCodec.liftBinary (F := Descriptor format) (plan := ()) Model.AddBackend.generic

/-- Width-generic proved subtraction. -/
@[inline] def genericSub {format : FloatFormat} :=
  ModelCodec.liftBinary (F := Descriptor format) (plan := ())
    (fun left right => Model.AddBackend.generic left (Model.neg right))

/-- Width-generic proved multiplication. -/
@[inline] def genericMul {format : FloatFormat} :=
  ModelCodec.liftBinary (F := Descriptor format) (plan := ()) Model.MulBackend.generic

/-- Width-generic proved division. -/
@[inline] def genericDiv {format : FloatFormat} :=
  ModelCodec.liftBinary (F := Descriptor format) (plan := ()) Model.DivBackend.generic

/-- Width-generic proved square root. -/
@[inline] def genericSqrt {format : FloatFormat} :=
  ModelCodec.liftUnary (F := Descriptor format) (plan := ()) Model.SqrtBackend.generic

/-- Width-generic proved fused multiply-add. -/
@[inline] def genericFma {format : FloatFormat} :=
  ModelCodec.liftTernary (F := Descriptor format) (plan := ()) Model.FmaBackend.generic

/-- Width-generic addition agrees with the descriptor reference specification. -/
theorem genericAdd_eq_spec {format : FloatFormat}
    (left right : FloatLib.Floats.ExecFloat (Descriptor format)) :
    genericAdd left right = Descriptor.Spec.add left right := by
  apply FloatLib.Floats.ExecFloat.ext
  exact Model.AddBackend.generic_eq_spec left.raw right.raw

/-- Width-generic subtraction agrees with the descriptor reference specification. -/
theorem genericSub_eq_spec {format : FloatFormat}
    (left right : FloatLib.Floats.ExecFloat (Descriptor format)) :
    genericSub left right = Descriptor.Spec.sub left right := by
  apply FloatLib.Floats.ExecFloat.ext
  change Model.AddBackend.generic left.raw (Model.neg right.raw) =
    Model.Spec.sub left.raw right.raw
  simpa [Model.Spec.sub] using
    Model.AddBackend.generic_eq_spec left.raw (Model.neg right.raw)

/-- Width-generic multiplication agrees with the descriptor reference specification. -/
theorem genericMul_eq_spec {format : FloatFormat}
    (left right : FloatLib.Floats.ExecFloat (Descriptor format)) :
    genericMul left right = Descriptor.Spec.mul left right := by
  apply FloatLib.Floats.ExecFloat.ext
  exact Model.MulBackend.generic_eq_spec left.raw right.raw

/-- Width-generic division agrees with the descriptor reference specification. -/
theorem genericDiv_eq_spec {format : FloatFormat}
    (left right : FloatLib.Floats.ExecFloat (Descriptor format)) :
    genericDiv left right = Descriptor.Spec.div left right := by
  apply FloatLib.Floats.ExecFloat.ext
  exact Model.DivBackend.generic_eq_spec left.raw right.raw

/-- Width-generic square root agrees with the descriptor reference specification. -/
theorem genericSqrt_eq_spec {format : FloatFormat}
    (value : FloatLib.Floats.ExecFloat (Descriptor format)) :
    genericSqrt value = Descriptor.Spec.sqrt value := by
  apply FloatLib.Floats.ExecFloat.ext
  exact Model.SqrtBackend.generic_eq_spec value.raw

/-- Width-generic fused multiply-add agrees with the descriptor reference specification. -/
theorem genericFma_eq_spec {format : FloatFormat}
    (left right addend : FloatLib.Floats.ExecFloat (Descriptor format)) :
    genericFma left right addend = Descriptor.Spec.fma left right addend := by
  apply FloatLib.Floats.ExecFloat.ext
  exact Model.FmaBackend.generic_eq_spec left.raw right.raw addend.raw

/-! ## Fixed-format and native-word routes -/

/--
Proved fixed-format/native-word addition route.

The candidate planner offers this route when the descriptor satisfies its eligibility predicate.
For closed descriptors, the compiler can specialize the format tests.
-/
@[inline] def wordAdd {format : FloatFormat} :=
  ModelCodec.liftBinary (F := Descriptor format) (plan := ()) Model.AddBackend.word

/-- Proved fixed-format/native-word subtraction route. -/
@[inline] def wordSub {format : FloatFormat} :=
  ModelCodec.liftBinary (F := Descriptor format) (plan := ()) Model.AddBackend.subWord

/-- Proved fixed-format/native-word/fixed-limb multiplication route. -/
@[inline] def wordMul {format : FloatFormat} :=
  ModelCodec.liftBinary (F := Descriptor format) (plan := ()) Model.MulBackend.word

/-- Proved fixed-format/native-word/fixed-limb division route. -/
@[inline] def wordDiv {format : FloatFormat} :=
  ModelCodec.liftBinary (F := Descriptor format) (plan := ()) Model.DivBackend.word

/-- Proved fixed-format/native-word square-root route. -/
@[inline] def wordSqrt {format : FloatFormat} :=
  ModelCodec.liftUnary (F := Descriptor format) (plan := ()) Model.SqrtBackend.word

/-- Proved fixed-format/native-word fused multiply-add route. -/
@[inline] def wordFma {format : FloatFormat} :=
  ModelCodec.liftTernary (F := Descriptor format) (plan := ()) Model.FmaBackend.word

/-- Square-root dispatcher, including eligible fixed-limb kernels. -/
@[inline] def fixedLimbSqrt {format : FloatFormat} :=
  ModelCodec.liftUnary (F := Descriptor format) (plan := ()) Model.SqrtBackend.dispatch

/-- Fused multiply-add dispatcher, including eligible fixed-limb kernels. -/
@[inline] def fixedLimbFma {format : FloatFormat} :=
  ModelCodec.liftTernary (F := Descriptor format) (plan := ()) Model.FmaBackend.dispatch

/-- Native-word addition agrees with the descriptor reference specification. -/
theorem wordAdd_eq_spec {format : FloatFormat}
    (left right : FloatLib.Floats.ExecFloat (Descriptor format)) :
    wordAdd left right = Descriptor.Spec.add left right := by
  apply FloatLib.Floats.ExecFloat.ext
  exact Model.AddBackend.word_eq_spec left.raw right.raw

/-- Native-word subtraction agrees with the descriptor reference specification. -/
theorem wordSub_eq_spec {format : FloatFormat}
    (left right : FloatLib.Floats.ExecFloat (Descriptor format)) :
    wordSub left right = Descriptor.Spec.sub left right := by
  apply FloatLib.Floats.ExecFloat.ext
  exact Model.AddBackend.subWord_eq_spec left.raw right.raw

/-- Native-word or fixed-limb multiplication agrees with the descriptor reference specification. -/
theorem wordMul_eq_spec {format : FloatFormat}
    (left right : FloatLib.Floats.ExecFloat (Descriptor format)) :
    wordMul left right = Descriptor.Spec.mul left right := by
  apply FloatLib.Floats.ExecFloat.ext
  exact Model.MulBackend.word_eq_spec left.raw right.raw

/-- Native-word or fixed-limb division agrees with the descriptor reference specification. -/
theorem wordDiv_eq_spec {format : FloatFormat}
    (left right : FloatLib.Floats.ExecFloat (Descriptor format)) :
    wordDiv left right = Descriptor.Spec.div left right := by
  apply FloatLib.Floats.ExecFloat.ext
  exact Model.DivBackend.word_eq_spec left.raw right.raw

/-- Native-word square root agrees with the descriptor reference specification. -/
theorem wordSqrt_eq_spec {format : FloatFormat}
    (value : FloatLib.Floats.ExecFloat (Descriptor format)) :
    wordSqrt value = Descriptor.Spec.sqrt value := by
  apply FloatLib.Floats.ExecFloat.ext
  exact Model.SqrtBackend.word_eq_spec value.raw

/-- Native-word fused multiply-add agrees with the descriptor reference specification. -/
theorem wordFma_eq_spec {format : FloatFormat}
    (left right addend : FloatLib.Floats.ExecFloat (Descriptor format)) :
    wordFma left right addend = Descriptor.Spec.fma left right addend := by
  apply FloatLib.Floats.ExecFloat.ext
  exact Model.FmaBackend.word_eq_spec left.raw right.raw addend.raw

/-- The square-root dispatcher agrees with the reference specification. -/
theorem fixedLimbSqrt_eq_spec {format : FloatFormat}
    (value : FloatLib.Floats.ExecFloat (Descriptor format)) :
    fixedLimbSqrt value = Descriptor.Spec.sqrt value := by
  apply FloatLib.Floats.ExecFloat.ext
  exact Model.SqrtBackend.dispatch_eq_spec value.raw

/-- The fused multiply-add dispatcher agrees with the reference specification. -/
theorem fixedLimbFma_eq_spec {format : FloatFormat}
    (left right addend : FloatLib.Floats.ExecFloat (Descriptor format)) :
    fixedLimbFma left right addend = Descriptor.Spec.fma left right addend := by
  apply FloatLib.Floats.ExecFloat.ext
  exact Model.FmaBackend.dispatch_eq_spec left.raw right.raw addend.raw

end Descriptor.Backend

end FloatLib.Floats.Formats.BinaryInterchange
