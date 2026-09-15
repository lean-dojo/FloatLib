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
public import FloatLib.Floats.ExecFloat.Carrier
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Storage.Core
public import FloatLib.Floats.Formats.BinaryInterchange.Spec.Dyadic
public import FloatLib.Floats.Formats.BinaryInterchange.Spec.SquareRoot
public import Mathlib.Algebra.Order.Algebra

/-!
# Runtime kernels for configured binary formats

Configured binary arithmetic lifts the descriptor-model operations through the carrier selected
by `StoragePlan`. The definitions are the total executable baseline for every precision and
encoding policy. Correctness proofs live in `Configured.Core.Proof`.

The carrier conversion is deliberately explicit. The execution planner can charge for it and
prefer a direct byte, word, fixed-limb, or family-defined kernel when one is available.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Configured

open FloatLib.Numerics
open FloatLib.Floats.ExecFloat

namespace Spec

/-- Reference addition for a configured carrier. -/
def add {format : FloatFormat} {plan : StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] :=
  ModelCodec.liftBinary (F := Family format code plan) (Model := Model format) (plan := plan) Model.Spec.add

/-- Reference subtraction for a configured carrier. -/
def sub {format : FloatFormat} {plan : StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] :=
  ModelCodec.liftBinary (F := Family format code plan) (Model := Model format) (plan := plan) Model.Spec.sub

/-- Reference multiplication for a configured carrier. -/
def mul {format : FloatFormat} {plan : StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] :=
  ModelCodec.liftBinary (F := Family format code plan) (Model := Model format) (plan := plan) Model.Spec.mul

/-- Reference division for a configured carrier. -/
def div {format : FloatFormat} {plan : StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] :=
  ModelCodec.liftBinary (F := Family format code plan) (Model := Model format) (plan := plan) Model.Spec.div

/-- Reference square root for a configured carrier. -/
def sqrt {format : FloatFormat} {plan : StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] :=
  ModelCodec.liftUnary (F := Family format code plan) (Model := Model format) (plan := plan) Model.Spec.sqrt

/-- Reference fused multiply-add for a configured carrier. -/
def fma {format : FloatFormat} {plan : StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] :=
  ModelCodec.liftTernary (F := Family format code plan) (Model := Model format) (plan := plan) Model.Spec.fma

end Spec

namespace Backend

variable {format : FloatFormat} {plan : StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

/-! ## Total generic kernels -/

/-- Width-generic proved addition. -/
@[inline] def genericAdd :=
  ModelCodec.liftBinary (F := Family format code plan) (Model := Model format) (plan := plan) Model.AddBackend.generic

/-- Width-generic proved subtraction. -/
@[inline] def genericSub :=
  ModelCodec.liftBinary (F := Family format code plan) (Model := Model format) (plan := plan)
    (fun left right => Model.AddBackend.generic left (Model.neg right))

/-- Width-generic proved multiplication. -/
@[inline] def genericMul :=
  ModelCodec.liftBinary (F := Family format code plan) (Model := Model format) (plan := plan) Model.MulBackend.generic

/-- Width-generic proved division. -/
@[inline] def genericDiv :=
  ModelCodec.liftBinary (F := Family format code plan) (Model := Model format) (plan := plan) Model.DivBackend.generic

/-- Width-generic proved square root. -/
@[inline] def genericSqrt :=
  ModelCodec.liftUnary (F := Family format code plan) (Model := Model format) (plan := plan) Model.SqrtBackend.generic

/-- Width-generic proved fused multiply-add. -/
@[inline] def genericFma :=
  ModelCodec.liftTernary (F := Family format code plan) (Model := Model format) (plan := plan) Model.FmaBackend.generic

/-! ## Proved word and fixed-limb arithmetic -/

/--
Parameterized word/fixed-format addition, adapted through the selected carrier.

The operation planner only advertises this candidate when the descriptor satisfies the kernel's
structural eligibility predicate.
-/
@[inline] def wordAdd :=
  ModelCodec.liftBinary (F := Family format code plan) (Model := Model format) (plan := plan) Model.AddBackend.word

/-- Parameterized word/fixed-format subtraction. -/
@[inline] def wordSub :=
  ModelCodec.liftBinary (F := Family format code plan) (Model := Model format) (plan := plan) Model.AddBackend.subWord

/-- Parameterized word or fixed-limb multiplication. -/
@[inline] def wordMul :=
  ModelCodec.liftBinary (F := Family format code plan) (Model := Model format) (plan := plan) Model.MulBackend.word

/-- Parameterized word or fixed-limb division. -/
@[inline] def wordDiv :=
  ModelCodec.liftBinary (F := Family format code plan) (Model := Model format) (plan := plan) Model.DivBackend.word

/-- Parameterized word square root. -/
@[inline] def wordSqrt :=
  ModelCodec.liftUnary (F := Family format code plan) (Model := Model format) (plan := plan) Model.SqrtBackend.word

/-- Parameterized word fused multiply-add. -/
@[inline] def wordFma :=
  ModelCodec.liftTernary (F := Family format code plan) (Model := Model format) (plan := plan) Model.FmaBackend.word

/-- Square-root dispatcher, including structurally eligible fixed-limb kernels. -/
@[inline] def fixedLimbSqrt :=
  ModelCodec.liftUnary (F := Family format code plan) (Model := Model format) (plan := plan) Model.SqrtBackend.dispatch

/-- Fused multiply-add dispatcher, including structurally eligible fixed-limb kernels. -/
@[inline] def fixedLimbFma :=
  ModelCodec.liftTernary (F := Family format code plan) (Model := Model format) (plan := plan) Model.FmaBackend.dispatch

end Backend

end FloatLib.Floats.Formats.BinaryInterchange.Configured
