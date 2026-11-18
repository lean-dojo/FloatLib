/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.Plan.Core.ModelCandidates

/-!
# General configured posit candidate portfolios

A general portfolio pairs the eligible two-limb rounding kernel with the width-generic
exact-dyadic implementation, and keeps the exact-rational specification as its final reference
baseline. Each kind of kernel appears once. The exact-dyadic candidate is the direct kernel
itself, so no model-valued alias of it shows up under another name. When the baseline runs, it is
because planning chose it, and it is never a hidden recovery path at runtime. Packed
candidates for particular carriers are assembled in the sibling planner modules.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured.Plan

open FloatLib.Floats.ExecFloat
open FloatLib.Floats.ExecFloat.Backend

/-- Representation-independent certified addition candidates for a configured posit. -/
@[noinline] def addCandidates
    (format : Format) (plan : StoragePlan format) {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] :
    CandidateSet (Certified (@Spec.addition format plan code inferInstance)) :=
  CandidateSet.withReference (genericEstimate plan .add) Spec.addition <|
    (nativeLimbAdd? format plan).toList ++
    [Certified.binary (dyadicEstimate plan .add)
      Spec.addition Backend.dyadicAdd Backend.dyadicAdd_eq_spec]

/-- Representation-independent certified subtraction candidates for a configured posit. -/
@[noinline] def subCandidates
    (format : Format) (plan : StoragePlan format) {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] :
    CandidateSet (Certified (@Spec.subtraction format plan code inferInstance)) :=
  CandidateSet.withReference (genericEstimate plan .sub) Spec.subtraction <|
    (nativeLimbSub? format plan).toList ++
    [Certified.binary (dyadicEstimate plan .sub)
      Spec.subtraction Backend.dyadicSub Backend.dyadicSub_eq_spec]

/-- Representation-independent certified multiplication candidates for a configured posit. -/
@[noinline] def mulCandidates
    (format : Format) (plan : StoragePlan format) {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] :
    CandidateSet (Certified (@Spec.multiplication format plan code inferInstance)) :=
  CandidateSet.withReference (genericEstimate plan .mul) Spec.multiplication <|
    (nativeLimbMul? format plan).toList ++
    [Certified.binary (dyadicEstimate plan .mul)
      Spec.multiplication Backend.dyadicMul Backend.dyadicMul_eq_spec]

/-- Representation-independent certified division candidates for a configured posit. -/
@[noinline] def divCandidates
    (format : Format) (plan : StoragePlan format) {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] :
    CandidateSet (Certified (@Spec.division format plan code inferInstance)) :=
  CandidateSet.withReference (genericEstimate plan .div) Spec.division <|
    [Certified.binary (dyadicEstimate plan .div)
      Spec.division Backend.dyadicDiv Backend.dyadicDiv_eq_spec]

/-- Representation-independent certified square-root candidates for a configured posit. -/
@[noinline] def sqrtCandidates
    (format : Format) (plan : StoragePlan format) {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] :
    CandidateSet (Certified (@Spec.sqrt format plan code inferInstance)) :=
  CandidateSet.withReference (genericEstimate plan .sqrt) Spec.sqrt <|
    [Certified.unary (dyadicEstimate plan .sqrt)
      Spec.sqrt Backend.dyadicSqrt Backend.dyadicSqrt_eq_spec]

/-- Representation-independent certified fused-multiply-add candidates for a configured posit. -/
@[noinline] def fmaCandidates
    (format : Format) (plan : StoragePlan format) {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] :
    CandidateSet (Certified (@Spec.fma format plan code inferInstance)) :=
  CandidateSet.withReference (genericEstimate plan .fma) Spec.fma <|
    (nativeLimbFma? format plan).toList ++
    [Certified.ternary (dyadicEstimate plan .fma)
      Spec.fma Backend.dyadicFma Backend.dyadicFma_eq_spec]

end FloatLib.Floats.Formats.Posit.Configured.Plan
