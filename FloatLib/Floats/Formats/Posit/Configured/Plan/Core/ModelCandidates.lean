/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Selection.Certified
public import FloatLib.Floats.Formats.Posit.Configured.Backend.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Plan.Core.Estimates

/-!
# Representation-independent configured posit candidates

These constructors package the model-valued two-limb backends with their refinement theorems.
They are independent of the persistent carrier: any configured representation with a `ModelCodec`
can use them. Each entry passes its eligibility witness to the two-limb rounder. Division and
square root have no two-limb entry because their kernels are the width-generic quotient-prefix and
root-prefix kernels already offered by the exact-dyadic candidate; offering the same kernel twice
would only duplicate a certificate.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured.Plan

open FloatLib.Floats.ExecFloat
open FloatLib.Floats.ExecFloat.Backend

/-! ## Representation-independent two-limb rounding candidates -/

/-- Certified two-limb-rounded addition candidate for formats of at most 128 bits. -/
@[inline] def nativeLimbAdd?
    (format : Format) (plan : StoragePlan format) {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] :
    Option (Certified (@Spec.add format plan code inferInstance)) :=
  if heligible : Model.NativeLimb.Eligible format then
    some (Certified.binary (nativeLimbEstimate plan .add)
      Spec.add (Backend.nativeLimbAdd heligible)
      (Backend.nativeLimbAdd_eq_spec heligible))
  else
    none

/-- Certified two-limb-rounded subtraction candidate. -/
@[inline] def nativeLimbSub?
    (format : Format) (plan : StoragePlan format) {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] :
    Option (Certified (@Spec.sub format plan code inferInstance)) :=
  if heligible : Model.NativeLimb.Eligible format then
    some (Certified.binary (nativeLimbEstimate plan .sub)
      Spec.sub (Backend.nativeLimbSub heligible)
      (Backend.nativeLimbSub_eq_spec heligible))
  else
    none

/-- Certified two-limb-rounded multiplication candidate. -/
@[inline] def nativeLimbMul?
    (format : Format) (plan : StoragePlan format) {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] :
    Option (Certified (@Spec.mul format plan code inferInstance)) :=
  if heligible : Model.NativeLimb.Eligible format then
    some (Certified.binary (nativeLimbEstimate plan .mul)
      Spec.mul (Backend.nativeLimbMul heligible)
      (Backend.nativeLimbMul_eq_spec heligible))
  else
    none

/-- Certified two-limb-rounded fused-multiply-add candidate. -/
@[inline] def nativeLimbFma?
    (format : Format) (plan : StoragePlan format) {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] :
    Option (Certified (@Spec.fma format plan code inferInstance)) :=
  if heligible : Model.NativeLimb.Eligible format then
    some (Certified.ternary (nativeLimbEstimate plan .fma)
      Spec.fma (Backend.nativeLimbFma heligible)
      (Backend.nativeLimbFma_eq_spec heligible))
  else
    none

end FloatLib.Floats.Formats.Posit.Configured.Plan
