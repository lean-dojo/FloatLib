/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.FirstOrder
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Direct.Proof
public import FloatLib.Floats.ExecFloat.Core.Capability

/-!
# Capability instances for configured binary formats

Representation-independent instances serve custom carriers. Higher-priority instances for
`Configured.Code` expose byte tables after dependent elimination of the selected storage plan, and
give the other non-limb plans a direct entry point to the selected structural or generic kernel.
A closed `ExecFloat.Binary` call can therefore specialize that kernel to its descriptor.

The priorities encode capability preference and carry no numerical meaning, because every
candidate must supply the same refinement contract before it can be selected. All of this wiring
lives in this module, so storage-specific instances do not leak into the rest of the configured
API.
-/

@[expose] public section
namespace FloatLib.Floats.Formats.BinaryInterchange.Configured

instance (priority := 100) addCapability
    (format : FloatFormat) (plan : StoragePlan format) (code : Type)
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Family format code plan)] :
    FloatLib.Floats.ExecFloat.Add (Family format code plan) where
  spec := Spec.add
  candidates := Plan.addCandidates format plan

instance (priority := 100) subCapability
    (format : FloatFormat) (plan : StoragePlan format) (code : Type)
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Family format code plan)] :
    FloatLib.Floats.ExecFloat.Sub (Family format code plan) where
  spec := Spec.sub
  candidates := Plan.subCandidates format plan

instance (priority := 100) mulCapability
    (format : FloatFormat) (plan : StoragePlan format) (code : Type)
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Family format code plan)] :
    FloatLib.Floats.ExecFloat.Mul (Family format code plan) where
  spec := Spec.mul
  candidates := Plan.mulCandidates format plan

instance (priority := 100) divCapability
    (format : FloatFormat) (plan : StoragePlan format) (code : Type)
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Family format code plan)] :
    FloatLib.Floats.ExecFloat.Div (Family format code plan) where
  spec := Spec.div
  candidates := Plan.divCandidates format plan

instance (priority := 100) sqrtCapability
    (format : FloatFormat) (plan : StoragePlan format) (code : Type)
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Family format code plan)] :
    FloatLib.Floats.ExecFloat.Sqrt (Family format code plan) where
  spec := Spec.sqrt
  candidates := Plan.sqrtCandidates format plan

instance (priority := 100) fmaCapability
    (format : FloatFormat) (plan : StoragePlan format) (code : Type)
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Family format code plan)] :
    FloatLib.Floats.ExecFloat.Fma (Family format code plan) where
  spec := Spec.fma
  candidates := Plan.fmaCandidates format plan

/-!
Higher-priority built-in-carrier instances match `Code plan` before inspecting the plan. This
works for every statically computed precision, including a `forKnownWidth` expression that has not
yet reduced to a storage constructor during typeclass indexing. The dependent candidate helpers
then add direct byte tables exactly when the selected plan is `.byte`.

Families with a custom carrier use the representation-independent instances above.
-/

/-!
## First-order entry points

A machine-word or pair plan calls its structural kernel directly when that candidate wins
against the generic kernel under the policy in scope. Non-byte, non-limb plans also expose a
direct call when the generic kernel wins. Byte tables, limb candidates, and the remaining
structural routes execute the memoized selection.

The guard stays inside `execute` so closed callers can specialize the selected kernel. A match
around the capability record would prevent the compiler from reducing the projection before
kernel specialization. The proofs below unfold candidate selection, including the choice between
word and fixed-limb square root and FMA. Numerical equivalence alone never justifies a route.
-/

namespace Plan

/--
The direct square root for a built-in carrier: stored two-word codes where the `NativePair` layout
allows, otherwise the structural candidate.
-/
@[always_inline] def directSqrt {format : FloatFormat} {plan : StoragePlan format} :
    FloatLib.Floats.ExecFloat (Family format (Code plan) plan) →
      FloatLib.Floats.ExecFloat (Family format (Code plan) plan) :=
  match plan with
  | .pair hgt hle =>
      if Model.NativePair.Eligible format then Backend.pairSqrt hgt hle else structuralSqrt
  | _ => structuralSqrt

/-- The direct square root computes the structural candidate's result. -/
theorem directSqrt_eq {format : FloatFormat} {plan : StoragePlan format}
    (value : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    directSqrt value = structuralSqrt value := by
  cases plan with
  | pair hgt hle =>
      simp only [directSqrt]
      split
      · rename_i hpair
        rw [Backend.pairSqrt_eq_spec hgt hle hpair]
        unfold structuralSqrt
        cases Descriptor.Plan.structuralRoute? format .sqrt with
        | none => exact (Backend.wordSqrt_eq_spec value).symm
        | some route =>
            cases route <;> first
              | exact (Backend.fixedLimbSqrt_eq_spec value).symm
              | exact (Backend.wordSqrt_eq_spec value).symm
      · rfl
  | _ => rfl

/--
The direct fused multiply-add for a built-in carrier: stored two-word codes where the `NativePair`
layout allows, otherwise the structural candidate.
-/
@[always_inline] def directFma {format : FloatFormat} {plan : StoragePlan format} :
    FloatLib.Floats.ExecFloat (Family format (Code plan) plan) →
      FloatLib.Floats.ExecFloat (Family format (Code plan) plan) →
        FloatLib.Floats.ExecFloat (Family format (Code plan) plan) →
          FloatLib.Floats.ExecFloat (Family format (Code plan) plan) :=
  match plan with
  | .pair hgt hle =>
      if Model.NativePair.Eligible format then Backend.pairFma hgt hle else structuralFma
  | _ => structuralFma

/-- The direct fused multiply-add computes the structural candidate's result. -/
theorem directFma_eq {format : FloatFormat} {plan : StoragePlan format}
    (left right addend : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    directFma left right addend = structuralFma left right addend := by
  cases plan with
  | pair hgt hle =>
      simp only [directFma]
      split
      · rename_i hpair
        rw [Backend.pairFma_eq_spec hgt hle hpair]
        unfold structuralFma
        cases Descriptor.Plan.structuralRoute? format .fma with
        | none => exact (Backend.wordFma_eq_spec left right addend).symm
        | some route =>
            cases route <;> first
              | exact (Backend.fixedLimbFma_eq_spec left right addend).symm
              | exact (Backend.wordFma_eq_spec left right addend).symm
      · rfl
  | _ => rfl

end Plan

@[always_inline] instance (priority := 200) automaticAddCapability
    (format : FloatFormat) (plan : StoragePlan format)
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor
      (Family format (Code plan) plan)] :
    FloatLib.Floats.ExecFloat.Add (Family format (Code plan) plan) :=
  let selection := Thunk.mk fun _ =>
    FloatLib.Floats.ExecFloat.Backend.selectCertified planning.policy
      (Plan.automaticAddCandidates format plan)
  { spec := Spec.add
    candidates := Plan.automaticAddCandidates format plan
    selection := selection
    execute := fun left right =>
      if Plan.firstOrderSelected planning.policy plan .add then
        Backend.directAdd left right
      else if Plan.firstOrderGenericSelected planning.policy plan .add then
        Backend.genericAdd left right
      else
        selection.get.run left right
    execute_eq_implementation := by
      funext left right
      split
      · rename_i h
        rw [Backend.directAdd_eq, ← Plan.select_add_run_of_firstOrder planning.policy plan h]
        rfl
      · split
        · rename_i h
          rw [← Plan.select_add_run_of_firstOrderGeneric planning.policy plan h]
          rfl
        · rfl }

@[always_inline] instance (priority := 200) automaticSubCapability
    (format : FloatFormat) (plan : StoragePlan format)
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor
      (Family format (Code plan) plan)] :
    FloatLib.Floats.ExecFloat.Sub (Family format (Code plan) plan) :=
  let selection := Thunk.mk fun _ =>
    FloatLib.Floats.ExecFloat.Backend.selectCertified planning.policy
      (Plan.automaticSubCandidates format plan)
  { spec := Spec.sub
    candidates := Plan.automaticSubCandidates format plan
    selection := selection
    execute := fun left right =>
      if Plan.firstOrderSelected planning.policy plan .sub then
        Backend.directSub left right
      else if Plan.firstOrderGenericSelected planning.policy plan .sub then
        Backend.genericSub left right
      else
        selection.get.run left right
    execute_eq_implementation := by
      funext left right
      split
      · rename_i h
        rw [Backend.directSub_eq, ← Plan.select_sub_run_of_firstOrder planning.policy plan h]
        rfl
      · split
        · rename_i h
          rw [← Plan.select_sub_run_of_firstOrderGeneric planning.policy plan h]
          rfl
        · rfl }

@[always_inline] instance (priority := 200) automaticMulCapability
    (format : FloatFormat) (plan : StoragePlan format)
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor
      (Family format (Code plan) plan)] :
    FloatLib.Floats.ExecFloat.Mul (Family format (Code plan) plan) :=
  let selection := Thunk.mk fun _ =>
    FloatLib.Floats.ExecFloat.Backend.selectCertified planning.policy
      (Plan.automaticMulCandidates format plan)
  { spec := Spec.mul
    candidates := Plan.automaticMulCandidates format plan
    selection := selection
    execute := fun left right =>
      if Plan.firstOrderSelected planning.policy plan .mul then
        Backend.directMul left right
      else if Plan.firstOrderGenericSelected planning.policy plan .mul then
        Backend.genericMul left right
      else
        selection.get.run left right
    execute_eq_implementation := by
      funext left right
      split
      · rename_i h
        rw [Backend.directMul_eq, ← Plan.select_mul_run_of_firstOrder planning.policy plan h]
        rfl
      · split
        · rename_i h
          rw [← Plan.select_mul_run_of_firstOrderGeneric planning.policy plan h]
          rfl
        · rfl }

@[always_inline] instance (priority := 200) automaticDivCapability
    (format : FloatFormat) (plan : StoragePlan format)
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor
      (Family format (Code plan) plan)] :
    FloatLib.Floats.ExecFloat.Div (Family format (Code plan) plan) :=
  let selection := Thunk.mk fun _ =>
    FloatLib.Floats.ExecFloat.Backend.selectCertified planning.policy
      (Plan.automaticDivCandidates format plan)
  { spec := Spec.div
    candidates := Plan.automaticDivCandidates format plan
    selection := selection
    execute := fun left right =>
      if Plan.firstOrderSelected planning.policy plan .div then
        Backend.directDiv left right
      else if Plan.firstOrderGenericSelected planning.policy plan .div then
        Backend.genericDiv left right
      else
        selection.get.run left right
    execute_eq_implementation := by
      funext left right
      split
      · rename_i h
        rw [Backend.directDiv_eq, ← Plan.select_div_run_of_firstOrder planning.policy plan h]
        rfl
      · split
        · rename_i h
          rw [← Plan.select_div_run_of_firstOrderGeneric planning.policy plan h]
          rfl
        · rfl }

@[always_inline] instance (priority := 200) automaticSqrtCapability
    (format : FloatFormat) (plan : StoragePlan format)
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor
      (Family format (Code plan) plan)] :
    FloatLib.Floats.ExecFloat.Sqrt (Family format (Code plan) plan) :=
  let selection := Thunk.mk fun _ =>
    FloatLib.Floats.ExecFloat.Backend.selectCertified planning.policy
      (Plan.automaticSqrtCandidates format plan)
  { spec := Spec.sqrt
    candidates := Plan.automaticSqrtCandidates format plan
    selection := selection
    execute := fun value =>
      if Plan.firstOrderSelected planning.policy plan .sqrt then
        Plan.directSqrt value
      else if Plan.firstOrderGenericSelected planning.policy plan .sqrt then
        Backend.genericSqrt value
      else
        selection.get.run value
    execute_eq_implementation := by
      funext value
      split
      · rename_i h
        rw [Plan.directSqrt_eq, ← Plan.select_sqrt_run_of_firstOrder planning.policy plan h]
        rfl
      · split
        · rename_i h
          rw [← Plan.select_sqrt_run_of_firstOrderGeneric planning.policy plan h]
          rfl
        · rfl }

@[always_inline] instance (priority := 200) automaticFmaCapability
    (format : FloatFormat) (plan : StoragePlan format)
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor
      (Family format (Code plan) plan)] :
    FloatLib.Floats.ExecFloat.Fma (Family format (Code plan) plan) :=
  let selection := Thunk.mk fun _ =>
    FloatLib.Floats.ExecFloat.Backend.selectCertified planning.policy
      (Plan.automaticFmaCandidates format plan)
  { spec := Spec.fma
    candidates := Plan.automaticFmaCandidates format plan
    selection := selection
    execute := fun left right addend =>
      if Plan.firstOrderSelected planning.policy plan .fma then
        Plan.directFma left right addend
      else if Plan.firstOrderGenericSelected planning.policy plan .fma then
        Backend.genericFma left right addend
      else
        selection.get.run left right addend
    execute_eq_implementation := by
      funext left right addend
      split
      · rename_i h
        rw [Plan.directFma_eq, ← Plan.select_fma_run_of_firstOrder planning.policy plan h]
        rfl
      · split
        · rename_i h
          rw [← Plan.select_fma_run_of_firstOrderGeneric planning.policy plan h]
          rfl
        · rfl }

/-!
Closed limb plans expose their concrete carrier during typeclass indexing. These instances
forward to the automatic portfolios so `ExecFloat.BinaryLimbs` retains the policy in scope,
its certified candidates, and the generic fallback.
-/

/--
The canonical lossless codec for the concrete limb carrier.

Its priority is below `codecForPlan` because `ModelCodec.Code` is an output parameter, so
unresolved codec goals must try the generic plan before the concrete limb carrier. That keeps
inference working for conversions between definitionally equal descriptors such as
`Binary.descriptor 8 23` and `binary32`.
-/
instance (priority := 900) limbCodec
    (format : FloatFormat) (width_gt : 128 < format.bitWidth) :
    FloatLib.Floats.ExecFloat.ModelCodec (.limbs width_gt : StoragePlan format)
      (Model format) (Model.WideLimb.Value format) :=
  codecForPlan format (.limbs width_gt)

/-- Policy-selected addition for the concrete limb carrier. -/
@[always_inline] instance (priority := 210) limbAddCapability
    (format : FloatFormat) (width_gt : 128 < format.bitWidth)
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor
      (Family format (Model.WideLimb.Value format) (.limbs width_gt))] :
    FloatLib.Floats.ExecFloat.Add
      (Family format (Model.WideLimb.Value format) (.limbs width_gt)) :=
  automaticAddCapability format (.limbs width_gt)

/-- Policy-selected subtraction for the concrete limb carrier. -/
@[always_inline] instance (priority := 210) limbSubCapability
    (format : FloatFormat) (width_gt : 128 < format.bitWidth)
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor
      (Family format (Model.WideLimb.Value format) (.limbs width_gt))] :
    FloatLib.Floats.ExecFloat.Sub
      (Family format (Model.WideLimb.Value format) (.limbs width_gt)) :=
  automaticSubCapability format (.limbs width_gt)

/-- Policy-selected multiplication for the concrete limb carrier. -/
@[always_inline] instance (priority := 210) limbMulCapability
    (format : FloatFormat) (width_gt : 128 < format.bitWidth)
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor
      (Family format (Model.WideLimb.Value format) (.limbs width_gt))] :
    FloatLib.Floats.ExecFloat.Mul
      (Family format (Model.WideLimb.Value format) (.limbs width_gt)) :=
  automaticMulCapability format (.limbs width_gt)

/-- Policy-selected division for the concrete limb carrier. -/
@[always_inline] instance (priority := 210) limbDivCapability
    (format : FloatFormat) (width_gt : 128 < format.bitWidth)
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor
      (Family format (Model.WideLimb.Value format) (.limbs width_gt))] :
    FloatLib.Floats.ExecFloat.Div
      (Family format (Model.WideLimb.Value format) (.limbs width_gt)) :=
  automaticDivCapability format (.limbs width_gt)

/-- Policy-selected square root for the concrete limb carrier. -/
@[always_inline] instance (priority := 210) limbSqrtCapability
    (format : FloatFormat) (width_gt : 128 < format.bitWidth)
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor
      (Family format (Model.WideLimb.Value format) (.limbs width_gt))] :
    FloatLib.Floats.ExecFloat.Sqrt
      (Family format (Model.WideLimb.Value format) (.limbs width_gt)) :=
  automaticSqrtCapability format (.limbs width_gt)

/-- Policy-selected fused multiply-add for the concrete limb carrier. -/
@[always_inline] instance (priority := 210) limbFmaCapability
    (format : FloatFormat) (width_gt : 128 < format.bitWidth)
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor
      (Family format (Model.WideLimb.Value format) (.limbs width_gt))] :
    FloatLib.Floats.ExecFloat.Fma
      (Family format (Model.WideLimb.Value format) (.limbs width_gt)) :=
  automaticFmaCapability format (.limbs width_gt)

end FloatLib.Floats.Formats.BinaryInterchange.Configured
