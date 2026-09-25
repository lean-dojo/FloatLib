/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.FirstOrder
public import FloatLib.Floats.ExecFloat.Core.Capability

/-!
# Capability instances for configured binary formats

Representation-independent instances serve custom carriers. Higher-priority instances for
`Configured.Code` expose byte tables after dependent elimination of the selected storage plan, and
give the other non-limb plans a direct entry point to the selected structural or generic kernel.
A closed `ExecFloat.Binary` call can therefore specialize that kernel to its descriptor.

The priorities encode capability preference, not numerical semantics: every candidate must supply
the same refinement contract before it can be selected. Keeping this wiring in one module makes
backend choice inspectable and prevents storage-specific instances from leaking through the rest
of the configured API.
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

Families with a custom carrier continue to use the representation-independent instances above.
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
word and fixed-limb square root and FMA; numerical equivalence alone does not justify a route.
-/

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
        Backend.wordAdd left right
      else if Plan.firstOrderGenericSelected planning.policy plan .add then
        Backend.genericAdd left right
      else
        selection.get.run left right
    execute_eq_implementation := by
      funext left right
      split
      · rename_i h
        rw [← Plan.select_add_run_of_firstOrder planning.policy plan h]
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
        Backend.wordSub left right
      else if Plan.firstOrderGenericSelected planning.policy plan .sub then
        Backend.genericSub left right
      else
        selection.get.run left right
    execute_eq_implementation := by
      funext left right
      split
      · rename_i h
        rw [← Plan.select_sub_run_of_firstOrder planning.policy plan h]
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
        Backend.wordMul left right
      else if Plan.firstOrderGenericSelected planning.policy plan .mul then
        Backend.genericMul left right
      else
        selection.get.run left right
    execute_eq_implementation := by
      funext left right
      split
      · rename_i h
        rw [← Plan.select_mul_run_of_firstOrder planning.policy plan h]
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
        Backend.wordDiv left right
      else if Plan.firstOrderGenericSelected planning.policy plan .div then
        Backend.genericDiv left right
      else
        selection.get.run left right
    execute_eq_implementation := by
      funext left right
      split
      · rename_i h
        rw [← Plan.select_div_run_of_firstOrder planning.policy plan h]
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
        Plan.structuralSqrt value
      else if Plan.firstOrderGenericSelected planning.policy plan .sqrt then
        Backend.genericSqrt value
      else
        selection.get.run value
    execute_eq_implementation := by
      funext value
      split
      · rename_i h
        rw [← Plan.select_sqrt_run_of_firstOrder planning.policy plan h]
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
        Plan.structuralFma left right addend
      else if Plan.firstOrderGenericSelected planning.policy plan .fma then
        Backend.genericFma left right addend
      else
        selection.get.run left right addend
    execute_eq_implementation := by
      funext left right addend
      split
      · rename_i h
        rw [← Plan.select_fma_run_of_firstOrder planning.policy plan h]
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

Keep this below `codecForPlan`: `ModelCodec.Code` is an output parameter, so unresolved codec
goals must try the generic plan before the concrete limb carrier. This preserves inference for
conversions between definitionally equal descriptors such as `Binary.format 8 23` and `binary32`.
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
