/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Tactic.AutomaticCapability
public import FloatLib.Tactic.LimbCapability
public import FloatLib.Tactic.PortfolioCapability

/-!
# Capability instances for configured binary formats

This module installs the operation capabilities of configured binary formats, with
representation-independent instances for custom carriers. Higher-priority instances for
`Configured.Code` expose byte tables after dependent elimination of the selected storage plan, and
give the other non-limb plans a direct entry point to the selected structural or generic kernel. So
a closed `ExecFloat.Binary` call can specialize that kernel to its descriptor.

Priorities encode capability preference and carry no numerical meaning, because every candidate
must supply the same refinement contract before it can be selected. All of this wiring lives in
this module, which keeps storage-specific instances out of the rest of the configured API.

Every instance takes the portfolio of candidates tagged `@[compiler_optimize]` for its reference
operation. A custom carrier selects among its own candidates and the tagged ones
(`Capability.ofTagged`). A built-in carrier keeps the direct entry points below where no tagged
candidate applies, and otherwise selects among its own choice and the tagged candidates
(`Capability.Static`).
-/

@[expose] public section
namespace FloatLib.Floats.Formats.BinaryInterchange.Configured

portfolio_capability Add add FloatFormat for Spec.add
portfolio_capability Sub sub FloatFormat for Spec.sub
portfolio_capability Mul mul FloatFormat for Spec.mul
portfolio_capability Div div FloatFormat for Spec.div
portfolio_capability Sqrt sqrt FloatFormat for Spec.sqrt
portfolio_capability Fma fma FloatFormat for Spec.fma

/-!
Higher-priority built-in-carrier instances match `Code plan` before inspecting the plan. This
works for every statically computed precision, including a `forKnownWidth` expression that has not
yet reduced to a storage constructor during typeclass indexing. The dependent candidate helpers
then add direct byte tables when the selected plan is `.byte`, and only then.

Families with a custom carrier use the representation-independent instances above.
-/

/-!
## First-order entry points

A machine-word or pair plan goes straight to its structural kernel when that candidate wins
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
      if hpair : Model.NativePair.Eligible format then Backend.pairSqrt hgt hle hpair
      else structuralSqrt
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
      if hpair : Model.NativePair.Eligible format then Backend.pairFma hgt hle hpair
      else structuralFma
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

automatic_capability Add add Plan.automaticAddCandidates (left right) :=
  Backend.directAdd, Backend.directAdd_eq
automatic_capability Sub sub Plan.automaticSubCandidates (left right) :=
  Backend.directSub, Backend.directSub_eq
automatic_capability Mul mul Plan.automaticMulCandidates (left right) :=
  Backend.directMul, Backend.directMul_eq
automatic_capability Div div Plan.automaticDivCandidates (left right) :=
  Backend.directDiv, Backend.directDiv_eq
automatic_capability Sqrt sqrt Plan.automaticSqrtCandidates (value) :=
  Plan.directSqrt, Plan.directSqrt_eq
automatic_capability Fma fma Plan.automaticFmaCandidates (left right addend) :=
  Plan.directFma, Plan.directFma_eq

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

limb_capability Add add "addition"
limb_capability Sub sub "subtraction"
limb_capability Mul mul "multiplication"
limb_capability Div div "division"
limb_capability Sqrt sqrt "square root"
limb_capability Fma fma "fused multiply-add"

end FloatLib.Floats.Formats.BinaryInterchange.Configured
