/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Tactic.FirstOrder

/-!
# Direct calls to selected kernels

Word and pair storage can call a structural kernel without projecting a certificate closure.
The guard below uses the same eligibility and cost comparison as the complete portfolio. Its
selection proofs unfold that portfolio and show that the direct call is the selected candidate's
own function. Another algorithm with the same numerical specification would not count.

The generic winner also has a direct entry point for carriers without a table or limb candidate,
which exposes constant format parameters to the compiler at arbitrary precision.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Configured

/-- Storage plans whose structural candidate can be called without a carrier-specific table or
limb closure. It tests storage eligibility and makes no selection decision. -/
@[inline] def StoragePlan.firstOrderDispatch {format : FloatFormat} : StoragePlan format → Bool
  | .word16 _ | .word32 _ | .word64 _ => true
  | .pair _ _ | .wide => decide (Model.NativePair.Eligible format)
  | .byte _ | .limbs _ => false

namespace Plan

open FloatLib.Floats.ExecFloat.Backend

/-- Whether the structural candidate wins its comparison with the generic kernel. -/
@[inline] def structuralSelected {format : FloatFormat}
    (policy : Policy) (plan : StoragePlan format) (operation : Operation) : Bool :=
  match Descriptor.Plan.structuralRoute? format operation with
  | none => false
  | some route =>
      (structuralEstimate plan operation route).admissible policy &&
        (structuralEstimate plan operation route).better policy (genericEstimate plan operation)

/-- Whether a direct structural call executes the winner of the complete configured portfolio.

It is kept out of the arithmetic body: the compiler caches closed format/plan/policy applications,
and the selected structural branch stays open to specialization. -/
@[noinline] def firstOrderSelected {format : FloatFormat}
    (policy : Policy) (plan : StoragePlan format) (operation : Operation) : Bool :=
  plan.firstOrderDispatch && structuralSelected policy plan operation

/-- Whether the generic kernel wins a portfolio with no carrier-specific direct candidates. -/
@[noinline] def firstOrderGenericSelected {format : FloatFormat}
    (policy : Policy) (plan : StoragePlan format) (operation : Operation) : Bool :=
  match plan with
  | .byte _ | .limbs _ => false
  | _ => !structuralSelected policy plan operation

/-- The square-root function stored in the descriptor's structural candidate. -/
@[always_inline] def structuralSqrt {format : FloatFormat} {plan : StoragePlan format}
    {code : Type} [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] :=
  match Descriptor.Plan.structuralRoute? format .sqrt with
  | some .fixedLimbs => @Backend.fixedLimbSqrt format plan code _
  | _ => @Backend.wordSqrt format plan code _

/-- The fused-multiply-add function stored in the descriptor's structural candidate. -/
@[always_inline] def structuralFma {format : FloatFormat} {plan : StoragePlan format}
    {code : Type} [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] :=
  match Descriptor.Plan.structuralRoute? format .fma with
  | some .fixedLimbs => @Backend.fixedLimbFma format plan code _
  | _ => @Backend.wordFma format plan code _

first_order Add add binary := Backend.wordAdd
first_order Sub sub binary := Backend.wordSub
first_order Mul mul binary := Backend.wordMul
first_order Div div binary := Backend.wordDiv
first_order Sqrt sqrt unary routed := structuralSqrt
first_order Fma fma ternary routed := structuralFma

end Plan

end FloatLib.Floats.Formats.BinaryInterchange.Configured
