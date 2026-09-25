/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.Automatic

/-!
# Direct calls to selected kernels

Word and pair storage can call a structural kernel without projecting a certificate closure.
The guard below uses the same eligibility and cost comparison as the complete portfolio. Its
selection proofs unfold that portfolio; they do not identify different algorithms through their
common numerical specification.

The generic winner also has a direct entry point for carriers without a table or limb candidate.
This exposes constant format parameters to the compiler at arbitrary precision.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Configured

/-- Storage plans whose structural candidate can be called without a carrier-specific table or
limb closure. This is a storage eligibility test, not a selection decision. -/
@[inline] def StoragePlan.firstOrderDispatch {format : FloatFormat} : StoragePlan format → Bool
  | .word16 _ | .word32 _ | .word64 _ => true
  | .wide => decide (Model.NativePair.Eligible format)
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

Keep this decision out of the arithmetic body: closed format/plan/policy applications are cached
by the compiler, while the selected structural branch remains available for specialization. -/
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

/-- A direct add call names the selected candidate's function. -/
theorem select_add_run_of_firstOrder {format : FloatFormat}
    (policy : Policy) (plan : StoragePlan format)
    (h : firstOrderSelected policy plan .add = true) :
    (selectCertified policy (automaticAddCandidates format plan)).run =
      @Backend.wordAdd format plan (Code plan) inferInstance := by
  rw [firstOrderSelected, Bool.and_eq_true] at h
  obtain ⟨hs, h⟩ := h
  cases plan <;> simp only [StoragePlan.firstOrderDispatch] at hs
  all_goals try contradiction
  all_goals
    unfold structuralSelected at h
    cases hr : Descriptor.Plan.structuralRoute? format .add with
    | none => simp [hr] at h
    | some route =>
      simp only [hr] at h
      simp [automaticAddCandidates, addCandidates, selectCertified,
        considerCertified, hr, Certified.binary, h]

/-- A direct sub call names the selected candidate's function. -/
theorem select_sub_run_of_firstOrder {format : FloatFormat}
    (policy : Policy) (plan : StoragePlan format)
    (h : firstOrderSelected policy plan .sub = true) :
    (selectCertified policy (automaticSubCandidates format plan)).run =
      @Backend.wordSub format plan (Code plan) inferInstance := by
  rw [firstOrderSelected, Bool.and_eq_true] at h
  obtain ⟨hs, h⟩ := h
  cases plan <;> simp only [StoragePlan.firstOrderDispatch] at hs
  all_goals try contradiction
  all_goals
    unfold structuralSelected at h
    cases hr : Descriptor.Plan.structuralRoute? format .sub with
    | none => simp [hr] at h
    | some route =>
      simp only [hr] at h
      simp [automaticSubCandidates, subCandidates, selectCertified,
        considerCertified, hr, Certified.binary, h]

/-- A direct mul call names the selected candidate's function. -/
theorem select_mul_run_of_firstOrder {format : FloatFormat}
    (policy : Policy) (plan : StoragePlan format)
    (h : firstOrderSelected policy plan .mul = true) :
    (selectCertified policy (automaticMulCandidates format plan)).run =
      @Backend.wordMul format plan (Code plan) inferInstance := by
  rw [firstOrderSelected, Bool.and_eq_true] at h
  obtain ⟨hs, h⟩ := h
  cases plan <;> simp only [StoragePlan.firstOrderDispatch] at hs
  all_goals try contradiction
  all_goals
    unfold structuralSelected at h
    cases hr : Descriptor.Plan.structuralRoute? format .mul with
    | none => simp [hr] at h
    | some route =>
      simp only [hr] at h
      simp [automaticMulCandidates, mulCandidates, selectCertified,
        considerCertified, hr, Certified.binary, h]

/-- A direct div call names the selected candidate's function. -/
theorem select_div_run_of_firstOrder {format : FloatFormat}
    (policy : Policy) (plan : StoragePlan format)
    (h : firstOrderSelected policy plan .div = true) :
    (selectCertified policy (automaticDivCandidates format plan)).run =
      @Backend.wordDiv format plan (Code plan) inferInstance := by
  rw [firstOrderSelected, Bool.and_eq_true] at h
  obtain ⟨hs, h⟩ := h
  cases plan <;> simp only [StoragePlan.firstOrderDispatch] at hs
  all_goals try contradiction
  all_goals
    unfold structuralSelected at h
    cases hr : Descriptor.Plan.structuralRoute? format .div with
    | none => simp [hr] at h
    | some route =>
      simp only [hr] at h
      simp [automaticDivCandidates, divCandidates, selectCertified,
        considerCertified, hr, Certified.binary, h]

/-- A direct sqrt call names the selected candidate's function. -/
theorem select_sqrt_run_of_firstOrder {format : FloatFormat}
    (policy : Policy) (plan : StoragePlan format)
    (h : firstOrderSelected policy plan .sqrt = true) :
    (selectCertified policy (automaticSqrtCandidates format plan)).run =
      @structuralSqrt format plan (Code plan) inferInstance := by
  rw [firstOrderSelected, Bool.and_eq_true] at h
  obtain ⟨hs, h⟩ := h
  cases plan <;> simp only [StoragePlan.firstOrderDispatch] at hs
  all_goals try contradiction
  all_goals
    unfold structuralSelected at h
    cases hr : Descriptor.Plan.structuralRoute? format .sqrt with
    | none => simp [hr] at h
    | some route =>
      simp only [hr] at h
      cases route <;>
        simp [automaticSqrtCandidates, sqrtCandidates, selectCertified,
          considerCertified, hr, Certified.unary, structuralSqrt, h]

/-- A direct fma call names the selected candidate's function. -/
theorem select_fma_run_of_firstOrder {format : FloatFormat}
    (policy : Policy) (plan : StoragePlan format)
    (h : firstOrderSelected policy plan .fma = true) :
    (selectCertified policy (automaticFmaCandidates format plan)).run =
      @structuralFma format plan (Code plan) inferInstance := by
  rw [firstOrderSelected, Bool.and_eq_true] at h
  obtain ⟨hs, h⟩ := h
  cases plan <;> simp only [StoragePlan.firstOrderDispatch] at hs
  all_goals try contradiction
  all_goals
    unfold structuralSelected at h
    cases hr : Descriptor.Plan.structuralRoute? format .fma with
    | none => simp [hr] at h
    | some route =>
      simp only [hr] at h
      cases route <;>
        simp [automaticFmaCandidates, fmaCandidates, selectCertified,
          considerCertified, hr, Certified.ternary, structuralFma, h]

/-- The direct generic add call names the selected candidate's function. -/
theorem select_add_run_of_firstOrderGeneric {format : FloatFormat}
    (policy : Policy) (plan : StoragePlan format)
    (h : firstOrderGenericSelected policy plan .add = true) :
    (selectCertified policy (automaticAddCandidates format plan)).run =
      @Backend.genericAdd format plan (Code plan) inferInstance := by
  cases plan <;> simp only [firstOrderGenericSelected] at h
  all_goals try contradiction
  all_goals
    unfold structuralSelected at h
    cases hr : Descriptor.Plan.structuralRoute? format .add with
    | none =>
      simp [automaticAddCandidates, addCandidates, selectCertified, hr, Certified.binary]
    | some route =>
      simp only [hr, Bool.not_eq] at h
      simp [automaticAddCandidates, addCandidates, selectCertified,
        considerCertified, hr, Certified.binary, h]

/-- The direct generic sub call names the selected candidate's function. -/
theorem select_sub_run_of_firstOrderGeneric {format : FloatFormat}
    (policy : Policy) (plan : StoragePlan format)
    (h : firstOrderGenericSelected policy plan .sub = true) :
    (selectCertified policy (automaticSubCandidates format plan)).run =
      @Backend.genericSub format plan (Code plan) inferInstance := by
  cases plan <;> simp only [firstOrderGenericSelected] at h
  all_goals try contradiction
  all_goals
    unfold structuralSelected at h
    cases hr : Descriptor.Plan.structuralRoute? format .sub with
    | none =>
      simp [automaticSubCandidates, subCandidates, selectCertified, hr, Certified.binary]
    | some route =>
      simp only [hr, Bool.not_eq] at h
      simp [automaticSubCandidates, subCandidates, selectCertified,
        considerCertified, hr, Certified.binary, h]

/-- The direct generic mul call names the selected candidate's function. -/
theorem select_mul_run_of_firstOrderGeneric {format : FloatFormat}
    (policy : Policy) (plan : StoragePlan format)
    (h : firstOrderGenericSelected policy plan .mul = true) :
    (selectCertified policy (automaticMulCandidates format plan)).run =
      @Backend.genericMul format plan (Code plan) inferInstance := by
  cases plan <;> simp only [firstOrderGenericSelected] at h
  all_goals try contradiction
  all_goals
    unfold structuralSelected at h
    cases hr : Descriptor.Plan.structuralRoute? format .mul with
    | none =>
      simp [automaticMulCandidates, mulCandidates, selectCertified, hr, Certified.binary]
    | some route =>
      simp only [hr, Bool.not_eq] at h
      simp [automaticMulCandidates, mulCandidates, selectCertified,
        considerCertified, hr, Certified.binary, h]

/-- The direct generic div call names the selected candidate's function. -/
theorem select_div_run_of_firstOrderGeneric {format : FloatFormat}
    (policy : Policy) (plan : StoragePlan format)
    (h : firstOrderGenericSelected policy plan .div = true) :
    (selectCertified policy (automaticDivCandidates format plan)).run =
      @Backend.genericDiv format plan (Code plan) inferInstance := by
  cases plan <;> simp only [firstOrderGenericSelected] at h
  all_goals try contradiction
  all_goals
    unfold structuralSelected at h
    cases hr : Descriptor.Plan.structuralRoute? format .div with
    | none =>
      simp [automaticDivCandidates, divCandidates, selectCertified, hr, Certified.binary]
    | some route =>
      simp only [hr, Bool.not_eq] at h
      simp [automaticDivCandidates, divCandidates, selectCertified,
        considerCertified, hr, Certified.binary, h]

/-- The direct generic sqrt call names the selected candidate's function. -/
theorem select_sqrt_run_of_firstOrderGeneric {format : FloatFormat}
    (policy : Policy) (plan : StoragePlan format)
    (h : firstOrderGenericSelected policy plan .sqrt = true) :
    (selectCertified policy (automaticSqrtCandidates format plan)).run =
      @Backend.genericSqrt format plan (Code plan) inferInstance := by
  cases plan <;> simp only [firstOrderGenericSelected] at h
  all_goals try contradiction
  all_goals
    unfold structuralSelected at h
    cases hr : Descriptor.Plan.structuralRoute? format .sqrt with
    | none =>
      simp [automaticSqrtCandidates, sqrtCandidates, selectCertified, hr, Certified.unary]
    | some route =>
      simp only [hr, Bool.not_eq] at h
      cases route <;>
      simp [automaticSqrtCandidates, sqrtCandidates, selectCertified,
        considerCertified, hr, Certified.unary, h]

/-- The direct generic fma call names the selected candidate's function. -/
theorem select_fma_run_of_firstOrderGeneric {format : FloatFormat}
    (policy : Policy) (plan : StoragePlan format)
    (h : firstOrderGenericSelected policy plan .fma = true) :
    (selectCertified policy (automaticFmaCandidates format plan)).run =
      @Backend.genericFma format plan (Code plan) inferInstance := by
  cases plan <;> simp only [firstOrderGenericSelected] at h
  all_goals try contradiction
  all_goals
    unfold structuralSelected at h
    cases hr : Descriptor.Plan.structuralRoute? format .fma with
    | none =>
      simp [automaticFmaCandidates, fmaCandidates, selectCertified, hr, Certified.ternary]
    | some route =>
      simp only [hr, Bool.not_eq] at h
      cases route <;>
      simp [automaticFmaCandidates, fmaCandidates, selectCertified,
        considerCertified, hr, Certified.ternary, h]

end Plan

end FloatLib.Floats.Formats.BinaryInterchange.Configured
