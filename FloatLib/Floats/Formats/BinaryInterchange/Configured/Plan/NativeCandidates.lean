/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Tactic.FixedFormat

/-!
# Certified fixed-format candidates for binary32 and binary64

Binary32 and binary64 need first-order capabilities because their public typeclass heads do not
always expose the computed storage plan during instance search. Named software certificates supply
these capabilities, and the selection theorems identify the certificate chosen by each ordinary
software portfolio under every `Policy`.

The guarded `NativeFPU.Unchecked` functions stay outside these certified portfolios. They are an
application, differential-test and benchmark API that you call by name.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan

open FloatLib.Floats.ExecFloat
open FloatLib.Floats.ExecFloat.Backend

/-! ## Cost facts for fixed-format selection -/

/--
The fixed-format structural candidate needs no resident or temporary memory, so the resource
limits of every policy admit it.
-/
theorem admissible_structuralFixedFormat {format : FloatFormat}
    (policy : Policy) (plan : StoragePlan format) (operation : Operation) :
    (structuralEstimate plan operation .fixedFormat).admissible policy = true := by
  unfold Candidate.admissible
  rw [show (structuralEstimate plan operation .fixedFormat).residentBytes = 0 from rfl,
    show (structuralEstimate plan operation .fixedFormat).temporaryBytes = 0 from rfl]
  simp

/-- Once its steady cost is lower, the fixed-format structural candidate beats the generic
baseline under every policy. -/
theorem better_structuralFixedFormat_generic {format : FloatFormat}
    (policy : Policy) (plan : StoragePlan format) (operation : Operation)
    (hsteady : (Descriptor.Plan.fixedFormatEstimate operation).steadyCost <
      (Descriptor.Plan.genericEstimate format operation).steadyCost) :
    (structuralEstimate plan operation .fixedFormat).better policy
      (genericEstimate plan operation) = true := by
  apply Candidate.better_of_warmCost_lt_of_coldCost_le
  · unfold Candidate.warmCost
    rw [show (structuralEstimate plan operation .fixedFormat).steadyCost =
          (Descriptor.Plan.fixedFormatEstimate operation).steadyCost from rfl,
      show (structuralEstimate plan operation .fixedFormat).marshallingCost =
          modelMarshallingCost plan operation from rfl,
      show (structuralEstimate plan operation .fixedFormat).allocations = 0 from rfl,
      show (structuralEstimate plan operation .fixedFormat).temporaryBytes = 0 from rfl,
      show (genericEstimate plan operation).steadyCost =
          (Descriptor.Plan.genericEstimate format operation).steadyCost from rfl,
      show (genericEstimate plan operation).marshallingCost =
          modelMarshallingCost plan operation from rfl,
      show (genericEstimate plan operation).temporaryBytes = 0 from rfl,
      Policy.memoryBlocks_zero]
    omega
  · unfold Candidate.coldCost
    rw [show (structuralEstimate plan operation .fixedFormat).setupCost = 0 from rfl,
      show (structuralEstimate plan operation .fixedFormat).setupAllocations = 0 from rfl,
      show (structuralEstimate plan operation .fixedFormat).residentBytes = 0 from rfl,
      show (genericEstimate plan operation).setupCost = 0 from rfl,
      show (genericEstimate plan operation).setupAllocations = 0 from rfl,
      show (genericEstimate plan operation).residentBytes = 0 from rfl,
      Policy.memoryBlocks_zero]

/--
A portfolio whose only alternative is the fixed-format structural candidate selects that candidate
under every policy once its steady cost is below the generic kernel's.
-/
theorem selectCertified_structuralFixedFormat {α : Type*} {spec : α} {format : FloatFormat}
    (policy : Policy) (plan : StoragePlan format) (operation : Operation)
    (dominant baseline : Certified spec)
    (hdominant : dominant.estimate = structuralEstimate plan operation .fixedFormat)
    (hbaseline : baseline.estimate = genericEstimate plan operation)
    (hsteady : (Descriptor.Plan.fixedFormatEstimate operation).steadyCost <
      (Descriptor.Plan.genericEstimate format operation).steadyCost) :
    selectCertified policy { alternatives := [dominant], baseline } = dominant := by
  refine selectCertified_cons_of_dominant policy dominant [] baseline ?_ ?_ (by simp)
  · rw [hdominant]
    exact admissible_structuralFixedFormat policy plan operation
  · rw [hdominant, hbaseline]
    exact better_structuralFixedFormat_generic policy plan operation hsteady

/-! ## Certificates, portfolios and their selection -/

fixed_format 32 Add add binary "addition"
fixed_format 32 Sub sub binary "subtraction"
fixed_format 32 Mul mul binary "multiplication"
fixed_format 32 Div div binary "division"
fixed_format 32 Sqrt sqrt unary "square root"
fixed_format 32 Fma fma ternary "fused multiply-add"

fixed_format 64 Add add binary "addition"
fixed_format 64 Sub sub binary "subtraction"
fixed_format 64 Mul mul binary "multiplication"
fixed_format 64 Div div binary "division"
fixed_format 64 Sqrt sqrt unary "square root"
fixed_format 64 Fma fma ternary "fused multiply-add"

end FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan
