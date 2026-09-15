/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.Candidates
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Storage.Codecs

/-!
# Certified fixed-format candidates for binary32 and binary64

Binary32 and binary64 need first-order capabilities because their public typeclass heads do not
always expose the computed storage plan during instance search. Named software certificates supply
these capabilities, and the selection theorems identify the certificate chosen by each ordinary
software portfolio under every `Policy`.

The guarded `NativeFPU.Unchecked` functions remain an explicit application, differential-test, and
benchmark API outside these certified portfolios.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan

open FloatLib.Floats.ExecFloat
open FloatLib.Floats.ExecFloat.Backend

/-! ## Named fixed-format certificates -/

/-- Certified fixed-word binary32 addition. -/
def softwareAdd32Certified (width_le : FloatFormat.binary32.bitWidth ≤ 32) :
    Certified
      (@Spec.add FloatFormat.binary32 (.word32 width_le) (Code (.word32 width_le))
        inferInstance) :=
  Certified.binary (structuralEstimate (.word32 width_le) .add .fixedFormat)
    Spec.add Backend.wordAdd Backend.wordAdd_eq_spec

/-- Certified fixed-word binary32 subtraction. -/
def softwareSub32Certified (width_le : FloatFormat.binary32.bitWidth ≤ 32) :
    Certified
      (@Spec.sub FloatFormat.binary32 (.word32 width_le) (Code (.word32 width_le))
        inferInstance) :=
  Certified.binary (structuralEstimate (.word32 width_le) .sub .fixedFormat)
    Spec.sub Backend.wordSub Backend.wordSub_eq_spec

/-- Certified fixed-word binary32 multiplication. -/
def softwareMul32Certified (width_le : FloatFormat.binary32.bitWidth ≤ 32) :
    Certified
      (@Spec.mul FloatFormat.binary32 (.word32 width_le) (Code (.word32 width_le))
        inferInstance) :=
  Certified.binary (structuralEstimate (.word32 width_le) .mul .fixedFormat)
    Spec.mul Backend.wordMul Backend.wordMul_eq_spec

/-- Certified fixed-word binary32 division. -/
def softwareDiv32Certified (width_le : FloatFormat.binary32.bitWidth ≤ 32) :
    Certified
      (@Spec.div FloatFormat.binary32 (.word32 width_le) (Code (.word32 width_le))
        inferInstance) :=
  Certified.binary (structuralEstimate (.word32 width_le) .div .fixedFormat)
    Spec.div Backend.wordDiv Backend.wordDiv_eq_spec

/-- Certified fixed-word binary32 square root. -/
def softwareSqrt32Certified (width_le : FloatFormat.binary32.bitWidth ≤ 32) :
    Certified
      (@Spec.sqrt FloatFormat.binary32 (.word32 width_le) (Code (.word32 width_le))
        inferInstance) :=
  Certified.unary (structuralEstimate (.word32 width_le) .sqrt .fixedFormat)
    Spec.sqrt Backend.wordSqrt Backend.wordSqrt_eq_spec

/-- Certified fixed-word binary32 fused multiply-add. -/
def softwareFma32Certified (width_le : FloatFormat.binary32.bitWidth ≤ 32) :
    Certified
      (@Spec.fma FloatFormat.binary32 (.word32 width_le) (Code (.word32 width_le))
        inferInstance) :=
  Certified.ternary (structuralEstimate (.word32 width_le) .fma .fixedFormat)
    Spec.fma Backend.wordFma Backend.wordFma_eq_spec

/-- Certified fixed-word binary64 addition. -/
def softwareAdd64Certified (width_le : FloatFormat.binary64.bitWidth ≤ 64) :
    Certified
      (@Spec.add FloatFormat.binary64 (.word64 width_le) (Code (.word64 width_le))
        inferInstance) :=
  Certified.binary (structuralEstimate (.word64 width_le) .add .fixedFormat)
    Spec.add Backend.wordAdd Backend.wordAdd_eq_spec

/-- Certified fixed-word binary64 subtraction. -/
def softwareSub64Certified (width_le : FloatFormat.binary64.bitWidth ≤ 64) :
    Certified
      (@Spec.sub FloatFormat.binary64 (.word64 width_le) (Code (.word64 width_le))
        inferInstance) :=
  Certified.binary (structuralEstimate (.word64 width_le) .sub .fixedFormat)
    Spec.sub Backend.wordSub Backend.wordSub_eq_spec

/-- Certified fixed-word binary64 multiplication. -/
def softwareMul64Certified (width_le : FloatFormat.binary64.bitWidth ≤ 64) :
    Certified
      (@Spec.mul FloatFormat.binary64 (.word64 width_le) (Code (.word64 width_le))
        inferInstance) :=
  Certified.binary (structuralEstimate (.word64 width_le) .mul .fixedFormat)
    Spec.mul Backend.wordMul Backend.wordMul_eq_spec

/-- Certified fixed-word binary64 division. -/
def softwareDiv64Certified (width_le : FloatFormat.binary64.bitWidth ≤ 64) :
    Certified
      (@Spec.div FloatFormat.binary64 (.word64 width_le) (Code (.word64 width_le))
        inferInstance) :=
  Certified.binary (structuralEstimate (.word64 width_le) .div .fixedFormat)
    Spec.div Backend.wordDiv Backend.wordDiv_eq_spec

/-- Certified fixed-word binary64 square root. -/
def softwareSqrt64Certified (width_le : FloatFormat.binary64.bitWidth ≤ 64) :
    Certified
      (@Spec.sqrt FloatFormat.binary64 (.word64 width_le) (Code (.word64 width_le))
        inferInstance) :=
  Certified.unary (structuralEstimate (.word64 width_le) .sqrt .fixedFormat)
    Spec.sqrt Backend.wordSqrt Backend.wordSqrt_eq_spec

/-- Certified fixed-word binary64 fused multiply-add. -/
def softwareFma64Certified (width_le : FloatFormat.binary64.bitWidth ≤ 64) :
    Certified
      (@Spec.fma FloatFormat.binary64 (.word64 width_le) (Code (.word64 width_le))
        inferInstance) :=
  Certified.ternary (structuralEstimate (.word64 width_le) .fma .fixedFormat)
    Spec.fma Backend.wordFma Backend.wordFma_eq_spec

/-! ## Complete software portfolios -/

/-- Every certified software implementation considered for binary32 addition. -/
def binary32AddCandidates (width_le : FloatFormat.binary32.bitWidth ≤ 32) :
    CandidateSet
      (Certified
        (@Spec.add FloatFormat.binary32 (.word32 width_le) (Code (.word32 width_le))
          inferInstance)) :=
  addCandidates FloatFormat.binary32 (.word32 width_le)

/-- Every certified software implementation considered for binary32 subtraction. -/
def binary32SubCandidates (width_le : FloatFormat.binary32.bitWidth ≤ 32) :
    CandidateSet
      (Certified
        (@Spec.sub FloatFormat.binary32 (.word32 width_le) (Code (.word32 width_le))
          inferInstance)) :=
  subCandidates FloatFormat.binary32 (.word32 width_le)

/-- Every certified software implementation considered for binary32 multiplication. -/
def binary32MulCandidates (width_le : FloatFormat.binary32.bitWidth ≤ 32) :
    CandidateSet
      (Certified
        (@Spec.mul FloatFormat.binary32 (.word32 width_le) (Code (.word32 width_le))
          inferInstance)) :=
  mulCandidates FloatFormat.binary32 (.word32 width_le)

/-- Every certified software implementation considered for binary32 division. -/
def binary32DivCandidates (width_le : FloatFormat.binary32.bitWidth ≤ 32) :
    CandidateSet
      (Certified
        (@Spec.div FloatFormat.binary32 (.word32 width_le) (Code (.word32 width_le))
          inferInstance)) :=
  divCandidates FloatFormat.binary32 (.word32 width_le)

/-- Every certified software implementation considered for binary32 square root. -/
def binary32SqrtCandidates (width_le : FloatFormat.binary32.bitWidth ≤ 32) :
    CandidateSet
      (Certified
        (@Spec.sqrt FloatFormat.binary32 (.word32 width_le) (Code (.word32 width_le))
          inferInstance)) :=
  sqrtCandidates FloatFormat.binary32 (.word32 width_le)

/-- Every certified software implementation considered for binary32 fused multiply-add. -/
def binary32FmaCandidates (width_le : FloatFormat.binary32.bitWidth ≤ 32) :
    CandidateSet
      (Certified
        (@Spec.fma FloatFormat.binary32 (.word32 width_le) (Code (.word32 width_le))
          inferInstance)) :=
  fmaCandidates FloatFormat.binary32 (.word32 width_le)

/-- Every certified software implementation considered for binary64 addition. -/
def binary64AddCandidates (width_le : FloatFormat.binary64.bitWidth ≤ 64) :
    CandidateSet
      (Certified
        (@Spec.add FloatFormat.binary64 (.word64 width_le) (Code (.word64 width_le))
          inferInstance)) :=
  addCandidates FloatFormat.binary64 (.word64 width_le)

/-- Every certified software implementation considered for binary64 subtraction. -/
def binary64SubCandidates (width_le : FloatFormat.binary64.bitWidth ≤ 64) :
    CandidateSet
      (Certified
        (@Spec.sub FloatFormat.binary64 (.word64 width_le) (Code (.word64 width_le))
          inferInstance)) :=
  subCandidates FloatFormat.binary64 (.word64 width_le)

/-- Every certified software implementation considered for binary64 multiplication. -/
def binary64MulCandidates (width_le : FloatFormat.binary64.bitWidth ≤ 64) :
    CandidateSet
      (Certified
        (@Spec.mul FloatFormat.binary64 (.word64 width_le) (Code (.word64 width_le))
          inferInstance)) :=
  mulCandidates FloatFormat.binary64 (.word64 width_le)

/-- Every certified software implementation considered for binary64 division. -/
def binary64DivCandidates (width_le : FloatFormat.binary64.bitWidth ≤ 64) :
    CandidateSet
      (Certified
        (@Spec.div FloatFormat.binary64 (.word64 width_le) (Code (.word64 width_le))
          inferInstance)) :=
  divCandidates FloatFormat.binary64 (.word64 width_le)

/-- Every certified software implementation considered for binary64 square root. -/
def binary64SqrtCandidates (width_le : FloatFormat.binary64.bitWidth ≤ 64) :
    CandidateSet
      (Certified
        (@Spec.sqrt FloatFormat.binary64 (.word64 width_le) (Code (.word64 width_le))
          inferInstance)) :=
  sqrtCandidates FloatFormat.binary64 (.word64 width_le)

/-- Every certified software implementation considered for binary64 fused multiply-add. -/
def binary64FmaCandidates (width_le : FloatFormat.binary64.bitWidth ≤ 64) :
    CandidateSet
      (Certified
        (@Spec.fma FloatFormat.binary64 (.word64 width_le) (Code (.word64 width_le))
          inferInstance)) :=
  fmaCandidates FloatFormat.binary64 (.word64 width_le)

/-! ## Cost facts for fixed-format selection -/

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

/-! ## Fixed-format selection for binary32 -/

theorem selectCertified_binary32AddCandidates
    (policy : Policy) (width_le : FloatFormat.binary32.bitWidth ≤ 32) :
    selectCertified policy (binary32AddCandidates width_le) =
      softwareAdd32Certified width_le := by
  unfold binary32AddCandidates addCandidates
  rw [show Descriptor.Plan.structuralRoute? FloatFormat.binary32 .add =
      some .fixedFormat from rfl]
  refine selectCertified_cons_of_dominant policy _ [] _ ?_ ?_ (by simp)
  · exact admissible_structuralFixedFormat policy (.word32 width_le) .add
  · exact better_structuralFixedFormat_generic policy (.word32 width_le) .add (by decide)

/-- Under every policy the binary32 subtraction portfolio selects the certified software kernel. -/
theorem selectCertified_binary32SubCandidates
    (policy : Policy) (width_le : FloatFormat.binary32.bitWidth ≤ 32) :
    selectCertified policy (binary32SubCandidates width_le) =
      softwareSub32Certified width_le := by
  unfold binary32SubCandidates subCandidates
  rw [show Descriptor.Plan.structuralRoute? FloatFormat.binary32 .sub =
      some .fixedFormat from rfl]
  refine selectCertified_cons_of_dominant policy _ [] _ ?_ ?_ (by simp)
  · exact admissible_structuralFixedFormat policy (.word32 width_le) .sub
  · exact better_structuralFixedFormat_generic policy (.word32 width_le) .sub (by decide)

/-- Under every policy the binary32 multiplication portfolio selects the certified software
kernel. -/
theorem selectCertified_binary32MulCandidates
    (policy : Policy) (width_le : FloatFormat.binary32.bitWidth ≤ 32) :
    selectCertified policy (binary32MulCandidates width_le) =
      softwareMul32Certified width_le := by
  unfold binary32MulCandidates mulCandidates
  rw [show Descriptor.Plan.structuralRoute? FloatFormat.binary32 .mul =
      some .fixedFormat from rfl]
  refine selectCertified_cons_of_dominant policy _ [] _ ?_ ?_ (by simp)
  · exact admissible_structuralFixedFormat policy (.word32 width_le) .mul
  · exact better_structuralFixedFormat_generic policy (.word32 width_le) .mul (by decide)

/-- Under every policy the binary32 division portfolio selects the certified software kernel. -/
theorem selectCertified_binary32DivCandidates
    (policy : Policy) (width_le : FloatFormat.binary32.bitWidth ≤ 32) :
    selectCertified policy (binary32DivCandidates width_le) =
      softwareDiv32Certified width_le := by
  unfold binary32DivCandidates divCandidates
  rw [show Descriptor.Plan.structuralRoute? FloatFormat.binary32 .div =
      some .fixedFormat from rfl]
  refine selectCertified_cons_of_dominant policy _ [] _ ?_ ?_ (by simp)
  · exact admissible_structuralFixedFormat policy (.word32 width_le) .div
  · exact better_structuralFixedFormat_generic policy (.word32 width_le) .div (by decide)

/-- Under every policy the binary32 square-root portfolio selects the certified software kernel. -/
theorem selectCertified_binary32SqrtCandidates
    (policy : Policy) (width_le : FloatFormat.binary32.bitWidth ≤ 32) :
    selectCertified policy (binary32SqrtCandidates width_le) =
      softwareSqrt32Certified width_le := by
  unfold binary32SqrtCandidates sqrtCandidates
  rw [show Descriptor.Plan.structuralRoute? FloatFormat.binary32 .sqrt =
      some .fixedFormat from rfl]
  refine selectCertified_cons_of_dominant policy _ [] _ ?_ ?_ (by simp)
  · exact admissible_structuralFixedFormat policy (.word32 width_le) .sqrt
  · exact better_structuralFixedFormat_generic policy (.word32 width_le) .sqrt (by decide)

/-- Under every policy the binary32 fused multiply-add portfolio selects the certified software
kernel. -/
theorem selectCertified_binary32FmaCandidates
    (policy : Policy) (width_le : FloatFormat.binary32.bitWidth ≤ 32) :
    selectCertified policy (binary32FmaCandidates width_le) =
      softwareFma32Certified width_le := by
  unfold binary32FmaCandidates fmaCandidates
  rw [show Descriptor.Plan.structuralRoute? FloatFormat.binary32 .fma =
      some .fixedFormat from rfl]
  refine selectCertified_cons_of_dominant policy _ [] _ ?_ ?_ (by simp)
  · exact admissible_structuralFixedFormat policy (.word32 width_le) .fma
  · exact better_structuralFixedFormat_generic policy (.word32 width_le) .fma (by decide)

/-! ## Fixed-format selection for binary64 -/

theorem selectCertified_binary64AddCandidates
    (policy : Policy) (width_le : FloatFormat.binary64.bitWidth ≤ 64) :
    selectCertified policy (binary64AddCandidates width_le) =
      softwareAdd64Certified width_le := by
  unfold binary64AddCandidates addCandidates
  rw [show Descriptor.Plan.structuralRoute? FloatFormat.binary64 .add =
      some .fixedFormat from rfl]
  refine selectCertified_cons_of_dominant policy _ [] _ ?_ ?_ (by simp)
  · exact admissible_structuralFixedFormat policy (.word64 width_le) .add
  · exact better_structuralFixedFormat_generic policy (.word64 width_le) .add (by decide)

/-- Under every policy the binary64 subtraction portfolio selects the certified software kernel. -/
theorem selectCertified_binary64SubCandidates
    (policy : Policy) (width_le : FloatFormat.binary64.bitWidth ≤ 64) :
    selectCertified policy (binary64SubCandidates width_le) =
      softwareSub64Certified width_le := by
  unfold binary64SubCandidates subCandidates
  rw [show Descriptor.Plan.structuralRoute? FloatFormat.binary64 .sub =
      some .fixedFormat from rfl]
  refine selectCertified_cons_of_dominant policy _ [] _ ?_ ?_ (by simp)
  · exact admissible_structuralFixedFormat policy (.word64 width_le) .sub
  · exact better_structuralFixedFormat_generic policy (.word64 width_le) .sub (by decide)

/-- Under every policy the binary64 multiplication portfolio selects the certified software
kernel. -/
theorem selectCertified_binary64MulCandidates
    (policy : Policy) (width_le : FloatFormat.binary64.bitWidth ≤ 64) :
    selectCertified policy (binary64MulCandidates width_le) =
      softwareMul64Certified width_le := by
  unfold binary64MulCandidates mulCandidates
  rw [show Descriptor.Plan.structuralRoute? FloatFormat.binary64 .mul =
      some .fixedFormat from rfl]
  refine selectCertified_cons_of_dominant policy _ [] _ ?_ ?_ (by simp)
  · exact admissible_structuralFixedFormat policy (.word64 width_le) .mul
  · exact better_structuralFixedFormat_generic policy (.word64 width_le) .mul (by decide)

/-- Under every policy the binary64 division portfolio selects the certified software kernel. -/
theorem selectCertified_binary64DivCandidates
    (policy : Policy) (width_le : FloatFormat.binary64.bitWidth ≤ 64) :
    selectCertified policy (binary64DivCandidates width_le) =
      softwareDiv64Certified width_le := by
  unfold binary64DivCandidates divCandidates
  rw [show Descriptor.Plan.structuralRoute? FloatFormat.binary64 .div =
      some .fixedFormat from rfl]
  refine selectCertified_cons_of_dominant policy _ [] _ ?_ ?_ (by simp)
  · exact admissible_structuralFixedFormat policy (.word64 width_le) .div
  · exact better_structuralFixedFormat_generic policy (.word64 width_le) .div (by decide)

/-- Under every policy the binary64 square-root portfolio selects the certified software kernel. -/
theorem selectCertified_binary64SqrtCandidates
    (policy : Policy) (width_le : FloatFormat.binary64.bitWidth ≤ 64) :
    selectCertified policy (binary64SqrtCandidates width_le) =
      softwareSqrt64Certified width_le := by
  unfold binary64SqrtCandidates sqrtCandidates
  rw [show Descriptor.Plan.structuralRoute? FloatFormat.binary64 .sqrt =
      some .fixedFormat from rfl]
  refine selectCertified_cons_of_dominant policy _ [] _ ?_ ?_ (by simp)
  · exact admissible_structuralFixedFormat policy (.word64 width_le) .sqrt
  · exact better_structuralFixedFormat_generic policy (.word64 width_le) .sqrt (by decide)

/-- Under every policy the binary64 fused multiply-add portfolio selects the certified software
kernel. -/
theorem selectCertified_binary64FmaCandidates
    (policy : Policy) (width_le : FloatFormat.binary64.bitWidth ≤ 64) :
    selectCertified policy (binary64FmaCandidates width_le) =
      softwareFma64Certified width_le := by
  unfold binary64FmaCandidates fmaCandidates
  rw [show Descriptor.Plan.structuralRoute? FloatFormat.binary64 .fma =
      some .fixedFormat from rfl]
  refine selectCertified_cons_of_dominant policy _ [] _ ?_ ?_ (by simp)
  · exact admissible_structuralFixedFormat policy (.word64 width_le) .fma
  · exact better_structuralFixedFormat_generic policy (.word64 width_le) .fma (by decide)

end FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan
