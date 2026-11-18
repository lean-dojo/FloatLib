/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Tactic.KernelRefl
public import FloatLib.Floats.Formats.P3109.Arithmetic.Queries.Proof
public import FloatLib.Tactic.KernelInline
public import FloatLib.Tactic.KernelOptimize
public import FloatLib.Tactic.CompilerOptimize

/-!
# P3109 classification, total order and policy queries

The unapproved P3109 interim report v4.1 (14 September 2026), §§4.12.1, 4.13.1
and 4.15, specifies these operations separately from ordinary comparisons and
predicates. `Class` implements the eight rows of Table 2. `TotalOrder` puts NaN
first, including when both operands are NaN, and accepts independent source
descriptors. Policy queries retain every supplied stochastic word.

`class_condition` proves the Table 2 condition of the returned class for every
valid descriptor. The total-order branch equations state its special-value
behavior, and the kernel rewrite preserves the complete classifier by definitional
equality.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.P3109

/-- The eight classifier results of P3109 interim report v4.1, §4.13.1, Table 2 (unapproved
    draft). -/
inductive ClassEnum where
  /-- The NaN. -/
  | ClsNaN
  /-- Negative infinity. -/
  | ClsNegativeInfinity
  /-- A negative normal number. -/
  | ClsNegativeNormal
  /-- A negative subnormal number. -/
  | ClsNegativeSubnormal
  /-- Zero. -/
  | ClsZero
  /-- A positive subnormal number. -/
  | ClsPositiveSubnormal
  /-- A positive normal number. -/
  | ClsPositiveNormal
  /-- Positive infinity. -/
  | ClsPositiveInfinity
  deriving DecidableEq, Repr

/-- Reconstruct a `ClassEnum` constructor from its constructor index. -/
add_decl_doc ClassEnum.ofNat_ctorIdx

namespace ProjectionPolicy

/-- P3109 interim report v4.1, §4.15: the rounding component of a projection specification.
This is the exact record projection, including the stochastic random word. -/
@[inline] def RoundOf (policy : ProjectionPolicy) : RoundingMode :=
  policy.rounding

/-- P3109 interim report v4.1, §4.15: the saturation component of a projection specification.
This is the exact record projection. -/
@[inline] def SatOf (policy : ProjectionPolicy) : SaturationMode :=
  policy.saturation

end ProjectionPolicy
end FloatLib.Floats.Formats.P3109

namespace FloatLib.Floats.ExecFloat.P3109

open Formats.P3109

variable {format rightFormat : Format}

/-- P3109 interim report v4.1, §4.13.1: classify any datum by Table 2, including precision one.
`class_condition` proves the condition of the selected row. -/
@[inline] def Class (value : ExecFloat.P3109 format) : ClassEnum :=
  if value.IsNaN then .ClsNaN
  else if value.IsInfinite then
    if value.IsSignMinus then .ClsNegativeInfinity else .ClsPositiveInfinity
  else if value.IsZero then .ClsZero
  else if value.IsNormal then
    if value.IsSignMinus then .ClsNegativeNormal else .ClsPositiveNormal
  else
    if value.IsSignMinus then .ClsNegativeSubnormal else .ClsPositiveSubnormal

/-- The condition of each row of P3109 interim report v4.1, §4.13.1, Table 2. -/
def ClassCondition (value : ExecFloat.P3109 format) : ClassEnum → Bool
  | .ClsNaN => value.IsNaN
  | .ClsNegativeInfinity => value.IsInfinite && value.IsSignMinus
  | .ClsNegativeNormal => value.IsNormal && value.IsSignMinus
  | .ClsNegativeSubnormal => value.IsSubnormal && value.IsSignMinus
  | .ClsZero => value.IsZero
  | .ClsPositiveSubnormal => value.IsSubnormal && !value.IsSignMinus
  | .ClsPositiveNormal => value.IsNormal && !value.IsSignMinus
  | .ClsPositiveInfinity => value.IsInfinite && !value.IsSignMinus

private theorem magnitudeBits_pos_of_nonzero (value : ExecFloat.P3109 format)
    (hnan : value.IsNaN = false) (hzero : value.IsZero = false) :
    0 < value.magnitudeBits := by
  have hzero' : value.toNatBits ≠ 0 := by simpa [IsZero] using hzero
  have hnan' : value.toNatBits ≠ format.nanBits := by simpa [IsNaN] using hnan
  cases hs : format.signedness <;>
    simp only [ne_eq, Format.nanBits, hs, magnitudeBits, BEq.rfl, Bool.true_and,
      Bool.and_eq_true, beq_iff_eq, reduceCtorEq, decide_eq_true_eq, false_and,
      ↓reduceIte, gt_iff_lt] at * <;>
    (try split_ifs) <;> omega

/-- For every valid descriptor, the returned class satisfies its exact Table 2 condition. -/
theorem class_condition (value : ExecFloat.P3109 format) :
    ClassCondition value (Class value) = true := by
  by_cases hn : value.IsNaN = true
  · simp [Class, ClassCondition, hn]
  have hn' := Bool.eq_false_of_not_eq_true hn
  by_cases hi : value.IsInfinite = true
  · cases hs : value.IsSignMinus <;> simp [Class, ClassCondition, hn', hi, hs]
  have hi' := Bool.eq_false_of_not_eq_true hi
  by_cases hz : value.IsZero = true
  · simp [Class, ClassCondition, hn', hi', hz]
  have hz' := Bool.eq_false_of_not_eq_true hz
  by_cases hm : value.IsNormal = true
  · cases hs : value.IsSignMinus <;> simp [Class, ClassCondition, hn', hi', hz', hm, hs]
  have hm' := Bool.eq_false_of_not_eq_true hm
  have hf : value.IsFinite = true := by simp [IsFinite, hn', hi']
  have hsub : value.IsSubnormal = true :=
    (isNormal_or_isSubnormal value hf (magnitudeBits_pos_of_nonzero value hn' hz')).resolve_left hm
  cases hs : value.IsSignMinus <;>
    simp [Class, ClassCondition, hn', hi', hz', hm', hsub, hs]

/-- The Table 2 conditions identify exactly one class for every valid descriptor. -/
theorem class_eq_iff (value : ExecFloat.P3109 format) (kind : ClassEnum) :
    Class value = kind ↔ ClassCondition value kind = true := by
  have hzero : value.IsZero = true →
      value.IsFinite = true ∧ value.magnitudeBits = 0 := by
    intro hz
    constructor
    · have he := (isZero_iff_toClosedRat value).mp hz
      change Arithmetic.toRat value.decode = .finite 0 at he
      apply (isFinite_iff_decode value).mpr
      cases hd : value.decode with
      | finite exact => exact ⟨exact, rfl⟩
      | infinity sign => simp only [hd, Arithmetic.toRat, reduceCtorEq] at he
      | exceptional exception =>
          simp only [hd, Arithmetic.toRat, Arithmetic.nan, reduceCtorEq] at he
    · have hb : value.toNatBits = 0 := by simpa [IsZero] using hz
      simp [magnitudeBits, hb]
  have hinf : value.IsInfinite = true → value.IsNaN = false := by
    intro hi
    obtain ⟨sign, hd⟩ := (isInf_iff_decode value).mp hi
    apply Bool.eq_false_of_not_eq_true
    intro hn
    have hn := (isNaN_iff_decode value).mp hn
    change value.decode = .exceptional .nan at hn
    rw [hd] at hn
    cases hn
  constructor
  · intro h
    simpa [h] using class_condition value
  · intro hk
    have hc := class_condition value
    generalize Class value = actual at hc ⊢
    cases actual <;> cases kind <;>
      simp_all [ClassCondition, IsNormal, IsSubnormal, IsFinite] <;> omega

/-- P3109 interim report v4.1, §4.12.1: NaN first, otherwise exact non-strict comparison.
The two operands may have independent P3109 descriptors; external formats are excluded. -/
@[inline] def TotalOrder (left : ExecFloat.P3109 format)
    (right : ExecFloat.P3109 rightFormat) : Bool :=
  if left.IsNaN then true
  else if right.IsNaN then false
  else CompareLessEqual left right

/-- P3109 total order places NaN first, including a pair of NaNs.

Reference: P3109 Interim Report v4.1 (unapproved draft), §§4.12.1.
-/
@[simp] theorem totalOrder_of_isNaN_left (left : ExecFloat.P3109 format)
    (right : ExecFloat.P3109 rightFormat) (h : left.IsNaN = true) :
    TotalOrder left right = true := by
  simp [TotalOrder, h]

/-- A non-NaN never precedes NaN in P3109 total order.

Reference: P3109 Interim Report v4.1 (unapproved draft), §§4.12.1.
-/
theorem totalOrder_of_isNaN_right (left : ExecFloat.P3109 format)
    (right : ExecFloat.P3109 rightFormat) (hl : left.IsNaN = false) (hr : right.IsNaN = true) :
    TotalOrder left right = false := by
  simp [TotalOrder, hl, hr]

/-- Away from NaN, P3109 total order is exact numerical non-strict comparison.

Reference: P3109 Interim Report v4.1 (unapproved draft), §§4.12.1.
-/
theorem totalOrder_of_not_isNaN (left : ExecFloat.P3109 format)
    (right : ExecFloat.P3109 rightFormat) (hl : left.IsNaN = false) (hr : right.IsNaN = false) :
    TotalOrder left right = CompareLessEqual left right := by
  simp [TotalOrder, hl, hr]

namespace QueryKernel

/-- The same P3109 Table 2 classifier with its field-reading stages unfolded for the kernel. -/
noncomputable def classify (value : ExecFloat.P3109 format) : ClassEnum :=
  kernel_inline% [Class, IsNaN, IsInfinite, IsZero, IsNormal, IsFinite, IsSignMinus,
    magnitudeBits] (Class value)

/-- NaN-first total order with the tests and comparison exposed to the kernel. -/
noncomputable def totalOrder (left : ExecFloat.P3109 format)
    (right : ExecFloat.P3109 rightFormat) : Bool :=
  kernel_inline% [TotalOrder, IsNaN, CompareLessEqual] (TotalOrder left right)

end QueryKernel

/-- Kernel staging preserves every P3109 classification result by definitional equality.

Reference: P3109 Interim Report v4.1 (unapproved draft), §§4.13.
-/
@[kernel_optimize] theorem Class_eq_kernel (value : ExecFloat.P3109 format) :
    Class value = QueryKernel.classify value :=
  kernel_refl%

/-- Kernel staging preserves the total order for independent source descriptors. -/
@[kernel_optimize] theorem TotalOrder_eq_kernel (left : ExecFloat.P3109 format)
    (right : ExecFloat.P3109 rightFormat) :
    TotalOrder left right = QueryKernel.totalOrder left right :=
  kernel_refl%

namespace QueryCompiled

/-- Engineering estimate for the executable query baseline; it is not a timing theorem. -/
def estimate (width : Nat) : Backend.Candidate where
  name := "P3109 report query"
  kind := .custom "P3109 query" 0
  storage := Backend.StorageClass.forBitWidth width
  steadyCost := 1

/-- The compiled classifier executes the proved Table 2 specification at every descriptor. -/
@[compiler_optimize baseline]
def classify (format : Format) : Backend.Certified (@Class format) :=
  .reference (estimate format.bitWidth) (@Class format)

/-- The compiled total-order baseline executes §4.12.1 for independent source descriptors. -/
@[compiler_optimize baseline]
def totalOrder (format rightFormat : Format) :
    Backend.Certified (@TotalOrder format rightFormat) :=
  .reference (estimate (max format.bitWidth rightFormat.bitWidth)) (@TotalOrder format rightFormat)

/-- P3109 interim report v4.1, §4.15: the compiled rounding query preserves all supplied
    stochastic bits. -/
@[compiler_optimize baseline]
def roundOf : Backend.Certified ProjectionPolicy.RoundOf :=
  .reference (estimate 0) ProjectionPolicy.RoundOf

/-- P3109 interim report v4.1, §4.15: the compiled saturation query is the exact policy
    projection. -/
@[compiler_optimize baseline]
def satOf : Backend.Certified ProjectionPolicy.SatOf :=
  .reference (estimate 0) ProjectionPolicy.SatOf

end QueryCompiled

attribute [kernel_optimize unfold] ProjectionPolicy.RoundOf ProjectionPolicy.SatOf

end FloatLib.Floats.ExecFloat.P3109
