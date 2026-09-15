/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.Backend.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Backend.FixedWords.Byte.Proof
public import FloatLib.Floats.Formats.Posit.Configured.ByteTable.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Plan.ByteCandidates
public import FloatLib.Floats.Formats.Posit.Configured.Plan.ByteDispatch.Runtime

/-!
# Correctness of first-order byte-sized posit dispatch

The tagged selector agrees with the shared planner metadata, and every named execution branch
implements the independent configured specification. These results ensure that removing closure
dispatch changes performance only, never arithmetic semantics or inspection metadata.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured.Plan.ByteDispatch

open FloatLib.Floats.ExecFloat
open FloatLib.Floats.ExecFloat.Backend

/-- Projecting a tagged comparison gives the shared metadata comparison. -/
private theorem estimate_consider
    (policy : Policy) (format : Format) (width_le : format.bits ≤ 8)
    (operation : Operation) (incumbent candidate : Choice) :
    (Choice.consider policy format width_le operation incumbent candidate).estimate
        format width_le operation =
      consider policy
        (incumbent.estimate format width_le operation)
        (candidate.estimate format width_le operation) := by
  simp only [Choice.consider, consider]
  split <;> rfl

/-- Tagged selection uses the same candidate comparison as the shared metadata planner. -/
theorem select_estimate
    (policy : Policy) (format : Format) (width_le : format.bits ≤ 8)
    (operation : Operation) :
    (select policy format width_le operation).estimate format width_le operation =
      selectCandidate policy (estimates format width_le operation) := by
  unfold select estimates selectCandidate
  simp only [List.foldl_cons, List.foldl_nil]
  rw [estimate_consider, estimate_consider, estimate_consider]
  rfl

/-! ## Agreement with the public certified portfolios -/

/-- Addition exposes exactly the metadata consumed by its first-order selector. -/
theorem addByteCandidates_estimates
    (format : Format) (width_le : format.bits ≤ 8) :
    (addByteCandidates format width_le).estimates =
      estimates format width_le .add := by
  rfl

/-- Subtraction exposes exactly the metadata consumed by its first-order selector. -/
theorem subByteCandidates_estimates
    (format : Format) (width_le : format.bits ≤ 8) :
    (subByteCandidates format width_le).estimates =
      estimates format width_le .sub := by
  rfl

/-- Multiplication exposes exactly the metadata consumed by its first-order selector. -/
theorem mulByteCandidates_estimates
    (format : Format) (width_le : format.bits ≤ 8) :
    (mulByteCandidates format width_le).estimates =
      estimates format width_le .mul := by
  rfl

/-- Division exposes exactly the metadata consumed by its first-order selector. -/
theorem divByteCandidates_estimates
    (format : Format) (width_le : format.bits ≤ 8) :
    (divByteCandidates format width_le).estimates =
      estimates format width_le .div := by
  rfl

/-- Square root exposes exactly the metadata consumed by its first-order selector. -/
theorem sqrtByteCandidates_estimates
    (format : Format) (width_le : format.bits ≤ 8) :
    (sqrtByteCandidates format width_le).estimates =
      estimates format width_le .sqrt := by
  rfl

/-- FMA exposes exactly the metadata consumed by its first-order selector. -/
theorem fmaByteCandidates_estimates
    (format : Format) (width_le : format.bits ≤ 8) :
    (fmaByteCandidates format width_le).estimates =
      estimates format width_le .fma := by
  rfl

/-- Executed and reported addition selection agree. -/
theorem select_add_estimate
    (policy : Policy) (format : Format) (width_le : format.bits ≤ 8) :
    (select policy format width_le .add).estimate format width_le .add =
      selectCandidate policy (addByteCandidates format width_le).estimates := by
  rw [select_estimate, addByteCandidates_estimates]

/-- Executed and reported subtraction selection agree. -/
theorem select_sub_estimate
    (policy : Policy) (format : Format) (width_le : format.bits ≤ 8) :
    (select policy format width_le .sub).estimate format width_le .sub =
      selectCandidate policy (subByteCandidates format width_le).estimates := by
  rw [select_estimate, subByteCandidates_estimates]

/-- Executed and reported multiplication selection agree. -/
theorem select_mul_estimate
    (policy : Policy) (format : Format) (width_le : format.bits ≤ 8) :
    (select policy format width_le .mul).estimate format width_le .mul =
      selectCandidate policy (mulByteCandidates format width_le).estimates := by
  rw [select_estimate, mulByteCandidates_estimates]

/-- Executed and reported division selection agree. -/
theorem select_div_estimate
    (policy : Policy) (format : Format) (width_le : format.bits ≤ 8) :
    (select policy format width_le .div).estimate format width_le .div =
      selectCandidate policy (divByteCandidates format width_le).estimates := by
  rw [select_estimate, divByteCandidates_estimates]

/-- Executed and reported square-root selection agree. -/
theorem select_sqrt_estimate
    (policy : Policy) (format : Format) (width_le : format.bits ≤ 8) :
    (select policy format width_le .sqrt).estimate format width_le .sqrt =
      selectCandidate policy (sqrtByteCandidates format width_le).estimates := by
  rw [select_estimate, sqrtByteCandidates_estimates]

/-- Executed and reported fused-multiply-add selection agree. -/
theorem select_fma_estimate
    (policy : Policy) (format : Format) (width_le : format.bits ≤ 8) :
    (select policy format width_le .fma).estimate format width_le .fma =
      selectCandidate policy (fmaByteCandidates format width_le).estimates := by
  rw [select_estimate, fmaByteCandidates_estimates]

variable {format : Format}

/-! ## Arithmetic refinement -/

/-- A byte-addition choice cannot change arithmetic semantics. -/
theorem addSelected_eq_spec
    (selection : Choice) (width_le : format.bits ≤ 8)
    (table : TinyTable.CertifiedBinary
      (ByteTable.encoding format width_le) Model.Spec.add)
    (left right : ByteFloat format width_le) :
    addSelected selection width_le table left right = Spec.add left right := by
  unfold addSelected
  cases selection with
  | reference => rfl
  | table => exact ByteTable.runBinary_eq_lift width_le table left right
  | word => exact Backend.Byte.add_eq_spec width_le left right
  | dyadic => exact Backend.dyadicAdd_eq_spec left right

/-- First-order byte addition refines the configured specification for every policy. -/
theorem add_eq_spec
    (policy : Policy) (width_le : format.bits ≤ 8)
    (left right : ByteFloat format width_le) :
    add policy width_le left right = Spec.add left right :=
  addSelected_eq_spec
    (select policy format width_le .add) width_le
    (ByteTable.addTable width_le) left right

/-- A byte-subtraction choice cannot change arithmetic semantics. -/
theorem subSelected_eq_spec
    (selection : Choice) (width_le : format.bits ≤ 8)
    (table : TinyTable.CertifiedBinary
      (ByteTable.encoding format width_le) Model.Spec.sub)
    (left right : ByteFloat format width_le) :
    subSelected selection width_le table left right = Spec.sub left right := by
  unfold subSelected
  cases selection with
  | reference => rfl
  | table => exact ByteTable.runBinary_eq_lift width_le table left right
  | word => exact Backend.Byte.sub_eq_spec width_le left right
  | dyadic => exact Backend.dyadicSub_eq_spec left right

/-- First-order byte subtraction refines the configured specification for every policy. -/
theorem sub_eq_spec
    (policy : Policy) (width_le : format.bits ≤ 8)
    (left right : ByteFloat format width_le) :
    sub policy width_le left right = Spec.sub left right :=
  subSelected_eq_spec
    (select policy format width_le .sub) width_le
    (ByteTable.subTable width_le) left right

/-- A byte-multiplication choice cannot change arithmetic semantics. -/
theorem mulSelected_eq_spec
    (selection : Choice) (width_le : format.bits ≤ 8)
    (table : TinyTable.CertifiedBinary
      (ByteTable.encoding format width_le) Model.Spec.mul)
    (left right : ByteFloat format width_le) :
    mulSelected selection width_le table left right = Spec.mul left right := by
  unfold mulSelected
  cases selection with
  | reference => rfl
  | table => exact ByteTable.runBinary_eq_lift width_le table left right
  | word => exact Backend.Byte.mul_eq_spec width_le left right
  | dyadic => exact Backend.dyadicMul_eq_spec left right

/-- First-order byte multiplication refines the configured specification for every policy. -/
theorem mul_eq_spec
    (policy : Policy) (width_le : format.bits ≤ 8)
    (left right : ByteFloat format width_le) :
    mul policy width_le left right = Spec.mul left right :=
  mulSelected_eq_spec
    (select policy format width_le .mul) width_le
    (ByteTable.mulTable width_le) left right

/-- A byte-division choice cannot change arithmetic semantics. -/
theorem divSelected_eq_spec
    (selection : Choice) (width_le : format.bits ≤ 8)
    (table : TinyTable.CertifiedBinary
      (ByteTable.encoding format width_le) Model.Spec.div)
    (left right : ByteFloat format width_le) :
    divSelected selection width_le table left right = Spec.div left right := by
  unfold divSelected
  cases selection with
  | reference => rfl
  | table => exact ByteTable.runBinary_eq_lift width_le table left right
  | word => exact Backend.Byte.div_eq_spec width_le left right
  | dyadic => exact Backend.dyadicDiv_eq_spec left right

/-- First-order byte division refines the configured specification for every policy. -/
theorem div_eq_spec
    (policy : Policy) (width_le : format.bits ≤ 8)
    (left right : ByteFloat format width_le) :
    div policy width_le left right = Spec.div left right :=
  divSelected_eq_spec
    (select policy format width_le .div) width_le
    (ByteTable.divTable width_le) left right

/-- A byte-square-root choice cannot change arithmetic semantics. -/
theorem sqrtSelected_eq_spec
    (selection : Choice) (width_le : format.bits ≤ 8)
    (table : TinyTable.CertifiedUnary
      (ByteTable.encoding format width_le) Model.Spec.sqrt)
    (value : ByteFloat format width_le) :
    sqrtSelected selection width_le table value = Spec.sqrt value := by
  unfold sqrtSelected
  cases selection with
  | reference => rfl
  | table => exact ByteTable.runUnary_eq_lift width_le table value
  | word => exact Backend.Byte.sqrt_eq_spec width_le value
  | dyadic => exact Backend.dyadicSqrt_eq_spec value

/-- First-order byte square root refines the configured specification for every policy. -/
theorem sqrt_eq_spec
    (policy : Policy) (width_le : format.bits ≤ 8)
    (value : ByteFloat format width_le) :
    sqrt policy width_le value = Spec.sqrt value :=
  sqrtSelected_eq_spec
    (select policy format width_le .sqrt) width_le
    (ByteTable.sqrtTable width_le) value

/-- A byte-FMA choice cannot change arithmetic semantics. -/
theorem fmaSelected_eq_spec
    (selection : Choice) (width_le : format.bits ≤ 8)
    (table : TinyTable.CertifiedTernary
      (ByteTable.encoding format width_le) Model.Spec.fma)
    (left right addend : ByteFloat format width_le) :
    fmaSelected selection width_le table left right addend =
      Spec.fma left right addend := by
  unfold fmaSelected
  cases selection with
  | reference => rfl
  | table => exact ByteTable.runTernary_eq_lift width_le table left right addend
  | word => exact Backend.Byte.fma_eq_spec width_le left right addend
  | dyadic => exact Backend.dyadicFma_eq_spec left right addend

/-- First-order byte FMA refines the configured specification for every policy. -/
theorem fma_eq_spec
    (policy : Policy) (width_le : format.bits ≤ 8)
    (left right addend : ByteFloat format width_le) :
    fma policy width_le left right addend = Spec.fma left right addend :=
  fmaSelected_eq_spec
    (select policy format width_le .fma)
    width_le (ByteTable.fmaTable width_le) left right addend

/-! ## Function equalities used by capability construction -/

/-- Policy-selected byte addition equals the configured specification as a function. -/
theorem add_fun_eq_spec (policy : Policy) (width_le : format.bits ≤ 8) :
    add policy width_le = Spec.add := by
  funext left right
  exact add_eq_spec policy width_le left right

/-- Policy-selected byte subtraction equals the configured specification as a function. -/
theorem sub_fun_eq_spec (policy : Policy) (width_le : format.bits ≤ 8) :
    sub policy width_le = Spec.sub := by
  funext left right
  exact sub_eq_spec policy width_le left right

/-- Policy-selected byte multiplication equals the configured specification as a function. -/
theorem mul_fun_eq_spec (policy : Policy) (width_le : format.bits ≤ 8) :
    mul policy width_le = Spec.mul := by
  funext left right
  exact mul_eq_spec policy width_le left right

/-- Policy-selected byte division equals the configured specification as a function. -/
theorem div_fun_eq_spec (policy : Policy) (width_le : format.bits ≤ 8) :
    div policy width_le = Spec.div := by
  funext left right
  exact div_eq_spec policy width_le left right

/-- Policy-selected byte square root equals the configured specification as a function. -/
theorem sqrt_fun_eq_spec (policy : Policy) (width_le : format.bits ≤ 8) :
    sqrt policy width_le = Spec.sqrt := by
  funext value
  exact sqrt_eq_spec policy width_le value

/-- Policy-selected byte fused multiply-add equals the configured specification as a function. -/
theorem fma_fun_eq_spec (policy : Policy) (width_le : format.bits ≤ 8) :
    fma policy width_le = Spec.fma := by
  funext left right addend
  exact fma_eq_spec policy width_le left right addend

end FloatLib.Floats.Formats.Posit.Configured.Plan.ByteDispatch
