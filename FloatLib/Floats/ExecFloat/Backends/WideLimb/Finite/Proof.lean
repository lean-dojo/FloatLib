/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Generic.Kernel.Proof
public import FloatLib.Floats.ExecFloat.Backends.Generic.ScaleAdd.Proof
public import FloatLib.Floats.ExecFloat.Backends.Generic.AddDyadic.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Spec.Dyadic
public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Classification

/-!
# From the compact finite kernels to the reference operations

The wide-limb kernels prove that an accepted result is the compact finite kernel
(`FiniteKernel.add?`, `mul?`, or `fma?`) on the operand models. This module supplies the last
step of each refinement: whenever a compact finite kernel accepts its operands, the reference
operation `Model.Spec.add`, `mul`, or `fma` returns the same value (`spec_add_of_add?_eq_some` and
its siblings). It also records that negating a model value flips only the decoded sign
(`decode?_neg`) and that the unsigned-scale sum is commutative (`roundSum_comm`), which the
alignment kernel uses to order its operands by scale.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb

variable {fmt : FloatFormat}

/-- An accepted compact finite addition is the reference addition. -/
theorem spec_add_of_add?_eq_some (x y r : Model fmt) (h : FiniteKernel.add? x y = some r) :
    Spec.add x y = r := by
  rw [FiniteKernel.add_eq_spec] at h
  unfold Spec.add
  cases hx : toDyadic? x with
  | none =>
      rw [hx] at h
      exact absurd h (by simp)
  | some dx =>
      cases hy : toDyadic? y with
      | none =>
          rw [hx, hy] at h
          exact absurd h (by simp)
      | some dy =>
          rw [hx, hy] at h
          simpa using h

/-- An accepted compact finite multiplication is the reference multiplication. -/
theorem spec_mul_of_mul?_eq_some (x y r : Model fmt) (h : FiniteKernel.mul? x y = some r) :
    Spec.mul x y = r := by
  rw [FiniteKernel.mul_eq_spec] at h
  unfold Spec.mul
  cases hx : toDyadic? x with
  | none =>
      rw [hx] at h
      exact absurd h (by simp)
  | some dx =>
      cases hy : toDyadic? y with
      | none =>
          rw [hx, hy] at h
          exact absurd h (by simp)
      | some dy =>
          rw [hx, hy] at h
          dsimp only at h ⊢
          split at h <;> rename_i hcond
          · rw [ite_eq_left hcond]
            simpa using h
          · rw [ite_eq_right hcond]
            simpa using h

/-- An accepted compact finite fused multiply-add is the reference fused multiply-add. -/
theorem spec_fma_of_fma?_eq_some (x y z r : Model fmt) (h : FiniteKernel.fma? x y z = some r) :
    Spec.fma x y z = r := by
  rw [FiniteKernel.fma_eq_spec] at h
  unfold Spec.fma
  cases hx : toDyadic? x with
  | none =>
      rw [hx] at h
      exact absurd h (by simp)
  | some dx =>
      cases hy : toDyadic? y with
      | none =>
          rw [hx, hy] at h
          exact absurd h (by simp)
      | some dy =>
          cases hz : toDyadic? z with
          | none =>
              rw [hx, hy, hz] at h
              exact absurd h (by simp)
          | some dz =>
              rw [hx, hy, hz] at h
              have hxNaN := isNaN_eq_false_of_toDyadic?_some hx
              have hyNaN := isNaN_eq_false_of_toDyadic?_some hy
              have hzNaN := isNaN_eq_false_of_toDyadic?_some hz
              have hxSNaN := isSNaN_eq_false_of_toDyadic?_some hx
              have hySNaN := isSNaN_eq_false_of_toDyadic?_some hy
              have hzSNaN := isSNaN_eq_false_of_toDyadic?_some hz
              have hxInf := isInf_eq_false_of_toDyadic?_some hx
              have hyInf := isInf_eq_false_of_toDyadic?_some hy
              have hzInf := isInf_eq_false_of_toDyadic?_some hz
              simp only [chooseNaN3, hxNaN, hyNaN, hzNaN, hxSNaN, hySNaN, hzSNaN, hxInf, hyInf, hzInf,
                Bool.false_eq_true, ite_false, Bool.or_self]
              simpa using h

/-- Negating a conventional IEEE value flips only the decoded sign. -/
theorem decode?_neg (hieee : fmt.isIEEE = true) (m : Model fmt) :
    FiniteKernel.decode? (neg m) = (FiniteKernel.decode? m).map fun c => { c with sign := !c.sign } := by
  have hencoding : fmt.encoding = .ieee := ((FloatFormat.isIEEE_eq_true_iff fmt).mp hieee).1
  have hsigned : fmt.supportsSignedZero = true := by
    simp [FloatFormat.supportsSignedZero, hencoding]
  have hfinite : isFinite (neg m) = isFinite m := by
    rw [isFinite, isFinite, hencoding]
    exact IEEE.isFinite_neg m
  unfold FiniteKernel.decode?
  rw [hfinite, signBit_neg, hsigned, expField_neg, fracField_neg]
  by_cases hfin : isFinite m = true
  · simp [hfin]
  · simp [hfin]

/-- The unsigned-scale exact sum does not depend on the order of its operands. -/
theorem roundSum_comm (hieee : fmt.isIEEE = true) (roundOffset : Nat) (aSign bSign : Bool)
    (a sa b sb : Nat) :
    FiniteScaleAdd.roundSum fmt roundOffset aSign bSign a sa b sb =
      FiniteScaleAdd.roundSum fmt roundOffset bSign aSign b sb a sa := by
  rw [FiniteScaleAdd.roundSum_eq fmt hieee, FiniteScaleAdd.roundSum_eq fmt hieee, addDyadic_comm]

end FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb
