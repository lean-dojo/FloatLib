/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Kernel.Exact
public import FloatLib.Floats.ExecFloat.Backends.Kernel.Plumbing
public import FloatLib.Floats.ExecFloat.Backends.Kernel.Form
public import FloatLib.Kernels.Execution.Instances -- shake: keep
public import FloatLib.Floats.Formats.Logarithmic.Configured.Plan
public import FloatLib.Floats.Formats.Logarithmic.Configured.Proof
public import FloatLib.Tactic.KernelShape

/-!
# Dispatch instance for exact logarithmic multiplication

With this instance in scope, ordinary `ExecFloat` multiplication on logarithmic values runs the
certified direct kernel, which xors the signs and adds the exponents.
For Lean's kernel, `spec_mul_eq_ofCode` states the reference product as the value of the product
of the two codes, which `Code.mul.kernel` computes with the kernel arithmetic of `Int`, and
`eq_iff_sameCode` decides the equality of two codes by cases.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Logarithmic

open FloatLib.Numerics

variable {radix : Radix}

/--
Exact logarithmic multiplication participates in ordinary `ExecFloat` dispatch: the planner
selects among the exact baseline and every candidate tagged `@[compiler_optimize]` for
`Logarithmic.mul`.
-/
@[always_inline] instance
    [planning : Backend.PolicyFor (Family radix)]
    [portfolio : Backend.Portfolio (Logarithmic.mul (radix := radix))] :
    ExecFloat.Mul (Family radix) :=
  ExecFloat.Capability.ofTagged .mul portfolio Plan.mulCertified Logarithmic.mul rfl

/--
Lean's kernel evaluates logarithmic multiplication as the sum of the two exponents: the reference
operation is the kernel operation.
-/
instance [Backend.PolicyFor (Family radix)]
    [Backend.Portfolio (Logarithmic.mul (radix := radix))] :
    KernelPath.DirectReference (Family radix) .mul where

/-! ## Kernel rules -/

/-!
The kernel shape of the product of two codes adds the exponents with the kernel arithmetic of
`Int` and reads the two codes with their recursor.
-/
kernel_shape Formats.Logarithmic.Code.mul inlining [Bool.xor, Bool.not]

/--
The reference product of two logarithmic values is the value of the product of their codes:
Lean's kernel computes it without unfolding the capability.
-/
@[kernel_optimize (cost := 30)]
theorem spec_mul_eq_ofCode [Backend.PolicyFor (Family radix)]
    [Backend.Portfolio (Logarithmic.mul (radix := radix))]
    (left right : ExecFloat.Logarithmic radix) :
    Spec.mul left right = ofCode (Formats.Logarithmic.Code.mul left.toCode right.toCode) :=
  rfl

-- The code of the value of a code is that code: a kernel rule as well.
attribute [kernel_optimize (cost := 1)] toCode_ofCode

/--
Whether two codes are equal: both zero, or two powers with the same sign and the same exponent.
It is written with recursors and the kernel comparison of `Int`, for Lean's kernel
(`eq_iff_sameCode`).
-/
noncomputable def sameCode (left right : Formats.Logarithmic.Code radix) : Bool :=
  Formats.Logarithmic.Code.rec (motive := fun _ => Bool)
    (Formats.Logarithmic.Code.rec (motive := fun _ => Bool) true (fun _ _ => false) right)
    (fun leftSign leftExponent =>
      Formats.Logarithmic.Code.rec (motive := fun _ => Bool) false
        (fun rightSign rightExponent =>
          Bool.rec (motive := fun _ => Bool) false (Int.beq' leftExponent rightExponent)
            (Bool.rec (motive := fun _ => Bool)
              (Bool.rec (motive := fun _ => Bool) true false rightSign) rightSign leftSign))
        right)
    left

/-- Two codes are equal exactly when `sameCode` says so. -/
@[kernel_optimize (cost := 8)]
theorem eq_iff_sameCode (left right : Formats.Logarithmic.Code radix) :
    left = right ↔ sameCode left right = true := by
  cases left with
  | zero => cases right <;> simp [sameCode]
  | value leftSign leftExponent =>
    cases right with
    | zero => simp [sameCode]
    | value rightSign rightExponent =>
      cases leftSign <;> cases rightSign <;>
        simp [sameCode]

end FloatLib.Floats.ExecFloat.Logarithmic
