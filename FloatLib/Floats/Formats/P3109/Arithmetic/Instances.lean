/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Instances -- shake: keep
public import FloatLib.Floats.Formats.P3109.Arithmetic.Sqrt.Runtime

/-!
# Public P3109 arithmetic capabilities

Every valid P3109 descriptor supplies addition, subtraction, multiplication, division, square
root, and fused multiply-add through common `ExecFloat` dispatch. Each has one exact arithmetic
kernel followed by the report projection. The supplied backend planning policy is retained.

Context-free operations use FloatLib's nearest-even, no-saturation projection policy. Explicit
rounding, stochastic random words, saturation, and mixed-format destinations remain available
through `ExecFloat.P3109.*To`. These operations neither raise nor synthesize IEEE exception flags.

The rational real-embedding and decoding proofs are in `Arithmetic.Proof`; the irrational-root
refinement and decoding proofs are in `Arithmetic.Sqrt.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.P3109

variable {format : Formats.P3109.Format}

namespace Plan

/--
Planner metadata for the exact arithmetic implementation.

The storage class describes the encoded operand, not an intermediate-size bound. Exact rational
arithmetic can allocate integers whose sizes depend on the descriptor's exponent range.
-/
def estimate (format : Formats.P3109.Format) (operation : Backend.Operation) :
    Backend.Candidate where
  name := "P3109 exact arithmetic and report projection"
  kind := .custom "P3109 exact arithmetic" 0
  storage := Backend.StorageClass.forBitWidth format.bitWidth
  steadyCost := match operation with
    | .add | .sub => 40
    | .mul => 60
    | .div => 100
    | .sqrt => 120
    | .fma => 100

/-- Package the single exact kernel without changing the caller's planning policy. -/
@[always_inline, instance_reducible] def capability
    [Backend.PolicyFor (Codebook.Family format.codebook)]
    (operation : Backend.Operation)
    (kernel : OperationSignature (Codebook.Family format.codebook) operation) :
    Capability (Codebook.Family format.codebook) operation :=
  Capability.ofDirectKernel operation kernel
    (Backend.Certified.reference (estimate format operation) kernel) kernel rfl

end Plan

/-- Report-default negation, including projection of unsigned results. -/
instance negInstance : Neg (ExecFloat.P3109 format) where
  neg value := neg value

/-- Exact addition with one nearest-even report projection. -/
@[always_inline] instance addCapability
    [Backend.PolicyFor (Codebook.Family format.codebook)] :
    ExecFloat.Add (Codebook.Family format.codebook) :=
  Plan.capability .add (fun left right => add left right)

/-- Exact subtraction with one nearest-even report projection. -/
@[always_inline] instance subCapability
    [Backend.PolicyFor (Codebook.Family format.codebook)] :
    ExecFloat.Sub (Codebook.Family format.codebook) :=
  Plan.capability .sub (fun left right => sub left right)

/-- Exact multiplication with one nearest-even report projection. -/
@[always_inline] instance mulCapability
    [Backend.PolicyFor (Codebook.Family format.codebook)] :
    ExecFloat.Mul (Codebook.Family format.codebook) :=
  Plan.capability .mul (fun left right => mul left right)

/-- Exact division with the report's NaN result for every zero denominator. -/
@[always_inline] instance divCapability
    [Backend.PolicyFor (Codebook.Family format.codebook)] :
    ExecFloat.Div (Codebook.Family format.codebook) :=
  Plan.capability .div (fun left right => div left right)

/-- Square root rounded by exact comparisons with the irrational result. -/
@[always_inline] instance sqrtCapability
    [Backend.PolicyFor (Codebook.Family format.codebook)] :
    ExecFloat.Sqrt (Codebook.Family format.codebook) :=
  Plan.capability .sqrt (fun value => sqrt value)

/-- Fused multiply-add with no rounded or saturated intermediate product. -/
@[always_inline] instance fmaCapability
    [Backend.PolicyFor (Codebook.Family format.codebook)] :
    ExecFloat.Fma (Codebook.Family format.codebook) :=
  Plan.capability .fma (fun left right addend => fma left right addend)

end FloatLib.Floats.ExecFloat.P3109
