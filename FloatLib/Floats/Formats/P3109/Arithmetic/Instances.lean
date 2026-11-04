/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Instances -- shake: keep
public import FloatLib.Floats.Formats.P3109.Arithmetic.Extrema.Runtime
public import FloatLib.Floats.Formats.P3109.Arithmetic.Sqrt.Runtime

/-!
# Public P3109 arithmetic capabilities

With these instances, every valid P3109 descriptor gets addition, subtraction, multiplication,
division, square root, and fused multiply-add through common `ExecFloat` dispatch. Each one is an
exact arithmetic kernel followed by the report projection, and the caller's backend planning
policy is kept.

Without context, an operation uses FloatLib's nearest-even, no-saturation projection policy. For
other rounding modes, stochastic random words, saturation, or mixed-format destinations, use the
`mode`, `saturation`, and `target` options of `ExecFloat.P3109.add` and its siblings. None of
these operations raises or synthesizes IEEE exception flags.

Literals round once from their exact rational value under the same default policy, and `==` is
numerical equality, so NaN compares unequal to every value, itself included.

The rational real-embedding and decoding proofs are in `Arithmetic.Proof`, and the irrational-root
refinement and decoding proofs in `Arithmetic.Sqrt.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.P3109

variable {format : Formats.P3109.Format}

namespace Plan

/--
Planner metadata for the exact arithmetic implementation.

The storage class describes the encoded operand and gives no bound on intermediate sizes. Exact
rational arithmetic can allocate integers whose sizes depend on the descriptor's exponent range.
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

/-- A natural literal rounds once, nearest-even with no saturation request. -/
instance (value : Nat) : OfNat (ExecFloat.P3109 format) value where
  ofNat := ofRat (value : Rat)

/-- A decimal or scientific literal rounds once from its exact rational value. -/
instance : OfScientific (ExecFloat.P3109 format) where
  ofScientific mantissa exponentSign decimalExponent :=
    ofRat (OfScientific.ofScientific mantissa exponentSign decimalExponent)

/-- `==` is numerical equality, so NaN compares unequal to every value, itself included. -/
instance comparison : ExecFloat.Comparison (Codebook.Family format.codebook) where
  compare := compare

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
