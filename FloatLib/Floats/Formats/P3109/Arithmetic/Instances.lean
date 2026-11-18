/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Kernel.Form
public import FloatLib.Kernels.Execution.Instances -- shake: keep
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
`mode`, `saturation`, and `target` options of `ExecFloat.P3109.Add` and its siblings. None of
these operations raises or synthesizes IEEE exception flags.

Literals round once from their exact rational value under the same default policy, and `==` is
numerical equality, so NaN compares unequal to every value, itself included.

The rational real-embedding and decoding proofs are in `Arithmetic.Proof`, and the irrational-root
refinement and decoding proofs in `Arithmetic.Sqrt.Proof`.

Reference: P3109 Interim Report v4.1 (unapproved draft), §§4.7 and 4.10.3–4.10.8.
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

/--
The reference operation of a P3109 format: exact arithmetic followed by one projection under the
default nearest-even, no-saturation policy. It is the specification of the format's capability,
and the operation that a candidate tagged `@[compiler_optimize]` for P3109 refines.

Reference: P3109 Interim Report v4.1 (unapproved draft), §§4.7 and 4.10.3–4.10.8.
-/
def reference (format : Formats.P3109.Format) :
    (operation : Backend.Operation) →
      OperationSignature (Codebook.Family format.codebook) operation
  | .add => fun left right => Add left right
  | .sub => fun left right => Subtract left right
  | .mul => fun left right => Multiply left right
  | .div => fun left right => Divide left right
  | .sqrt => fun value => Sqrt value
  | .fma => fun left right addend => FMA left right addend

/-- The exact kernel is its own reference, and the family's baseline. -/
@[compiler_optimize baseline]
def certified (format : Formats.P3109.Format) (operation : Backend.Operation) :
    Backend.Certified (reference format operation) :=
  Backend.Certified.reference (estimate format operation) (reference format operation)

/--
The capability of one operation: the planner selects among the exact baseline and every
candidate tagged `@[compiler_optimize]` for `reference format operation`.
-/
@[always_inline, instance_reducible] def capability
    [Backend.PolicyFor (Codebook.Family format.codebook)]
    (operation : Backend.Operation)
    (portfolio : Backend.Portfolio (reference format operation)) :
    Capability (Codebook.Family format.codebook) operation :=
  Capability.ofTagged operation portfolio (certified format operation)
    (reference format operation) rfl

end Plan

/-- Report-default negation, including projection of unsigned results. -/
instance negInstance : Neg (ExecFloat.P3109 format) where
  neg value := Negate value

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

/--
The capability of each operation: its exact result with one nearest-even report projection.
Division returns the report's NaN for every zero denominator, the square root is rounded by exact
comparisons with the irrational result, and the fused multiply-add rounds no intermediate product.
-/
@[always_inline] instance operationCapability
    [Backend.PolicyFor (Codebook.Family format.codebook)] (operation : Backend.Operation)
    [portfolio : Backend.Portfolio (Plan.reference format operation)] :
    Capability (Codebook.Family format.codebook) operation :=
  Plan.capability operation portfolio

/--
Lean's kernel evaluates every P3109 operation as its reference: the exact result and one
projection, without the planner's selection.

Reference: P3109 Interim Report v4.1 (unapproved draft), §§4.7 and 4.10.3–4.10.8.
-/
instance directReference [Backend.PolicyFor (Codebook.Family format.codebook)]
    (operation : Backend.Operation) [Capability (Codebook.Family format.codebook) operation] :
    KernelPath.DirectReference (Codebook.Family format.codebook) operation where

end FloatLib.Floats.ExecFloat.P3109
