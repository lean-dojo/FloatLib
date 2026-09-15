/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Dyadic.Direct.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.Boundary.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Rounding.Runtime
public import FloatLib.Numerics.Exact.Dyadic.Arithmetic.Runtime

/-!
# Two-limb posit arithmetic runtime

These kernels decode each finite operand once, perform the exact dyadic operation, and use the
two-limb rounding backends through Posit128. Division reuses the shared width-generic
quotient-prefix kernel through `divWords`. The packed square-root adapter likewise reuses the
width-generic root-prefix kernel.

Refinement to the representation-independent Posit Standard operations lives in
`Arithmetic.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeLimbArithmetic

open FloatLib.Numerics

variable {format : Format}

/-- Exact dyadic addition followed by certified two-limb standard rounding. -/
@[noinline] def add (heligible : NativeLimb.Eligible format)
    (left right : Model format) : Model format :=
  NativeLimbPacked.Boundary.binaryResult (nar format)
    (fun leftValue rightValue =>
      NativeLimbRounding.round format heligible
        (FloatLib.Numerics.Dyadic.add leftValue rightValue))
    left.toDyadic? right.toDyadic?

/-- Exact dyadic subtraction followed by certified two-limb standard rounding. -/
@[noinline] def sub (heligible : NativeLimb.Eligible format)
    (left right : Model format) : Model format :=
  NativeLimbPacked.Boundary.binaryResult (nar format)
    (fun leftValue rightValue =>
      NativeLimbRounding.round format heligible
        (FloatLib.Numerics.Dyadic.sub leftValue rightValue))
    left.toDyadic? right.toDyadic?

/-- Exact dyadic multiplication followed by certified two-limb standard rounding. -/
@[noinline] def mul (heligible : NativeLimb.Eligible format)
    (left right : Model format) : Model format :=
  NativeLimbPacked.Boundary.binaryResult (nar format)
    (fun leftValue rightValue =>
      NativeLimbRounding.round format heligible
        (FloatLib.Numerics.Dyadic.mul leftValue rightValue))
    left.toDyadic? right.toDyadic?

/--
Decode two stored pair words and divide them with the shared width-generic quotient-prefix
kernel.

This function is a carrier adapter, not a separate fixed-limb divider.
-/
@[noinline] def divWords
    (format : Format)
    (left right : FloatLib.Numerics.FixedWord.UInt128) :
    Model format :=
  DirectDyadicArithmetic.divDecoded format
    (NativeLimb.toDyadic? format left)
    (NativeLimb.toDyadic? format right)

/-- Exact fused multiplication and addition with one certified two-limb rounding step. -/
@[noinline] def fma (heligible : NativeLimb.Eligible format)
    (left right addend : Model format) : Model format :=
  NativeLimbPacked.Boundary.ternaryResult (nar format)
    (fun leftValue rightValue addendValue =>
      NativeLimbRounding.round format heligible
        (FloatLib.Numerics.Dyadic.add
          (FloatLib.Numerics.Dyadic.mul leftValue rightValue)
          addendValue))
    left.toDyadic? right.toDyadic? addend.toDyadic?

end FloatLib.Floats.Formats.Posit.Model.NativeLimbArithmetic
