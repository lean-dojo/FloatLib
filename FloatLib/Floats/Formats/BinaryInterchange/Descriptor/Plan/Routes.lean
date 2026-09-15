/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Plan.Estimates
public import FloatLib.Floats.ExecFloat.Backends.FixedLimb.Pair.Core.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Word.Small.Core.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Word.Small.Mul.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Word.TwoWordMul.Runtime

/-!
# Structural routes for binary descriptor execution

A structural route identifies the specialized kernel family entered by an operation's executable
dispatcher. The route and its cost metadata are kept separate from certified candidate
construction so configured-format planning can use them without importing tiny-table proofs.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Plan

open FloatLib.Floats.ExecFloat
open FloatLib.Floats.ExecFloat.Backend

/--
The structural implementation entered by an operation's executable dispatcher.

This classifies the route that will actually run; it is not a second list of competing algorithms.
Several routes share one dispatcher function, but retain distinct cost metadata because their
specialized kernels have different performance.
-/
inductive StructuralRoute where
  | fixedFormat
  | nativeWord
  | fixedLimbs
  deriving DecidableEq, Repr

namespace StructuralRoute

/-- Cost estimate associated with a structural route. -/
def estimate (route : StructuralRoute)
    (format : FloatFormat) (operation : Operation) : Candidate :=
  match route with
  | .fixedFormat => fixedFormatEstimate operation
  | .nativeWord => nativeWordEstimate format operation
  | .fixedLimbs => fixedLimbEstimate operation

end StructuralRoute

/-- Whether the descriptor structurally satisfies a fixed-format kernel capability. -/
def isFixedFormat (format : FloatFormat) : Bool :=
  decide (FloatFormat.IsBinary32 format ∨ FloatFormat.IsBinary64 format)

/--
Whether the descriptor structurally satisfies the two-word pair-kernel capability: an IEEE layout
of at most 128 bits whose fraction is wider than one word.
-/
def pairKernelEligible (format : FloatFormat) : Bool :=
  decide (Model.NativePair.Eligible format)

/--
Select the single structural route entered by the executable dispatcher.

The branch order mirrors the corresponding `Model.*Backend` implementation. Returning `none`
means that the operation proceeds directly to its width-generic kernel.
-/
def structuralRoute? (format : FloatFormat) : Operation → Option StructuralRoute
  | .add | .sub =>
      if isFixedFormat format then
        some .fixedFormat
      else if pairKernelEligible format then
        some .fixedLimbs
      else if decide (Model.NativeSmallWord.StorageEligible format) then
        some .nativeWord
      else
        none
  | .mul =>
      if isFixedFormat format then
        some .fixedFormat
      else if pairKernelEligible format then
        some .fixedLimbs
      else if decide (Model.NativeSmallWordMul.Eligible format) then
        some .nativeWord
      else if decide (Model.NativeTwoWordMul.Eligible format) then
        some .fixedLimbs
      else
        none
  | .div =>
      if isFixedFormat format then
        some .fixedFormat
      else if pairKernelEligible format then
        some .fixedLimbs
      else if decide (Model.NativeSmallWord.Eligible format) then
        some .nativeWord
      else
        none
  | .sqrt | .fma =>
      if pairKernelEligible format then
        some .fixedLimbs
      else if isFixedFormat format then
        some .fixedFormat
      else if decide (Model.NativeSmallWord.StorageEligible format) then
        some .nativeWord
      else
        none

end FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Plan
