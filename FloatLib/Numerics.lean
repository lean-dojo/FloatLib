/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Automation.Interval
public import FloatLib.Numerics.Automation.Numerics
public import FloatLib.Numerics.Capabilities
public import FloatLib.Numerics.Core
public import FloatLib.Numerics.Core.Declaration
public import FloatLib.Numerics.Enclosure
public import FloatLib.Numerics.Exact
public import FloatLib.Numerics.IEEEComparison
public import FloatLib.Numerics.IEEEStatus.Proof
public import FloatLib.Numerics.MixedError.Basic
public import FloatLib.Numerics.MixedError.Elementary
public import FloatLib.Numerics.Operation
public import FloatLib.Numerics.Quantization
public import FloatLib.Numerics.Quantization.Affine.Real
public import FloatLib.Numerics.Quantization.Automation
public import FloatLib.Numerics.Quantization.Spec
public import FloatLib.Numerics.Reduction
public import FloatLib.Numerics.Reduction.Error
public import FloatLib.Numerics.Representations
public import FloatLib.Numerics.ShiftRightJam.Proof

/-!
# Representation-independent numerical semantics

This layer holds the mathematics that FloatLib's formats share, stated without committing to an
encoding: numerical systems, exact dyadic and rational values, quantization contracts, reduction
errors, mixed relative and absolute error bounds, and the primitive representations that the
concrete formats use.

`At` and `AtFinite` attach erased proofs to a system's runtime carrier. Optional capabilities state
the order, radix, rounding, error, or block-scaling assumptions that a theorem needs.

Use these definitions when you implement a format or prove a result that doesn't depend on its
encoding. Application examples start with `import FloatLib`, and the concrete families are under
`FloatLib.Floats.Formats`.
-/

@[expose] public section
