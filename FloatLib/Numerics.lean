/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Automation.Numerics
public import FloatLib.Numerics.Capabilities
public import FloatLib.Numerics.Core
public import FloatLib.Numerics.Core.Declaration
public import FloatLib.Numerics.Enclosure
public import FloatLib.Numerics.Exact
public import FloatLib.Numerics.IEEEComparison
public import FloatLib.Numerics.IEEEStatus.Proof
public import FloatLib.Numerics.Operation
public import FloatLib.Numerics.Quantization
public import FloatLib.Numerics.Quantization.Automation
public import FloatLib.Numerics.Quantization.Spec
public import FloatLib.Numerics.Reduction
public import FloatLib.Numerics.Representations
public import FloatLib.Numerics.ShiftRightJam.Proof

/-!
# Representation-independent numerical semantics

Numerical systems, exact dyadic and rational values, quantization contracts, reduction errors,
and primitive representations used by the concrete formats.

`At` and `AtFinite` attach erased proofs to a system's runtime carrier. Optional capabilities state
the order, radix, rounding, error, or block-scaling assumptions needed by a theorem.

Use these definitions when implementing a format or proving a result independent of its encoding.
Application examples start with `import FloatLib`; concrete families are under
`FloatLib.Floats.Formats`.
-/

@[expose] public section
