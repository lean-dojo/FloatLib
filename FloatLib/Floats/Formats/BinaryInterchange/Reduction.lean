/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Tree

/-!
# Binary reductions and their error bounds

Exact-accumulation reduction kernels are exported together with their correctness proofs.
`Reduction.Tree` bounds the accumulated error when each addition rounds separately.
Runtime-only consumers of exact accumulation should import `Reduction.Runtime`.
-/
