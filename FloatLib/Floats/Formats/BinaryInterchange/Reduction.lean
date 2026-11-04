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

This entry point exports the exact-accumulation reduction kernels with their correctness
proofs. When every addition rounds its own result, `Reduction.Tree` bounds the accumulated
error. If you only run exact accumulation and need none of the proofs, import
`Reduction.Runtime`.
-/
