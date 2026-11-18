/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Dot.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Sum.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Schedule.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Tree

/-!
# Binary reductions and their error bounds

This entry point exports the exact-accumulation reduction kernels with their correctness
proofs. When every addition rounds its own result, `Reduction.Tree` bounds the accumulated
error. If you only run exact accumulation and need none of the proofs, import
`Reduction.Runtime`.

IEEE 754-2019 §9.4 lets a reduction associate in any order and evaluate in any wider format.
`Reduction.Schedule.Runtime` defines `sum`, `sumAbs`, `sumSquare` and `dot` over that freedom
(`sumAlong`, `sumInOrder` and their siblings, with the accumulator and destination formats as
arguments), and the opt-in module `Reduction.Schedule.Proof` bounds their error, for every
order and, through `roundoff`, for the left-to-right loop of any length.
-/
