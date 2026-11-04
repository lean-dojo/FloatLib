/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.Core.Proof.Word
public import FloatLib.Kernels.FixedWord.Core.Proof.Rounding
public import FloatLib.Kernels.FixedWord.Core.Proof.UInt128

/-!
# Verified fixed-word core

The proofs come in three files. `Core.Proof.Word` has the single-word bit, shift, and restoring-root
facts, `Core.Proof.Rounding` refines the nearest-even shift and quotient, and `Core.Proof.UInt128`
covers the two-word representation and exact wide multiplication.
-/
