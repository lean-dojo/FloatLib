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

Single-word bit, shift, and restoring-root facts are in `Core.Proof.Word`; nearest-even shift and
quotient refinement is in `Core.Proof.Rounding`. Two-word representation and exact wide
multiplication facts are in `Core.Proof.UInt128`.
-/
