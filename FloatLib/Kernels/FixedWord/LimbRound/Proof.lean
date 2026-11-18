/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.LimbRound.Proof.Arithmetic
public import FloatLib.Kernels.FixedWord.LimbRound.Proof.UInt128
public import FloatLib.Kernels.FixedWord.LimbRound.Proof.UInt256
public import FloatLib.Numerics.ShiftRightJam

/-!
# Verified fixed-limb rounding

The verified two- and four-limb rounding kernels rest on generic shift-with-jam laws.
-/
