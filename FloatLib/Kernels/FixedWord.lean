/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.Core
public import FloatLib.Kernels.FixedWord.CertifiedDivision.Proof
public import FloatLib.Kernels.FixedWord.Difference.Proof
public import FloatLib.Kernels.FixedWord.DyadicCompare.Proof
public import FloatLib.Kernels.FixedWord.IntegerSquareRoot.Proof
public import FloatLib.Kernels.FixedWord.LimbRound.Proof
public import FloatLib.Kernels.FixedWord.Product.Proof
public import FloatLib.Kernels.FixedWord.Quotient.Proof
public import FloatLib.Kernels.FixedWord.Quotient.Restoring128Proof
public import FloatLib.Kernels.FixedWord.RestoringSqrt.Proof
public import FloatLib.Kernels.FixedWord.SignedMagnitude.Proof
public import FloatLib.Kernels.FixedWord.SignedMagnitude.UInt128.Proof

/-!
# Verified fixed-word kernels

Reusable one-, two-, and four-limb algorithms live here independently of any concrete numerical
format. Runtime modules provide executable kernels; proof modules refine them to natural-number
semantics. Binary floating-point and posit backends import this layer and supply their own
decoding, rounding policy, and packing. Declarations use the
`FloatLib.Numerics.FixedWord` namespace because they operate on the primitive fixed-word
representations used throughout the numerical library. Their implementations and proofs are
grouped here so different formats can reuse them.
-/

@[expose] public section
