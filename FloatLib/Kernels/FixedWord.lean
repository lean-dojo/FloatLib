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

These are the one-, two-, and four-limb algorithms, written once for every numerical format. Runtime
modules hold the executable kernels and proof modules refine them to natural-number semantics, while
binary floating-point and posit backends import this layer and supply their own decoding, rounding
policy, and packing.

Its declarations sit in the `FloatLib.Numerics.FixedWord` namespace, because they work on the
primitive fixed-word representations that the whole numerical library uses. We keep their
implementations and proofs together here so that different formats can reuse them.
-/

@[expose] public section
