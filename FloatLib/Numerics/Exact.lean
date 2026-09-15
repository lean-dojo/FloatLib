/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Elementary.Proof
public import FloatLib.Numerics.Exact.DecimalText.Proof
public import FloatLib.Numerics.Exact.Hyperbolic.Proof
public import FloatLib.Numerics.Exact.Trigonometric.Proof
public import FloatLib.Numerics.Exact.Trigonometric.Pi.Proof
public import FloatLib.Numerics.Exact.Trigonometric.Atan2.Proof
public import FloatLib.Numerics.Exact.Trigonometric.PiValues.Inverse
public import FloatLib.Numerics.Exact.Trigonometric.PiValues.TangentClassify

public import FloatLib.Numerics.Exact.Zero
public import FloatLib.Numerics.Exact.Dyadic.Arithmetic.Runtime
public import FloatLib.Numerics.Exact.Dyadic.Arithmetic.Proof
public import FloatLib.Numerics.Exact.Dyadic.Real
public import FloatLib.Numerics.Exact.RationalBinary
public import FloatLib.Numerics.Exact.RationalPower.Enclosure.Proof
public import FloatLib.Numerics.Exact.SignedRat

/-!
# Format-independent exact numerical values

Exact carriers, comparisons, and decimal text conversion are shared across numerical families.
Signed zeros retain their arithmetic sign rules; encoding layouts and destination rounding
belong to the individual formats.
-/

@[expose] public section
