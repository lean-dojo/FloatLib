/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Elementary.Convergence
public import FloatLib.Numerics.Enclosure.Elementary.ComplexTranscendental
public import FloatLib.Numerics.Enclosure.Elementary.TrigonometricIrrational
public import FloatLib.Numerics.Enclosure.Rational.Proof
public import FloatLib.Numerics.Enclosure.Trigonometric.Convergence
public import FloatLib.Numerics.Enclosure.Trigonometric.Termination

/-!
# Executable analytic enclosures

Rational interval arithmetic and exponential, logarithmic, and trigonometric kernels, with
proofs that their computed endpoints enclose the exact real values. Concrete numerical formats
can refine these bounds until they determine a rounding decision.
-/

@[expose] public section
