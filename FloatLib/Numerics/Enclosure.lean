/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Elementary.Convergence
public import FloatLib.Numerics.Enclosure.Elementary.ComplexTranscendental
public import FloatLib.Numerics.Enclosure.Elementary.TrigonometricIrrational
public import FloatLib.Numerics.Enclosure.Expression.BackendsProof
public import FloatLib.Numerics.Enclosure.Expression.CheckProof
public import FloatLib.Numerics.Enclosure.Interval.Proof
public import FloatLib.Numerics.Enclosure.Interval.Real
public import FloatLib.Numerics.Enclosure.Rational.Proof
public import FloatLib.Numerics.Enclosure.Trigonometric.Convergence
public import FloatLib.Numerics.Enclosure.Trigonometric.Termination

/-!
# Executable interval and analytic enclosures

Rational interval arithmetic and exponential, logarithmic, and trigonometric kernels, with
proofs that their computed endpoints enclose the exact real values. Concrete numerical formats
can refine these bounds until they determine a rounding decision.

`Interval` also accepts arbitrary endpoint representations. Partial outward-rounding contracts
separate the common ordered-field enclosure proofs from a format's range and encoding.
`Interval.Expr` composes these operations into real expressions; rational and integer binary-grid
backends share its containment theorem and adaptive subdivision checker.
-/

@[expose] public section
