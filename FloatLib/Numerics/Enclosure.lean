/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Constants.Proof
public import FloatLib.Numerics.Enclosure.Elementary.Convergence
public import FloatLib.Numerics.Enclosure.Elementary.ComplexTranscendental
public import FloatLib.Numerics.Enclosure.Elementary.LogTable.Proof
public import FloatLib.Numerics.Enclosure.Elementary.TrigonometricIrrational
public import FloatLib.Numerics.Enclosure.Expression.BackendsProof
public import FloatLib.Numerics.Enclosure.Expression.CheckProof
public import FloatLib.Numerics.Enclosure.Interval.Proof
public import FloatLib.Numerics.Enclosure.Interval.Real
public import FloatLib.Numerics.Enclosure.Rational.Proof
public import FloatLib.Numerics.Enclosure.Trigonometric.Convergence
public import FloatLib.Numerics.Enclosure.Trigonometric.ArgumentReduction.Termination
public import FloatLib.Numerics.Enclosure.Trigonometric.Termination

/-!
# Executable interval and analytic enclosures

Rational interval arithmetic and exponential, logarithmic, and trigonometric kernels, with proofs
that their computed endpoints enclose the exact real values. Concrete numerical formats can refine
these bounds until they determine a rounding decision. `Constants` caches proved integer bounds of
`π / 2`, `2 / π` and `log 2` at every precision. The binary interchange kernels read them: sine and
cosine reduction, exponential reduction, generated configurations, the certified power and
`Model.pi`. The exact comparators and `BinaryGrid.log` compute their own `π / 4` and `log 2`.
`ArgumentReduction` reduces an argument `m * 2 ^ e` modulo `π / 2` by the method of Payne and Hanek,
from a window of the cached `2 / π`, with a proved bound on the error of its remainder.

`Interval` also accepts arbitrary endpoint representations. Partial outward-rounding contracts
separate the common ordered-field enclosure proofs from a format's range and encoding.
`Interval.Expr` composes these operations into real expressions, and its rational and integer
binary-grid backends share one containment theorem and adaptive subdivision checker.
-/

@[expose] public section
