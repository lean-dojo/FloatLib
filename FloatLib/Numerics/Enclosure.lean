/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Affine.ExprProof
public import FloatLib.Numerics.Enclosure.Constants.Proof
public import FloatLib.Numerics.Enclosure.Elementary.ComplexTranscendental
public import FloatLib.Numerics.Enclosure.Elementary.Convergence
public import FloatLib.Numerics.Enclosure.Elementary.LogTable.Proof
public import FloatLib.Numerics.Enclosure.Elementary.TrigonometricIrrational
public import FloatLib.Numerics.Enclosure.Expression.BackendsProof
public import FloatLib.Numerics.Enclosure.Expression.CheckProof
public import FloatLib.Numerics.Enclosure.Expression.Diagnose
public import FloatLib.Numerics.Enclosure.Expression.ElementaryTableProof
public import FloatLib.Numerics.Enclosure.Expression.StandardProof
public import FloatLib.Numerics.Enclosure.Interval.ExactProof
public import FloatLib.Numerics.Enclosure.Interval.Proof
public import FloatLib.Numerics.Enclosure.Interval.Real
public import FloatLib.Numerics.Enclosure.Interval.RoundingProof
public import FloatLib.Numerics.Enclosure.Interval.SharpTrigProof
public import FloatLib.Numerics.Enclosure.Interval.TotalProof
public import FloatLib.Numerics.Enclosure.Rational.Proof
public import FloatLib.Numerics.Enclosure.Trigonometric.ArgumentReduction.Termination
public import FloatLib.Numerics.Enclosure.Trigonometric.Convergence
public import FloatLib.Numerics.Enclosure.Trigonometric.Termination

/-!
# Executable interval and analytic enclosures

To round an exponential correctly, you need to know it well enough to tell which side of a rounding
boundary it falls on. This layer gives you that, as rational interval arithmetic and exponential,
logarithmic, and trigonometric kernels, with proofs that their computed endpoints enclose the exact
real values. A concrete numerical format refines these bounds until they determine its rounding
decision.

`Constants` caches proved integer bounds of `π / 2`, `2 / π` and `log 2` at every precision. Binary
interchange kernels read them: sine and cosine reduction, exponential reduction, generated
configurations, the certified power, the correctly rounded logarithm and weighted exponential
searches, and `Model.pi`. Only the exact comparators and `BinaryGrid.log` compute their own `π / 4`
and `log 2`. `ArgumentReduction` reduces an argument `m * 2 ^ e` modulo
`π / 2` by the method of Payne and Hanek, from a window of the cached `2 / π`, with a proved bound
on the error of its remainder.

`Interval` also accepts arbitrary endpoint representations. Its outward-rounding contracts are
partial, which keeps the common ordered-field enclosure proofs apart from a format's range and
encoding. `Interval.Exact` has the total operations on rational intervals, with their endpoints in
ordinary notation, and `Interval.Rounding` rounds rational intervals outward to binary grids: a
fixed grid, a grid that follows the magnitude of each endpoint, and a grid for quotients.

`Interval.Expr` composes these operations into real expressions, and its backends share one
containment theorem and one adaptive subdivision checker. `Backend.ofRoundings` takes one outward
rounding for the algebraic operations, one for quotients and one for the elementary functions,
and a table of elementary enclosures. `Backend.elementaryWith` is that table, with settings: a
degree for each family of functions, sharper sine and cosine (`Interval.SharpTrig`), and
Mathlib's total square root, arcsine, arccosine and logarithm (`Interval.Total`). At its legacy
setting it is the table of the `interval` tactic, which `Backend.ofRounding` and
`Backend.rational` use with one rounding for every operation and `Backend.binaryGrid` uses on an
integer grid. `Backend.Standard.extensions` adds `π`, the real power and `e` as calls, and
`Expr.diagnose` reports why an evaluation has no enclosure. `Affine` encloses the polynomial part
of the language with affine arithmetic, which keeps track of a variable that occurs more than once
(`Affine.Expr.affineRange?`).
-/

@[expose] public section
