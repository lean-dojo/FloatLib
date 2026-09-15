/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Trigonometric.AtanConvergence
public import FloatLib.Numerics.Enclosure.Trigonometric.SinCosConvergence

/-!
# Arbitrarily accurate rational trigonometric enclosures

Both rational endpoints approach the exact real value of sine, cosine, or arctangent as the
degree grows. A format can combine these limits with a separate rounding-boundary argument;
these results alone do not assert termination of a correctly rounded operation.
-/
