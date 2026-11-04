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

As the degree grows, both rational endpoints approach the exact real value of sine, cosine, or
arctangent. That isn't enough to prove that a correctly rounded operation terminates, which also
needs an argument for equality with a rounding boundary.
-/
