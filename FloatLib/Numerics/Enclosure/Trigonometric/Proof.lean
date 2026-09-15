/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Trigonometric.AtanProof
public import FloatLib.Numerics.Enclosure.Trigonometric.SinCosProof

/-!
# Rational trigonometric containment

The arctangent kernel uses exact rational argument reduction. The sine and cosine kernels use
global Taylor bounds. Each computed interval contains the corresponding real function value
for every rational input and every finite degree.
-/
