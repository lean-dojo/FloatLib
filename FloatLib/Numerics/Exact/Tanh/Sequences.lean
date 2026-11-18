/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Product.Angle
public import FloatLib.Numerics.Enclosure.Rational.Product
public import FloatLib.Numerics.Enclosure.Elementary.BinaryGridRuntime

/-!
# Enclosures for the hyperbolic tangent of a complex rational

For `a > 0` the parts of `tanh (a + i b)` are quotients with the positive denominator
`cosh 2a + cos 2b`. With `u = exp (-2a)` and `v = exp (-4a)`, the order of a part and a rational
`t` is the sign of a numerator that involves only the small exponentials:

* real part: `(1 - t) - (1 + t) v - 2 t u cos 2b`;
* imaginary part: `2 u sin 2b - t - t v - 2 t u cos 2b`.

So a huge `a` never produces a huge number. `expLadder` encloses an exponential with fast
binary-grid enclosures at its first levels and the rational Taylor enclosures, whose convergence
is proved, after them.
-/

@[expose] public section

namespace FloatLib.Numerics.TanhComparison

open RationalInterval

/--
Enclosures of `exp x`: on the binary grid of `32 * 2 ^ n` fractional bits at the first
`ProductComparison.fastLevels` levels, and the rational Taylor enclosure of degree `2 ^ n` after
them.
-/
def expLadder (x : ℚ) : Nat → RationalInterval :=
  prefixed (fun n => Enclosure.BinaryGrid.exp x (8 + 2 ^ n) (32 * 2 ^ n))
    ProductComparison.fastLevels
    (fun n => Enclosure.exp x (2 ^ n))

/-- The enclosure of `u + cos 2b`, whose sign orders the real part against one. -/
def unitInterval (u cosine : RationalInterval) : RationalInterval :=
  u.add cosine

/-- The enclosure of the numerator `(1 - t) - (1 + t) v - 2 t u cos 2b` of the real part. -/
def reInterval (u v cosine : RationalInterval) (t : ℚ) : RationalInterval :=
  ((point (1 - t)).sub (v.scale (1 + t))).sub ((u.mul cosine).scale (2 * t))

/-- The enclosure of the numerator `2 u sin 2b - t - t v - 2 t u cos 2b` of the imaginary part. -/
def imInterval (u v sine cosine : RationalInterval) (t : ℚ) : RationalInterval :=
  ((((u.mul sine).scale 2).sub (point t)).sub (v.scale t)).sub ((u.mul cosine).scale (2 * t))

end FloatLib.Numerics.TanhComparison
