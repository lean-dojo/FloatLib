/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Product.Factors
public import FloatLib.Numerics.Enclosure.Constants.Runtime
public import FloatLib.Numerics.Enclosure.Expression.Closed
public import FloatLib.Numerics.Enclosure.Rational.Product

/-!
# Enclosures of the cosine and sine of an enclosed angle

`trigBounds?` encloses `cos x` or `sin x` for a real `x` known by a rational interval, at any
size of `x`, with a relative accuracy that does not depend on that size.

* A large angle is reduced by whole quarter turns with the cached enclosure of `π / 2` at as
  many bits as the angle has above the binary point, plus the working precision. The cost of the
  series stays that of a small argument.
* A small angle keeps its relative accuracy: `smallAngleBounds?` uses `a - a³ / 6 < sin a < a`
  and `1 - a² / 2 ≤ cos a ≤ 1`, which a grid of absolute precision cannot give for an angle of
  `2 ^ -1000`.
* Any other reduced angle is evaluated on the binary grid, finer by the bits that the angle lies
  below one.

`Trig.intervals` is the sequence of enclosures that the exact comparators of the complex
functions refine: `trigBounds?` at the first levels, so that an angle of any size is cheap, and
the enclosures by argument reduction of `Trig.reduced`, whose convergence is proved, after them.

`AngleProof` proves every returned enclosure sound and the sequence convergent.
-/

@[expose] public section

namespace FloatLib.Numerics

/--
The number of bits by which a rational below one lies below one, within one bit: the extra
precision that keeps the relative accuracy of a result of that size.
-/
def bitsBelowOne (x : Rat) : Nat :=
  if 1 ≤ x then 0 else x.den.log2 + 1 - x.num.natAbs.log2

namespace ProductComparison

/--
Enclose `cos a` or `sin a` for a real `a` in an interval of positive or of negative numbers of
magnitude at most `2 ^ -(precision / 2)`, by `a - a³ / 6 < sin a < a` and
`1 - a² / 2 ≤ cos a ≤ 1` for a positive `a`. The enclosure keeps the relative accuracy of the
interval however small the angle is. `none` for every other interval.
-/
def smallAngleBounds? (trig : Trig) (angle : RationalInterval) (precision : Nat) :
    Option RationalInterval :=
  if 0 < angle.lo ∧ angle.hi ≤ 1 / 2 ^ (precision / 2) then
    some (match trig with
      | .sin => ⟨angle.lo - angle.lo ^ 3 / 6, angle.hi⟩
      | .cos => ⟨1 - angle.hi ^ 2 / 2, 1⟩)
  else if angle.hi < 0 ∧ -(1 / 2 ^ (precision / 2)) ≤ angle.lo then
    some (match trig with
      | .sin => ⟨angle.lo, angle.hi - angle.hi ^ 3 / 6⟩
      | .cos => ⟨1 - angle.lo ^ 2 / 2, 1⟩)
  else none

/-- `π / 2` between the cached lower bound with `bits` fractional bits and two units above. -/
def halfPiBounds (bits : Nat) : RationalInterval :=
  ⟨(Enclosure.Constants.halfPiLower bits : ℚ) / 2 ^ bits,
    ((Enclosure.Constants.halfPiLower bits : ℚ) + 2) / 2 ^ bits⟩

/-- The number of quarter turns nearest to the middle of the interval. -/
def quarterTurns (angle halfPi : RationalInterval) : Int :=
  ⌊(angle.lo + angle.hi) / (halfPi.lo + halfPi.hi) + 1 / 2⌋

/-- The other function of the pair. -/
def Trig.swap : Trig → Trig
  | .cos => .sin
  | .sin => .cos

/-- The function of the reduced angle that gives `trig` after `k` quarter turns, up to sign. -/
def Trig.turned (trig : Trig) (k : Int) : Trig :=
  if k % 2 = 0 then trig else trig.swap

/-- Whether `trig` after `k` quarter turns is the negated function of the reduced angle. -/
def Trig.turnedNegative (trig : Trig) (k : Int) : Bool :=
  match trig with
  | .cos => decide (k % 4 = 1 ∨ k % 4 = 2)
  | .sin => decide (k % 4 = 2 ∨ k % 4 = 3)

/--
Enclose `cos r` or `sin r` for a real `r` in a reduced interval: by `smallAngleBounds?` when it
applies, and otherwise on the binary grid of `precision` bits and as many more as the interval
lies below one, up to `precision / 2`. The Taylor degree is the one that this grid needs at an
angle below one, and less for a smaller angle.
-/
def reducedTrigBounds? (trig : Trig) (reduced : RationalInterval) (precision : Nat) :
    Option RationalInterval :=
  match smallAngleBounds? trig reduced precision with
  | some small => some small
  | none =>
      let below := bitsBelowOne (max |reduced.lo| |reduced.hi|)
      let grid := precision + min below (precision / 2 + 1)
      (Interval.Expr.unary trig.op (.var 0)).gridEnclosureWith? [reduced] grid
        (2 * grid / (grid.log2 + 2 * below) + 8)

/--
Enclose `cos x` or `sin x` for a real `x` in the interval `angle`, with about `precision` bits.
An interval within `[-3 / 4, 3 / 4]` needs no reduction. From any other the nearest number of
quarter turns is subtracted, with `π / 2` known to the bits of the angle above the binary point
plus `precision`, and the function of the reduced angle that the quadrant selects is enclosed.
-/
def trigBounds? (trig : Trig) (angle : RationalInterval) (precision : Nat) :
    Option RationalInterval :=
  if max |angle.lo| |angle.hi| ≤ 3 / 4 then reducedTrigBounds? trig angle precision
  else
    (reducedTrigBounds?
      (trig.turned (quarterTurns angle
        (halfPiBounds (precision + ⌈max |angle.lo| |angle.hi|⌉₊.log2 + 8))))
      (angle.sub ((halfPiBounds (precision + ⌈max |angle.lo| |angle.hi|⌉₊.log2 + 8)).scale
        (quarterTurns angle (halfPiBounds (precision + ⌈max |angle.lo| |angle.hi|⌉₊.log2 + 8)))))
      precision).map fun bounds =>
        if trig.turnedNegative (quarterTurns angle
          (halfPiBounds (precision + ⌈max |angle.lo| |angle.hi|⌉₊.log2 + 8))) then bounds.neg
        else bounds

/--
Number of leading levels of a sequence of enclosures that use fast enclosures, before the ones
whose convergence is proved: of `Trig.intervals` here, and of the exponential ladder of the
tangent.
-/
def fastLevels : Nat := 12

/--
Enclosures of the bounded factor at `b` for the exact comparators: `trigBounds?` with
`64 * 2 ^ n` bits at the first `fastLevels` levels, and the enclosures by argument reduction
after them.
-/
def Trig.intervals (trig : Trig) (b : ℚ) : Nat → RationalInterval :=
  RationalInterval.prefixed (fun n => (trigBounds? trig ⟨b, b⟩ (64 * 2 ^ n)).getD ⟨-1, 1⟩)
    fastLevels (trig.reduced b)

end ProductComparison
end FloatLib.Numerics
