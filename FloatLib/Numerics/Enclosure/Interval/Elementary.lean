/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.Basic
public import FloatLib.Numerics.Enclosure.Elementary.Runtime
public import FloatLib.Numerics.Enclosure.Trigonometric.Reduction.Runtime
public import Mathlib.Data.Nat.Sqrt

/-!
# Elementary functions on rational intervals

Monotone functions use lower and upper endpoint enclosures. Sine and cosine instead enclose
the midpoint and add the half-width, using their global Lipschitz constant one. Intersecting
with `[-1, 1]` keeps the bounds useful even when the requested Taylor degree is small.

The analytic point enclosures come from `Numerics.Enclosure`. Square root uses an integer
square root after exact dyadic scaling. `ElementaryProof` proves containment of every real
member of the input interval, including irrational members.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval

/--
Combine the lower enclosure at the left endpoint with the upper enclosure at the right.

Soundness requires a monotone real function and sound point enclosures. A point interval
evaluates the enclosure only once.
-/
def monotoneBounds (enclose : ℚ → Interval ℚ) (I : Interval ℚ) : Interval ℚ :=
  let lo := enclose I.lo
  if I.lo = I.hi then lo else ⟨lo.lo, (enclose I.hi).hi⟩

/-- Enclose the exponential on the whole interval, with the supplied Taylor degree. -/
def expBounds (I : Interval ℚ) (terms : Nat) : Interval ℚ :=
  monotoneBounds (fun x =>
    let J := Enclosure.exp x terms
    ⟨max 0 J.lo, J.hi⟩) I

/-- Enclose the logarithm when the entire input interval is strictly positive. -/
def logBounds? (I : Interval ℚ) (terms : Nat) : Option (Interval ℚ) :=
  if 0 < I.lo then
    some (monotoneBounds (fun x =>
      let J := Enclosure.log x terms
      ⟨J.lo, J.hi⟩) I)
  else none

/-- Enclose arctangent on the whole interval, using the reduced rational point kernel. -/
def atanBounds (I : Interval ℚ) (terms : Nat) : Interval ℚ :=
  monotoneBounds (fun x =>
    let J := Enclosure.atan x terms
    ⟨J.lo, J.hi⟩) I

/--
Enclose a function with Lipschitz constant one and range in `[-1, 1]`.

The midpoint enclosure is widened by the half-width. Widths at least four already give the
whole unit range after this widening, so they skip the point kernel.
-/
def lipschitzUnitBounds (enclose : ℚ → Interval ℚ) (I : Interval ℚ) : Interval ℚ :=
  if 4 ≤ I.hi - I.lo then ⟨-1, 1⟩
  else
    let midpoint := (I.lo + I.hi) / 2
    let radius := (I.hi - I.lo) / 2
    let J := enclose midpoint
    ⟨max (-1) (J.lo - radius), min 1 (J.hi + radius)⟩

/-- Share the period certificate and turn count between the value and error bounds. -/
def Internal.reducedTrigBounds (taylor : ℚ → Nat → ℚ) (x : ℚ)
    (terms : Nat) : RationalInterval :=
  let pi := Enclosure.piQuarter terms
  let quarter := max (1 / 2) (min 1 pi.lo)
  let turns : Int := ⌊x / (8 * quarter) + 1 / 2⌋
  let arg := x - 8 * (turns : ℚ) * quarter
  let radius :=
    Enclosure.trigRadius arg terms + 8 * |(turns : ℚ)| * (pi.hi - quarter)
  Enclosure.restrictUnit (RationalInterval.around (taylor arg terms) radius)

/--
Enclose sine for every real in the interval, including intervals crossing an extremum.

Small midpoints use the direct Taylor kernel. Larger ones use proved rational period
reduction; the resulting period error is included in the point enclosure.
-/
def sinBounds (I : Interval ℚ) (terms : Nat) : Interval ℚ :=
  lipschitzUnitBounds (fun x =>
    let J := if |x| ≤ 4 then Enclosure.sin x terms
      else Internal.reducedTrigBounds Enclosure.sinTaylor x terms
    ⟨J.lo, J.hi⟩) I

/-- Enclose cosine by the midpoint Lipschitz bound, without assuming endpoint monotonicity. -/
def cosBounds (I : Interval ℚ) (terms : Nat) : Interval ℚ :=
  lipschitzUnitBounds (fun x =>
    let J := if |x| ≤ 4 then Enclosure.cos x terms
      else Internal.reducedTrigBounds Enclosure.cosTaylor x terms
    ⟨J.lo, J.hi⟩) I

/--
Dyadic bounds for the square root of a nonnegative rational.

The lower endpoint is `floor (sqrt x * 2^precision) / 2^precision`, computed by an integer
square root. The upper endpoint is one grid step higher, unless the lower endpoint squares
to `x` exactly. The width is therefore at most `2^(-precision)`.
-/
def sqrtPointBounds (x : ℚ) (precision : Nat) : Interval ℚ :=
  let scale := (2 : ℚ) ^ precision
  let root := Nat.sqrt ⌊x * scale ^ 2⌋₊
  let lo := (root : ℚ) / scale
  ⟨lo, if lo ^ 2 = x then lo else (root + 1 : ℚ) / scale⟩

/--
Enclose square root on a nonnegative interval with a dyadic grid of step `2^(-precision)`.

A negative lower endpoint returns `none`, including intervals that cross zero from below.
Zero and exact dyadic squares are accepted without an artificial positive lower bound.
-/
def sqrtBounds? (I : Interval ℚ) (precision : Nat) : Option (Interval ℚ) :=
  if 0 ≤ I.lo then some (monotoneBounds (fun x => sqrtPointBounds x precision) I)
  else none

end FloatLib.Numerics.Interval
