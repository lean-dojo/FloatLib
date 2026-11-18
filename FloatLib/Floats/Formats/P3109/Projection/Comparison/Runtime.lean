/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Projection.Comparison.Decision
public import FloatLib.Numerics.Order.Bisection.Runtime

/-!
# P3109 projection from exact rational comparisons

P3109 interim report v4.1 (14 September 2026), §§4.7–4.8, unapproved draft.
The target is specified by comparison with rational boundaries. A bounded search
finds its lower positive grid point, and exact fractional threshold comparisons
select the rounded significand in every report policy.

One extra grid point beyond the largest finite encoding detects rounded overflow.
Larger magnitudes use an overflow representative before the shared saturation
step. This representative is not the full unbounded precision-rounded value.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109.ComparisonRounding

/-- Search through the first precision-grid point beyond the finite encoding range. -/
def lowerCode (format : Format) (compareTarget : Rat → Ordering) : Nat :=
  bisect (fun code =>
    decide (compareTarget (format.decodePositiveFinite code).toRat ≠ .lt))
    (format.bitWidth + 1) 0 (format.maxFiniteBits + 2)

/-- Reflect the two directed policies when rounding a negative magnitude. -/
def magnitudeMode (mode : RoundingMode) (negative : Bool) : RoundingMode :=
  if negative then
    match mode with
    | .up => .down
    | .down => .up
    | other => other
  else mode

/-- Round at a selected lower grid point, admitting the carry significand `2^P`. -/
def roundedAt (format : Format) (mode : RoundingMode) (negative : Bool)
    (compareTarget : Rat → Ordering) (code : Nat) : Numerics.Dyadic :=
  let lower := (format.decodePositiveFinite code).significand
  let exponent := format.decodeQuantum code
  let unit : Rat := 2 ^ exponent
  let upper := format.roundMagnitudeUp (magnitudeMode mode negative) exponent lower
    (compareTarget ((lower : Rat) * unit) == .eq)
    (fun scale threshold => compareTarget ((threshold : Rat) / scale * unit))
  let rounded := if upper then lower + 1 else lower
  if rounded = 0 then .zero else ⟨negative, rounded, exponent⟩

/-- A signed precision-grid representative, with magnitudes clipped only above finite overflow. -/
def rounded (format : Format) (mode : RoundingMode)
    (compareTarget : Rat → Ordering) : Numerics.Dyadic :=
  if compareTarget 0 = .eq then .zero
  else
    let negative := compareTarget 0 == .lt
    let compareMagnitude := if negative then
      fun boundary => (compareTarget (-boundary)).swap else compareTarget
    roundedAt format mode negative compareMagnitude (lowerCode format compareMagnitude)

/-- Saturate the rounded grid representative according to the supplied report policy. -/
def value (format : Format) (policy : ProjectionPolicy)
    (compareTarget : Rat → Ordering) : NumericalValue Numerics.Dyadic :=
  format.saturate policy.saturation policy.rounding
    (.finite (rounded format policy.rounding compareTarget))

/-- Encode the exact-comparison projection after rounding and saturation. -/
def code (format : Format) (policy : ProjectionPolicy)
    (compareTarget : Rat → Ordering) : BitVec format.bitWidth :=
  BitVec.ofNat format.bitWidth
    (Format.Internal.encodeDatumNat format (value format policy compareTarget))

end FloatLib.Floats.Formats.P3109.ComparisonRounding
