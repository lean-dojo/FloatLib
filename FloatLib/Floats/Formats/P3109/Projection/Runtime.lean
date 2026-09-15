/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Runtime
public import FloatLib.Numerics.Exact.Dyadic.Comparison.Runtime
public import FloatLib.Numerics.Quantization.Deterministic

/-!
# P3109 projection

P3109 projection has three distinct steps:

1. round finite dyadics to the descriptor's precision, preserve infinities, and map exceptions
   to NaN;
2. apply the selected saturation rule at the descriptor's finite endpoints;
3. encode the resulting datum.

This module follows that order directly. All integer widths, exponent bounds, and special codes
come from `Format`; there are no named-width branches or host floating-point conversions.

The stochastic modes receive a caller-supplied `BitVec`, whose width enforces the random-word
range.

## Reference

* IEEE Working Group P3109, *Interim Report on Arithmetic Formats for Machine Learning*,
  version 4.0.3 (1 September 2026), Sections 4.7.3--4.7.6, repository revision `34f5964`,
  <https://github.com/P3109/Public/tree/34f5964d9bb2382b2665d15467fc3517b990b308>.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109

/-- Exact random bits supplied to one P3109 stochastic-rounding decision. -/
structure RandomBits where
  /-- Number of random bits (`N` in the report). -/
  width : Nat
  /-- Unsigned random integer, intrinsically restricted to `0 ≤ R < 2^N`. -/
  bits : BitVec width
  deriving Repr

namespace RandomBits

/-- Construct a supplied random word from the low `width` bits of a natural number. -/
@[inline] def ofNat (width value : Nat) : RandomBits :=
  { width, bits := BitVec.ofNat width value }

/-- Read the supplied random bits as an unsigned natural number. -/
@[inline] def toNat (random : RandomBits) : Nat :=
  random.bits.toNat

end RandomBits

/-- Rounding modes defined by P3109 Section 4.7.4. -/
inductive RoundingMode where
  | towardZero
  | towardPositive
  | towardNegative
  | nearestTiesToAway
  | nearestTiesToEven
  | toOdd
  | stochasticA (random : RandomBits)
  | stochasticB (random : RandomBits)
  | stochasticC (random : RandomBits)
  deriving Repr

/-- Saturation modes defined by P3109 Section 4.7.5. -/
inductive SaturationMode where
  | finite
  | propagate
  | none
  deriving DecidableEq, Repr

/-- Complete policy used by one P3109 projection. -/
structure ProjectionPolicy where
  /-- Rule used when precision rounding discards nonzero low bits. -/
  rounding : RoundingMode := .nearestTiesToEven
  /-- Rule used after rounding produces a value outside the target datum set. -/
  saturation : SaturationMode := .none
  deriving Repr

namespace ProjectionPolicy

/-- FloatLib default projection: nearest-even rounding and no finite saturation request. -/
def nearestEven : ProjectionPolicy := {}

/-- Nearest-even projection clamped to the finite range. -/
def finite : ProjectionPolicy :=
  { saturation := .finite }

end ProjectionPolicy

namespace Format

/-- Largest finite positive code point for this descriptor. -/
@[inline] def maxFiniteBits (format : Format) : Nat :=
  match format.domain with
  | .finite => format.positiveInfinityBits
  | .extended => format.positiveInfinityBits - 1

/-- Exact largest finite value in this descriptor. -/
@[inline] def maxFinite (format : Format) : Numerics.Dyadic :=
  format.decodePositiveFinite format.maxFiniteBits

/-- Exact smallest finite value in this descriptor. -/
@[inline] def minFinite (format : Format) : Numerics.Dyadic :=
  match format.signedness with
  | .signed => format.maxFinite.neg
  | .unsigned => .zero

/--
Whether the lower candidate has an even P3109 code at a rounding boundary.

For `P > 1`, code parity is ordinary significand parity. The `P = 1` branch is the special rule
from Section 4.7.4: zero is even, and a nonzero code is even exactly when `Q + B` is even.
-/
@[inline] def lowerCodeIsEven (format : Format)
    (quantumExponent : Int) (lowerSignificand : Nat) : Bool :=
  if 1 < format.precision then
    lowerSignificand % 2 == 0
  else if lowerSignificand == 0 then
    true
  else
    decide ((quantumExponent + Int.ofNat format.exponentBias) % 2 = 0)

namespace Internal

/-- Floor of `(remainder / 2^discardedBits) * 2^outputBits`. -/
@[inline] def scaleFractionFloor
    (remainder discardedBits outputBits : Nat) : Nat :=
  if discardedBits ≤ outputBits then
    Nat.shiftLeft remainder (outputBits - discardedBits)
  else
    Nat.shiftRight remainder (discardedBits - outputBits)

/-- Nearest-even integer to `(remainder / 2^discardedBits) * 2^outputBits`. -/
@[inline] def scaleFractionNearestEven
    (remainder discardedBits outputBits : Nat) : Nat :=
  if discardedBits ≤ outputBits then
    Nat.shiftLeft remainder (outputBits - discardedBits)
  else
    Numerics.roundShiftRightEven remainder (discardedBits - outputBits)

/-- Decide whether precision rounding selects the integer above the floor candidate. -/
@[inline] def roundAway (format : Format) (mode : RoundingMode)
    (negative : Bool) (quantumExponent : Int) (lower remainder discardedBits : Nat) : Bool :=
  if remainder == 0 then
    false
  else
    let half := Nat.shiftLeft 1 (discardedBits - 1)
    match mode with
    | .towardZero => false
    | .towardPositive => !negative
    | .towardNegative => negative
    | .nearestTiesToAway => decide (half ≤ remainder)
    | .nearestTiesToEven =>
        decide (half < remainder) ||
          (remainder == half && !format.lowerCodeIsEven quantumExponent lower)
    | .toOdd => format.lowerCodeIsEven quantumExponent lower
    | .stochasticA random =>
        let scaled :=
          scaleFractionFloor remainder discardedBits random.width
        decide (2 ^ random.width ≤ scaled + random.toNat)
    | .stochasticB random =>
        let scaled :=
          scaleFractionFloor remainder discardedBits (random.width + 1)
        decide (2 ^ (random.width + 1) ≤ scaled + (2 * random.toNat + 1))
    | .stochasticC random =>
        let scaled :=
          scaleFractionNearestEven remainder discardedBits random.width
        decide (2 ^ random.width ≤ scaled + random.toNat)

end Internal

/--
Round one exact finite dyadic to P3109 precision before saturation.

The quantum is
`max(floor(log2 |X|), 1 - B) - P + 1`, so the same implementation handles normals,
subnormals, `P = 1`, and arbitrary descriptor widths.
-/
@[inline] def roundFiniteToPrecision
    (format : Format) (mode : RoundingMode)
    (value : Numerics.Dyadic) : Numerics.Dyadic :=
  if value.significand == 0 then
    .zero
  else
    let leadingExponent :=
      Int.ofNat value.significand.log2 + value.exponent
    let quantumExponent :=
      max leadingExponent format.minimumNormalExponent -
        Int.ofNat format.precision + 1
    match value.exponent - quantumExponent with
    | .ofNat shift =>
        {
          negative := value.negative
          significand := Nat.shiftLeft value.significand shift
          exponent := quantumExponent
        }
    | .negSucc shift =>
        let discardedBits := shift + 1
        let lower := Nat.shiftRight value.significand discardedBits
        let remainder :=
          Numerics.shiftRightRemainder value.significand discardedBits
        let rounded :=
          if Internal.roundAway format mode value.negative quantumExponent
              lower remainder discardedBits then
            lower + 1
          else
            lower
        if rounded == 0 then
          .zero
        else
          {
            negative := value.negative
            significand := rounded
            exponent := quantumExponent
          }

/-- Apply P3109 precision rounding while preserving infinities and mapping exceptions to NaN. -/
@[inline] def roundToPrecision
    (format : Format) (mode : RoundingMode)
    (value : NumericalValue Numerics.Dyadic) :
    NumericalValue Numerics.Dyadic :=
  match value with
  | .finite finite => .finite (format.roundFiniteToPrecision mode finite)
  | .infinity negative => .infinity negative
  | .exceptional _ => .exceptional (.nan)

namespace Internal

/-- Saturate a rounded value below the finite range. -/
@[inline] def saturateBelow
    (format : Format) (mode : SaturationMode) (rounding : RoundingMode) :
    NumericalValue Numerics.Dyadic :=
  match mode with
  | .finite | .propagate => .finite format.minFinite
  | .none =>
      match rounding with
      | .towardZero | .towardPositive => .finite format.minFinite
      | _ =>
          match format.signedness, format.domain with
          | .signed, .extended => .infinity true
          | .unsigned, .extended => .exceptional (.nan)
          | _, .finite => .exceptional (.nan)

/-- Saturate a rounded value above the finite range. -/
@[inline] def saturateAbove
    (format : Format) (mode : SaturationMode) (rounding : RoundingMode) :
    NumericalValue Numerics.Dyadic :=
  match mode with
  | .finite | .propagate => .finite format.maxFinite
  | .none =>
      match rounding with
      | .towardZero | .towardNegative => .finite format.maxFinite
      | _ =>
          match format.domain with
          | .extended => .infinity false
          | .finite => .exceptional (.nan)

end Internal

/-- Apply P3109 Section 4.7.5 to a value that has already been rounded to precision. -/
@[inline] def saturate
    (format : Format) (mode : SaturationMode) (rounding : RoundingMode)
    (value : NumericalValue Numerics.Dyadic) :
    NumericalValue Numerics.Dyadic :=
  match value with
  | .exceptional _ => .exceptional (.nan)
  | .infinity false =>
      match mode, format.domain with
      | .finite, _ => .finite format.maxFinite
      | .propagate, .extended | .none, .extended => .infinity false
      | .propagate, .finite => .finite format.maxFinite
      | .none, .finite => .exceptional (.nan)
  | .infinity true =>
      match mode, format.signedness, format.domain with
      | .finite, _, _ => .finite format.minFinite
      | .propagate, .signed, .extended => .infinity true
      | .propagate, _, _ => .finite format.minFinite
      | .none, .signed, .extended => .infinity true
      | .none, .unsigned, .extended | .none, _, .finite =>
          .exceptional (.nan)
  | .finite finite =>
      if Numerics.Dyadic.Internal.compareScalable
          finite format.minFinite == .lt then
        Internal.saturateBelow format mode rounding
      else if Numerics.Dyadic.Internal.compareScalable
          format.maxFinite finite == .lt then
        Internal.saturateAbove format mode rounding
      else
        .finite finite

/--
Mathematical result of P3109 projection before representation encoding.

Precision rounding is followed by saturation. The result gives the datum meaning before encoding.
-/
@[inline] def projectValue
    (format : Format) (policy : ProjectionPolicy)
    (value : NumericalValue Numerics.Dyadic) :
    NumericalValue Numerics.Dyadic :=
  format.saturate policy.saturation policy.rounding
    (format.roundToPrecision policy.rounding value)

namespace Internal

/--
Encode a positive finite datum.

The caller supplies a value already rounded to precision and inside the finite range. This is the
integer form of Section 4.7.6; it does not enumerate the codebook.
-/
@[inline] def encodePositiveFinite
    (format : Format) (value : Numerics.Dyadic) : Nat :=
  if value.significand == 0 then
    0
  else
    let exponent :=
      max (Int.ofNat value.significand.log2 + value.exponent)
        format.minimumNormalExponent
    let scale :=
      value.exponent - exponent + Int.ofNat format.trailingBits
    let significand :=
      match scale with
      | .ofNat shift => Nat.shiftLeft value.significand shift
      | .negSucc shift => Nat.shiftRight value.significand (shift + 1)
    let trailingUnit := 2 ^ format.trailingBits
    let trailing := significand % trailingUnit
    if significand < trailingUnit then
      trailing
    else
      trailing +
        Int.toNat (exponent + Int.ofNat format.exponentBias) * trailingUnit

/-- Encode a value known to be in this descriptor's datum set. -/
@[inline] def encodeDatumNat
    (format : Format) (value : NumericalValue Numerics.Dyadic) : Nat :=
  match value with
  | .exceptional _ => format.nanBits
  | .infinity false => format.positiveInfinityBits
  | .infinity true => format.negativeInfinityBits
  | .finite finite =>
      if finite.significand == 0 then
        0
      else
        let magnitude :=
          encodePositiveFinite format { finite with negative := false }
        if finite.negative then format.signBoundary + magnitude else magnitude

end Internal

/--
P3109 equality of datum meanings.

Finite values are equal numerically, infinity signs must match, and every NaN payload denotes the
format's single NaN datum. Other exceptional categories are not P3109 datums.
-/
def SameDatum :
    NumericalValue Numerics.Dyadic →
      NumericalValue Numerics.Dyadic → Prop
  | .finite left, .finite right => left.toRat = right.toRat
  | .infinity left, .infinity right => left = right
  | .exceptional (.nan _), .exceptional (.nan _) => True
  | _, _ => False

/--
Executable equality of P3109 datum meanings.

Finite dyadics are compared numerically, so harmless differences in significand normalization do
not make a representable value fail the checked encoder. P3109 has one NaN, so its optional
payload is not semantically observable here.
-/
@[inline] def datumEqual :
  NumericalValue Numerics.Dyadic →
      NumericalValue Numerics.Dyadic → Bool
  | .finite left, .finite right =>
      Numerics.Dyadic.Internal.compareScalable left right == .eq
  | .infinity left, .infinity right => left == right
  | .exceptional (.nan _), .exceptional (.nan _) => true
  | _, _ => false

/--
Encode a value only when it belongs to this descriptor's datum set.

Unlike projection, this operation performs no rounding or saturation. It computes the direct
P3109 code, decodes it, and accepts the result only when the numerical datum is unchanged.
-/
@[inline] def encode?
    (format : Format) (value : NumericalValue Numerics.Dyadic) :
    Option (BitVec format.bitWidth) :=
  let candidate :=
    BitVec.ofNat format.bitWidth (Internal.encodeDatumNat format value)
  if datumEqual (format.decode candidate) value then
    some candidate
  else
    none

/-- Project one exact closed value and return its descriptor-width code. -/
@[inline] def projectCode
    (format : Format) (policy : ProjectionPolicy)
    (value : NumericalValue Numerics.Dyadic) : BitVec format.bitWidth :=
  BitVec.ofNat format.bitWidth
    (Internal.encodeDatumNat format (format.projectValue policy value))

end Format
end FloatLib.Floats.Formats.P3109

namespace FloatLib.Floats.ExecFloat.P3109

variable {format : Formats.P3109.Format}

/--
Project an exact finite, infinite, or NaN value into a P3109 descriptor.

The operation rounds once to P3109 precision, applies saturation, and encodes the result directly.
It never routes through IEEE 754 or a host float.
-/
@[inline] def project
    (policy : Formats.P3109.ProjectionPolicy)
    (value : NumericalValue Numerics.Dyadic) :
    ExecFloat.P3109 format :=
  ExecFloat.Codebook.ofCode (format.projectCode policy value)

/-- Project one exact finite dyadic into a P3109 descriptor. -/
@[inline] def ofDyadic
    (policy : Formats.P3109.ProjectionPolicy)
    (value : Numerics.Dyadic) :
    ExecFloat.P3109 format :=
  project policy (.finite value)

/-- Encode an already representable P3109 datum without rounding it. -/
@[inline] def encode?
    (value : NumericalValue Numerics.Dyadic) :
    Option (ExecFloat.P3109 format) :=
  (format.encode? value).map ExecFloat.Codebook.ofCode

end FloatLib.Floats.ExecFloat.P3109
