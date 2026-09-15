/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Arithmetic.Mixed.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.Core
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Conversion.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Rounding

/-!
# P3109 arithmetic with external binary destinations

The report's projection uses the external format's actual precision, bias, and finite endpoints.
It retains all nine rounding modes and all three saturation modes, with explicit stochastic bits.
Finite overflow under `SaturationMode.propagate` clamps, while an infinite exact input remains
infinite.
The destination encoder writes positive zero and canonical quiet NaN, as required by §4.8.2.

Finite encoding uses the proved binary dyadic encoder on an already rounded, in-range datum;
the proof facet establishes that this encoding does not introduce another rounding error.
The adapters accept IEEE-style encoding descriptors, including binary16, binary32, binary64,
and BFloat16. They do not change the ordinary IEEE arithmetic or signed-zero conversion APIs.

Reference: P3109 unapproved interim report 4.0.3, revision `34f5964`, §§4.7–4.10 and 4.14.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109.Arithmetic.External

open BinaryInterchange

/-- Round an exact rational with the external format's precision and exponent bias. -/
def roundFinite (format : FloatFormat) (mode : P3109.RoundingMode) (exact : Rat) :
    Numerics.Dyadic :=
  let numerator := exact.num.natAbs
  if numerator == 0 then .zero
  else
    let leading := RationalBinary.floorLog2 numerator exact.den
    let quantum := max leading format.minNormalExponent - Int.ofNat format.fracWidth
    let scaled := RationalBinary.scaleByPowerOfTwo numerator exact.den (-quantum)
    let lower := scaled.1 / scaled.2
    let rounded :=
      if P3109.Format.Internal.roundRationalAwayWithParity mode (exact.num < 0)
          (lower % 2 == 0) (scaled.1 % scaled.2) scaled.2 then lower + 1 else lower
    if rounded == 0 then .zero
    else { negative := exact.num < 0, significand := rounded, exponent := quantum }

/-- Apply precision rounding, retaining infinity and canonicalizing NaN. -/
def roundValue (format : FloatFormat) (mode : P3109.RoundingMode) :
    NumericalValue Rat → NumericalValue Numerics.Dyadic
  | .finite value => .finite (roundFinite format mode value)
  | .infinity sign => .infinity sign
  | .exceptional _ => .exceptional (.nan)

/-- Exact largest finite external binary value, with a supplied sign. -/
def endpoint (format : FloatFormat) (negative : Bool) : Numerics.Dyadic :=
  { negative
    significand := 2 ^ (format.fracWidth + 1) - 1
    exponent := format.maxNormalExponent - Int.ofNat format.fracWidth }

/-- Saturate a finite overflow under the external format's signed, extended domain. -/
def finiteOverflow (format : FloatFormat) (policy : ProjectionPolicy) (negative : Bool) :
    NumericalValue Numerics.Dyadic :=
  match policy.saturation with
  | .finite | .propagate => .finite (endpoint format negative)
  | .none =>
      match policy.rounding with
      | .towardZero => .finite (endpoint format negative)
      | .towardPositive =>
          if negative then .finite (endpoint format true) else .infinity false
      | .towardNegative =>
          if negative then .infinity true else .finite (endpoint format false)
      | _ => .infinity negative

/-- Saturate after rounding; `.propagate` distinguishes finite overflow from infinity. -/
def saturate (format : FloatFormat) (policy : ProjectionPolicy) :
    NumericalValue Numerics.Dyadic → NumericalValue Numerics.Dyadic
  | .exceptional _ => .exceptional (.nan)
  | .infinity negative =>
      if policy.saturation == .finite then .finite (endpoint format negative)
      else .infinity negative
  | .finite value =>
      if Numerics.Dyadic.Internal.compareScalable
          (endpoint format false) { value with negative := false } == .lt then
        finiteOverflow format policy value.negative
      else .finite value

/-- Exact rounded and saturated result, before external encoding. -/
def projectValue (format : FloatFormat) (policy : ProjectionPolicy) (value : NumericalValue Rat) :
    NumericalValue Numerics.Dyadic :=
  saturate format policy (roundValue format policy.rounding value)

/-- Encode a projected external datum, using positive zero and canonical quiet NaN. -/
def encode (format : FloatFormat) : NumericalValue Numerics.Dyadic → Model format
  | .exceptional _ => Model.canonicalNaN format
  | .infinity negative => if negative then Model.negInf format else Model.posInf format
  | .finite value =>
      if value.significand == 0 then Model.zero format false
      else Model.roundDyadic format value

/-- External report projection; the evidence excludes non-IEEE exceptional encodings. -/
def project (format : FloatFormat) (_ieee : format.isIEEE = true)
    (policy : ProjectionPolicy) (value : NumericalValue Rat) : Model format :=
  encode format (projectValue format policy value)

/-- Complete exact external decoding with zero signs and NaN payloads erased. -/
def decode {format : FloatFormat} (value : Model format) : NumericalValue Rat :=
  Arithmetic.toRat ((Model.exactNumericalSystem format).denote value)

/-- A binary model can be an external source of mixed report arithmetic. -/
instance modelDecoder (format : FloatFormat) : ExecFloat.ExactDecoder (Model format) Rat where
  decode := decode

/-- Report projection into an external model, with no storage-plan requirements. -/
def destination (format : FloatFormat) (ieee : format.isIEEE = true := by decide) :
    Destination (Model format) :=
  ⟨project format ieee⟩

/-- Report projection into a configured external carrier through its exact model codec. -/
def configuredDestination (format : FloatFormat)
    (plan : Configured.StoragePlan format) (code : Type)
    [ExecFloat.ModelCodec plan (Model format) code]
    (ieee : format.isIEEE = true := by decide) :
    Destination (ExecFloat (Configured.Family format code plan)) :=
  ⟨fun policy value => ExecFloat.Binary.ofModel (project format ieee policy value)⟩

/-- External bit width from the complete binary descriptor. -/
@[inline] def bitwidthOf (format : FloatFormat) : Nat := format.bitWidth

/-- External precision includes the implicit leading bit. -/
@[inline] def precisionOf (format : FloatFormat) : Nat := format.fracWidth + 1

/-- External IEEE formats are signed. -/
@[inline] def signednessOf (_format : FloatFormat) : Signedness := .signed

/-- External IEEE formats have the extended domain. -/
@[inline] def domainOf (_format : FloatFormat) : Domain := .extended

/-- External exponent-field width. -/
@[inline] def exponentBitwidthOf (format : FloatFormat) : Nat := format.expWidth

/-- External fraction-field width. -/
@[inline] def trailingSignificandBitwidthOf (format : FloatFormat) : Nat := format.fracWidth

/-- The actual external bias; no P3109 bias is substituted. -/
@[inline] def exponentBiasOf (format : FloatFormat) : Nat := format.exponentBias

/-- Largest finite external datum. -/
@[inline] def maxFiniteOf (format : FloatFormat) : Model format := Model.posMaxFinite format

/-- Smallest finite external datum. -/
@[inline] def minFiniteOf (format : FloatFormat) : Model format := Model.negMaxFinite format

/-- Smallest strictly positive external datum. -/
@[inline] def minPositiveOf (format : FloatFormat) : Model format := Model.ofNatBits 1

/-- Largest positive external subnormal. -/
@[inline] def maxSubnormalOf (format : FloatFormat) : Model format :=
  Model.ofNatBits (2 ^ format.fracWidth - 1)

/-- Smallest positive external normal. -/
@[inline] def minNormalOf (format : FloatFormat) : Model format :=
  Model.ofNatBits (2 ^ format.fracWidth)

end FloatLib.Floats.Formats.P3109.Arithmetic.External
