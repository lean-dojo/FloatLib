/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Rational
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Directed.Dyadic
public import FloatLib.Numerics.Operation.Context
public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Decode

/-!
# Executable policy-aware binary quantization

Encoding policy and operation policy are distinct. E4M3FN, for example, has one fixed collection
of bit patterns but supports both saturating and non-saturating conversions. Hardware may also
flush a subnormal result to zero even though the storage format can represent that subnormal.

`QuantizationPolicy` records the three choices needed when an exact rational is written into a
binary format:

1. integer rounding at the discarded-bit boundary;
2. behavior beyond the largest finite magnitude;
3. gradual underflow or flush-to-zero after rounding.

The implementation uses natural-number arithmetic only. It never passes through a host float.
The local stochastic choice in `roundQuot` is deterministic given `entropy` and is unbiased when
`entropy % den` is uniform. That statement does not by itself give a global unbiasedness theorem
for quantization with saturation, overflow, or flush-to-zero.

`roundDyadicGeneral` always executes the rational policy algorithm below. The ordinary
`roundDyadic` entry point dispatches the four `IEEERoundingMode` choices with native overflow
and gradual underflow to the shift-based rounders in `Rounding.Directed.Dyadic`. Every other
policy uses the general engine. Keeping these two implementations independent makes the
agreement theorem in `Rounding.Policy.Agreement` meaningful rather than a consequence of
delegation.

Both engines resolve overflow through `directedOverflow`, so a finite-with-NaN encoding such as
E4M3FN saturates to its largest finite value in the truncating direction and produces its NaN word
only when the direction carries the magnitude past that value.

References:

* IEEE 754-2019, Sections 4.3 and 7.4, for directed and nearest rounding and overflow behavior.
* Open Compute Project, *8-bit Floating Point Specification (OFP8), Revision 1.0*, Section 5.2,
  <https://www.opencompute.org/documents/ocp-8-bit-floating-point-specification-ofp8-revision-1-0-2023-12-01-pdf-1>.
* NVIDIA, *CUDA Math API: FP8 Conversion and Data Movement*, for `NOSAT` and `SATFINITE`,
  <https://docs.nvidia.com/cuda/cuda-math-api/cuda_math_api/group__CUDA__MATH__FP8__MISC.html>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Numerics

namespace Policy

/--
Round `num / den` to a natural number according to `mode`.

`sign` is needed only by directed modes. For stochastic rounding with `den > 0`,
`entropy % den < num % den` chooses the upper integer. A uniform `entropy % den` therefore selects
the upper value with probability equal to the fractional part of `num / den`.
-/
@[inline] def roundQuot (mode : RoundingMode) (sign : Bool) (entropy num den : Nat) : Nat :=
  let quotient := num / den
  let remainder := num % den
  if remainder == 0 then
    quotient
  else
    match mode with
    | .nearestEven =>
        let twice := 2 * remainder
        if twice < den then quotient
        else if twice > den then quotient + 1
        else if quotient % 2 == 0 then quotient else quotient + 1
    | .nearestAway =>
        if 2 * remainder < den then quotient else quotient + 1
    | .towardZero => quotient
    | .towardPositive => if sign then quotient else quotient + 1
    | .towardNegative => if sign then quotient + 1 else quotient
    | .stochastic => if entropy % den < remainder then quotient + 1 else quotient

/--
The `IEEERoundingMode` constructor with the same direction as `mode`, when available.

This type has no nearest-away or stochastic constructor, so those modes map to `none`.
-/
def ieeeRoundingMode? : RoundingMode → Option IEEERoundingMode
  | .nearestEven => some .nearestEven
  | .towardZero => some .towardZero
  | .towardPositive => some .towardPositiveInfinity
  | .towardNegative => some .towardNegativeInfinity
  | .nearestAway | .stochastic => none

/--
The IEEE rounding direction that `policy` reduces to, if any.

This returns a direction when overflow is native, underflow is gradual, and the rounding mode
has an `IEEERoundingMode` constructor. `roundDyadic` executes such
policies with the directed rounders instead of the general engine.
-/
def policyIEEERoundingMode? (policy : QuantizationPolicy) : Option IEEERoundingMode :=
  match policy.overflow, policy.underflow with
  | .native, .gradual => ieeeRoundingMode? policy.rounding
  | .native, .flushToZero | .saturate, _ => none

/--
Whether an overflowing magnitude of sign `sign` is carried upward under `mode`.

This is the direction test of IEEE 754-2019 Section 7.4 on the policy vocabulary; see
`directedOverflow`. Nearest-away and stochastic rounding overflow as the nearest modes do.
-/
@[inline] def overflowRoundsMagnitudeUp (mode : RoundingMode) (sign : Bool) : Bool :=
  match mode with
  | .towardZero => false
  | .towardPositive => !sign
  | .towardNegative => sign
  | .nearestEven | .nearestAway | .stochastic => true

/--
Whether a positive magnitude below half the least subnormal rounds up to that subnormal.

The answer is `none` for stochastic rounding, where it depends on the entropy. Nearest modes and
toward-zero rounding take such a magnitude to zero; the two infinity-directed modes take it to the
least subnormal when the direction carries the magnitude away from zero.
-/
@[inline] def tinyRoundsMagnitudeUp? (mode : RoundingMode) (sign : Bool) : Option Bool :=
  match mode with
  | .towardPositive => some (!sign)
  | .towardNegative => some sign
  | .nearestEven | .nearestAway | .towardZero => some false
  | .stochastic => none

/--
Result selected by a magnitude overflow.

With `.saturate` the result is the largest finite value of the requested sign. With `.native` the
direction rule of `directedOverflow` applies: a magnitude carried upward becomes the format's
native overflow value (signed infinity for the IEEE encoding, the NaN word for the two
finite-with-NaN encodings, the largest finite value for the fully finite encoding) and a magnitude
carried downward becomes the largest finite value of the requested sign.
-/
@[inline] def overflowResult (fmt : FloatFormat) (mode : OverflowMode)
    (rounding : RoundingMode) (sign : Bool) : Model fmt :=
  match mode with
  | .saturate => Model.maxFinite fmt sign
  | .native => directedOverflow fmt sign (overflowRoundsMagnitudeUp rounding sign)

/-- Apply output flush-to-zero after gradual rounding has selected an encoding. -/
@[inline] def applyUnderflow (fmt : FloatFormat) (mode : UnderflowMode)
    (x : Model fmt) : Model fmt :=
  match mode with
  | .gradual => x
  | .flushToZero =>
      if Model.isSubnormal x then Model.zero fmt (Model.signBit x) else x

/--
Round the nonnegative rational magnitude `num / den` into `fmt` with the requested sign.

This is the statically checked arithmetic core used after a caller has established that `den > 0`.
A magnitude below half the least subnormal is decided by the rounding direction alone, except
under stochastic rounding, so the subnormal alignment shift is not materialized for such inputs.
Stochastic rounding of a far-below-subnormal quotient does shift `num` by the full alignment
`fmt.exponentBias + fmt.fracWidth - 1`, because the exact remainder decides the outcome.
-/
def roundRatGeneralOfDenNeZero (fmt : FloatFormat) (policy : QuantizationPolicy) (entropy : Nat)
    (sign : Bool) (num den : Nat) (_hden : den ≠ 0) : Model fmt :=
  let precision := fmt.fracWidth
  let minNormal := fmt.minNormalExponent
  let maxNormal := fmt.maxNormalExponent
  let overflow := overflowResult fmt policy.overflow policy.rounding sign
  let gradual : Model fmt :=
    if num == 0 then
      Model.zero fmt sign
    else
      let exponent := Numerics.RationalBinary.floorLog2 num den
      if exponent > maxNormal then
        overflow
      else if exponent < minNormal then
        let tiny :=
          if exponent + 1 < fmt.minSubnormalExponent then
            tinyRoundsMagnitudeUp? policy.rounding sign
          else
            none
        match tiny with
        | some true => Model.ofFields fmt sign 0 1
        | some false => Model.zero fmt sign
        | none =>
            let shift := fmt.exponentBias + precision - 1
            let fraction :=
              roundQuot policy.rounding sign entropy (Nat.shiftLeft num shift) den
            Model.packRoundedSubnormal fmt sign (Model.zero fmt sign) fraction
      else
        let shift : Int := Int.ofNat precision - exponent
        let (scaledNum, scaledDen) :=
          match shift with
          | .ofNat amount => (Nat.shiftLeft num amount, den)
          | .negSucc amount => (num, Nat.shiftLeft den (amount + 1))
        let rounded := roundQuot policy.rounding sign entropy scaledNum scaledDen
        Model.packRoundedNormal fmt sign overflow exponent rounded
  applyUnderflow fmt policy.underflow gradual

/--
Round the nonnegative rational magnitude `num / den` into `fmt` with the requested sign.

A zero denominator returns `none`. Otherwise the function first performs gradual quantization and
then applies `policy.underflow`; this matters at the normal/subnormal boundary, where a value below
the smallest normal can nevertheless round up to that normal value.
-/
def roundRatGeneral (fmt : FloatFormat) (policy : QuantizationPolicy) (entropy : Nat)
    (sign : Bool) (num den : Nat) : Option (Model fmt) :=
  if hden : den = 0 then
    none
  else
    some (roundRatGeneralOfDenNeZero fmt policy entropy sign num den hden)

/--
Round an exact rational magnitude into `fmt` under `policy`.

Nearest-even with native overflow and gradual underflow is the canonical `Model.roundRat`
operation for every complete format descriptor. Other rounding, overflow, or
underflow policies use the explicit general algorithm above. A zero denominator returns `none`
uniformly, including for finite-only formats that have no NaN encoding.
-/
def roundRat (fmt : FloatFormat) (policy : QuantizationPolicy) (entropy : Nat)
    (sign : Bool) (num den : Nat) : Option (Model fmt) :=
  if hden : den = 0 then
    none
  else if policy == QuantizationPolicy.nearestEven then
    some (Model.roundRat fmt sign num den)
  else
    some (roundRatGeneralOfDenNeZero fmt policy entropy sign num den hden)

/--
Round an exact signed dyadic with the independent rational policy algorithm.

This definition deliberately does not dispatch to the directed dyadic rounders. It is the
general implementation used for policies outside the directed dispatch. It is compared
independently with `roundDyadicWithRounding` in `Rounding.Policy.Agreement`.
-/
def roundDyadicGeneral (fmt : FloatFormat) (policy : QuantizationPolicy) (entropy : Nat)
    (value : Numerics.Dyadic) : Model fmt :=
  match value.exponent with
  | .ofNat shift =>
      roundRatGeneralOfDenNeZero fmt policy entropy value.negative
        (Nat.shiftLeft value.significand shift) 1 (by decide)
  | .negSucc shift =>
      roundRatGeneralOfDenNeZero fmt policy entropy value.negative value.significand
        (Nat.shiftLeft 1 (shift + 1)) (by simp)

/--
Round an exact signed dyadic into a policy-aware format.

IEEE directions with native overflow and gradual underflow use the dedicated directed dyadic
rounders. Other policies use `roundDyadicGeneral`, including nearest-away, stochastic, saturating,
and flush-to-zero policies.
-/
@[inline] def roundDyadic (fmt : FloatFormat) (policy : QuantizationPolicy) (entropy : Nat)
    (value : Numerics.Dyadic) : Model fmt :=
  match policyIEEERoundingMode? policy with
  | some mode => roundDyadicWithRounding fmt mode value
  | none => roundDyadicGeneral fmt policy entropy value

/-- Quantize a finite source value. NaN and infinity require an explicit cast policy. -/
def castFinite? (src dst : FloatFormat) (policy : QuantizationPolicy) (entropy : Nat)
    (x : Model src) : Option (Model dst) :=
  (Model.toDyadic? x).map (roundDyadic dst policy entropy)

end Policy

end FloatLib.Floats.Formats.BinaryInterchange.Model
