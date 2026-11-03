/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Model.ExactNumericalSystem
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Status.Runtime
public import FloatLib.Floats.ExecFloat.Conversion.Core
public import FloatLib.Numerics.Exact.SignedRat

/-!
# Binary-interchange conversion runtime

Every binary-interchange family uses the same representation-independent conversion policy.
A concrete carrier supplies only a `pack` function from its `Model format`, so configured
machine-word formats and nominal static-byte formats share one exact quantizer.

The exact domain is `SignedRat`, so the sign of a zero input reaches the destination. Finite values
are rounded once by `Model.Policy.roundRat`, with the sign bit taken from the signed rational and
the magnitude from its value. Infinity and exceptional observations have their own policies
because finite-only formats cannot preserve every IEEE value class. Status flags are computed from
exact rational comparisons, never through a host floating-point value.

A binary `Model` value is a conversion source as well. `modelDecoder` decodes it into `SignedRat`
the way the configured and static-byte carriers decode their stored model, so it keeps a negative
zero and a NaN's sign, payload, and signaling class.

`specWith pack` is the graph of `runWith pack` (`specWith_iff_eq_runWith`) together with a
nearest-value clause for nearest-even/native-overflow/gradual-underflow conversion to conventional
IEEE descriptors. The clause is stated without the runtime, and its proof uses the descriptor's
real rounding semantics. It constrains only a delivered model with a finite rational denotation;
`runWith_nearest_of_abs_le_posMaxFinite` shows that the result is finite whenever the exact
magnitude is at most the largest finite value. Overflow beyond that magnitude, tie selection,
signed zero, status, and the other policies are fixed only by the equation with `runWith`.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics
open FloatLib.Floats.Formats.BinaryInterchange

namespace ExecFloat.Binary
namespace Conversion

universe u

/--
Binary models decode into `SignedRat`, like every configured and static-byte binary carrier.

A negative zero decodes to `SignedRat.negZero`, an infinity keeps its sign, and a NaN carries its
diagnostic payload, sign bit, and signaling class, so converting a `Model` value, or using one as a
mixed-arithmetic operand, behaves like converting the configured value that stores it.
-/
instance modelDecoder (format : FloatFormat) :
    FloatLib.Floats.ExecFloat.ExactDecoder (Model format) SignedRat where
  decode value := ((Model.exactNumericalSystem format).denote value).map SignedRat.ofDyadic

/-- Policy for an infinity presented to a binary-interchange destination. -/
inductive InfinityPolicy where
  /-- Preserve infinity when the destination encoding supports it, and otherwise reject the cast. -/
  | preserve
  /-- Clamp infinity to the finite destination value of greatest magnitude with the same sign. -/
  | saturate
  /-- Reject infinity even when the destination could represent it. -/
  | reject
  deriving DecidableEq, Repr

/-- Policy for NaN, NaR, reserved, or undefined observations. -/
inductive ExceptionalPolicy where
  /--
  Propagate a source NaN as `Model.propagatedNaN` does in `Model.cast`. IEEE destinations keep the
  sign, set the quiet bit, and preserve a payload that fits, otherwise using payload zero.
  Other encodings follow their own NaN rule. Other exceptional observations become the
  destination's canonical NaN. This is the default.
  -/
  | propagateNaN
  /-- Produce the destination's canonical NaN for every exceptional observation. -/
  | canonicalNaN
  /-- Reject every exceptional observation. -/
  | reject
  deriving DecidableEq, Repr

/--
Complete context of the binary-interchange quantizer `run`: a finite rounding direction together
with every other conversion policy.

The conversion entry points, such as `ExecFloat.convert`, `cast`, and the mixed operations, do not
take a `Context`. They take the direction as their `mode` and the other policies as a `Policy`,
and run in `policy.withRounding mode`.
-/
structure Context where
  /-- Finite rounding, overflow, and underflow behavior. -/
  quantization : QuantizationPolicy := .nearest
  /-- Entropy consumed only by stochastic finite rounding. -/
  entropy : Nat := 0
  /-- Treatment of source infinity. -/
  infinity : InfinityPolicy := .preserve
  /-- Treatment of source exceptional values. -/
  exceptional : ExceptionalPolicy := .propagateNaN
  deriving DecidableEq, Repr

/--
Canonical binary conversion context.

Finite values use nearest-even/native-overflow/gradual-underflow behavior. Infinities and
exceptional values keep their value class when the destination encoding supports that class, and
otherwise conversion fails. An IEEE destination quiets a NaN, keeps its sign and any
payload that fits, and replaces an oversized payload with zero. Maximum-NaN encodings keep only
the sign, while FNUZ has a single NaN. A signaling NaN raises `invalid`.
-/
def Context.default : Context := {}

/--
The policies of a conversion into a binary-interchange destination other than its rounding
direction: the type of the `(context := ...)` option of `ExecFloat.convert`, `cast`, and the mixed
operations.

The direction is the conversion's `mode`, and a policy has no field for one, so the two options
cannot disagree. Stochastic rounding is `(mode := .stochastic) (context := { entropy := e })`, and
a saturating downward conversion is `(mode := .down) (context := { overflow := .saturate })`.
`withRounding` adds the direction and gives the complete `Context` that `run` takes.
-/
structure Policy where
  /-- Rule used when the exact magnitude exceeds the finite range. -/
  overflow : OverflowMode := .native
  /-- Rule used for nonzero results below the normal range. -/
  underflow : UnderflowMode := .gradual
  /-- Entropy consumed only by stochastic finite rounding. -/
  entropy : Nat := 0
  /-- Treatment of source infinity. -/
  infinity : InfinityPolicy := .preserve
  /-- Treatment of source exceptional values. -/
  exceptional : ExceptionalPolicy := .propagateNaN
  deriving DecidableEq, Repr

/--
Canonical binary conversion policy, used by a conversion that names no `context`: native overflow,
gradual underflow, and the infinity and NaN behavior of `Context.default`.
-/
def Policy.default : Policy := {}

/--
The complete context that rounds in direction `rounding` and applies `policy`'s overflow,
underflow, entropy, infinity, and NaN policies.

A conversion with `(mode := m) (context := p)` runs in `p.withRounding m`, and
`Policy.default.withRounding .nearest` is `Context.default`.
-/
@[inline] def Policy.withRounding (policy : Policy) (rounding : RoundingMode) : Context where
  quantization := { rounding, overflow := policy.overflow, underflow := policy.underflow }
  entropy := policy.entropy
  infinity := policy.infinity
  exceptional := policy.exceptional

/-- Exact addition with the destination's cancellation-sign rule, before rounding. -/
@[inline] def addExact (context : Context) (left right : SignedRat) : SignedRat :=
  SignedRat.addWithCancellationSign (context.quantization.rounding == .down) left right

/-- Exact subtraction applies the same cancellation rule to the negated right operand. -/
@[inline] def subExact (context : Context) (left right : SignedRat) : SignedRat :=
  addExact context left (-right)

/--
Overflow and tininess of the exact magnitude `numerator / denominator` from its significand rounded
under `rounding` with an unbounded exponent range, as a pair `(overflow, tiny)`.

The denominator must be nonzero, as it is for every `Rat`. A zero numerator gives
`(false, false)`: an exact zero neither overflows nor underflows. Otherwise the significand is the
quotient scaled to `fracWidth + 1` significant bits and rounded by `Model.Policy.roundQuot`, with
`sign` and `entropy` for the directions and stochastic rounding that need them. It overflows above
the largest finite significand of the top binade. Below the normal range it is tiny unless
rounding carries it up to the smallest normal value. `finiteStatus` uses this calculation for
rounding modes without an `IEEERoundingMode` direction.
-/
@[inline] def roundedSignificandStatus (format : FloatFormat) (rounding : RoundingMode)
    (entropy : Nat) (sign : Bool) (numerator denominator : Nat) : Bool × Bool :=
  if numerator == 0 then
    (false, false)
  else
    let exponent := Numerics.RationalBinary.floorLog2 numerator denominator
    let (scaledNum, scaledDen) := Numerics.RationalBinary.scaleByPowerOfTwo
      numerator denominator (Int.ofNat format.fracWidth - exponent)
    let mantissa := Model.Policy.roundQuot rounding sign entropy scaledNum scaledDen
    let overflow := exponent > format.maxNormalExponent ||
      (exponent == format.maxNormalExponent &&
        mantissa > (Model.maxFiniteDyadic format).significand)
    let tiny := exponent < format.minNormalExponent &&
      (exponent + 1 < format.minNormalExponent ||
        mantissa < 2 ^ (format.fracWidth + 1))
    (overflow, tiny)

/--
Status derived from exact rational binary rounding.

Overflow and tininess use the precision-rounded value with an unbounded exponent range. Merely
exceeding the largest finite value does not signal overflow when rounding brings the value back
into range. Rounding modes with an `IEEERoundingMode` direction use the exact classifiers
`rationalRoundingOverflows` and `rationalIsTinyAfterRoundingScaled`. Stochastic policies use
`roundedSignificandStatus`, with their own integer rounding rule and the supplied entropy, at the
same precision boundary.

`rounded` must be the value that `Model.Policy.roundRat` delivers for `exact` under `context`, as in
`quantizeFiniteWith`. The flags read it, and the direction classifiers count a delivered zero or
subnormal as tiny, so a status computed for an unrelated pair has no meaning.
-/
@[inline] def finiteStatus {format : FloatFormat}
    (context : Context) (exact : Rat) (rounded : Model format) :
    FloatLib.Floats.ExecFloat.ConversionStatus :=
  let numerator := exact.num.natAbs
  let denominator := exact.den
  let sign := exact < 0
  let (overflow, tiny) :=
    match Model.Policy.ieeeRoundingMode? context.quantization.rounding with
    | some mode =>
        (Model.rationalRoundingOverflows format mode sign numerator denominator,
          Model.rationalIsTinyAfterRoundingScaled format mode sign
            numerator denominator 0 rounded)
    | none =>
        roundedSignificandStatus format context.quantization.rounding context.entropy sign
          numerator denominator
  let inexact := Model.toRat? rounded != some exact
  { inexact
    overflow
    underflow := (tiny || (context.quantization.underflow == .flushToZero &&
      Model.isTinyAfterRounding rounded)) && inexact
    saturated := overflow && context.quantization.overflow == .saturate }

/--
Round one finite signed rational and pack the resulting binary model into a destination carrier.

The sign bit of the result comes from `exact.negative`, so a negative zero rounds to the
destination's negative zero when the encoding has one. `pack` is the only representation-specific
argument. It is applied after exact rounding, so changing storage or an execution backend cannot
change numerical meaning.
-/
@[inline] def quantizeFiniteWith {format : FloatFormat} {Destination : Type u}
    (pack : Model format → Destination) (context : Context) (exact : SignedRat) :
    FloatLib.Floats.ExecFloat.ConversionOutcome Destination :=
  match Model.Policy.roundRat format context.quantization context.entropy
      exact.negative exact.value.num.natAbs exact.value.den with
  | some rounded =>
      .success (pack rounded) (finiteStatus context exact.value rounded)
  | none =>
      .failure .unsupportedPolicy

/--
Apply the exceptional-value policy and pack a destination NaN.

A signaling NaN raises `invalid` under either NaN-producing policy (IEEE 754-2019 §7.2). Under
`propagateNaN` a source NaN becomes `Model.propagatedNaN format negative payload`, with the payload
supplied by the source decoder without encoding markers. Binary decoders use `Model.nanPayload`,
so this is the NaN that `Model.cast` delivers across unequal descriptors. It stays in the NaN
class, so `mappedSpecial` is clear. NaR, reserved, and undefined observations, and every
observation under `canonicalNaN`, become the canonical NaN with `mappedSpecial`. A destination
without a NaN encoding rejects the conversion.
-/
@[inline] def quantizeExceptionalWith {format : FloatFormat} {Destination : Type u}
    (pack : Model format → Destination) (context : Context)
    (exceptional : ExceptionalValue) :
    FloatLib.Floats.ExecFloat.ConversionOutcome Destination :=
  match context.exceptional with
  | .reject =>
      .failure (.exceptional .source exceptional)
  | .propagateNaN =>
      match Model.canonicalNaN? format, exceptional with
      | none, _ =>
          .failure (.exceptional .source exceptional)
      | some _, .nan payload negative signaling =>
          .success
            (pack (Model.propagatedNaN format negative (payload.getD 0)))
            { invalid := signaling }
      | some value, _ =>
          .success (pack value) { mappedSpecial := true }
  | .canonicalNaN =>
      match Model.canonicalNaN? format with
      | some value =>
          .success (pack value)
            { mappedSpecial := true, invalid := exceptional.isSNaN }
      | none =>
          .failure (.exceptional .source exceptional)

/-- Apply the infinity policy and pack the selected binary model value. -/
@[inline] def quantizeInfinityWith {format : FloatFormat} {Destination : Type u}
    (pack : Model format → Destination) (context : Context) (negative : Bool) :
    FloatLib.Floats.ExecFloat.ConversionOutcome Destination :=
  match context.infinity with
  | .reject =>
      .failure (.infinity .source negative)
  | .saturate =>
      .success (pack (Model.maxFinite format negative))
        { inexact := true
          overflow := true
          saturated := true
          mappedSpecial := true }
  | .preserve =>
      match Model.infinity? format negative with
      | some value => .success (pack value)
      | none => .failure (.infinity .source negative)

/-- Reference conversion shared by every carrier for the same binary descriptor. -/
@[inline] def runWith {format : FloatFormat} {Destination : Type u}
    (pack : Model format → Destination) (context : Context) :
    NumericalValue SignedRat → FloatLib.Floats.ExecFloat.ConversionOutcome Destination
  | .finite exact => quantizeFiniteWith pack context exact
  | .infinity negative => quantizeInfinityWith pack context negative
  | .exceptional exceptional => quantizeExceptionalWith pack context exceptional

/-- A finite rounded denotation is no farther from the input than any finite destination value. -/
def NearestFinite {format : FloatFormat} (exact : Rat) (rounded : Model format) : Prop :=
  ∀ value, Model.toRat? rounded = some value →
    ∀ candidate : Model format, ∀ candidateValue, Model.toRat? candidate = some candidateValue →
      |value - exact| ≤ |candidateValue - exact|

/--
Complete conversion outcome, together with a runtime-free nearest-value clause for IEEE defaults.

The first conjunct makes `specWith` the graph of `runWith` (`specWith_iff_eq_runWith`), so the
clause adds no constraint of its own; its value is that `NearestFinite` is stated without the
runtime and proved through real rounding in `Conversion.Proof`. The clause says nothing about a
nonfinite result, which `runWith_nearest_of_abs_le_posMaxFinite` excludes up to the largest finite
magnitude. The real value of a finite result is also nearest-even rounding
(`Model.toReal_roundRatScaled_eq_roundAt`), which settles ties, but the clause records only
nearness. Overflow beyond the largest finite magnitude, zero signs, all status fields, and every
nondefault policy are fixed only by the equation with `runWith`.
-/
def specWith {format : FloatFormat} {Destination : Type u}
    (pack : Model format → Destination) :
    Quantization.Spec Context (NumericalValue SignedRat)
      (FloatLib.Floats.ExecFloat.ConversionOutcome Destination) :=
  fun context input outcome =>
    outcome = runWith pack context input ∧
      match input with
      | .finite exact =>
          context.quantization = QuantizationPolicy.nearest → format.isIEEE = true →
            ∃ rounded : Model format,
              outcome = .success (pack rounded) (finiteStatus context exact.value rounded) ∧
                NearestFinite exact.value rounded
      | .infinity _ => True
      | .exceptional _ => True

end Conversion
end ExecFloat.Binary
end FloatLib.Floats
