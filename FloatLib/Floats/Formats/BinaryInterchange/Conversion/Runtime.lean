/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Status.Runtime
public import FloatLib.Floats.ExecFloat.Conversion.Core
public import FloatLib.Numerics.Exact.SignedRat

/-!
# Binary-interchange conversion runtime

Every binary-interchange family uses the same representation-independent conversion policy.
A concrete carrier supplies only a `pack` function from its
`Model format`; configured machine-word formats and nominal static-byte formats therefore share
one exact quantizer.

The exact domain is `SignedRat`, so the sign of a zero input reaches the destination. Finite values
are rounded once by `Model.Policy.roundRat`, with the sign bit taken from the signed rational and
the magnitude from its value. Infinity and exceptional observations use separate explicit policies
because finite-only formats cannot preserve every IEEE value class. Status flags are computed from
exact rational comparisons, never through a host floating-point value.

`specWith pack` preserves the complete executable outcome and adds an independent nearest-value
predicate for nearest-even/native-overflow/gradual-underflow conversion to conventional IEEE
descriptors. Its proof uses the descriptor's real rounding semantics. The nearest-value clause
applies when the delivered model has a finite rational denotation; overflow, tie selection, signed
zero, status, and the other policies retain the complete executable-outcome clause.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics
open FloatLib.Floats.Formats.BinaryInterchange

namespace ExecFloat.Binary
namespace Conversion

universe u

/-- Policy for an infinity presented to a binary-interchange destination. -/
inductive InfinityPolicy where
  /-- Preserve infinity when the destination encoding supports it; otherwise reject the cast. -/
  | preserve
  /-- Clamp infinity to the finite destination value of greatest magnitude with the same sign. -/
  | saturate
  /-- Reject infinity even when the destination could represent it. -/
  | reject
  deriving DecidableEq, Repr

/-- Policy for NaN, NaR, reserved, or undefined observations. -/
inductive ExceptionalPolicy where
  /-- Produce the destination's canonical NaN when one exists. -/
  | canonicalNaN
  /-- Reject every exceptional observation. -/
  | reject
  deriving DecidableEq, Repr

/-- Complete explicit context for conversion into a binary-interchange destination. -/
structure Context where
  /-- Finite rounding, overflow, and underflow behavior. -/
  quantization : QuantizationPolicy := .nearestEven
  /-- Entropy consumed only by stochastic finite rounding. -/
  entropy : Nat := 0
  /-- Treatment of source infinity. -/
  infinity : InfinityPolicy := .preserve
  /-- Treatment of source exceptional values. -/
  exceptional : ExceptionalPolicy := .canonicalNaN
  deriving DecidableEq, Repr

/--
Canonical binary conversion context.

Finite values use nearest-even/native-overflow/gradual-underflow behavior. Infinities and
exceptional values retain their value class when the destination encoding supports that class;
otherwise conversion fails explicitly.
-/
def Context.default : Context := {}

namespace Context

/--
Canonical conversion context with one caller-selected finite rounding direction.

Native overflow, gradual underflow, infinity preservation, and canonical-NaN mapping retain their
default behavior. Use a record update when any of those policies must also change.
-/
@[inline] def withRounding (rounding : RoundingMode) : Context :=
  { quantization := { rounding } }

end Context

/-- Exact addition with the destination's cancellation-sign rule, before rounding. -/
@[inline] def addExact (context : Context) (left right : SignedRat) : SignedRat :=
  SignedRat.addWithCancellationSign (context.quantization.rounding == .towardNegative) left right

/-- Exact subtraction applies the same cancellation rule to the negated right operand. -/
@[inline] def subExact (context : Context) (left right : SignedRat) : SignedRat :=
  addExact context left (-right)

/--
Status derived from exact rational binary rounding.

Overflow and tininess use the precision-rounded value with an unbounded exponent range. Merely
exceeding the largest finite value does not signal overflow when rounding brings the value back
into range. Nearest-away and stochastic policies use their own integer rounding rule, including
the supplied entropy, at the same precision boundary.
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
        if numerator == 0 then
          (false, false)
        else
          let exponent := Numerics.RationalBinary.floorLog2 numerator denominator
          let (scaledNum, scaledDen) := Numerics.RationalBinary.scaleByPowerOfTwo
            numerator denominator (Int.ofNat format.fracWidth - exponent)
          let mantissa := Model.Policy.roundQuot context.quantization.rounding
            sign context.entropy scaledNum scaledDen
          let overflow := exponent > format.maxNormalExponent ||
            (exponent == format.maxNormalExponent &&
              mantissa > (Model.maxFiniteDyadic format).significand)
          let tiny := exponent < format.minNormalExponent &&
            (exponent + 1 < format.minNormalExponent ||
              mantissa < 2 ^ (format.fracWidth + 1))
          (overflow, tiny)
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
argument. It is deliberately applied after exact rounding, so changing storage or an execution
backend cannot change numerical meaning.
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

/-- Apply the exceptional-value policy and pack a supported canonical NaN. -/
@[inline] def quantizeExceptionalWith {format : FloatFormat} {Destination : Type u}
    (pack : Model format → Destination) (context : Context)
    (exceptional : ExceptionalValue) :
    FloatLib.Floats.ExecFloat.ConversionOutcome Destination :=
  match context.exceptional with
  | .reject =>
      .failure (.exceptional .source exceptional)
  | .canonicalNaN =>
      match Model.canonicalNaN? format with
      | some value =>
          .success (pack value) { mappedSpecial := true }
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
Complete conversion outcome, together with an independent nearest-value clause for IEEE defaults.

The rational predicate is runtime-free: its proof uses real rounding only in `Conversion.Proof`.
Complete outcome equality additionally preserves overflow, tie selection, zero signs, all status
fields, and every nondefault policy. A nonfinite result has no nearest finite denotation.
-/
def specWith {format : FloatFormat} {Destination : Type u}
    (pack : Model format → Destination) :
    Quantization.Spec Context (NumericalValue SignedRat)
      (FloatLib.Floats.ExecFloat.ConversionOutcome Destination) :=
  fun context input outcome =>
    outcome = runWith pack context input ∧
      match input with
      | .finite exact =>
          context.quantization = QuantizationPolicy.nearestEven → format.isIEEE = true →
            ∃ rounded : Model format,
              outcome = .success (pack rounded) (finiteStatus context exact.value rounded) ∧
                NearestFinite exact.value rounded
      | .infinity _ => True
      | .exceptional _ => True

end Conversion
end ExecFloat.Binary
end FloatLib.Floats
