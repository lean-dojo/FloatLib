/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.Constants
public import FloatLib.Floats.Formats.Posit.Configured.Value.Runtime
public import FloatLib.Floats.Formats.Posit.Rounding.Runtime
public import FloatLib.Floats.ExecFloat.Conversion.Core

/-!
# Configured posit conversion runtime

Every configured posit uses `Rat` as its executable exact domain. Finite conversion follows the
Posit Standard (2022) directly: interior values use the appended-bit boundary, nonzero values
below `minPos` select signed `minPos`, and values above `maxPos` select signed `maxPos`.

The default context maps infinity and exceptional observations to the unique `NaR`. For IEEE
infinities and NaNs this follows §6.5 of the Posit Standard (2022); both IEEE signed zeros become
posit zero.
Callers may explicitly reject infinity or exceptional observations, or saturate infinity to signed
`maxPos`.

The mathematical conversion relation is declared in `Conversion.Proof`, where the real rounding
specification and its rational bridge are available without adding them to runtime imports.

## References

* [Posit Standard (2022)](https://posithub.org/docs/posit_standard-2.pdf), §6.5.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics
open FloatLib.Floats.Formats.Posit

namespace ExecFloat.Posit
namespace Conversion

/-- Policy for source infinity presented to a posit destination. -/
inductive InfinityPolicy where
  /-- Reject infinity because the posit scalar domain has no infinite point. -/
  | reject
  /-- Map infinity to the unique posit `NaR`. -/
  | toNaR
  /-- Clamp infinity to signed `maxPos`. -/
  | saturate
  deriving DecidableEq, Repr

/-- Policy for NaN, NaR, reserved, or undefined observations. -/
inductive ExceptionalPolicy where
  /-- Reject the observation. -/
  | reject
  /-- Map the observation to the unique posit `NaR`. -/
  | toNaR
  deriving DecidableEq, Repr

/-- Posit conversion policies, defaulting to the Posit Standard (2022) special-value mapping. -/
structure Context where
  /-- Source infinity maps to `NaR` by default, as required by §6.5. -/
  infinity : InfinityPolicy := .toNaR
  /-- Source exceptional observations map to `NaR` by default, including IEEE NaNs (§6.5). -/
  exceptional : ExceptionalPolicy := .toNaR
  deriving DecidableEq, Repr

/-- Map source infinity and exceptional observations to `NaR` (Posit Standard (2022), §6.5). -/
def Context.default : Context := {}

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

/-- Exact magnitude of the largest positive finite posit. -/
@[inline] def maxPositiveRat (format : Format) : Rat :=
  Model.nonnegativeRatAt format (format.signMaskNat - 1)

/-- Conversion status computed by exact rational comparison with the posit endpoints. -/
@[inline] def finiteStatus (exact : Rat) (rounded : Model format) :
    FloatLib.Floats.ExecFloat.ConversionStatus :=
  let magnitude := if exact < 0 then -exact else exact
  let overflow := decide (maxPositiveRat format < magnitude)
  let underflow :=
    exact != 0 && decide (magnitude < Model.minPositiveRat format)
  { inexact := Model.toRat? rounded != some exact
    overflow
    underflow
    saturated := overflow }

/-- Quantize a finite rational by the exact arbitrary-width posit reference rounder. -/
@[inline] def quantizeFinite (exact : Rat) :
    FloatLib.Floats.ExecFloat.ConversionOutcome
      (FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :=
  let rounded := Model.roundRat format exact
  .success (ExecFloat.Posit.ofModel rounded) (finiteStatus exact rounded)

/-- Explicitly handle source infinity. -/
@[inline] def quantizeInfinity (context : Context) (negative : Bool) :
    FloatLib.Floats.ExecFloat.ConversionOutcome
      (FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :=
  match context.infinity with
  | .reject =>
      .failure (.infinity .source negative)
  | .toNaR =>
      .success (ExecFloat.Posit.nar) { mappedSpecial := true }
  | .saturate =>
      let magnitude := Model.roundRat format (maxPositiveRat format)
      let rounded := if negative then Model.neg magnitude else magnitude
      .success (ExecFloat.Posit.ofModel rounded)
        { inexact := true
          overflow := true
          saturated := true
          mappedSpecial := true }

/-- Explicitly handle a source exceptional observation. -/
@[inline] def quantizeExceptional (context : Context) (exceptional : ExceptionalValue) :
    FloatLib.Floats.ExecFloat.ConversionOutcome
      (FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :=
  match context.exceptional with
  | .reject =>
      .failure (.exceptional .source exceptional)
  | .toNaR =>
      .success (ExecFloat.Posit.nar) { mappedSpecial := true }

/-- Reference conversion for every exact-rational observation. -/
@[inline] def run (context : Context) :
    NumericalValue Rat →
      FloatLib.Floats.ExecFloat.ConversionOutcome
        (FloatLib.Floats.ExecFloat (Configured.Family format code plan))
  | .finite exact => quantizeFinite exact
  | .infinity negative => quantizeInfinity context negative
  | .exceptional exceptional => quantizeExceptional context exceptional

/-- Configured posit decoding selects the exact-rational conversion domain. -/
instance exactDecoder :
    FloatLib.Floats.ExecFloat.ExactDecoder
      (FloatLib.Floats.ExecFloat (Configured.Family format code plan)) Rat where
  decode := ExecFloat.Posit.decode

end Conversion
end ExecFloat.Posit
end FloatLib.Floats
