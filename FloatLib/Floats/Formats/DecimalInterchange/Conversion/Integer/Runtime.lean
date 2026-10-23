/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Runtime
public import FloatLib.Numerics.Quantization.Integer.Runtime

/-!
# Decimal conversions to and from integers

IEEE 754-2019 §§5.4.1, 5.8 and 7.2(j) require rounding to an integer before
checking its destination range. In particular, a negative fraction can convert
to unsigned zero, and a value just outside an endpoint can round into range.

The ten operations, one per direction and exactness, share the exact coefficient
rounder used by decimal integral rounding. No intervening decimal precision rounding
occurs. The `Exact` variants signal inexact only on successful conversion. Every NaN,
infinity, or rounded integer outside the destination range raises invalid instead,
and the invalid result is integer zero.

Signed destinations use the two's-complement `FixedInt` bounds.
Unsigned destinations use the range of `BitVec`. Width zero denotes only zero
in both cases. Integer sources have no signed zero and therefore convert to +0.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Conversion.Integer

open FloatLib.Numerics FloatLib.Numerics.Representations

/-- Integer destination format, whose signedness and width do not depend on the decimal source. -/
abbrev IntegerFormat := FloatLib.Numerics.IntegerFormat

/-- An integer result and the flags raised by this conversion alone. -/
structure IntegerOutcome where
  /-- The rounded integer when valid, or zero when the conversion is invalid. -/
  value : Int
  /-- Flags raised by this operation alone. A successful `Exact` variant may raise inexact. -/
  status : Numerics.IEEEStatus := {}
  deriving DecidableEq, Repr

/-- Round an exact rational once to the integer grid, with sign-sensitive directed rounding. -/
def roundInteger (mode : RoundingMode) (value : ℚ) : Int :=
  let negative := decide (value < 0)
  let magnitude := (mode.roundMagnitude negative |value| : Int)
  if negative then -magnitude else magnitude

/-- Invalid result: integer zero with only the invalid flag set. -/
def invalidOutcome : IntegerOutcome :=
  { value := 0, status := { invalid := true } }

/-- Shared conversion kernel. `signalInexact` selects exact or quiet conversion and changes
neither the rounding direction nor the delivered integer. -/
def convertToInteger (destination : IntegerFormat) (mode : RoundingMode)
    (signalInexact : Bool) (source : Datum) : IntegerOutcome :=
  match source.toRat? with
  | none => invalidOutcome
  | some value =>
      match destination.range.round? (roundInteger mode) value with
      | some rounded =>
        { value := rounded
          status := { inexact := signalInexact && decide ((rounded : ℚ) ≠ value) } }
      | none => invalidOutcome

/--
Convert to the nearest integer, ties to even. Never raises inexact, and raises invalid only for a
nonfinite input or a rounded result outside the destination range.
-/
abbrev convertToIntegerTiesToEven (destination : IntegerFormat) :
    Datum → IntegerOutcome :=
  convertToInteger destination .nearestEven false

/--
Convert to the nearest integer, ties away from zero. Never raises inexact, and raises invalid only
for a nonfinite input or a rounded result outside the destination range.
-/
abbrev convertToIntegerTiesToAway (destination : IntegerFormat) :
    Datum → IntegerOutcome :=
  convertToInteger destination .nearestAway false

/--
Convert toward zero. Never raises inexact, and raises invalid only for a nonfinite input
or a rounded result outside the destination range.
-/
abbrev convertToIntegerTowardZero (destination : IntegerFormat) :
    Datum → IntegerOutcome :=
  convertToInteger destination .towardZero false

/--
Convert toward positive infinity. Never raises inexact, and raises invalid only for a nonfinite
input or a rounded result outside the destination range.
-/
abbrev convertToIntegerTowardPositive (destination : IntegerFormat) :
    Datum → IntegerOutcome :=
  convertToInteger destination .towardPositive false

/--
Convert toward negative infinity. Never raises inexact, and raises invalid only for a nonfinite
input or a rounded result outside the destination range.
-/
abbrev convertToIntegerTowardNegative (destination : IntegerFormat) :
    Datum → IntegerOutcome :=
  convertToInteger destination .towardNegative false

/-- Convert to the nearest integer, ties to even, raising inexact when a valid result changes. -/
abbrev convertToIntegerExactTiesToEven (destination : IntegerFormat) :
    Datum → IntegerOutcome :=
  convertToInteger destination .nearestEven true

/-- Convert to the nearest integer, ties away, raising inexact when a valid result changes. -/
abbrev convertToIntegerExactTiesToAway (destination : IntegerFormat) :
    Datum → IntegerOutcome :=
  convertToInteger destination .nearestAway true

/-- Convert toward zero, raising inexact when a valid result changes value. -/
abbrev convertToIntegerExactTowardZero (destination : IntegerFormat) :
    Datum → IntegerOutcome :=
  convertToInteger destination .towardZero true

/-- Convert toward positive infinity, raising inexact when a valid result changes value. -/
abbrev convertToIntegerExactTowardPositive (destination : IntegerFormat) :
    Datum → IntegerOutcome :=
  convertToInteger destination .towardPositive true

/-- Convert toward negative infinity, raising inexact when a valid result changes value. -/
abbrev convertToIntegerExactTowardNegative (destination : IntegerFormat) :
    Datum → IntegerOutcome :=
  convertToInteger destination .towardNegative true

/-- Convert an arbitrary signed integer to a decimal destination, with preferred
quantum zero and one destination rounding (§5.4.1). -/
def convertFromInt (destination : Format) (mode : RoundingMode) (source : Int) : Outcome :=
  project destination mode (source : ℚ) 0

/-- Convert a two's-complement source by its exact signed value. -/
def convertFromFixedInt (destination : Format) (mode : RoundingMode)
    {width : Nat} (source : FixedInt width) : Outcome :=
  convertFromInt destination mode source.toInt

/-- Convert an unsigned word by its exact nonnegative value. -/
def convertFromUnsigned (destination : Format) (mode : RoundingMode)
    {width : Nat} (source : BitVec width) : Outcome :=
  convertFromInt destination mode source.toNat

/-- Pack a signed conversion into the fixed-width carrier, keeping its status.
The conversion has already checked the range, so packing never wraps around. -/
def convertToFixedInt (width : Nat) (mode : RoundingMode) (signalInexact : Bool)
    (source : Datum) : FixedInt width × Numerics.IEEEStatus :=
  let result := convertToInteger (.signed width) mode signalInexact source
  (FixedInt.ofInt result.value, result.status)

/-- Pack an unsigned conversion after its range check. -/
def convertToUnsigned (width : Nat) (mode : RoundingMode) (signalInexact : Bool)
    (source : Datum) : BitVec width × Numerics.IEEEStatus :=
  let result := convertToInteger (.unsigned width) mode signalInexact source
  (BitVec.ofNat width result.value.toNat, result.status)

end FloatLib.Floats.Formats.DecimalInterchange.Conversion.Integer
