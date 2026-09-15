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

The ten explicit-direction operations share the exact coefficient rounder used
by decimal integral rounding. No intervening decimal precision rounding occurs.
The `Exact` variants signal inexact only on successful conversion. Every NaN,
infinity, or rounded integer outside the destination range instead raises invalid.
This binding documents integer zero as its default invalid delivery and reports
invalid explicitly in the result status.

Signed destinations use the existing two's-complement `FixedInt` bounds.
Unsigned destinations use the range of `BitVec`. Width zero denotes only zero
in both cases. Integer sources have no signed zero and therefore convert to +0.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Conversion.Integer

open FloatLib.Numerics FloatLib.Numerics.Representations

/-- Signedness and width are independent of the decimal source format. -/
abbrev IntegerFormat := FloatLib.Numerics.IntegerFormat

/-- An integer result and the flags raised by this conversion alone. -/
structure IntegerOutcome where
  /-- The rounded integer when valid, or zero for this binding's invalid delivery. -/
  value : Int
  /-- Flags raised by this operation alone; successful exact variants may raise inexact. -/
  status : Status := {}
  deriving DecidableEq, Repr

/-- Round an exact rational once to the integer grid, with sign-sensitive directed rounding. -/
def roundInteger (mode : RoundingMode) (value : ℚ) : Int :=
  let negative := decide (value < 0)
  let magnitude := (mode.roundMagnitude negative |value| : Int)
  if negative then -magnitude else magnitude

/-- This binding's invalid integer result is zero, with only the invalid flag set. -/
def invalidOutcome : IntegerOutcome :=
  { value := 0, status := { invalid := true } }

/-- Shared conversion kernel. `signalInexact` selects exact versus quiet conversion;
it does not change the rounding direction or the delivered integer. -/
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

/-- Nearest integer, ties to even; suppress inexact, but report invalid conversion. -/
abbrev convertToIntegerTiesToEven (destination : IntegerFormat) :
    Datum → IntegerOutcome :=
  convertToInteger destination .nearestEven false

/-- Nearest integer, ties away from zero; suppress inexact, but report invalid conversion. -/
abbrev convertToIntegerTiesToAway (destination : IntegerFormat) :
    Datum → IntegerOutcome :=
  convertToInteger destination .nearestAway false

/-- Round toward zero; suppress inexact, but report invalid conversion. -/
abbrev convertToIntegerTowardZero (destination : IntegerFormat) :
    Datum → IntegerOutcome :=
  convertToInteger destination .towardZero false

/-- Round toward positive infinity; suppress inexact, but report invalid conversion. -/
abbrev convertToIntegerTowardPositive (destination : IntegerFormat) :
    Datum → IntegerOutcome :=
  convertToInteger destination .towardPositive false

/-- Round toward negative infinity; suppress inexact, but report invalid conversion. -/
abbrev convertToIntegerTowardNegative (destination : IntegerFormat) :
    Datum → IntegerOutcome :=
  convertToInteger destination .towardNegative false

/-- Nearest integer, ties to even; report inexact precisely when a valid result changes value. -/
abbrev convertToIntegerExactTiesToEven (destination : IntegerFormat) :
    Datum → IntegerOutcome :=
  convertToInteger destination .nearestEven true

/-- Nearest integer, ties away from zero; report inexact on a valid numerical change. -/
abbrev convertToIntegerExactTiesToAway (destination : IntegerFormat) :
    Datum → IntegerOutcome :=
  convertToInteger destination .nearestAway true

/-- Round toward zero; report inexact on a valid numerical change. -/
abbrev convertToIntegerExactTowardZero (destination : IntegerFormat) :
    Datum → IntegerOutcome :=
  convertToInteger destination .towardZero true

/-- Round toward positive infinity; report inexact on a valid numerical change. -/
abbrev convertToIntegerExactTowardPositive (destination : IntegerFormat) :
    Datum → IntegerOutcome :=
  convertToInteger destination .towardPositive true

/-- Round toward negative infinity; report inexact on a valid numerical change. -/
abbrev convertToIntegerExactTowardNegative (destination : IntegerFormat) :
    Datum → IntegerOutcome :=
  convertToInteger destination .towardNegative true

/-- Convert an arbitrary signed integer directly to a decimal destination, with preferred
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

/-- Pack a signed conversion into the existing fixed-width carrier, retaining its status.
The conversion has already checked the range; packing does not implement wraparound conversion. -/
def convertToFixedInt (width : Nat) (mode : RoundingMode) (signalInexact : Bool)
    (source : Datum) : FixedInt width × Status :=
  let result := convertToInteger (.signed width) mode signalInexact source
  (FixedInt.ofInt result.value, result.status)

/-- Pack an unsigned conversion after its range check. -/
def convertToUnsigned (width : Nat) (mode : RoundingMode) (signalInexact : Bool)
    (source : Datum) : BitVec width × Status :=
  let result := convertToInteger (.unsigned width) mode signalInexact source
  (BitVec.ofNat width result.value.toNat, result.status)

end FloatLib.Floats.Formats.DecimalInterchange.Conversion.Integer
