/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.Proof
public import FloatLibTests.Regression.BinaryInterchange.Harness

/-!
# Policy-aware `Model` examples

This file complements the general theorems with executable checks of the named low-precision
formats. It never converts through Lean's native `Float`: every expected value is either a raw bit
pattern or an exact `Numerics.Dyadic`.

`smallFormatRoundTripFailures` enumerates every bit pattern of E2M1, E2M3, E3M2, E4M3FN,
E4M3FNUZ, E5M2, and E5M2FNUZ. For each finite pattern it decodes the exact value and quantizes that
value back under nearest-even rounding. A zero count is a useful regression check but no
replacement for the encoding-independent theorems in
`FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.Agreement`.

The nearest-away checks compare the general policy engine with the dyadic rounder
`roundDyadicNearestAway`, which `Policy.roundDyadic` dispatches to through
`Internal.Directed.roundDyadic .nearestAway`, with the rational rounder
`roundRatNearestAwayScaled`, and with the classifier-built status of `finiteStatus_of_nearestAway`.
They cover normal and subnormal ties, half the least subnormal, the overflow midpoint, and every
small format exhaustively on a six-bit significand grid.

The golden patterns come from the OCP OFP8 and MX tables and the ONNX FNUZ description:

* <https://www.opencompute.org/documents/ocp-8-bit-floating-point-specification-ofp8-revision-1-0-2023-12-01-pdf-1>
* <https://www.opencompute.org/documents/ocp-microscaling-formats-mx-v1-0-spec-final-pdf>
* <https://onnx.ai/onnx/technical/float8.html>
-/

@[expose] public section

-- Keep lazy regression bodies out of module initialization, including closed subexpressions.
-- This affects native code generation only. Elaboration and kernel checking are unchanged.
set_option compiler.extract_closed false

namespace FloatLibTests.Regression.BinaryInterchange.PolicyRounding

open FloatLib

open FloatLib.Numerics
open FloatLib.Floats.Formats.BinaryInterchange
open Model
open FloatLibTests.Accounting
open FloatLibTests.Regression.BinaryInterchange.Harness

/-- Whether a quantized value has the expected raw bit pattern. -/
@[inline] def hasBits (fmt : FloatFormat) (x : Model fmt) (expected : Nat) : Bool :=
  Model.toNatBits x == expected

/--
Count finite encodings that do not survive exact decode followed by nearest-even quantization.

The function is intended for small formats: it enumerates all `2 ^ fmt.bitWidth` patterns.
-/
def finiteRoundTripFailures (fmt : FloatFormat) : Nat :=
  countWhereFailures (List.range (2 ^ fmt.bitWidth)) fun bits =>
    let x := Model.ofNatBits (fmt := fmt) bits
    match Model.toDyadic? x with
    | none => true
    | some exact =>
        let restored := Model.Policy.roundDyadic fmt QuantizationPolicy.nearest 0 exact
        restored == x

/-- Exhaustive round-trip checks for every named format of at most eight bits. -/
def smallFormatRoundTripFailures : Thunk Nat := ⟨fun _ =>
  finiteRoundTripFailures FloatFormat.e2m1 +
  finiteRoundTripFailures FloatFormat.e2m3 +
  finiteRoundTripFailures FloatFormat.e3m2 +
  finiteRoundTripFailures FloatFormat.e4m3fn +
  finiteRoundTripFailures FloatFormat.e4m3fnuz +
  finiteRoundTripFailures FloatFormat.e5m2 +
  finiteRoundTripFailures FloatFormat.e5m2fnuz⟩

/-! ## Published encodings and conversion policies -/

/-- Check the exceptional patterns and largest finite values stated in the format tables. -/
def formatTableFailures : Thunk Nat := ⟨fun _ =>
  let e4NaN := Model.ofNatBits (fmt := FloatFormat.e4m3fn) 0x7f
  let e4Max := Model.ofNatBits (fmt := FloatFormat.e4m3fn) 0x7e
  let e5Inf := Model.ofNatBits (fmt := FloatFormat.e5m2) 0x7c
  let e4uzNaN := Model.ofNatBits (fmt := FloatFormat.e4m3fnuz) 0x80
  let e4uzZero := Model.ofNatBits (fmt := FloatFormat.e4m3fnuz) 0x00
  let e2m1Max := Model.ofNatBits (fmt := FloatFormat.e2m1) 0x07
  failureCount (Model.isNaN e4NaN) +
  failureCount
    (Model.toDyadic? e4Max == some { negative := false, significand := 14, exponent := 5 }) +
  failureCount (Model.isInf e5Inf) +
  failureCount (Model.isNaN e4uzNaN) +
  failureCount (Model.isZero e4uzZero) +
  failureCount
    (Model.toDyadic? e2m1Max == some { negative := false, significand := 3, exponent := 1 })⟩

/--
Check saturation, native E4M3FN overflow, FNUZ zero canonicalization, and output FTZ.

E4M3FN represents `448` as `0x7e`, and its next pattern `0x7f` is NaN. So the same exact overflow
may become either `0x7e` or `0x7f`, depending on the operation's overflow policy.
-/
def policyFailures : Thunk Nat := ⟨fun _ =>
  let exact448 : Numerics.Dyadic := { negative := false, significand := 448, exponent := 0 }
  let exact500 : Numerics.Dyadic := { negative := false, significand := 500, exponent := 0 }
  let negativeZero : Numerics.Dyadic := { negative := true, significand := 0, exponent := 0 }
  let minSubnormal : Numerics.Dyadic :=
    { negative := false, significand := 1, exponent := FloatFormat.e4m3fn.minSubnormalExponent }
  let nativeMax := Model.Policy.roundDyadic FloatFormat.e4m3fn
    QuantizationPolicy.nearest 0 exact448
  let nativeOverflow := Model.Policy.roundDyadic FloatFormat.e4m3fn
    QuantizationPolicy.nearest 0 exact500
  let saturatedOverflow := Model.Policy.roundDyadic FloatFormat.e4m3fn
    QuantizationPolicy.saturating 0 exact500
  let fnuzZero := Model.Policy.roundDyadic FloatFormat.e4m3fnuz
    QuantizationPolicy.nearest 0 negativeZero
  let gradual := Model.Policy.roundDyadic FloatFormat.e4m3fn
    QuantizationPolicy.nearest 0 minSubnormal
  let flushed := Model.Policy.roundDyadic FloatFormat.e4m3fn
    QuantizationPolicy.flushToZero 0 minSubnormal
  failureCount (hasBits FloatFormat.e4m3fn nativeMax 0x7e) +
  failureCount (hasBits FloatFormat.e4m3fn nativeOverflow 0x7f) +
  failureCount (hasBits FloatFormat.e4m3fn saturatedOverflow 0x7e) +
  failureCount (hasBits FloatFormat.e4m3fnuz fnuzZero 0x00) +
  failureCount (hasBits FloatFormat.e4m3fn gradual 0x01) +
  failureCount (hasBits FloatFormat.e4m3fn flushed 0x00)⟩

/-- Invalid rational inputs are rejected even for formats without a NaN encoding. -/
def invalidRationalFailures : Thunk Nat := ⟨fun _ =>
  failureCount (Model.Policy.roundRat FloatFormat.binary32
    QuantizationPolicy.nearest 0 false 1 0 == none) +
  failureCount (Model.Policy.roundRatGeneral FloatFormat.e2m1
    QuantizationPolicy.nearest 0 false 1 0 == none)⟩

/-! ## Nearest-away and away-from-zero rounding -/

/-- Nearest-away rounding with native overflow and gradual underflow. -/
def nearestAwayPolicy : QuantizationPolicy := { rounding := .nearestAway }

/-- The exact dyadic `±significand * 2^exponent`. -/
@[inline] def dyadic (negative : Bool) (significand : Nat) (exponent : Int) : Numerics.Dyadic :=
  { negative, significand, exponent }

/-- The named formats of at most eight bits, one per encoding policy and layout. -/
def smallFormats : List FloatFormat :=
  [ FloatFormat.e2m1, FloatFormat.e2m3, FloatFormat.e3m2, FloatFormat.e4m3fn,
    FloatFormat.e4m3fnuz, FloatFormat.e5m2, FloatFormat.e5m2fnuz ]

/--
Whether the general engine, the nearest-away dyadic rounder, and the policy dispatcher, which
uses that rounder natively, all deliver the `expected` bit pattern for `exact`.
-/
def nearestAwayDelivers (fmt : FloatFormat) (exact : Numerics.Dyadic) (expected : Nat) : Bool :=
  hasBits fmt (Model.Policy.roundDyadicGeneral fmt nearestAwayPolicy 0 exact) expected &&
    hasBits fmt (Model.roundDyadicNearestAway fmt exact) expected &&
    hasBits fmt (Model.Policy.roundDyadic fmt nearestAwayPolicy 0 exact) expected

/--
Named nearest-away cases for binary32, E4M3FN, and E5M2: a normal tie, subnormal ties, half the
least subnormal, and the overflow midpoint, with both signs where the sign matters.
-/
def nearestAwayTieFailures : Thunk Nat := ⟨fun _ =>
  let b32 := FloatFormat.binary32
  let e4 := FloatFormat.e4m3fn
  let e5 := FloatFormat.e5m2
  countFailures
    [ -- binary32: 1 + 2^-24 lies halfway between 1 and its successor; 1 + 2^-25 does not.
      nearestAwayDelivers b32 (dyadic false (2 ^ 24 + 1) (-24)) 0x3f800001
    , nearestAwayDelivers b32 (dyadic true (2 ^ 24 + 1) (-24)) 0xbf800001
    , nearestAwayDelivers b32 (dyadic false (2 ^ 25 + 1) (-25)) 0x3f800000
      -- binary32 subnormal ties: half the least subnormal, and 2.5 least subnormals.
    , nearestAwayDelivers b32 (dyadic false 1 (-150)) 0x00000001
    , nearestAwayDelivers b32 (dyadic true 1 (-150)) 0x80000001
    , nearestAwayDelivers b32 (dyadic false 1 (-151)) 0x00000000
    , nearestAwayDelivers b32 (dyadic false 5 (-150)) 0x00000003
      -- binary32: the overflow midpoint 2^128 - 2^103 overflows, and the value below it does not.
    , nearestAwayDelivers b32 (dyadic false (2 ^ 25 - 1) 103) 0x7f800000
    , nearestAwayDelivers b32 (dyadic true (2 ^ 25 - 1) 103) 0xff800000
    , nearestAwayDelivers b32 (dyadic false (2 ^ 26 - 3) 102) 0x7f7fffff
      -- E4M3FN: 1.0625 rounds to 1.125 and half the least subnormal to that subnormal. The
      -- midpoint 464 between 448 and the next grid value 480, whose encoding is the NaN pattern,
      -- overflows to NaN, although 448 has an even significand and nearest-even keeps it.
    , nearestAwayDelivers e4 (dyadic false 17 (-4)) 0x39
    , nearestAwayDelivers e4 (dyadic false 1 (-10)) 0x01
    , nearestAwayDelivers e4 (dyadic false 5 (-10)) 0x03
    , nearestAwayDelivers e4 (dyadic false 29 4) 0x7f
    , nearestAwayDelivers e4 (dyadic true 29 4) 0xff
    , hasBits e4 (Model.roundDyadic e4 (dyadic false 29 4)) 0x7e
      -- E5M2: 1.125 rounds to 1.25, half the least subnormal to that subnormal, and the
      -- midpoint 61440 overflows to infinity.
    , nearestAwayDelivers e5 (dyadic false 9 (-3)) 0x3d
    , nearestAwayDelivers e5 (dyadic false 1 (-17)) 0x01
    , nearestAwayDelivers e5 (dyadic false 15 12) 0x7c
    , nearestAwayDelivers e5 (dyadic true 15 12) 0xfc
    ]⟩

/--
Every dyadic with a significand below `2^6`, at exponents from three below the least subnormal to
one above the largest normal exponent, with both signs. Six significant bits put an exact tie in
every binade of a small format.
-/
def sweepDyadics (fmt : FloatFormat) : List Numerics.Dyadic :=
  let exponents :=
    (List.range (fmt.maxNormalExponent - fmt.minSubnormalExponent + 5).toNat).map fun offset =>
      fmt.minSubnormalExponent - 3 + offset
  [false, true].flatMap fun negative =>
    (List.range 64).flatMap fun significand =>
      exponents.map fun exponent => dyadic negative significand exponent

/--
Compare the general engine with `roundDyadicNearestAway`, and `roundDyadicAway` with the
directed rounder toward the infinity of the value's sign, on the sweep of every small format. The
dyadic tie and overflow tests must also agree with their rational twins at denominator one.
-/
def nearestAwaySweepFailures : Thunk Nat := ⟨fun _ =>
  smallFormats.foldl (init := 0) fun failures fmt =>
    failures + countWhereFailures (sweepDyadics fmt) fun exact =>
      Model.Policy.roundDyadicGeneral fmt nearestAwayPolicy 0 exact ==
          Model.roundDyadicNearestAway fmt exact &&
        Model.roundDyadicAway fmt exact ==
          Model.Internal.Directed.roundDyadic fmt
            (if exact.negative then .down else .up) exact &&
        Model.dyadicIsGridTie fmt exact ==
          Model.rationalIsGridTieScaled fmt exact.significand 1 exact.exponent &&
        Model.dyadicNearestAwayOverflows fmt exact ==
          Model.rationalNearestAwayOverflowsScaled fmt exact.significand 1 exact.exponent⟩

/--
Quotients `n / d` with `n < 48` and `0 < d ≤ 11`, scaled by `2^-16`, `2^-5`, `1`, and `2^12`, so
that every small format meets subnormal, normal, and overflowing magnitudes.
-/
def sweepRationals : List (Nat × Nat × Int) :=
  (List.range 48).flatMap fun numerator =>
    (List.range 11).flatMap fun denominatorOffset =>
      [-16, -5, 0, 12].map fun exponent => (numerator, denominatorOffset + 1, exponent)

/--
Compare `roundRatNearestAwayScaled` with the general engine on the rational sweep of every small
format, for both signs.
-/
def rationalNearestAwayFailures : Thunk Nat := ⟨fun _ =>
  smallFormats.foldl (init := 0) fun failures fmt =>
    failures + countWhereFailures sweepRationals fun (numerator, denominator, exponent) =>
      [false, true].all fun sign =>
        let scaled := Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator exponent
        Model.Policy.roundRatGeneral fmt nearestAwayPolicy 0 sign scaled.1 scaled.2 ==
          some (Model.roundRatNearestAwayScaled fmt sign numerator denominator exponent)⟩

/-- The bits and conversion status of a nearest-away conversion of `exact` under `policy`. -/
def nearestAwayStatus (fmt : FloatFormat) (policy : QuantizationPolicy) (exact : Rat) :
    Option (Nat × Floats.ExecFloat.ConversionStatus) :=
  let context : Floats.ExecFloat.Binary.Conversion.Context := { quantization := policy }
  (Model.Policy.roundRat fmt policy 0 (decide (exact < 0)) exact.num.natAbs exact.den).map
    fun rounded =>
      (Model.toNatBits rounded,
        Floats.ExecFloat.Binary.Conversion.finiteStatus context exact rounded)

/--
Named nearest-away status vectors. Around the smallest normal `μ` with least subnormal `δ`, both
`μ - δ/2` and `μ - δ/4` deliver `μ`, but only the first is tiny after rounding.
-/
def nearestAwayStatusVectorFailures : Thunk Nat := ⟨fun _ =>
  let b32 := FloatFormat.binary32
  let e4 := FloatFormat.e4m3fn
  let e5 := FloatFormat.e5m2
  let minNormal : Rat := 2 ^ (-126 : Int)
  let minSubnormal : Rat := 2 ^ (-149 : Int)
  countFailures
    [ nearestAwayStatus b32 nearestAwayPolicy (1 + 2 ^ (-24 : Int)) ==
        some (0x3f800001, { inexact := true })
    , nearestAwayStatus b32 nearestAwayPolicy (2 ^ 128 - 2 ^ 103) ==
        some (0x7f800000, { inexact := true, overflow := true })
    , nearestAwayStatus b32 nearestAwayPolicy (-(2 ^ 128 - 2 ^ 103)) ==
        some (0xff800000, { inexact := true, overflow := true })
    , nearestAwayStatus b32 nearestAwayPolicy (2 ^ 128 - 2 ^ 103 - 2 ^ 102) ==
        some (0x7f7fffff, { inexact := true })
    , nearestAwayStatus b32 nearestAwayPolicy (minNormal - minSubnormal / 2) ==
        some (0x00800000, { inexact := true, underflow := true })
    , nearestAwayStatus b32 nearestAwayPolicy (minNormal - minSubnormal / 4) ==
        some (0x00800000, { inexact := true })
    , nearestAwayStatus b32 nearestAwayPolicy (minSubnormal / 2) ==
        some (0x00000001, { inexact := true, underflow := true })
    , nearestAwayStatus b32 nearestAwayPolicy 0 == some (0x00000000, {})
      -- E4M3FN: a normal tie, half the least subnormal, and the overflow midpoint 464, which
      -- overflows to NaN natively and saturates to 448 otherwise.
    , nearestAwayStatus e4 nearestAwayPolicy (17 / 16) == some (0x39, { inexact := true })
    , nearestAwayStatus e4 nearestAwayPolicy (2 ^ (-10 : Int)) ==
        some (0x01, { inexact := true, underflow := true })
    , nearestAwayStatus e4 nearestAwayPolicy (-2 ^ (-10 : Int)) ==
        some (0x81, { inexact := true, underflow := true })
    , nearestAwayStatus e4 nearestAwayPolicy 464 ==
        some (0x7f, { inexact := true, overflow := true })
    , nearestAwayStatus e4 { rounding := .nearestAway, overflow := .saturate } 464 ==
        some (0x7e, { inexact := true, overflow := true, saturated := true })
      -- Flush-to-zero: half the least subnormal rounds up to it and is then flushed.
    , nearestAwayStatus e4 { rounding := .nearestAway, underflow := .flushToZero }
        (2 ^ (-10 : Int)) == some (0x00, { inexact := true, underflow := true })
      -- E5M2: a normal tie, half the least subnormal, and the overflow midpoint 61440, which
      -- overflows to infinity natively and saturates to 57344 otherwise.
    , nearestAwayStatus e5 nearestAwayPolicy (9 / 8) == some (0x3d, { inexact := true })
    , nearestAwayStatus e5 nearestAwayPolicy (-9 / 8) == some (0xbd, { inexact := true })
    , nearestAwayStatus e5 nearestAwayPolicy (2 ^ (-17 : Int)) ==
        some (0x01, { inexact := true, underflow := true })
    , nearestAwayStatus e5 nearestAwayPolicy (-2 ^ (-17 : Int)) ==
        some (0x81, { inexact := true, underflow := true })
    , nearestAwayStatus e5 nearestAwayPolicy 61440 ==
        some (0x7c, { inexact := true, overflow := true })
    , nearestAwayStatus e5 nearestAwayPolicy (-61440) ==
        some (0xfc, { inexact := true, overflow := true })
    , nearestAwayStatus e5 nearestAwayPolicy 59392 == some (0x7b, { inexact := true })
    , nearestAwayStatus e5 { rounding := .nearestAway, overflow := .saturate } 61440 ==
        some (0x7b, { inexact := true, overflow := true, saturated := true })
    ]⟩

/--
Compare `finiteStatus` for nearest-away conversions, which reads the nearest-away classifiers, with
the status built from the independent significand calculation `roundedSignificandStatus`, on the
rational sweep of every small format, both signs, and every overflow and underflow policy.
`finiteStatus_eq_roundedSignificandStatus_of_nearestAway` proves the same equality for every
rational.
-/
def nearestAwayStatusSweepFailures : Thunk Nat := ⟨fun _ =>
  let policies : List QuantizationPolicy :=
    [ nearestAwayPolicy, { rounding := .nearestAway, overflow := .saturate },
      { rounding := .nearestAway, underflow := .flushToZero },
      { rounding := .nearestAway, overflow := .saturate, underflow := .flushToZero } ]
  smallFormats.foldl (init := 0) fun failures fmt =>
    failures + countWhereFailures sweepRationals fun (numerator, denominator, exponent) =>
      policies.all fun policy => [false, true].all fun negative =>
        let magnitude : Rat := (numerator : Rat) / denominator * (2 : Rat) ^ exponent
        let exact := if negative then -magnitude else magnitude
        let context : Floats.ExecFloat.Binary.Conversion.Context := { quantization := policy }
        match Model.Policy.roundRat fmt policy 0 negative exact.num.natAbs exact.den with
        | none => false
        | some rounded =>
            let (overflow, tiny) :=
              Floats.ExecFloat.Binary.Conversion.roundedSignificandStatus fmt .nearestAway 0
                (decide (exact < 0)) exact.num.natAbs exact.den
            let inexact := Model.toRat? rounded != some exact
            Floats.ExecFloat.Binary.Conversion.finiteStatus context exact rounded ==
              { inexact
                overflow
                underflow := (tiny || (policy.underflow == .flushToZero &&
                  Model.isTinyAfterRounding rounded)) && inexact
                saturated := overflow && policy.overflow == .saturate }⟩

/--
Named away-from-zero cases, the policy dispatch of nearest-away and away-from-zero rounding, and
the magnitude rule of each rounding direction.
-/
def awayFailures : Thunk Nat := ⟨fun _ =>
  let b32 := FloatFormat.binary32
  let e4 := FloatFormat.e4m3fn
  countFailures
    [ hasBits b32 (Model.roundDyadicAway b32 (dyadic false (2 ^ 30 + 1) (-30))) 0x3f800001
    , hasBits b32 (Model.roundDyadicAway b32 (dyadic true (2 ^ 30 + 1) (-30))) 0xbf800001
    , hasBits b32 (Model.roundDyadicAway b32 (dyadic false 1 (-200))) 0x00000001
    , hasBits b32 (Model.roundDyadicAway b32 (dyadic true 1 (-200))) 0x80000001
    , hasBits b32 (Model.roundDyadicAway b32 (dyadic false 3 0)) 0x40400000
    , hasBits b32 (Model.roundDyadicAway b32 (dyadic true 0 0)) 0x80000000
    , hasBits b32 (Model.roundDyadicAway b32 (dyadic false 1 128)) 0x7f800000
    , hasBits e4 (Model.roundDyadicAway e4 (dyadic false 449 0)) 0x7f
    , Model.IEEERoundingMode.all.map (fun mode =>
          (mode.magnitudeRounding false, mode.magnitudeRounding true)) ==
        [ (.nearestEven, .nearestEven), (.nearestAway, .nearestAway), (.down, .down),
          (.up, .down), (.down, .up), (.up, .up) ]
      -- An away-from-zero policy with native overflow and gradual underflow dispatches to the
      -- dyadic rounder, and the general engine agrees with it.
    , hasBits b32 (Model.Policy.roundDyadic b32 { rounding := .away } 0
        (dyadic true (2 ^ 30 + 1) (-30))) 0xbf800001
    , hasBits b32 (Model.Policy.roundDyadicGeneral b32 { rounding := .away } 0
        (dyadic true (2 ^ 30 + 1) (-30))) 0xbf800001
    , hasBits e4 (Model.Policy.roundDyadic e4 { rounding := .away } 0
        (dyadic false 449 0)) 0x7f
    , Model.Policy.policyIEEERoundingMode? { rounding := .away } == some .away
    , Model.Policy.policyIEEERoundingMode? nearestAwayPolicy == some .nearestAway
      -- Saturating policies still use the general engine.
    , Model.Policy.policyIEEERoundingMode?
        { rounding := .away, overflow := .saturate } == none
    , hasBits e4 (Model.Policy.roundDyadic e4 { rounding := .away, overflow := .saturate }
        0 (dyadic false 449 0)) 0x7e
    ]⟩

/-- Named failure counters for the policy-aware binary-format checks. -/
def failureRows : Thunk (List (String × Nat)) := ⟨fun _ =>
  [ ("smallFormatRoundTrips", smallFormatRoundTripFailures.get)
  , ("formatTables", formatTableFailures.get)
  , ("conversionPolicies", policyFailures.get)
  , ("invalidRationals", invalidRationalFailures.get)
  , ("nearestAwayTies", nearestAwayTieFailures.get)
  , ("nearestAwaySweep", nearestAwaySweepFailures.get)
  , ("rationalNearestAway", rationalNearestAwayFailures.get)
  , ("nearestAwayStatusVectors", nearestAwayStatusVectorFailures.get)
  , ("nearestAwayStatusSweep", nearestAwayStatusSweepFailures.get)
  , ("away", awayFailures.get)
  ]⟩

/-- Aggregate failure count for the policy-aware binary-format regression checks. -/
def totalFailures : Thunk Nat := ⟨fun _ =>
  namedFailureTotal failureRows.get⟩

/-- Human-readable regression report. Every row should be zero. -/
def report : Thunk String := ⟨fun _ =>
  renderFailureReport failureRows.get⟩

end FloatLibTests.Regression.BinaryInterchange.PolicyRounding
