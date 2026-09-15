/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.Proof
public import FloatLibTests.Regression.BinaryInterchange.Harness

/-!
# Policy-aware `Model` examples

This file complements the general theorems with executable checks of the named low-precision
formats. It never converts through Lean's native `Float`: every expected value is either a raw bit
pattern or an exact `Numerics.Dyadic`.

`smallFormatRoundTripFailures` enumerates every bit pattern of E2M1, E2M3, E3M2, E4M3FN,
E4M3FNUZ, E5M2, and E5M2FNUZ. For each finite pattern it decodes the exact value and quantizes that
value back under nearest-even rounding. A zero count is a useful regression check, but it is not a
replacement for the encoding-independent theorems in
`FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.Agreement`.

The golden patterns come from the OCP OFP8 and MX tables and the ONNX FNUZ description:

* <https://www.opencompute.org/documents/ocp-8-bit-floating-point-specification-ofp8-revision-1-0-2023-12-01-pdf-1>
* <https://www.opencompute.org/documents/ocp-microscaling-formats-mx-v1-0-spec-final-pdf>
* <https://onnx.ai/onnx/technical/float8.html>
-/

@[expose] public section

-- Keep lazy regression bodies out of module initialization, including closed subexpressions.
-- This affects native code generation only; elaboration and kernel checking are unchanged.
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
        let restored := Model.Policy.roundDyadic fmt QuantizationPolicy.nearestEven 0 exact
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

E4M3FN represents `448` as `0x7e`; its next pattern `0x7f` is NaN. The same exact overflow may
therefore become either `0x7e` or `0x7f`, depending on the operation's overflow policy.
-/
def policyFailures : Thunk Nat := ⟨fun _ =>
  let exact448 : Numerics.Dyadic := { negative := false, significand := 448, exponent := 0 }
  let exact500 : Numerics.Dyadic := { negative := false, significand := 500, exponent := 0 }
  let negativeZero : Numerics.Dyadic := { negative := true, significand := 0, exponent := 0 }
  let minSubnormal : Numerics.Dyadic :=
    { negative := false, significand := 1, exponent := FloatFormat.e4m3fn.minSubnormalExponent }
  let nativeMax := Model.Policy.roundDyadic FloatFormat.e4m3fn
    QuantizationPolicy.nearestEven 0 exact448
  let nativeOverflow := Model.Policy.roundDyadic FloatFormat.e4m3fn
    QuantizationPolicy.nearestEven 0 exact500
  let saturatedOverflow := Model.Policy.roundDyadic FloatFormat.e4m3fn
    QuantizationPolicy.saturating 0 exact500
  let fnuzZero := Model.Policy.roundDyadic FloatFormat.e4m3fnuz
    QuantizationPolicy.nearestEven 0 negativeZero
  let gradual := Model.Policy.roundDyadic FloatFormat.e4m3fn
    QuantizationPolicy.nearestEven 0 minSubnormal
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
    QuantizationPolicy.nearestEven 0 false 1 0 == none) +
  failureCount (Model.Policy.roundRatGeneral FloatFormat.e2m1
    QuantizationPolicy.nearestEven 0 false 1 0 == none)⟩

/-- Named failure counters for the policy-aware binary-format checks. -/
def failureRows : Thunk (List (String × Nat)) := ⟨fun _ =>
  [ ("smallFormatRoundTrips", smallFormatRoundTripFailures.get)
  , ("formatTables", formatTableFailures.get)
  , ("conversionPolicies", policyFailures.get)
  , ("invalidRationals", invalidRationalFailures.get)
  ]⟩

/-- Aggregate failure count for the policy-aware binary-format regression checks. -/
def totalFailures : Thunk Nat := ⟨fun _ =>
  namedFailureTotal failureRows.get⟩

/-- Human-readable regression report. Every row should be zero. -/
def report : Thunk String := ⟨fun _ =>
  renderFailureReport failureRows.get⟩

end FloatLibTests.Regression.BinaryInterchange.PolicyRounding
