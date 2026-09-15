/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Parsing
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Formatting
public import FloatLib.Floats.Formats.IEEE754.Native
public import FloatLibTests.Accounting

/-!
# Decimal notation and bounded input regressions

Known binary64 words check parsing independently of output formatting. Decimal goldens exercise
ties, a carry into the next decade, trailing zeros, signed zero, and special values. Small-format
enumeration checks exact fixed output for every finite word; binary64 cases check native adapters.
-/

@[expose] public section

-- Keep regression computations in their requested suite rather than module initialization.
set_option compiler.extract_closed false

namespace FloatLibTests.Regression.BinaryInterchange.Text

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLibTests.Accounting

def golden (input : String) (places : Nat) (fixed scientific : String) : Bool :=
  match Model.parse FloatFormat.binary64 input with
  | .error _ => false
  | .ok value =>
      Model.formatFixed value places == fixed &&
      Model.formatScientific value places == scientific

def parsingBits : Nat :=
  countWhereFailures
    [ ("0.1", 0x3fb999999999999a), ("1.25", 0x3ff4000000000000)
    , (" 1 ", 0x3ff0000000000000), ("-0", 0x8000000000000000)
    , ("0x1.8p+2", 0x4018000000000000), ("1e309", 0x7ff0000000000000)
    , ("1e-400", 0), ("-1e-400", 0x8000000000000000) ] fun (input, bits) =>
      match Model.parse FloatFormat.binary64 input (limits := true) with
      | .error _ => false
      | .ok value => Model.toNatBits value == bits

def notationGoldens : Nat :=
  countFailures
    [ golden "12.5" 3 "12.500" "1.250e1"
    , golden "0.1" 3 "0.100" "1.000e-1"
    , golden "-0" 3 "-0.000" "-0.000e0"
    , golden "0" 0 "0" "0e0"
    , golden "2.5" 0 "2" "2e0"
    , golden "3.5" 0 "4" "4e0"
    , golden "-2.5" 0 "-2" "-2e0"
    , golden "9.999" 2 "10.00" "1.00e1"
    , golden "0.03125" 4 "0.0312" "3.1250e-2"
    , golden "-0.0001" 3 "-0.000" "-1.000e-4"
    , golden "inf" 2 "Infinity" "Infinity"
    , golden "-inf" 2 "-Infinity" "-Infinity" ]

def boundedErrors : Nat :=
  let fmt := FloatFormat.binary64
  let check (limits : Model.ParseLimits) (input : String) (expected : Model.ParseError) : Bool :=
    match Model.parse fmt input (limits := true)
        (maxBytes := limits.maxBytes) (maxExponent := limits.maxExponent) (status := true) with
    | .error actual => decide (actual = expected)
    | .ok _ => false
  countFailures
    [ check { maxBytes := 2 } "1.0" (.inputTooLong 3 2)
    , check { maxBytes := 2 } " 1 " (.inputTooLong 3 2)
    , check { maxBytes := 1 } "é" (.inputTooLong 2 1)
    , check { maxExponent := 2 } "1e3" (.exponentTooLarge 3 2)
    , check { maxExponent := 2 } "0.001" (.exponentTooLarge 3 2)
    , check { maxExponent := 2 } "0x1p-3" (.exponentTooLarge 3 2)
    , check { maxExponent := 2 } "1*2^3" (.exponentTooLarge 3 2)
    , check {} "1e1000000000" (.exponentTooLarge 1000000000 10000)
    , check {} "" .emptyInput
    , check {} "1e" (.invalidSyntax "1e")
    , check {} "1 0" (.invalidSyntax "1 0")
    , check {} "1.2.3" (.invalidSyntax "1.2.3")
    , check {} "1_0" (.invalidSyntax "1_0") ]

def roundingDirections : Nat :=
  countWhereFailures
    [ (Model.IEEERoundingMode.nearestEven, "0.12", "-0.12")
    , (.towardZero, "0.12", "-0.12")
    , (.towardPositiveInfinity, "0.13", "-0.12")
    , (.towardNegativeInfinity, "0.12", "-0.13") ] fun (mode, positive, negative) =>
      match Model.parse FloatFormat.binary64 "0.125",
          Model.parse FloatFormat.binary64 "-0.125" with
      | .ok p, .ok n =>
          let a := Model.formatDecimalWithStatus mode (.fixed 2) p
          let b := Model.formatDecimalWithStatus mode (.fixed 2) n
          a.text == positive && b.text == negative &&
            a.status == { inexact := true } && b.status == { inexact := true }
      | _, _ => false

def scientificDirections : Nat :=
  countWhereFailures
    [ (Model.IEEERoundingMode.nearestEven, "1.00e1", "-1.00e1")
    , (.towardZero, "9.99e0", "-9.99e0")
    , (.towardPositiveInfinity, "1.00e1", "-9.99e0")
    , (.towardNegativeInfinity, "9.99e0", "-1.00e1") ] fun (mode, positive, negative) =>
      match Model.parse FloatFormat.binary64 "9.99609375",
          Model.parse FloatFormat.binary64 "-9.99609375" with
      | .ok p, .ok n =>
          let a := Model.formatDecimalWithStatus mode (.scientific 2) p
          let b := Model.formatDecimalWithStatus mode (.scientific 2) n
          a.text == positive && b.text == negative &&
            a.status == { inexact := true } && b.status == { inexact := true }
      | _, _ => false

def boundedAgreement : Nat :=
  countPairFailures Model.IEEERoundingMode.all
    ["0.1", "-0.1", "-0", "0x1.8p-2", "3 * 2^-2", "1e309", "-1e-400",
      "inf", "nan", "-sNaN1", " 12.5 ", "1e", ""] fun mode input =>
      match Model.parse FloatFormat.binary64 input (rounding := mode)
          (limits := true) (status := true),
          Model.parse FloatFormat.binary64 input (rounding := mode) (status := true) with
      | .ok bounded, .ok original =>
          bounded.value.bits == original.value.bits && bounded.status == original.status
      | .error bounded, .error original => decide (bounded = original)
      | _, _ => false

def smallFormatRoundTrips : Nat :=
  let fmt := FloatFormat.ieee 3 2
  countWhereFailures (List.range (2 ^ fmt.bitWidth)) fun bits =>
    let value := Model.ofNatBits (fmt := fmt) bits
    if Model.isFinite value then
      let output := Model.formatDecimalWithStatus .nearestEven (.fixed 5) value
      output.status == {} &&
        match Model.parse fmt output.text (limits := true) with
        | .error _ => false
        | .ok restored => restored.bits == value.bits
    else
      Model.formatFixed value 5 == Model.formatDecimal value &&
      Model.formatScientific value 5 == Model.formatDecimal value

def nativeAdapters : Nat :=
  countWhereFailures
    [0, 0x8000000000000000, 1, 0x000fffffffffffff, 0x0010000000000000,
      0x3fb999999999999a, 0x3ff0000000000000, 0x7fefffffffffffff] fun bits =>
      let value := ExecFloat.Binary.ofFloat (Float.ofBits (UInt64.ofNat bits))
      let text := ExecFloat.Binary.formatDecimal value
      let result : Except Model.ParseError Float :=
        (ExecFloat.Binary.parse text (limits := true)).map ExecFloat.Binary.toFloat
      match result with
      | .error _ => false
      | .ok restored => restored.toBits.toNat == bits

/-- Failure counts for the parser and decimal presentation cases. -/
def report : Thunk ReportSection := ⟨fun _ =>
  ReportSection.ofRows "text conversion"
    #[ ("known binary64 words", parsingBits)
     , ("fixed and scientific notation", notationGoldens)
     , ("byte and exponent limits", boundedErrors)
     , ("directed output and status", roundingDirections)
     , ("scientific carry and direction", scientificDirections)
     , ("bounded parser agreement", boundedAgreement)
     , ("small-format round trips", smallFormatRoundTrips)
     , ("native binary64 adapters", nativeAdapters) ]⟩

end FloatLibTests.Regression.BinaryInterchange.Text
