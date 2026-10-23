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
enumeration checks exact fixed output for every finite word, and binary64 cases check native
adapters. The display reads back as every binary16, bfloat16 and 8-bit word and sampled binary32 and
binary64 words, and when it isn't the exact value no decimal with fewer digits reads back. A NaN
only has to read back as some NaN.
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
      Model.format value (style := .fixed places) == fixed &&
      Model.format value (style := .scientific places) == scientific

def parsingBits : Nat :=
  countWhereFailures
    [ ("0.1", 0x3fb999999999999a), ("1.25", 0x3ff4000000000000)
    , (" 1 ", 0x3ff0000000000000), ("-0", 0x8000000000000000)
    , ("0x1.8p+2", 0x4018000000000000), ("1e309", 0x7ff0000000000000)
    , ("1e-400", 0), ("-1e-400", 0x8000000000000000) ] fun (input, bits) =>
      match Model.parse FloatFormat.binary64 input (limits := some {}) with
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
    match Model.parse fmt input (limits := some limits) (status := true) with
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
    [ (Model.IEEERoundingMode.nearest, "0.12", "-0.12")
    , (.nearestAway, "0.13", "-0.13")
    , (.towardZero, "0.12", "-0.12")
    , (.up, "0.13", "-0.12")
    , (.down, "0.12", "-0.13")
    , (.away, "0.13", "-0.13") ] fun (mode, positive, negative) =>
      match Model.parse FloatFormat.binary64 "0.125",
          Model.parse FloatFormat.binary64 "-0.125" with
      | .ok p, .ok n =>
          let a := Model.format p (style := .fixed 2) (mode := mode) (status := true)
          let b := Model.format n (style := .fixed 2) (mode := mode) (status := true)
          a.text == positive && b.text == negative &&
            a.status == { inexact := true } && b.status == { inexact := true }
      | _, _ => false

def scientificDirections : Nat :=
  countWhereFailures
    [ (Model.IEEERoundingMode.nearest, "1.00e1", "-1.00e1")
    , (.nearestAway, "1.00e1", "-1.00e1")
    , (.away, "1.00e1", "-1.00e1")
    , (.towardZero, "9.99e0", "-9.99e0")
    , (.up, "1.00e1", "-9.99e0")
    , (.down, "9.99e0", "-1.00e1") ] fun (mode, positive, negative) =>
      match Model.parse FloatFormat.binary64 "9.99609375",
          Model.parse FloatFormat.binary64 "-9.99609375" with
      | .ok p, .ok n =>
          let a := Model.format p (style := .scientific 2) (mode := mode) (status := true)
          let b := Model.format n (style := .scientific 2) (mode := mode) (status := true)
          a.text == positive && b.text == negative &&
            a.status == { inexact := true } && b.status == { inexact := true }
      | _, _ => false

def boundedAgreement : Nat :=
  countPairFailures Model.IEEERoundingMode.all
    ["0.1", "-0.1", "-0", "0x1.8p-2", "3 * 2^-2", "1e309", "-1e-400",
      "inf", "nan", "-sNaN1", " 12.5 ", "1e", ""] fun mode input =>
      match Model.parse FloatFormat.binary64 input (mode := mode)
          (limits := some {}) (status := true),
          Model.parse FloatFormat.binary64 input (mode := mode) (status := true) with
      | .ok bounded, .ok original =>
          bounded.value.bits == original.value.bits && bounded.status == original.status &&
            bounded.ternary == original.ternary
      | .error bounded, .error original => decide (bounded = original)
      | _, _ => false

/-- A parsed value carries the ternary value of its one rounding, comparing it with the text. -/
def parsingTernary : Nat :=
  countWhereFailures
    [ ("0.1", Ordering.gt), ("-0.1", .lt), ("0.5", .eq), ("0x1.8p+2", .eq), ("3 * 2^-2", .eq)
    , ("1e309", .gt), ("-1e309", .lt), ("1e-400", .lt), ("-1e-400", .gt)
    , ("inf", .eq), ("-inf", .eq), ("nan", .eq), ("sNaN", .eq) ] fun (input, ternary) =>
      match Model.parse FloatFormat.binary64 input (limits := some {}) (status := true) with
      | .error _ => false
      | .ok outcome => outcome.ternary == ternary

/--
Clamping a far exponent leaves the whole outcome unchanged, ternary value included, for both signs,
every rounding direction, and formats with and without infinities and signed zero.
-/
def clampAgreement : Nat :=
  let decimals : List FloatLib.Numerics.DecimalText.Decimal :=
    [ ⟨false, 7, 5000⟩, ⟨true, 7, 5000⟩, ⟨false, 3, -5000⟩, ⟨true, 3, -5000⟩
    , ⟨false, 1, 60⟩, ⟨true, 1, -60⟩, ⟨false, 7, 5⟩, ⟨true, 7, -9⟩ ]
  countPairFailures Model.IEEERoundingMode.all decimals fun mode decimal =>
    Model.convertDecimalText FloatFormat.binary32 mode decimal ==
        Model.convertDecimalTextExact FloatFormat.binary32 mode decimal &&
      Model.convertDecimalText FloatFormat.e4m3fn mode decimal ==
        Model.convertDecimalTextExact FloatFormat.e4m3fn mode decimal &&
      Model.convertDecimalText FloatFormat.e4m3fnuz mode decimal ==
        Model.convertDecimalTextExact FloatFormat.e4m3fnuz mode decimal &&
      Model.convertDecimalText FloatFormat.e2m3 mode decimal ==
        Model.convertDecimalTextExact FloatFormat.e2m3 mode decimal

def smallFormatRoundTrips : Nat :=
  let fmt := FloatFormat.ieee 3 2
  countWhereFailures (List.range (2 ^ fmt.bitWidth)) fun bits =>
    let value := Model.ofNatBits (fmt := fmt) bits
    if Model.isFinite value then
      let output := Model.format value (style := .fixed 5) (status := true)
      output.status == {} &&
        match Model.parse fmt output.text (limits := some {}) with
        | .error _ => false
        | .ok restored => restored.bits == value.bits
    else
      Model.format value (style := .fixed 5) == Model.format value (style := .exact) &&
      Model.format value (style := .scientific 5) == Model.format value (style := .exact)

def nativeAdapters : Nat :=
  countWhereFailures
    [0, 0x8000000000000000, 1, 0x000fffffffffffff, 0x0010000000000000,
      0x3fb999999999999a, 0x3ff0000000000000, 0x7fefffffffffffff] fun bits =>
      let value : Binary64 := ExecFloat.Binary.ofFloat (Float.ofBits (UInt64.ofNat bits))
      let text := ExecFloat.Binary.format value (style := .exact)
      let result : Except Model.ParseError Float :=
        (ExecFloat.Binary.parse text (limits := some {})).map fun x : Binary64 => x.toFloat
      match result with
      | .error _ => false
      | .ok restored => restored.toBits.toNat == bits

/-- Check nearest-even significant-digit output followed by nearest-even input. -/
def significantRoundTrip (fmt : FloatFormat) (digits : ℕ+) (bits : Nat) : Bool :=
  let value := Model.ofNatBits (fmt := fmt) bits
  if value.isFinite then
    let output := Model.format value (style := .significant digits) (status := true)
    match Model.parse fmt output.text with
    | .error _ => false
    | .ok restored => restored.bits == value.bits
  else true

/-- Exhaustive binary16 Pmin checks and boundary samples at the other basic format minima. -/
def minimumDigitRoundTrips : Nat :=
  countWhereFailures (List.range 65536) (significantRoundTrip .binary16 5) +
  countWhereFailures
    [0, 0x80000000, 1, 0x80000001, 0x007fffff, 0x00800000, 0x3f800000,
      0x3f800001, 0x3f7fffff, 0x7f7fffff, 0xff7fffff]
    (significantRoundTrip .binary32 9) +
  countWhereFailures
    [0, 0x8000000000000000, 1, 0x8000000000000001, 0x000fffffffffffff,
      0x0010000000000000, 0x3ff0000000000000, 0x3ff0000000000001,
      0x3fefffffffffffff, 0x7fefffffffffffff, 0xffefffffffffffff]
    (significantRoundTrip .binary64 17) +
  countWhereFailures
    [0, 2 ^ 127, 1, 2 ^ 127 + 1, 2 ^ 112 - 1, 2 ^ 112, 16383 * 2 ^ 112,
      16383 * 2 ^ 112 + 1, 16383 * 2 ^ 112 - 1, 32767 * 2 ^ 112 - 1,
      2 ^ 127 + 32767 * 2 ^ 112 - 1]
    (significantRoundTrip .binary128 36)

/-- Both exact text forms preserve every stored NaN fraction bit, including the quiet bit. -/
def nanTextRoundTrip (fmt : FloatFormat) (bits : Nat) : Bool :=
  let value := Model.ofNatBits (fmt := fmt) bits
  if value.isNaN then
    [Model.format value (style := .exact), Model.format value (style := .hex)].all fun text =>
      match Model.parse fmt text with
      | .error _ => false
      | .ok restored => restored.bits == value.bits
  else true

/-- Exhaust all binary16 NaNs and the signed and unsigned-zero FP8 NaN encodings. -/
def nanTextRoundTrips : Nat :=
  countWhereFailures (List.range 65536) (nanTextRoundTrip .binary16) +
  countPairFailures [FloatFormat.e4m3fn, .e4m3fnuz, .e5m2fnuz]
    (List.range 256) nanTextRoundTrip

/-- Significant digits of a decimal significand, ignoring trailing zeros. -/
def significantDigits (n : Nat) : Nat :=
  let rec trim : Nat → Nat → Nat
    | 0, n => n
    | fuel + 1, n => if n ≠ 0 ∧ n % 10 = 0 then trim fuel (n / 10) else n
  (Nat.toDigits 10 (trim 400 n)).length

/--
The display reads back as the value, and a display that is not the exact value has no decimal
with one significant digit fewer that reads back: neither the truncation nor the ceiling of the
value at that precision does, and every coarser decimal in the rounding interval would be one
of them.
-/
def shortestDisplay (fmt : FloatFormat) (bits : Nat) : Bool :=
  let value := Model.ofNatBits (fmt := fmt) bits
  let text := toString value
  let restored :=
    match Model.parse fmt text with
    | .ok parsed => if value.isNaN then parsed.isNaN else parsed.bits == value.bits
    | .error _ => false
  restored &&
    match Model.toDyadic? value with
    | none => true
    | some exact =>
        let record := Model.Shortest.decimal .nearest value exact
        let digits := significantDigits record.significand
        record.toRat == exact.toRat || digits ≤ 1 ||
          [Model.IEEERoundingMode.towardZero, .away].all fun mode =>
            match Model.parse fmt
                (Model.format value (style := .scientific (digits - 2)) (mode := mode)) with
            | .ok parsed => parsed.bits != value.bits
            | .error _ => true

/-- One step of a 64-bit xorshift generator, for reproducible sample words. -/
def nextSample (state : UInt64) : UInt64 :=
  let state := state ^^^ (state <<< 13)
  let state := state ^^^ (state >>> 7)
  state ^^^ (state <<< 17)

/-- `count` reproducible words of `width` bits. -/
def sampleWords (seed : UInt64) (width count : Nat) : List Nat :=
  (List.range count).foldl (fun (state, words) _ =>
    let state := nextSample state
    (state, (state.toNat % 2 ^ width) :: words)) (seed, []) |>.2

/-- Every binary16 and bfloat16 word, and samples of binary32 and binary64 words. -/
def shortestDisplays : Nat :=
  countWhereFailures (List.range 65536) (shortestDisplay .binary16) +
  countWhereFailures (List.range 65536) (shortestDisplay .bfloat16) +
  countWhereFailures (sampleWords 0x9E3779B97F4A7C15 32 20000) (shortestDisplay .binary32) +
  countWhereFailures (sampleWords 0x2545F4914F6CDD1D 64 20000) (shortestDisplay .binary64) +
  countPairFailures [FloatFormat.e4m3fn, .e4m3fnuz, .e5m2, .e5m2fnuz, .e2m3, .e3m2, .e2m1]
    (List.range 256) fun fmt bits => bits ≥ 2 ^ fmt.bitWidth || shortestDisplay fmt bits

/-- Display goldens, including precision above 4096 bits and a wide exponent range. -/
def displayGoldens : Nat :=
  let display (fmt : FloatFormat) (bits : Nat) : String :=
    toString (Model.ofNatBits (fmt := fmt) bits)
  let wide := FloatFormat.ieee 22 23
  -- This is 2^-1999977, whose exact decimal has over a million significant digits.
  let tinyWide : Model wide := Model.ofFields wide false 97174 0
  countWhereFailures
    [ (display .binary64 0x3fb999999999999a, "0.1")
    , (Model.format (Model.ofRat (FloatFormat.ieee 15 4096) (1 / 10)), "0.1")
    , (Model.format (Model.ofRat (FloatFormat.ieee 15 8192) (1 / 10)), "0.1")
    , (Model.format tinyWide, "8.557796e-602054")
    , (display .binary64 0x3fd3333333333334, "0.30000000000000004")
    , (display .binary64 0x3ff8000000000000, "1.5")
    , (display .binary64 0x4059000000000000, "100")
    , (display .binary64 0x4340000000000000, "9007199254740992")
    , (display .binary64 0x4340000000000001, "9007199254740994")
    , (display .binary64 0x4341c37937e08000, "10000000000000000")
    , (display .binary64 0x4376345785d8a000, "1e17")
    , (display .binary64 0x3f1a36e2eb1c432d, "0.0001")
    , (display .binary64 0x3ee4f8b588e368f1, "1e-5")
    , (display .binary64 1, "5e-324")
    , (display .binary64 0x7fefffffffffffff, "1.7976931348623157e308")
    , (display .binary64 0x8000000000000000, "-0")
    , (display .binary64 0xbff8000000000000, "-1.5")
    , (display .binary64 0x7ff0000000000000, "inf")
    , (display .binary64 0xfff0000000000000, "-inf")
    , (display .binary64 0x7ff8000000000001, "nan")
    , (display .binary32 0x3dcccccd, "0.1")
    , (display .binary32 0x4b800000, "16777216")
    , (display .binary32 0x4ceb79a3, "123456792")
    , (display .binary32 0x60ad78ec, "1e20")
    , (display .binary32 0x7f7fffff, "3.4028235e38")
    , (display .binary32 1, "1e-45")
    , (display .binary16 0x7bff, "65504")
    , (display .binary16 0x2e66, "0.1")
    , (display .binary16 0x0400, "6.104e-5")
    , (display .binary16 1, "6e-8")
    , (display .bfloat16 0x7f7f, "3.39e38")
    , (display .bfloat16 0x461c, "9984")
    , (display .bfloat16 0x4641, "1.235e4")
    , (display .bfloat16 0x4070, "3.75")
    , (display .e4m3fn 0x47, "3.75")
    , (display .e4m3fn 0x7e, "448")
    , (display .e4m3fn 0x01, "0.002") ] fun (actual, expected) => actual == expected

/-- Every style of `format` against goldens, with and without the status option. -/
def styleGoldens : Nat :=
  match Model.parse FloatFormat.binary64 "0.1" with
  | .error _ => 1
  | .ok value =>
      countFailures
        [ Model.format value == "0.1"
        , Model.format value (style := .exact) ==
            "10000000000000000555111512312578270211815834045410156250e-56"
        , Model.format value (style := .significant 3) == "100e-3"
        , Model.format value (style := .fixed 3) == "0.100"
        , Model.format value (style := .scientific 2) == "1.00e-1"
        , Model.format value (style := .hex) == "0x1999999999999ap-56"
        , Model.format value (style := .hex (.significant 2)) == "0x1ap-8"
        , Model.format value (status := true) == { text := "0.1", status := { inexact := true } }
        , Model.format value (style := .exact) (status := true) ==
            { text := Model.format value (style := .exact) }
        , Model.format value (style := .fixed 1) (mode := .up) == "0.2"
        , Model.format value (mode := .up) == "0.1"
        , Model.format value (mode := .down) == "0.10000000000000001"
        , toString (some value) == "(some 0.1)"
        , Std.Format.pretty (repr (some (Model.neg value))) == "some (-0.1)" ]

/-- Failure counts for the parser and decimal presentation cases. -/
def report : Thunk ReportSection := ⟨fun _ =>
  ReportSection.ofRows "text conversion"
    #[ ("known binary64 words", parsingBits)
     , ("fixed and scientific notation", notationGoldens)
     , ("byte and exponent limits", boundedErrors)
     , ("directed output and status", roundingDirections)
     , ("scientific carry and direction", scientificDirections)
     , ("bounded parser agreement", boundedAgreement)
     , ("ternary value of parsed text", parsingTernary)
     , ("exponent clamp agreement", clampAgreement)
     , ("small-format round trips", smallFormatRoundTrips)
     , ("IEEE minimum-digit round trips", minimumDigitRoundTrips)
     , ("NaN encoding text round trips", nanTextRoundTrips)
     , ("native binary64 adapters", nativeAdapters)
     , ("shortest display round trips", shortestDisplays)
     , ("display goldens", displayGoldens)
     , ("format style goldens", styleGoldens) ]⟩

end FloatLibTests.Regression.BinaryInterchange.Text
