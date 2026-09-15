/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.MixedPrecision.Matmul
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.MixedPrecision.Accumulation
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.Parsing
public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.Formatting
public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Status
public import FloatLibTests.Accounting
public import FloatLibTests.Regression.BinaryInterchange.ExecFloatInterval
public import FloatLibTests.Regression.BinaryInterchange.ExecFloatScaledRationals
public import FloatLibTests.Regression.BinaryInterchange.Harness

/-!
# Descriptor-model executable regression checks

Computational checks for the format-generic `Model` implementation:

- **bf16 / f16**: cast idempotence and classifier sanity on sample bit patterns
- **custom formats**: exhaustive square-root agreement with Lean's logical model at small widths
- **directed arithmetic**: exhaustive tiny-format enclosure checks
- **exception status**: focused IEEE edge cases
- **character input**: exact decimal and radix-two parsing, errors, and formatting round trips
- **mixed precision**: golden bf16-storage / binary32-accumulator cases

`totalFailures = 0` means every deterministic regression in this module passed.
-/

@[expose] public section

-- Keep lazy regression bodies out of module initialization, including closed subexpressions.
-- This affects native code generation only; elaboration and kernel checking are unchanged.
set_option compiler.extract_closed false

open FloatLib.Floats.Formats.BinaryInterchange

namespace FloatLibTests.Regression.BinaryInterchange.Model

open FloatLib

open FloatLib.Floats.Formats.BinaryInterchange.Model
open Harness
open FloatLibTests.Accounting

abbrev bf16 := FloatFormat.bfloat16
abbrev f16 := FloatFormat.binary16
abbrev f32 := FloatFormat.binary32

/-! ## bf16 -/

/-- Low 16-bit bf16 patterns (sign / exp / frac in IEEE bf16 layout). -/
def bf16SampleBits : List Nat :=
  [ 0x0000  -- +0
  , 0x8000  -- -0
  , 0x3F80  -- +1
  , 0xBF80  -- -1
  , 0x4000  -- +2
  , 0x3F00  -- +0.5
  , 0x7F80  -- +∞
  , 0xFF80  -- -∞
  , 0x7FC0  -- qNaN
  , 0x0001  -- min subnormal
  , 0x0080  -- min normal
  , 0x7F7F  -- near max finite
  ]

def bf16Samples : List (Model bf16) :=
  bf16SampleBits.map Model.ofNatBits

/-- f32 widen → narrow → widen is idempotent on bf16 samples. -/
def failBf16CastIdempotent : Thunk Nat := ⟨fun _ =>
  countWhereFailures bf16Samples fun x =>
    let y := Model.cast bf16 f32 x
    let z := Model.cast bf16 f32 (Model.cast f32 bf16 y)
    z.toBits == y.toBits⟩

/-- Classifiers stable under bf16 → f32 → bf16 round-trip. -/
def failBf16Classifiers : Thunk Nat := ⟨fun _ =>
  countWhereFailures bf16Samples fun x =>
    let y := Model.cast bf16 f32 x
    let g := Model.cast f32 bf16 y
    (Model.isNaN x == Model.isNaN g) &&
    (Model.isInf x == Model.isInf g) &&
    (Model.isZero x == Model.isZero g) &&
    (Model.isFinite x == Model.isFinite g)⟩

/-! ## f16 -/

def f16SampleBits : List Nat :=
  [ 0x0000, 0x8000, 0x3C00, 0xBC00, 0x4000, 0x3800, 0x7C00, 0xFC00, 0x7E00, 0x0001, 0x0400
  , 0x7BFF ]

def f16Samples : List (Model f16) :=
  f16SampleBits.map Model.ofNatBits

def failF16CastIdempotent : Thunk Nat := ⟨fun _ =>
  countWhereFailures f16Samples fun x =>
    let y := Model.cast f16 f32 x
    let z := Model.cast f16 f32 (Model.cast f32 f16 y)
    z.toBits == y.toBits⟩

def failF16Classifiers : Thunk Nat := ⟨fun _ =>
  countWhereFailures f16Samples fun x =>
    let y := Model.cast f16 f32 x
    let g := Model.cast f32 f16 y
    (Model.isNaN x == Model.isNaN g) &&
    (Model.isInf x == Model.isInf g) &&
    (Model.isZero x == Model.isZero g) &&
    (Model.isFinite x == Model.isFinite g)⟩

/-! ## arbitrary-width square root -/

/--
Count square-root disagreements over every bit pattern of a small format.

NaN payloads are canonicalized before comparison because `Model.sqrt` preserves and quiets the
input payload, whereas Lean's logical model returns its canonical NaN. All non-NaN results are
compared bit-for-bit.
-/
def sqrtModelMismatchCount (fmt : FloatFormat) : Nat :=
  countWhereFailures (List.range (2 ^ fmt.bitWidth)) fun bits =>
    let x : Model fmt := Model.ofNatBits bits
    let actual := Model.canonicalizeModel (Model.sqrt x)
    let expected := Model.ofModel fmt <|
      Float.Model.UnpackedFloat.sqrt (FloatFormat.toModel fmt) (Model.toModel x)
    actual == expected

/-- Exhaustive checks that exercise normal and subnormal results at several tiny layouts. -/
def failSmallFormatSqrt : Thunk Nat := ⟨fun _ =>
  sqrtModelMismatchCount (FloatFormat.ieee 2 1) +
  sqrtModelMismatchCount (FloatFormat.ieee 2 2) +
  sqrtModelMismatchCount (FloatFormat.ieee 2 3) +
  sqrtModelMismatchCount (FloatFormat.ieee 3 4) +
  sqrtModelMismatchCount (FloatFormat.ieee 4 6)⟩

/-! ## exhaustive tiny-format directed enclosures -/

def dyadicLowerEncloses {fmt : FloatFormat} (exact : Numerics.Dyadic)
    (rounded : Model fmt) : Bool :=
  if Model.isInf rounded then
    Model.signBit rounded
  else
    match Model.toDyadic? rounded with
    | some actual => Model.cmpDyadic actual exact != .gt
    | none => false

def dyadicUpperEncloses {fmt : FloatFormat} (exact : Numerics.Dyadic)
    (rounded : Model fmt) : Bool :=
  if Model.isInf rounded then
    !Model.signBit rounded
  else
    match Model.toDyadic? rounded with
    | some actual => Model.cmpDyadic exact actual != .gt
    | none => false

def rationalLowerEnclosesScaled {fmt : FloatFormat} (sign : Bool)
    (numerator denominator : Nat) (exponent : Int) (rounded : Model fmt) : Bool :=
  if Model.isInf rounded then
    Model.signBit rounded
  else
    match Model.toDyadic? rounded with
    | some actual =>
        (Numerics.RationalBinary.compareDyadicScaled?
          sign numerator denominator exponent actual).any
          fun order => order != .lt
    | none => false

def rationalUpperEnclosesScaled {fmt : FloatFormat} (sign : Bool)
    (numerator denominator : Nat) (exponent : Int) (rounded : Model fmt) : Bool :=
  if Model.isInf rounded then
    !Model.signBit rounded
  else
    match Model.toDyadic? rounded with
    | some actual =>
        (Numerics.RationalBinary.compareDyadicScaled?
          sign numerator denominator exponent actual).any
          fun order => order != .gt
    | none => false

def addEnclosed {fmt : FloatFormat} (x y : Model fmt) : Bool :=
  match Model.toDyadic? x, Model.toDyadic? y with
  | some left, some right =>
      let exact := Model.addDyadic left right
      dyadicLowerEncloses exact (Model.addDown x y) &&
      dyadicUpperEncloses exact (Model.addUp x y)
  | _, _ => true

def mulEnclosed {fmt : FloatFormat} (x y : Model fmt) : Bool :=
  match Model.toDyadic? x, Model.toDyadic? y with
  | some left, some right =>
      let exact : Numerics.Dyadic :=
        { negative := Bool.xor left.negative right.negative
          significand := left.significand * right.significand
          exponent := left.exponent + right.exponent }
      dyadicLowerEncloses exact (Model.mulDown x y) &&
      dyadicUpperEncloses exact (Model.mulUp x y)
  | _, _ => true

def divEnclosed {fmt : FloatFormat} (x y : Model fmt) : Bool :=
  match Model.toDyadic? x, Model.toDyadic? y with
  | some left, some right =>
      if right.significand == 0 then
        true
      else
        let sign := Bool.xor left.negative right.negative
        let exponentDifference := left.exponent - right.exponent
        rationalLowerEnclosesScaled sign left.significand right.significand exponentDifference
            (Model.divDown x y) &&
          rationalUpperEnclosesScaled sign left.significand right.significand exponentDifference
            (Model.divUp x y)
  | _, _ => true

def squaredDyadic (value : Numerics.Dyadic) : Numerics.Dyadic :=
  { negative := false
    significand := value.significand * value.significand
    exponent := value.exponent + value.exponent }

def sqrtEnclosed {fmt : FloatFormat} (x : Model fmt) : Bool :=
  match Model.toDyadic? x with
  | none => true
  | some exact =>
      if exact.negative && exact.significand != 0 then
        true
      else
        match Model.toDyadic? (Model.sqrtDown x),
            Model.toDyadic? (Model.sqrtUp x) with
        | some lower, some upper =>
            Model.cmpDyadic (squaredDyadic lower) exact != .gt &&
            Model.cmpDyadic exact (squaredDyadic upper) != .gt
        | _, _ => false

def tinyFormatFailures (fmt : FloatFormat) : Nat :=
  let values := (List.range (2 ^ fmt.bitWidth)).map
    (Model.ofNatBits (fmt := fmt))
  (countPairFailures values values fun x y =>
    addEnclosed x y && mulEnclosed x y && divEnclosed x y) +
  countWhereFailures values sqrtEnclosed

def failTinyDirectedEnclosures : Thunk Nat := ⟨fun _ =>
  tinyFormatFailures (FloatFormat.ieee 2 1) +
  tinyFormatFailures (FloatFormat.ieee 2 2) +
  tinyFormatFailures (FloatFormat.ieee 3 2)⟩

/-! ## exact character input -/

def parsedAs {fmt : FloatFormat} (result : Except Model.ParseError (Model fmt))
    (expected : Model fmt) : Bool :=
  match result with
  | .ok value => sameBits value expected
  | .error _ => false

def failedWith {fmt : FloatFormat} (result : Except Model.ParseError (Model fmt))
    (expected : Model.ParseError) : Bool :=
  match result with
  | .ok _ => false
  | .error actual => decide (actual = expected)

def formatRoundTrips {fmt : FloatFormat} (value : Model fmt) : Bool :=
  match Model.parseNearest fmt (Model.format value) with
  | .error _ => false
  | .ok parsed =>
      if Model.isNaN value then Model.isNaN parsed
      else sameBits parsed value

def failExactParsing : Thunk Nat := ⟨fun _ =>
  let finite := FloatFormat.e2m1
  let checks :=
    [ parsedAs (Model.parseNearest f32 " 1.5 ")
        (Model.ofNatBits (fmt := f32) 0x3fc00000)
    , parsedAs (Model.parse f32 .towardZero "0.1")
        (Model.ofNatBits (fmt := f32) 0x3dcccccc)
    , parsedAs (Model.parse f32 .towardNegativeInfinity "-0.1")
        (Model.ofNatBits (fmt := f32) 0xbdcccccd)
    , parsedAs (Model.parseNearest f32 "3 * 2^-1")
        (Model.ofNatBits (fmt := f32) 0x3fc00000)
    , parsedAs (Model.parseNearest f32 "inf") (Model.posInf f32)
    , parsedAs (Model.parseNearest f32 "-inf") (Model.negInf f32)
    , parsedAs (Model.parseNearest f32 "nan") (Model.canonicalNaN f32)
    , failedWith (Model.parseNearest f32 "   ") .emptyInput
    , failedWith (Model.parseNearest f32 "1.2.3") (.invalidSyntax "1.2.3")
    , failedWith (Model.parseNearest finite "inf") (.unsupportedInfinity false)
    , failedWith (Model.parseNearest finite "-inf") (.unsupportedInfinity true)
    , failedWith (Model.parseNearest finite "nan") .unsupportedNaN
    ]
  countFailures checks + countWhereFailures f16Samples formatRoundTrips⟩

/-! ## signed zero and IEEE exception edge cases -/

def failSignedZeroModes : Thunk Nat := ⟨fun _ =>
  let fmt := FloatFormat.binary32
  let one := Model.posOne fmt
  let negOne := Model.negOne fmt
  countWhereFailures Model.IEEERoundingMode.all fun mode =>
    let expected :=
      if mode == .towardNegativeInfinity then Model.negZero fmt else Model.posZero fmt
    sameBits (Model.addWithRounding mode one negOne) expected &&
    sameBits (Model.addWithRounding mode (Model.negZero fmt)
      (Model.negZero fmt)) (Model.negZero fmt)⟩

def failOverflowModes : Thunk Nat := ⟨fun _ =>
  let fmt := FloatFormat.binary32
  let maximum := Model.posMaxFinite fmt
  let negativeMaximum := Model.negMaxFinite fmt
  let increment := Model.posMinSubnormal fmt
  let negativeIncrement := Model.negMinSubnormal fmt
  -- A value just beyond `maxFinite` does not necessarily overflow. IEEE overflow is determined
  -- after rounding to the destination precision with an unbounded exponent range. Directions
  -- toward the finite side therefore keep both the finite result and a clear overflow flag here.
  let checks :=
    [ outcomeIs (Model.addWithStatus maximum increment .nearestEven)
        maximum false false false false true
    , outcomeIs (Model.addWithStatus maximum increment .towardZero)
        maximum false false false false true
    , outcomeIs (Model.addWithStatus maximum increment .towardPositiveInfinity)
        (Model.posInf fmt) false false true false true
    , outcomeIs (Model.addWithStatus maximum increment .towardNegativeInfinity)
        maximum false false false false true
    , outcomeIs (Model.addWithStatus negativeMaximum negativeIncrement .nearestEven)
        negativeMaximum false false false false true
    , outcomeIs (Model.addWithStatus negativeMaximum negativeIncrement .towardZero)
        negativeMaximum false false false false true
    , outcomeIs (Model.addWithStatus negativeMaximum negativeIncrement .towardPositiveInfinity)
        negativeMaximum false false false false true
    , outcomeIs (Model.addWithStatus negativeMaximum negativeIncrement .towardNegativeInfinity)
        (Model.negInf fmt) false false true false true
    , outcomeIs (Model.addWithStatus maximum maximum .nearestEven)
        (Model.posInf fmt) false false true false true
    ]
  countFailures checks⟩

def failUnderflowModes : Thunk Nat := ⟨fun _ =>
  let fmt := FloatFormat.binary32
  let two := Model.roundDyadic fmt { negative := false, significand := 2, exponent := 0 }
  let minimum := Model.posMinSubnormal fmt
  let negativeMinimum := Model.negMinSubnormal fmt
  let tiny := FloatFormat.ieee 2 1
  let half := Model.roundDyadic tiny { negative := false, significand := 1, exponent := -1 }
  -- With two significand bits, upward `sqrt (1/2)` first rounds to the tiny value `3/4` on
  -- the unbounded-exponent grid. Its delivered encoding is the smallest normal value, `1`, but
  -- tininess-after-rounding still raises underflow because the precision-rounded value is tiny.
  let upwardSqrt := Model.sqrtWithStatus half .towardPositiveInfinity
  -- These fused operations land on the smallest normal encoding from just below it. Tininess
  -- after rounding depends on both the direction and the sign, even though the stored result is
  -- normal. Berkeley TestFloat exposed both boundaries during the conformance campaign.
  let negativeFma :=
    Model.fmaWithStatus
      (Model.ofNatBits (fmt := f16) 0x876F)
      (Model.ofNatBits (fmt := f16) 0x1387)
      (Model.ofNatBits (fmt := f16) 0x83FE)
      .towardNegativeInfinity
  let positiveFma :=
    Model.fmaWithStatus
      (Model.ofNatBits (fmt := f16) 0x0001)
      (Model.ofNatBits (fmt := f16) 0xB5E0)
      (Model.ofNatBits (fmt := f16) 0x0400)
      .towardPositiveInfinity
  let checks :=
    [ outcomeIs (Model.divWithStatus minimum two .nearestEven)
        (Model.posZero fmt) false false false true true
    , outcomeIs (Model.divWithStatus minimum two .towardPositiveInfinity)
        minimum false false false true true
    , outcomeIs (Model.divWithStatus minimum two .towardNegativeInfinity)
        (Model.posZero fmt) false false false true true
    , outcomeIs (Model.divWithStatus negativeMinimum two .towardNegativeInfinity)
        negativeMinimum false false false true true
    , outcomeIs (Model.divWithStatus negativeMinimum two .towardPositiveInfinity)
        (Model.negZero fmt) false false false true true
    , outcomeIs negativeFma (Model.ofNatBits (fmt := f16) 0x8400)
        false false false false true
    , outcomeIs positiveFma (Model.ofNatBits (fmt := f16) 0x0400)
        false false false false true
    , outcomeIs upwardSqrt (Model.posOne tiny)
        false false false true true
    ]
  countFailures checks⟩

def failInvalidAndDivideByZero : Thunk Nat := ⟨fun _ =>
  let fmt := FloatFormat.binary32
  let signalingNaN := Model.ofFields fmt false (FloatFormat.expAllOnesNat fmt) 1
  let checks :=
    [ statusIs (Model.divWithStatus (Model.posZero fmt)
        (Model.posZero fmt)).status true false false false false
    , statusIs (Model.divWithStatus (Model.posOne fmt)
        (Model.posZero fmt)).status false true false false false
    , statusIs (Model.mulWithStatus (Model.posInf fmt)
        (Model.posZero fmt)).status true false false false false
    , statusIs (Model.fmaWithStatus (Model.posInf fmt)
        (Model.posZero fmt) (Model.posOne fmt)).status true false false false false
    , statusIs (Model.sqrtWithStatus (Model.negOne fmt)).status
        true false false false false
    , statusIs (Model.addWithStatus signalingNaN (Model.posOne fmt)).status
        true false false false false
    ]
  countFailures checks⟩

/-! ## standard IEEE-style operations -/

/--
Exercise the semantic branches of remainder, integral rounding, power-of-two scaling, exponent
extraction, and quiet sign operations on binary32.
-/
def failStandardOperations : Thunk Nat := ⟨fun _ =>
  let fmt := FloatFormat.binary32
  let integer := fun coefficient : Int =>
    Model.roundDyadic fmt (Numerics.Dyadic.ofScaledInt coefficient 0)
  let half := Model.roundDyadic fmt
    { negative := false, significand := 1, exponent := -1 }
  let oneAndHalf := Model.roundDyadic fmt
    { negative := false, significand := 3, exponent := -1 }
  let negativeOneAndHalf := Model.neg oneAndHalf
  let zero := Model.posZero fmt
  let negativeZero := Model.negZero fmt
  let one := integer 1
  let two := integer 2
  let three := integer 3
  let four := integer 4
  let five := integer 5
  let six := integer 6
  let seven := integer 7
  let eight := integer 8
  let negativeOne := integer (-1)
  let negativeTwo := integer (-2)
  let negativeSeven := integer (-7)
  let quietNaN := Model.canonicalNaN fmt
  let signalingNaN :=
    Model.ofFields fmt false (FloatFormat.expAllOnesNat fmt) 1
  let checks :=
    [ outcomeIs (Model.remainderWithStatus five two)
        one false false false false false
    , outcomeIs (Model.remainderWithStatus seven two)
        negativeOne false false false false false
    , outcomeIs (Model.remainderWithStatus six four)
        negativeTwo false false false false false
    , outcomeIs (Model.remainderWithStatus negativeSeven two)
        one false false false false false
    , outcomeIs (Model.remainderWithStatus seven negativeTwo)
        negativeOne false false false false false
    , outcomeIs (Model.remainderWithStatus negativeZero two)
        negativeZero false false false false false
    , outcomeIs (Model.remainderWithStatus five (Model.posInf fmt))
        five false false false false false
    , outcomeIs (Model.remainderWithStatus (Model.posInf fmt) two)
        (Model.invalidResult fmt) true false false false false
    , outcomeIs (Model.remainderWithStatus one zero)
        (Model.invalidResult fmt) true false false false false
    , outcomeIs (Model.remainderWithStatus signalingNaN two)
        (Model.quietNaN signalingNaN) true false false false false
    , outcomeIs (Model.remainderWithStatus quietNaN two)
        quietNaN false false false false false
    , outcomeIs
        (Model.roundToIntegralExactWithStatus oneAndHalf .nearestEven)
        two false false false false true
    , outcomeIs
        (Model.roundToIntegralExactWithStatus oneAndHalf .towardZero)
        one false false false false true
    , outcomeIs
        (Model.roundToIntegralExactWithStatus negativeOneAndHalf
          .towardNegativeInfinity)
        negativeTwo false false false false true
    , outcomeIs
        (Model.roundToIntegralExactWithStatus three .nearestEven)
        three false false false false false
    , outcomeIs (Model.scaleBWithStatus one 3 .nearestEven)
        eight false false false false false
    , outcomeIs (Model.logBWithStatus eight)
        three false false false false false
    , outcomeIs (Model.logBWithStatus half)
        negativeOne false false false false false
    , outcomeIs (Model.logBWithStatus zero)
        (Model.negInf fmt) false true false false false
    , outcomeIs (Model.logBWithStatus (Model.posInf fmt))
        (Model.posInf fmt) false false false false false
    , sameBits (Model.copySign seven negativeOne) negativeSeven
    , sameBits (Model.abs negativeSeven) seven
    , sameBits (Model.nextUp zero) (Model.posMinSubnormal fmt)
    , sameBits (Model.nextDown zero) (Model.negMinSubnormal fmt)
    , sameBits (Model.minNum quietNaN two) two
    , sameBits (Model.maxNum two quietNaN) two
    , sameBits (Model.minNum signalingNaN two) (Model.quietNaN signalingNaN)
    , sameBits (Model.minimumNumber signalingNaN two) two
    , sameBits (Model.maximumNumber two signalingNaN) two
    , sameBits (Model.minimumNumber quietNaN two) two
    , outcomeIs (Model.minimumNumberWithStatus signalingNaN two)
        two true false false false false
    , outcomeIs (Model.minimumNumberWithStatus quietNaN two)
        two false false false false false
    , outcomeIs (Model.nextUpWithStatus signalingNaN)
        (Model.quietNaN signalingNaN) true false false false false
    ]
  countFailures checks⟩

/-! ## correctly rounded reductions -/

/-- Exact one-round sum and dot checks across finite and exceptional boundary cases. -/
def failCorrectlyRoundedReductions : Thunk Nat := ⟨fun _ =>
  let fmt := FloatFormat.binary32
  let half := FloatFormat.binary16
  let finiteOnly := FloatFormat.e4m3fn
  let one := Model.posOne fmt
  let large : Model fmt := Model.ofNatBits 0x4b800000
  let negativeLarge : Model fmt := Model.ofNatBits 0xcb800000
  let maximum := Model.posMaxFinite fmt
  let minimum := Model.posMinSubnormal fmt
  let signalingNaN :=
    Model.ofFields fmt false (FloatFormat.expAllOnesNat fmt) 1
  let quietNaN :=
    Model.ofFields fmt false (FloatFormat.expAllOnesNat fmt)
      (Model.pow2 (fmt.fracWidth - 1) + 7)
  let cancellation := #[large, one, negativeLarge]
  let productLeft := #[large, one, large]
  let productRight := #[one, one, Model.negOne fmt]
  let checks :=
    [ outcomeIs
        (Model.sumWithStatus fmt cancellation .nearestEven)
        one false false false false false
    , outcomeIs
        (Model.sumWithStatus fmt #[one, Model.negOne fmt] .nearestEven)
        (Model.posZero fmt) false false false false false
    , outcomeIs
        (Model.sumWithStatus fmt #[one, Model.negOne fmt] .towardNegativeInfinity)
        (Model.negZero fmt) false false false false false
    , outcomeIs
        (Model.sumWithStatus fmt #[Model.negZero fmt, Model.negZero fmt] .nearestEven)
        (Model.negZero fmt) false false false false false
    , outcomeIs
        (Model.sumWithStatus fmt #[maximum, maximum] .nearestEven)
        (Model.posInf fmt) false false true false true
    , outcomeIs
        (Model.sumWithStatus half #[minimum] .nearestEven)
        (Model.posZero half) false false false true true
    , outcomeIs
        (Model.sumWithStatus half #[minimum] .towardPositiveInfinity)
        (Model.posMinSubnormal half) false false false true true
    , outcomeIs
        (Model.sumWithStatus half #[minimum] .towardZero)
        (Model.posZero half) false false false true true
    , outcomeIs
        (Model.sumWithStatus fmt #[Model.posInf fmt, one] .nearestEven)
        (Model.posInf fmt) false false false false false
    , outcomeIs
        (Model.sumWithStatus finiteOnly #[Model.posInf fmt, one] .nearestEven)
        (Model.ofNatBits 0x7f) false false true false true
    , outcomeIs
        (Model.sumWithStatus finiteOnly #[Model.negInf fmt] .nearestEven)
        (Model.ofNatBits 0x7f) false false true false true
    , statusIs
        (Model.sumWithStatus fmt #[Model.posInf fmt, Model.negInf fmt]
          .nearestEven).status
        true false false false false
    , outcomeIs
        (Model.sumWithStatus fmt #[quietNaN, signalingNaN] .nearestEven)
        (Model.quietNaN signalingNaN) true false false false false
    , outcomeIs
        (Model.sumWithStatus fmt #[quietNaN, one] .nearestEven)
        quietNaN false false false false false
    , match Model.dotWithStatus fmt productLeft productRight .nearestEven with
      | .ok outcome =>
          outcomeIs outcome one false false false false false
      | .error _ => false
    , match Model.dotWithStatus fmt #[Model.posZero fmt] #[Model.posInf fmt]
          .nearestEven with
      | .ok outcome =>
          statusIs outcome.status true false false false false
      | .error _ => false
    , match Model.dotWithStatus fmt #[one, one] #[one] .nearestEven with
      | .error (.lengthMismatch 2 1) => true
      | _ => false
    ]
  countFailures checks⟩

/-! ## mixed precision -/

/-- Demo vectors stored directly in bfloat16: `[1.0, 1.0] · [1.0, 1.0]`. -/
def mixedXs : Array (Model bf16) :=
  #[Model.ofNatBits 0x3F80, Model.ofNatBits 0x3F80]

def mixedYs : Array (Model bf16) :=
  #[Model.ofNatBits 0x3F80, Model.ofNatBits 0x3F80]

def bf16x32Policy : SitePolicy :=
  SitePolicy.mixedStoreProductAcc bf16 FloatFormat.binary32

/-- Golden result for the bfloat16-storage, binary32-accumulator regression case. -/
def mixedDotGolden : UInt32 := 0x40000000

def failMixedBf16Dot : Thunk Nat := ⟨fun _ =>
  match Model.dotSequential bf16x32Policy mixedXs mixedYs with
  | .error _ => 1
  | .ok got => failureCount (got.toNatBits == mixedDotGolden.toNat)⟩

/-- A sequential dot product must reject unequal input lengths rather than truncate them. -/
def failMixedBf16DotLengthMismatch : Thunk Nat := ⟨fun _ =>
  match Model.dotSequential bf16x32Policy mixedXs #[mixedYs[0]!] with
  | .error (.lengthMismatch 2 1) => 0
  | _ => 1⟩

def failMixedMulAccStep : Thunk Nat := ⟨fun _ =>
  let acc0 := Model.posZero f32
  let step := Model.mulAcc bf16x32Policy mixedXs[0]! mixedYs[0]! acc0
  failureCount (step.toNatBits == 0x3F800000)⟩

/-! ## malformed input rejection -/

def matmulOne : Model FloatFormat.binary32 :=
  Model.ofNatBits 0x3F800000

def matmulTwo : Model FloatFormat.binary32 :=
  Model.ofNatBits 0x40000000

def failValidMatmul : Thunk Nat := ⟨fun _ =>
  match matmulUniform FloatFormat.binary32
      #[#[matmulOne, matmulTwo]] #[#[matmulOne], #[matmulOne]] with
  | .error _ => 1
  | .ok result =>
      failureCount <|
        result.size == 1 && result[0]!.size == 1 &&
          (result[0]!)[0]!.toNatBits == 0x40400000⟩

def failMatmulInnerMismatch : Thunk Nat := ⟨fun _ =>
  match matmulUniform FloatFormat.binary32 #[#[matmulOne, matmulTwo]] #[#[matmulOne]] with
  | .error (.innerDimensionMismatch 2 1) => 0
  | _ => 1⟩

def failMatmulRaggedLeft : Thunk Nat := ⟨fun _ =>
  match matmulUniform FloatFormat.binary32
      #[#[matmulOne], #[matmulOne, matmulTwo]] #[#[matmulOne]] with
  | .error (.raggedLeft 1) => 0
  | _ => 1⟩

def failMatmulRaggedRight : Thunk Nat := ⟨fun _ =>
  match matmulUniform FloatFormat.binary32
      #[#[matmulOne, matmulTwo]] #[#[matmulOne], #[]] with
  | .error (.raggedRight 1) => 0
  | _ => 1⟩

def failZeroDenominatorRounders : Thunk Nat := ⟨fun _ =>
  let generic := Model.roundRat FloatFormat.binary32 false 1 0
  failureCount (Model.isNaN generic)⟩

/-! ## Complete-format model policies -/

/--
Check generated zero, invalid, overflow, and adjacency results for every encoding policy.

These checks exercise the public logical `Model` operations. They do not call the configured
`NativeFPU.Unchecked` host operations. `Conformance.BinaryInterchange.NativeExecution` separately
samples that opt-in API and the certified public operations; matching host values do not prove a
refinement theorem.
-/
def failFormatPolicies : Thunk Nat := ⟨fun _ =>
  let fnuz := FloatFormat.e4m3fnuz
  let fnuzZero := Model.zero fnuz false
  let fnuzNaN := Model.invalidResult fnuz
  let fnuzMax := Model.posMaxFinite fnuz
  let fnuzNegMax := Model.negMaxFinite fnuz
  let fn := FloatFormat.e4m3fn
  let fnZero := Model.zero fn false
  let finite := FloatFormat.e2m1
  let finiteZero := Model.zero finite false
  let finiteMax := Model.posMaxFinite finite
  let finiteNegMax := Model.negMaxFinite finite
  let ieee := FloatFormat.binary32
  let fnMidpoint := Model.overflowMidpoint fn
  let fnNegativeMidpoint := { fnMidpoint with negative := true }
  let fnOverflowLimit := Model.overflowLimit fn
  let fnAboveMidpoint : Numerics.Dyadic :=
    { negative := false
      significand := 2 * fnMidpoint.significand + 1
      exponent := fnMidpoint.exponent - 1 }
  let fnuzMidpoint := Model.overflowMidpoint fnuz
  let finiteMidpoint := Model.overflowMidpoint finite
  let checks :=
    [ (Model.neg fnuzZero).toNatBits == 0x00
    , (Model.neg fnuzNaN).toNatBits == 0x80
    , (Model.mul (Model.negOne fnuz) fnuzZero).toNatBits == 0x00
    , (Model.div (Model.posOne fnuz) fnuzZero).toNatBits == 0x80
    , (Model.div fnuzZero fnuzZero).toNatBits == 0x80
    , (Model.roundRat fnuz false 1 0).toNatBits == 0x80
    , (Model.nextUp fnuzZero).toNatBits == 0x01
    , (Model.nextDown fnuzZero).toNatBits == 0x81
    , Model.nextUp (Model.negMinSubnormal fnuz) == fnuzZero
    , Model.nextUp fnuzMax == fnuzMax
    , Model.nextDown fnuzNegMax == fnuzNegMax
    , (Model.div (Model.posOne fn) fnZero).toNatBits == 0x7f
    , (Model.div fnZero fnZero).toNatBits == 0x7f
    , (Model.roundRat fn false 1 0).toNatBits == 0x7f
    , Model.nextUp (Model.posMaxFinite fn) == Model.posMaxFinite fn
    , Model.nextDown (Model.negMaxFinite fn) == Model.negMaxFinite fn
    , (Model.div (Model.posOne finite) finiteZero).toNatBits == 0x07
    , (Model.div (Model.negOne finite) finiteZero).toNatBits == 0x0f
    , (Model.div finiteZero finiteZero).toNatBits == 0x00
    , (Model.roundRat finite false 1 0).toNatBits == 0x00
    , (Model.roundDyadic finite
        { negative := false, significand := 1, exponent := 100 }).toNatBits == 0x07
    , (Model.roundDyadic finite
        { negative := true, significand := 1, exponent := 100 }).toNatBits == 0x0f
    , (Model.sqrt (Model.negOne finite)).toNatBits == 0x00
    , Model.nextUp finiteMax == finiteMax
    , Model.nextDown finiteNegMax == finiteNegMax
    , Model.isInf
        (Model.div (Model.posOne ieee) (Model.zero ieee false))
    , Model.isNaN
        (Model.div (Model.zero ieee false) (Model.zero ieee false))
    , !(Model.dyadicRoundingOverflows fn .nearestEven fnMidpoint)
    , Model.dyadicRoundingOverflows fn .nearestEven fnAboveMidpoint
    , !(Model.dyadicRoundingOverflows fn .towardZero fnMidpoint)
    , !(Model.dyadicRoundingOverflows fn .towardNegativeInfinity fnMidpoint)
    , Model.dyadicRoundingOverflows fn .towardPositiveInfinity fnMidpoint
    , !(Model.dyadicRoundingOverflows fn .towardZero fnNegativeMidpoint)
    , !(Model.dyadicRoundingOverflows fn .towardPositiveInfinity fnNegativeMidpoint)
    , Model.dyadicRoundingOverflows fn .towardNegativeInfinity fnNegativeMidpoint
    , Model.dyadicRoundingOverflows fn .towardZero fnOverflowLimit
    , Model.dyadicRoundingOverflows fnuz .nearestEven fnuzMidpoint
    , Model.dyadicRoundingOverflows finite .nearestEven finiteMidpoint
    , !(Model.rationalRoundingOverflowsScaled fn .nearestEven false
        fnMidpoint.significand 1 fnMidpoint.exponent)
    , !(Model.rationalRoundingOverflowsScaled fn .towardZero false
        fnMidpoint.significand 1 fnMidpoint.exponent)
    , Model.rationalRoundingOverflowsScaled fn .towardPositiveInfinity false
        fnMidpoint.significand 1 fnMidpoint.exponent
    , !(Model.rationalRoundingOverflowsScaled fn .towardPositiveInfinity true
        fnMidpoint.significand 1 fnMidpoint.exponent)
    , Model.rationalRoundingOverflowsScaled fn .towardNegativeInfinity true
        fnMidpoint.significand 1 fnMidpoint.exponent
    , Model.rationalRoundingOverflowsScaled fn .towardZero false
        fnOverflowLimit.significand 1 fnOverflowLimit.exponent
    , Model.rationalRoundingOverflowsScaled fnuz .nearestEven false
        fnuzMidpoint.significand 1 fnuzMidpoint.exponent
    ]
  countFailures checks⟩

/-! ## aggregate -/

/-- Named counters for every deterministic descriptor-model regression in this module. -/
def failureRows : Thunk (List (String × Nat)) := ⟨fun _ =>
  [ ("bf16CastIdempotent", failBf16CastIdempotent.get)
  , ("bf16Classifiers", failBf16Classifiers.get)
  , ("f16CastIdempotent", failF16CastIdempotent.get)
  , ("f16Classifiers", failF16Classifiers.get)
  , ("smallFormatSqrt", failSmallFormatSqrt.get)
  , ("tinyDirectedEnclosures", failTinyDirectedEnclosures.get)
  , ("exactParsing", failExactParsing.get)
  , ("signedZeroModes", failSignedZeroModes.get)
  , ("overflowModes", failOverflowModes.get)
  , ("underflowModes", failUnderflowModes.get)
  , ("invalidAndDivideByZero", failInvalidAndDivideByZero.get)
  , ("standardOperations", failStandardOperations.get)
  , ("correctlyRoundedReductions", failCorrectlyRoundedReductions.get)
  , ("mixedBf16Dot", failMixedBf16Dot.get)
  , ("mixedBf16DotLengthMismatch", failMixedBf16DotLengthMismatch.get)
  , ("mixedMulAccStep", failMixedMulAccStep.get)
  , ("validMatmul", failValidMatmul.get)
  , ("matmulInnerMismatch", failMatmulInnerMismatch.get)
  , ("matmulRaggedLeft", failMatmulRaggedLeft.get)
  , ("matmulRaggedRight", failMatmulRaggedRight.get)
  , ("zeroDenominatorRounders", failZeroDenominatorRounders.get)
  , ("formatPolicies", failFormatPolicies.get)
  , ("intervalTinyPairs", ExecFloatInterval.failTinyPairEnclosures.get)
  , ("intervalTinyUnary", ExecFloatInterval.failTinyUnaryEnclosures.get)
  , ("intervalBinary32Representative",
      ExecFloatInterval.failBinary32RepresentativeEnclosures.get)
  , ("scaledRationalStandardFormats",
      ExecFloatScaledRationals.failStandardFormats.get)
  , ("scaledRationalCustomWideFormat",
      ExecFloatScaledRationals.failCustomWideFormat.get)
  ]⟩

/-- Collect model and enclosure failures when the core suite runs. -/
def report : Thunk ReportSection := ⟨fun _ =>
  ReportSection.ofRows "binary-interchange model" (failureRows.get)⟩

end FloatLibTests.Regression.BinaryInterchange.Model
