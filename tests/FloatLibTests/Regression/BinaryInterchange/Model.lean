/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.MixedPrecision.Matmul
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.MixedPrecision.Accumulation
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.BoundedParsing
public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.Formatting
public import FloatLib.Floats.Formats.BinaryInterchange.DType.Cast
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
- **ternary values**: MPFR-oriented comparison of each delivered value with the exact result
- **algebraic operations**: signed zeros, exact powers and roots, and norms whose squares overflow
- **character input**: exact decimal and radix-two parsing, errors, and formatting round trips
- **mixed precision**: golden bf16-storage / binary32-accumulator cases

`totalFailures = 0` means every deterministic regression in this module passed.
-/

@[expose] public section

-- Keep lazy regression bodies out of module initialization, including closed subexpressions.
-- This affects native code generation only. Elaboration and kernel checking are unchanged.
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
      dyadicLowerEncloses exact (Model.add x y (mode := .down)) &&
      dyadicUpperEncloses exact (Model.add x y (mode := .up))
  | _, _ => true

def mulEnclosed {fmt : FloatFormat} (x y : Model fmt) : Bool :=
  match Model.toDyadic? x, Model.toDyadic? y with
  | some left, some right =>
      let exact : Numerics.Dyadic :=
        { negative := Bool.xor left.negative right.negative
          significand := left.significand * right.significand
          exponent := left.exponent + right.exponent }
      dyadicLowerEncloses exact (Model.mul x y (mode := .down)) &&
      dyadicUpperEncloses exact (Model.mul x y (mode := .up))
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
            (Model.div x y (mode := .down)) &&
          rationalUpperEnclosesScaled sign left.significand right.significand exponentDifference
            (Model.div x y (mode := .up))
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
        match Model.toDyadic? (Model.sqrt x (mode := .down)),
            Model.toDyadic? (Model.sqrt x (mode := .up)) with
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
  match Model.parse fmt (Model.format value) with
  | .error _ => false
  | .ok parsed =>
      if Model.isNaN value then Model.isNaN parsed
      else sameBits parsed value

def failExactParsing : Thunk Nat := ⟨fun _ =>
  let finite := FloatFormat.e2m1
  let checks :=
    [ parsedAs (Model.parse f32 " 1.5 ")
        (Model.ofNatBits (fmt := f32) 0x3fc00000)
    , parsedAs (Model.parse f32 "0.1" (mode := .towardZero))
        (Model.ofNatBits (fmt := f32) 0x3dcccccc)
    , parsedAs (Model.parse f32 "-0.1" (mode := .down))
        (Model.ofNatBits (fmt := f32) 0xbdcccccd)
    , parsedAs (Model.parse f32 "3 * 2^-1")
        (Model.ofNatBits (fmt := f32) 0x3fc00000)
    , parsedAs (Model.parse f32 "inf") (Model.posInf f32)
    , parsedAs (Model.parse f32 "-inf") (Model.negInf f32)
    , parsedAs (Model.parse f32 "nan") (Model.canonicalNaN f32)
    , failedWith (Model.parse f32 "   ") .emptyInput
    , failedWith (Model.parse f32 "1.2.3") (.invalidSyntax "1.2.3")
    , failedWith (Model.parse finite "inf") (.unsupportedInfinity false)
    , failedWith (Model.parse finite "-inf") (.unsupportedInfinity true)
    , failedWith (Model.parse finite "nan") .unsupportedNaN
    ]
  countFailures checks + countWhereFailures f16Samples formatRoundTrips⟩

/-! ## signed zero and IEEE exception edge cases -/

def failSignedZeroModes : Thunk Nat := ⟨fun _ =>
  let fmt := FloatFormat.binary32
  let one := Model.posOne fmt
  let negOne := Model.negOne fmt
  countWhereFailures Model.IEEERoundingMode.all fun mode =>
    let expected :=
      if mode == .down then Model.negZero fmt else Model.posZero fmt
    sameBits (Model.add one negOne (mode := mode)) expected &&
    sameBits (Model.add (Model.negZero fmt)
      (Model.negZero fmt) (mode := mode)) (Model.negZero fmt)⟩

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
    [ outcomeIs (Model.add maximum increment (mode := .nearest) (status := true))
        maximum false false false false true .lt
    , outcomeIs (Model.add maximum increment (mode := .towardZero) (status := true))
        maximum false false false false true .lt
    , outcomeIs (Model.add maximum increment (mode := .up) (status := true))
        (Model.posInf fmt) false false true false true .gt
    , outcomeIs (Model.add maximum increment (mode := .down) (status := true))
        maximum false false false false true .lt
    , outcomeIs (Model.add negativeMaximum negativeIncrement (mode := .nearest) (status := true))
        negativeMaximum false false false false true .gt
    , outcomeIs (Model.add negativeMaximum negativeIncrement (mode := .towardZero) (status := true))
        negativeMaximum false false false false true .gt
    , outcomeIs (Model.add negativeMaximum negativeIncrement (mode := .up) (status := true))
        negativeMaximum false false false false true .gt
    , outcomeIs (Model.add negativeMaximum negativeIncrement (mode := .down) (status := true))
        (Model.negInf fmt) false false true false true .lt
    , outcomeIs (Model.add maximum maximum (mode := .nearest) (status := true))
        (Model.posInf fmt) false false true false true .gt
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
  let upwardSqrt := Model.sqrt half (mode := .up) (status := true)
  -- These fused operations land on the smallest normal encoding from just below it. Tininess
  -- after rounding depends on both the direction and the sign, even though the stored result is
  -- normal. Berkeley TestFloat exposed both boundaries during the conformance campaign.
  let negativeFma :=
    Model.fma
      (Model.ofNatBits (fmt := f16) 0x876F)
      (Model.ofNatBits (fmt := f16) 0x1387)
      (Model.ofNatBits (fmt := f16) 0x83FE) (mode := .down) (status := true)
  let positiveFma :=
    Model.fma
      (Model.ofNatBits (fmt := f16) 0x0001)
      (Model.ofNatBits (fmt := f16) 0xB5E0)
      (Model.ofNatBits (fmt := f16) 0x0400) (mode := .up) (status := true)
  let checks :=
    [ outcomeIs (Model.div minimum two (mode := .nearest) (status := true))
        (Model.posZero fmt) false false false true true .lt
    , outcomeIs (Model.div minimum two (mode := .up) (status := true))
        minimum false false false true true .gt
    , outcomeIs (Model.div minimum two (mode := .down) (status := true))
        (Model.posZero fmt) false false false true true .lt
    , outcomeIs (Model.div negativeMinimum two (mode := .down) (status := true))
        negativeMinimum false false false true true .lt
    , outcomeIs (Model.div negativeMinimum two (mode := .up) (status := true))
        (Model.negZero fmt) false false false true true .gt
    , outcomeIs negativeFma (Model.ofNatBits (fmt := f16) 0x8400)
        false false false false true .lt
    , outcomeIs positiveFma (Model.ofNatBits (fmt := f16) 0x0400)
        false false false false true .gt
    , outcomeIs upwardSqrt (Model.posOne tiny)
        false false false true true .gt
    ]
  countFailures checks⟩

def failInvalidAndDivideByZero : Thunk Nat := ⟨fun _ =>
  let fmt := FloatFormat.binary32
  let signalingNaN := Model.ofFields fmt false (FloatFormat.expAllOnesNat fmt) 1
  let checks :=
    [ statusIs (Model.div (Model.posZero fmt)
        (Model.posZero fmt) (status := true)).status true false false false false
    , statusIs (Model.div (Model.posOne fmt)
        (Model.posZero fmt) (status := true)).status false true false false false
    , statusIs (Model.mul (Model.posInf fmt)
        (Model.posZero fmt) (status := true)).status true false false false false
    , statusIs (Model.fma (Model.posInf fmt)
        (Model.posZero fmt) (Model.posOne fmt) (status := true)).status true false false false false
    , statusIs (Model.sqrt (Model.negOne fmt) (status := true)).status
        true false false false false
    , statusIs (Model.add signalingNaN (Model.posOne fmt) (status := true)).status
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
    [ outcomeIs (Model.remainder five two (status := true))
        one false false false false false .eq
    , outcomeIs (Model.remainder seven two (status := true))
        negativeOne false false false false false .eq
    , outcomeIs (Model.remainder six four (status := true))
        negativeTwo false false false false false .eq
    , outcomeIs (Model.remainder negativeSeven two (status := true))
        one false false false false false .eq
    , outcomeIs (Model.remainder seven negativeTwo (status := true))
        negativeOne false false false false false .eq
    , outcomeIs (Model.remainder negativeZero two (status := true))
        negativeZero false false false false false .eq
    , outcomeIs (Model.remainder five (Model.posInf fmt) (status := true))
        five false false false false false .eq
    , outcomeIs (Model.remainder (Model.posInf fmt) two (status := true))
        (Model.invalidResult fmt) true false false false false .eq
    , outcomeIs (Model.remainder one zero (status := true))
        (Model.invalidResult fmt) true false false false false .eq
    , outcomeIs (Model.remainder signalingNaN two (status := true))
        (Model.quietNaN signalingNaN) true false false false false .eq
    , outcomeIs (Model.remainder quietNaN two (status := true))
        quietNaN false false false false false .eq
    , outcomeIs
        (Model.roundToIntegral oneAndHalf .nearest (status := true))
        two false false false false true .gt
    , outcomeIs
        (Model.roundToIntegral oneAndHalf .towardZero (status := true))
        one false false false false true .lt
    , outcomeIs
        (Model.roundToIntegral negativeOneAndHalf
          .down (status := true))
        negativeTwo false false false false true .lt
    , outcomeIs
        (Model.roundToIntegral three .nearest (status := true))
        three false false false false false .eq
    , outcomeIs (Model.scale one 3 .nearest (status := true))
        eight false false false false false .eq
    , outcomeIs (Model.binaryExponent eight (status := true))
        three false false false false false .eq
    , outcomeIs (Model.binaryExponent half (status := true))
        negativeOne false false false false false .eq
    , outcomeIs (Model.binaryExponent zero (status := true))
        (Model.negInf fmt) false true false false false .eq
    , outcomeIs (Model.binaryExponent (Model.posInf fmt) (status := true))
        (Model.posInf fmt) false false false false false .eq
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
    , outcomeIs (Model.minimumNumber signalingNaN two (status := true))
        two true false false false false .eq
    , outcomeIs (Model.minimumNumber quietNaN two (status := true))
        two false false false false false .eq
    , outcomeIs (Model.nextUp signalingNaN (status := true))
        (Model.quietNaN signalingNaN) true false false false false .eq
    ]
  countFailures checks⟩

/-! ## ternary values -/

/--
Check the ternary value, MPFR's comparison of the delivered value with the exact result, over the
conventions it uses: an inexact quotient under every direction, overflow delivered as infinity and
saturated, an exact infinity delivered as itself, saturated, or as an overflow NaN, NaN operands,
division by zero with and without infinities, cancellation, square root, a rounded `logB`, signed
zero in FNUZ, exact casts, integral rounding that saturates to its own input, and the default
outcome.
-/
def failTernaryValues : Thunk Nat := ⟨fun _ =>
  let fmt := FloatFormat.binary32
  let integer := fun coefficient : Int =>
    Model.roundDyadic fmt (Numerics.Dyadic.ofScaledInt coefficient 0)
  let one := integer 1
  let negativeOne := integer (-1)
  let two := integer 2
  let three := integer 3
  let four := integer 4
  let maximum := Model.posMaxFinite fmt
  let negativeMaximum := Model.negMaxFinite fmt
  let quietNaN := Model.canonicalNaN fmt
  let signalingNaN := Model.ofFields fmt false (FloatFormat.expAllOnesNat fmt) 1
  let thirdAbove : Model fmt := Model.ofNatBits 0x3eaaaaab
  let thirdBelow : Model fmt := Model.ofNatBits 0x3eaaaaaa
  let rootTwoBelow : Model fmt := Model.ofNatBits 0x3fb504f3
  let rootTwoAbove : Model fmt := Model.ofNatBits 0x3fb504f4
  let e4 := FloatFormat.e4m3fn
  let fnuz := FloatFormat.e4m3fnuz
  let e2 := FloatFormat.e2m3
  let lowPrecision := FloatFormat.ieee 5 1
  let narrowCustom := FloatFormat.custom 5 7 12 .ieee
  let wideCustom := FloatFormat.custom 5 10 12 .ieee
  let overflowInexact := (false, false, true, false, true)
  let inexact := (false, false, false, false, true)
  let check {target : FloatFormat} (outcome : Model.IEEEOutcome target) (expected : Model target)
      (flags : Bool × Bool × Bool × Bool × Bool) (ternary : Ordering) : Bool :=
    let (invalid, divideByZero, overflow, underflow, inexactFlag) := flags
    outcomeIs outcome expected invalid divideByZero overflow underflow inexactFlag ternary
  -- One third and minus one third: a directed or nearest neighbour above or below the quotient.
  let thirds := Model.IEEERoundingMode.all.map fun mode =>
    let (positive, positiveTernary, negative, negativeTernary) :
        Model fmt × Ordering × Model fmt × Ordering :=
      match mode with
      | .towardZero => (thirdBelow, .lt, Model.neg thirdBelow, .gt)
      | .down => (thirdBelow, .lt, Model.neg thirdAbove, .lt)
      | .up => (thirdAbove, .gt, Model.neg thirdBelow, .gt)
      | .nearest | .nearestAway | .away =>
          (thirdAbove, .gt, Model.neg thirdAbove, .lt)
    check (Model.div one three (mode := mode) (status := true)) positive inexact positiveTernary &&
      check (Model.div negativeOne three (mode := mode) (status := true)) negative inexact
          negativeTernary
  countFailures thirds +
  countFailures
    [ -- Overflow to infinity lies above a positive exact value; saturation lies below it.
      check (Model.mul maximum two (mode := .nearest) (status := true)) (Model.posInf fmt)
          overflowInexact .gt
    , check (Model.mul maximum two (mode := .towardZero) (status := true)) maximum
        overflowInexact .lt
    , check (Model.mul negativeMaximum two (mode := .nearest) (status := true)) (Model.negInf fmt)
        overflowInexact .lt
    , check (Model.mul negativeMaximum two (mode := .towardZero) (status := true)) negativeMaximum
        overflowInexact .gt
      -- E4M3FN overflows to its NaN word, which takes the sign of the exact value.
    , check (Model.cast fmt e4 (integer 500) .nearest (status := true)) (Model.ofNatBits 0x7f)
        overflowInexact .gt
    , check (Model.cast fmt e4 (integer 500) .towardZero (status := true)) (Model.ofNatBits 0x7e)
        overflowInexact .lt
    , check (Model.cast fmt e4 (integer (-500)) .nearest (status := true)) (Model.ofNatBits 0xff)
        overflowInexact .lt
      -- An exact infinity is `.eq` when kept, and otherwise `.lt` for `+∞` and `.gt` for `-∞`.
    , check (Model.cast fmt .binary16 (Model.posInf fmt) .nearest (status := true))
        (Model.posInf .binary16) (false, false, false, false, false) .eq
    , check (Model.cast fmt e4 (Model.posInf fmt) .nearest (status := true)) (Model.ofNatBits 0x7f)
        overflowInexact .lt
    , check (Model.cast fmt e4 (Model.negInf fmt) .nearest (status := true)) (Model.ofNatBits 0xff)
        overflowInexact .gt
    , check (Model.cast fmt fnuz (Model.posInf fmt) .nearest (status := true))
        (Model.ofNatBits 0x80) overflowInexact .lt
    , check (Model.cast fmt fnuz (Model.negInf fmt) .nearest (status := true))
        (Model.ofNatBits 0x80) overflowInexact .gt
    , check (Model.cast fmt e2 (Model.posInf fmt) .nearest (status := true)) (Model.ofNatBits 0x1f)
        overflowInexact .lt
    , check (Model.cast fmt e2 (Model.negInf fmt) .nearest (status := true)) (Model.ofNatBits 0x3f)
        overflowInexact .gt
    , check (Model.sum e2 #[Model.posInf fmt] .nearest (status := true)) (Model.ofNatBits 0x1f)
        overflowInexact .lt
    , check (Model.sum fnuz #[Model.negInf fmt] .nearest (status := true)) (Model.ofNatBits 0x80)
        overflowInexact .gt
      -- NaN operands give the convention `.eq`.
    , check (Model.add quietNaN one (mode := .nearest) (status := true)) quietNaN
        (false, false, false, false, false) .eq
    , check (Model.add signalingNaN one (mode := .towardZero) (status := true))
        (Model.quietNaN signalingNaN)
        (true, false, false, false, false) .eq
      -- Division by zero has an exact infinity. Without infinities the replacement is ordered.
    , check (Model.div one (Model.posZero fmt) (mode := .nearest) (status := true))
        (Model.posInf fmt)
        (false, true, false, false, false) .eq
    , check (Model.div negativeOne (Model.posZero fmt) (mode := .nearest) (status := true))
        (Model.negInf fmt)
        (false, true, false, false, false) .eq
    , check (Model.div (Model.posOne e4) (Model.posZero e4) (mode := .nearest) (status := true))
        (Model.ofNatBits 0x7f) (false, true, false, false, false) .lt
    , check (Model.div (Model.posOne e2) (Model.posZero e2) (mode := .nearest) (status := true))
        (Model.ofNatBits 0x1f) (false, true, false, false, false) .lt
    , check (Model.div (Model.negOne e2) (Model.posZero e2) (mode := .nearest) (status := true))
        (Model.ofNatBits 0x3f) (false, true, false, false, false) .gt
      -- Exact cancellation is exact in every direction.
    , check (Model.add one negativeOne (mode := .nearest) (status := true)) (Model.posZero fmt)
        (false, false, false, false, false) .eq
    , check (Model.add one negativeOne (mode := .down) (status := true)) (Model.negZero fmt)
        (false, false, false, false, false) .eq
      -- Square root compares the square of the delivered root with the radicand.
    , check (Model.sqrt two (mode := .towardZero) (status := true)) rootTwoBelow inexact .lt
    , check (Model.sqrt two (mode := .nearest) (status := true)) rootTwoBelow inexact .lt
    , check (Model.sqrt two (mode := .up) (status := true)) rootTwoAbove inexact .gt
    , check (Model.sqrt four (mode := .towardZero) (status := true)) two
        (false, false, false, false, false) .eq
      -- `logB(2^13)` in `ieee 5 1` rounds the exponent 13 to 12.
    , check
        (Model.binaryExponent
          (Model.roundDyadic lowPrecision { negative := false, significand := 1, exponent := 13 })
            (status := true))
        (Model.roundDyadic lowPrecision (Numerics.Dyadic.ofScaledInt 12 0)) inexact .lt
      -- `logB(0)` is `-∞`. Formats without infinity deliver a NaN or saturate, above it.
    , check (Model.binaryExponent (Model.posZero fmt) (status := true)) (Model.negInf fmt)
        (false, true, false, false, false) .eq
    , check (Model.binaryExponent (Model.posZero e4) (status := true)) (Model.ofNatBits 0xff)
        (false, true, false, false, false) .gt
    , check (Model.binaryExponent (Model.posZero e2) (status := true)) (Model.ofNatBits 0x3f)
        (false, true, false, false, false) .gt
      -- FNUZ has one zero: exact zero is `.eq`, and the zero a negative value rounds to lies
      -- above it.
    , check (Model.add (Model.posOne fnuz) (Model.negOne fnuz) (mode := .nearest) (status := true))
        (Model.posZero fnuz) (false, false, false, false, false) .eq
    , check
        (Model.mul (Model.negMinSubnormal fnuz)
          (Model.roundDyadic fnuz { negative := false, significand := 1, exponent := -1 })
          (status := true))
        (Model.posZero fnuz) (false, false, false, true, true) .gt
      -- Identity casts and compatible widenings are exact, including a custom bias.
    , check (Model.cast fmt fmt thirdAbove .towardZero (status := true)) thirdAbove
        (false, false, false, false, false) .eq
    , check
        (Model.cast .binary16 fmt (Model.ofNatBits (fmt := .binary16) 0x3555)
          .nearest (status := true))
        (Model.cast .binary16 fmt (Model.ofNatBits (fmt := .binary16) 0x3555))
        (false, false, false, false, false) .eq
    , check
        (Model.cast narrowCustom wideCustom
          (Model.roundDyadic narrowCustom { negative := false, significand := 129, exponent := -7 })
          .towardZero (status := true))
        (Model.roundDyadic wideCustom { negative := false, significand := 129, exponent := -7 })
        (false, false, false, false, false) .eq
    , check
        (Model.cast wideCustom narrowCustom
          (Model.roundDyadic wideCustom
            { negative := false, significand := 1025, exponent := -10 })
          .nearest (status := true))
        (Model.posOne narrowCustom) inexact .lt
      -- E2M3 saturates the integer 8 back to its input 7.5: inexact, and equal to the input.
    , check (Model.roundToIntegral (Model.ofNatBits (fmt := e2) 31) .nearest (status := true))
        (Model.ofNatBits 31) overflowInexact .eq
      -- Integer conversion compares with the integer.
    , check
        (ExecDType.intToFloat .binary16
          (FloatLib.Numerics.Representations.FixedInt.ofInt (width := 32) 2049) .nearest
          (status := true))
        (Model.roundDyadic .binary16 (Numerics.Dyadic.ofScaledInt 2048 0)) inexact .lt
      -- The default outcome is an exact positive zero with a clear status.
    , check (default : Model.IEEEOutcome fmt) (Model.posZero fmt)
        (false, false, false, false, false) .eq
    ]⟩

/-! ## single-round algebraic operations -/

/-- Exact identities across widths and biases, including norms beyond intermediate range. -/
def algebraicFormatFailures (fmt : FloatFormat) : Nat :=
  let integer (n : Int) := Model.roundDyadic fmt (Numerics.Dyadic.ofScaledInt n 0)
  let half := Model.roundDyadic fmt ⟨false, 1, -1⟩
  let eighth := Model.roundDyadic fmt ⟨false, 1, -3⟩
  let tiny := Model.posMinSubnormal fmt
  let large := Model.roundDyadic fmt ⟨false, 1, fmt.maxNormalExponent / 2 + 1⟩
  countFailures
    [ sameBits (Model.rsqrt (integer 4)) half
    , sameBits (Model.hypot (integer 3) (integer 4)) (integer 5)
    , sameBits (Model.hypot tiny (Model.posZero fmt)) tiny
    , sameBits (Model.hypot large (Model.posZero fmt)) large
    , sameBits (Model.powInt (integer (-2)) 3) (integer (-8))
    , sameBits (Model.powInt (integer 2) (-3)) eighth
    , sameBits (Model.rootN (integer (-8)) 3) (integer (-2))
    , sameBits (Model.rootN (integer (-8)) (-3)) (Model.neg half)
    , sameBits (Model.rootN tiny 1) tiny
    ]

/-- Signed-zero and exceptional-value rules are independent of the finite arithmetic path. -/
def failAlgebraicOperations : Thunk Nat := ⟨fun _ =>
  let fmt := FloatFormat.binary32
  let positiveZero := Model.posZero fmt
  let negativeZero := Model.negZero fmt
  let positiveInfinity := Model.posInf fmt
  let negativeInfinity := Model.negInf fmt
  let quietNaN := Model.canonicalNaN fmt
  let signalingNaN := Model.ofFields fmt false (FloatFormat.expAllOnesNat fmt) 1
  let specials := countFailures
    [ sameBits (Model.rsqrt positiveZero) positiveInfinity
    , sameBits (Model.rsqrt negativeZero) negativeInfinity
    , sameBits (Model.rsqrt positiveInfinity) positiveZero
    , Model.isNaN (Model.rsqrt (Model.negOne fmt))
    , sameBits (Model.hypot positiveInfinity quietNaN) positiveInfinity
    , sameBits (Model.hypot quietNaN negativeInfinity) positiveInfinity
    , sameBits (Model.hypot positiveInfinity signalingNaN) (Model.quietNaN signalingNaN)
    , sameBits (Model.hypot negativeZero negativeZero) positiveZero
    , sameBits (Model.powInt quietNaN 0) (Model.posOne fmt)
    , sameBits (Model.powInt signalingNaN 0) (Model.quietNaN signalingNaN)
    , sameBits (Model.powInt negativeZero (-3)) negativeInfinity
    , sameBits (Model.powInt negativeZero 3) negativeZero
    , sameBits (Model.rootN negativeZero 2) positiveZero
    , sameBits (Model.rootN negativeZero 3) negativeZero
    , sameBits (Model.rootN negativeZero (-2)) positiveInfinity
    , sameBits (Model.rootN negativeZero (-3)) negativeInfinity
    , Model.isNaN (Model.rootN (Model.negOne fmt) 2)
    , Model.isNaN (Model.rootN (Model.posOne fmt) 0)
    ]
  specials + ([FloatFormat.binary16, .binary32, .binary64, .binary128,
    FloatFormat.custom 5 7 12 .ieee, .e4m3fn, .e4m3fnuz].map
      algebraicFormatFailures).sum⟩

/-! ## correctly rounded reductions -/

/-- Exact one-round sum and dot checks across finite and exceptional boundary cases. -/
def failCorrectlyRoundedReductions : Thunk Nat := ⟨fun _ =>
  let fmt := FloatFormat.binary32
  let half := FloatFormat.binary16
  let finiteWithNaN := FloatFormat.e4m3fn
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
        (Model.sum fmt cancellation .nearest (status := true))
        one false false false false false .eq
    , outcomeIs
        (Model.sum fmt #[one, Model.negOne fmt] .nearest (status := true))
        (Model.posZero fmt) false false false false false .eq
    , outcomeIs
        (Model.sum fmt #[one, Model.negOne fmt] .down (status := true))
        (Model.negZero fmt) false false false false false .eq
    , outcomeIs
        (Model.sum fmt #[Model.negZero fmt, Model.negZero fmt] .nearest (status := true))
        (Model.negZero fmt) false false false false false .eq
    , outcomeIs
        (Model.sum fmt #[maximum, maximum] .nearest (status := true))
        (Model.posInf fmt) false false true false true .gt
    , outcomeIs
        (Model.sum half #[minimum] .nearest (status := true))
        (Model.posZero half) false false false true true .lt
    , outcomeIs
        (Model.sum half #[minimum] .up (status := true))
        (Model.posMinSubnormal half) false false false true true .gt
    , outcomeIs
        (Model.sum half #[minimum] .towardZero (status := true))
        (Model.posZero half) false false false true true .lt
    , outcomeIs
        (Model.sum fmt #[Model.posInf fmt, one] .nearest (status := true))
        (Model.posInf fmt) false false false false false .eq
    , outcomeIs
        (Model.sum finiteWithNaN #[Model.posInf fmt, one] .nearest (status := true))
        (Model.ofNatBits 0x7f) false false true false true .lt
    , outcomeIs
        (Model.sum finiteWithNaN #[Model.negInf fmt] .nearest (status := true))
        (Model.ofNatBits 0xff) false false true false true .gt
    , statusIs
        (Model.sum fmt #[Model.posInf fmt, Model.negInf fmt]
          .nearest (status := true)).status
        true false false false false
    , outcomeIs
        (Model.sum fmt #[quietNaN, signalingNaN] .nearest (status := true))
        (Model.quietNaN signalingNaN) true false false false false .eq
    , outcomeIs
        (Model.sum fmt #[quietNaN, one] .nearest (status := true))
        quietNaN false false false false false .eq
    , match Model.dot fmt productLeft productRight .nearest (status := true) with
      | .ok outcome =>
          outcomeIs outcome one false false false false false .eq
      | .error _ => false
    , match Model.dot fmt #[Model.posZero fmt] #[Model.posInf fmt]
          .nearest (status := true) with
      | .ok outcome =>
          statusIs outcome.status true false false false false
      | .error _ => false
    , match Model.dot fmt #[one, one] #[one] .nearest (status := true) with
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
`NativeFPU.Unchecked` host operations. `Conformance.BinaryInterchange.NativeExecution` samples
that opt-in API and the certified public operations, and matching host values prove no refinement
theorem.
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
    , !(Model.dyadicRoundingOverflows fn .nearest fnMidpoint)
    , Model.dyadicRoundingOverflows fn .nearest fnAboveMidpoint
    , !(Model.dyadicRoundingOverflows fn .towardZero fnMidpoint)
    , !(Model.dyadicRoundingOverflows fn .down fnMidpoint)
    , Model.dyadicRoundingOverflows fn .up fnMidpoint
    , !(Model.dyadicRoundingOverflows fn .towardZero fnNegativeMidpoint)
    , !(Model.dyadicRoundingOverflows fn .up fnNegativeMidpoint)
    , Model.dyadicRoundingOverflows fn .down fnNegativeMidpoint
    , Model.dyadicRoundingOverflows fn .towardZero fnOverflowLimit
    , Model.dyadicRoundingOverflows fnuz .nearest fnuzMidpoint
    , Model.dyadicRoundingOverflows finite .nearest finiteMidpoint
    , !(Model.rationalRoundingOverflowsScaled fn .nearest false
        fnMidpoint.significand 1 fnMidpoint.exponent)
    , !(Model.rationalRoundingOverflowsScaled fn .towardZero false
        fnMidpoint.significand 1 fnMidpoint.exponent)
    , Model.rationalRoundingOverflowsScaled fn .up false
        fnMidpoint.significand 1 fnMidpoint.exponent
    , !(Model.rationalRoundingOverflowsScaled fn .up true
        fnMidpoint.significand 1 fnMidpoint.exponent)
    , Model.rationalRoundingOverflowsScaled fn .down true
        fnMidpoint.significand 1 fnMidpoint.exponent
    , Model.rationalRoundingOverflowsScaled fn .towardZero false
        fnOverflowLimit.significand 1 fnOverflowLimit.exponent
    , Model.rationalRoundingOverflowsScaled fnuz .nearest false
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
  , ("ternaryValues", failTernaryValues.get)
  , ("algebraicOperations", failAlgebraicOperations.get)
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
