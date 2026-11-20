/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Floats.Formats.BinaryInterchange.Operations.MagnitudeExtrema.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Operations.Payload.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Operations.Augmented.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Operations.FormatOf.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Operations.FormatOf.SquareRoot.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Recommended.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Directed.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Directed.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Format.Catalog
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Conversion
import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Magnitude.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Reduction.ScaledProduct.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Decode
import FloatLib.Floats.Formats.DecimalInterchange.KernelPath.Runtime
import FloatLib.Floats.Formats.DecimalInterchange.Recommended.Runtime
import FloatLib.Floats.Formats.DecimalInterchange.Reduction.Runtime
import FloatLib.Floats.Formats.DecimalInterchange.Reduction.ScaledProduct.Runtime
import FloatLib.Floats.Formats.DecimalInterchange.Reduction.Schedule.Runtime
import FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Recommended.Runtime
import FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.CorrectlyRounded.Runtime

/-!
# The operations of IEEE 754-2019 against brute force and against other implementations

`oracle ieee2019 exhaustive` runs the binary operations of IEEE 754-2019 §9.4 to §9.7 on every
pair of encodings of a six-bit IEEE format (three exponent bits, two fraction bits, 64
encodings, 4,096 pairs) and on every encoding of a ten-bit format for the payload operations.
The expected results are computed here by brute force from the definitions: the nearest of all
finite values to an exact rational, with the tie rule and the overflow threshold of the
operation. Nothing of the implementation is used except decoding an encoding to its exact value.

`oracle ieee2019 formatOf` runs the formatOf operations of §5.4.1. With the three formats
equal, every pair of encodings of the six-bit format in each of the six rounding directions
must give the value, the flags and the ternary value of `add`, `sub`, `mul` and `div`, and
`fma` the same with eight addends. With an operand of six bits, an operand of eight bits and
destinations of five, eight and twelve bits, the expected outcome is computed here from the
rules of the standard for special operands and by rounding the exact rational result with
`Model.ofRat`, which rounds a quotient of integers and shares no code with the dyadic rounding
of the formatOf sum, product and fused multiply-add.

`oracle ieee2019 check` reads cases from standard input and compares FloatLib with the result
that another implementation computed: Python's `decimal` for decimal addition, subtraction,
multiplication (the specification and the kernel path), the extrema and the decimal reductions
`sum`, `sumAbs`, `sumSquare` and `dot`, exact rational
arithmetic in Python for the augmented operations and the reductions on binary64, the C
library for the payload operations, and `mpmath` at high precision for the recommended
functions of §9.2 on five binary formats in five rounding directions, with their flags.
`tests/oracles/ieee2019/reference.py`, `functions.py` and `payload.c` write the cases and document
the line formats.
-/

open FloatLib.Floats.Formats
open FloatLib.Floats.Formats.BinaryInterchange

-- Keep command-specific exhaustive computations inside their IO actions.
set_option compiler.extract_closed false

namespace FloatLibTests.Oracle.IEEE2019

/-- The five flags as the sum of invalid 1, divideByZero 2, overflow 4, underflow 8, inexact 16. -/
def mask (status : FloatLib.Numerics.IEEEStatus) : Nat :=
  (if status.invalid then 1 else 0) + (if status.divideByZero then 2 else 0) +
    (if status.overflow then 4 else 0) + (if status.underflow then 8 else 0) +
    (if status.inexact then 16 else 0)

/-- One named group of checks: how many ran and the descriptions of the first failures. -/
structure Tally where
  cases : Nat := 0
  failures : Nat := 0
  reports : Array String := #[]

def Tally.record (tally : Tally) (holds : Bool) (description : Unit → String) : Tally :=
  if holds then { tally with cases := tally.cases + 1 }
  else
    { cases := tally.cases + 1, failures := tally.failures + 1
      reports := if tally.reports.size < 5 then tally.reports.push (description ()) else
        tally.reports }

/-! ## Brute force on a six-bit format -/

/-- Three exponent bits and two fraction bits: 64 encodings, precision three. -/
abbrev Small : FloatFormat := FloatFormat.ieee 3 2

def small (bits : Nat) : Model Small := Model.ofNatBits bits

/-- The finite encodings with their exact values. -/
def finiteValues : Array (Nat × Rat) :=
  (List.range 64).toArray.filterMap fun bits => (Model.toRat? (small bits)).map fun q => (bits, q)

def largest : Rat := finiteValues.foldl (fun best entry => max best entry.2) 0

def secondLargest : Rat :=
  finiteValues.foldl (fun best entry => if entry.2 < largest then max best entry.2 else best) 0

/-- The midpoint between the largest finite value and the next value of the unbounded grid. -/
def overflowMidpoint : Rat := largest + (largest - secondLargest) / 2

/--
The finite value nearest to `exact`, or `none` when the rounding overflows. A tie goes to the
smaller magnitude (`tieTowardZero`) or to the even significand, and the midpoint beyond the
largest finite value overflows only in the second case.
-/
def nearest (tieTowardZero : Bool) (exact : Rat) : Option Rat :=
  let overflows :=
    if tieTowardZero then overflowMidpoint < |exact| else overflowMidpoint ≤ |exact|
  if overflows then none
  else
    let best := finiteValues.foldl
      (fun (best : Nat × Rat) (entry : Nat × Rat) =>
        let distance := |entry.2 - exact|
        let bestDistance := |best.2 - exact|
        if distance < bestDistance then entry
        else if distance == bestDistance && entry.2 != best.2 then
          if tieTowardZero then (if |entry.2| < |best.2| then entry else best)
          else (if entry.1 % 2 == 0 then entry else best)
        else best)
      (0, 0)
    some best.2

/-- The encoding of a finite value. `negative` is the sign of a zero. -/
def encode (negative : Bool) (value : Rat) : Nat :=
  let negative := if value == 0 then negative else decide (value < 0)
  (finiteValues.find? fun entry => entry.2 == value && (32 ≤ entry.1) == negative).elim 999
    fun entry => entry.1

def infinity (negative : Bool) : Nat := if negative then 0x3C else 0x1C

/-- What an operation must deliver: an encoding, or any quiet NaN. -/
inductive Expected where
  | bits (encoding : Nat)
  | quietNaN
  deriving BEq

def Expected.matches (expected : Expected) (actual : Model Small) : Bool :=
  match expected with
  | .bits encoding => actual.toNatBits == encoding
  | .quietNaN => Model.isNaN actual && !Model.isSignaling actual

/-- Head, tail and flags of an augmented operation from its definition. -/
def augmentedReference (multiply : Bool) (x y : Model Small) :
    Expected × Expected × Nat :=
  let signaling := Model.isSignaling x || Model.isSignaling y
  if Model.isNaN x || Model.isNaN y then (.quietNaN, .quietNaN, if signaling then 1 else 0)
  else
    match Model.toRat? x, Model.toRat? y with
    | some qx, some qy =>
        let exact := if multiply then qx * qy else qx + qy
        if exact == 0 then
          let signedZero := encode
            (if multiply then Model.signBit x != Model.signBit y
              else Model.signBit x && Model.signBit y) 0
          (.bits signedZero, .bits signedZero, 0)
        else
          match nearest true exact with
          | none => (.bits (infinity (exact < 0)), .bits (infinity (exact < 0)), 4 + 16)
          | some head =>
              let error := exact - head
              if error == 0 then (.bits (encode (exact < 0) head), .bits (encode (exact < 0) 0), 0)
              else
                let tail := (nearest true error).getD 0
                (.bits (encode (exact < 0) head), .bits (encode (error < 0) tail),
                  if tail == error then 0 else 8 + 16)
    | _, _ =>
        -- An infinite operand and no NaN.
        let invalid :=
          if multiply then Model.isZero x || Model.isZero y
          else Model.isInfinite x && Model.isInfinite y && Model.signBit x != Model.signBit y
        if invalid then (.quietNaN, .quietNaN, 1)
        else
          let negative :=
            if multiply then Model.signBit x != Model.signBit y
            else if Model.isInfinite x then Model.signBit x else Model.signBit y
          (.bits (infinity negative), .bits (infinity negative), 0)

/-- The magnitude of an operand that is not a NaN: `none` is infinite. -/
def magnitude (x : Model Small) : Option Rat := (Model.toRat? x).map fun q => |q|

/-- Whether the first magnitude is smaller than the second. -/
def magnitudeLess : Option Rat → Option Rat → Bool
  | some a, some b => a < b
  | some _, none => true
  | none, _ => false

/-- The selection by magnitude from its definition. -/
def magnitudeReference (larger number : Bool) (x y : Model Small) : Expected :=
  match Model.isNaN x, Model.isNaN y with
  | true, true => .quietNaN
  | true, false => if number then .bits y.toNatBits else .quietNaN
  | false, true => if number then .bits x.toNatBits else .quietNaN
  | false, false =>
      let xSmaller := magnitudeLess (magnitude x) (magnitude y)
      let ySmaller := magnitudeLess (magnitude y) (magnitude x)
      if xSmaller then .bits (if larger then y else x).toNatBits
      else if ySmaller then .bits (if larger then x else y).toNatBits
      else
        -- Equal magnitudes: the negative operand is the minimum, the positive the maximum.
        .bits (if Model.signBit x == !larger then x else y).toNatBits

/-- `sumAbs` or `sumSquare` of a list from its definition: value and invalid, overflow, inexact. -/
def reductionReference (square : Bool) (operands : List (Model Small)) : Expected × Nat :=
  if operands.any Model.isSignaling then (.quietNaN, 1)
  else if operands.any Model.isInfinite then (.bits (infinity false), 0)
  else if operands.any Model.isNaN then (.quietNaN, 0)
  else
    let exact := operands.foldl
      (fun total x => let q := (Model.toRat? x).getD 0; total + (if square then q * q else |q|)) 0
    match nearest false exact with
    | none => (.bits (infinity false), 4 + 16)
    | some value => (.bits (encode false value), if value == exact then 0 else 16)

/-- The exponent `s` with `2 ^ s ≤ |value| < 2 ^ (s + 1)` of a nonzero rational of small size. -/
def leadingExponent (value : Rat) : Int :=
  ((List.range 80).map fun index => (index : Int) - 40).foldl
    (fun found s => if (2 : Rat) ^ s ≤ |value| then s else found) (-40)

/-- `scaledProd` of a list from its definition: product, scale factor, invalid and inexact. -/
def scaledReference (operands : List (Model Small)) : Expected × Int × Nat :=
  let negative := operands.foldl (fun sign x => sign != Model.signBit x) false
  if operands.any Model.isSignaling then (.quietNaN, 0, 1)
  else if operands.any Model.isNaN then (.quietNaN, 0, 0)
  else if operands.any Model.isInfinite then
    if operands.any Model.isZero then (.quietNaN, 0, 1) else (.bits (infinity negative), 0, 0)
  else
    let exact := operands.foldl (fun product x => product * (Model.toRat? x).getD 0) 1
    if exact == 0 then (.bits (encode negative 0), 0, 0)
    else
      let scale := leadingExponent exact
      let scaled := exact / (2 : Rat) ^ scale
      let rounded := (nearest false scaled).getD 0
      (.bits (encode negative rounded), scale, if rounded == scaled then 0 else 16)

/-- Ten bits, for the payload operations: payloads below 16. -/
abbrev Medium : FloatFormat := FloatFormat.ieee 4 5

/-- The three payload operations on one encoding of the ten-bit format, from their definitions. -/
def payloadHolds (bits : Nat) : Bool :=
  let x : Model Medium := Model.ofNatBits bits
  let fraction := bits % 32
  let isNaN := bits / 32 % 16 == 15 && fraction != 0
  let payload := fraction % 16
  let get := Model.getPayload x
  let getHolds :=
    if isNaN then Model.toRat? get == some (payload : Rat) && !Model.signBit get
    else Model.toRat? get == some (-1)
  -- A nonnegative integer below 16 with a clear sign names a payload.
  let named : Option Nat :=
    match Model.toRat? x with
    | some q => if !Model.signBit x && q.den == 1 && 0 ≤ q && q < 16 then some q.num.toNat else none
    | none => none
  let set := Model.setPayload x
  let setHolds :=
    match named with
    | some n => set.toNatBits == 15 * 32 + 16 + n
    | none => set.toNatBits == 0
  let signaling := Model.setPayloadSignaling x
  let signalingHolds :=
    match named with
    | some n => if n == 0 then signaling.toNatBits == 0 else signaling.toNatBits == 15 * 32 + n
    | none => signaling.toNatBits == 0
  getHolds && setHolds && signalingHolds

def describe (name : String) (x y : Nat) : Unit → String :=
  fun _ => s!"{name} {x} {y}"

/-- Every pair of encodings of the six-bit format, and every encoding of the ten-bit format. -/
def exhaustive : IO (Array (String × Tally)) := do
  let mut addition : Tally := {}
  let mut subtraction : Tally := {}
  let mut multiplication : Tally := {}
  let mut extrema : Tally := {}
  let mut sums : Tally := {}
  let mut products : Tally := {}
  for a in [0:64] do
    for b in [0:64] do
      let x := small a
      let y := small b
      let sum := Model.augmentedAddition x y
      let (head, tail, flags) := augmentedReference false x y
      addition := addition.record
        (head.matches sum.head && tail.matches sum.tail && mask sum.status == flags)
        (describe "augmentedAddition" a b)
      let difference := Model.augmentedSubtraction x y
      let (head, tail, flags) := augmentedReference false x (Model.neg y)
      subtraction := subtraction.record
        (head.matches difference.head && tail.matches difference.tail &&
          mask difference.status == flags)
        (describe "augmentedSubtraction" a b)
      let product := Model.augmentedMultiplication x y
      let (head, tail, flags) := augmentedReference true x y
      multiplication := multiplication.record
        (head.matches product.head && tail.matches product.tail && mask product.status == flags)
        (describe "augmentedMultiplication" a b)
      let invalid := if Model.isSignaling x || Model.isSignaling y then 1 else 0
      extrema := extrema.record
        ((magnitudeReference false false x y).matches (Model.minimumMagnitude x y) &&
          (magnitudeReference true false x y).matches (Model.maximumMagnitude x y) &&
          (magnitudeReference false true x y).matches (Model.minimumMagnitudeNumber x y) &&
          (magnitudeReference true true x y).matches (Model.maximumMagnitudeNumber x y) &&
          mask (Model.minimumMagnitude x y (status := true)).status == invalid &&
          mask (Model.maximumMagnitudeNumber x y (status := true)).status == invalid)
        (describe "magnitude extrema" a b)
      let absolute := Model.sumAbs Small #[x, y] .nearest (status := true)
      let squares := Model.sumSquare Small #[x, y] .nearest (status := true)
      let (absoluteValue, absoluteFlags) := reductionReference false [x, y]
      let (squaresValue, squaresFlags) := reductionReference true [x, y]
      -- The reference does not compute tininess, so the underflow flag is left out.
      sums := sums.record
        (absoluteValue.matches absolute.value && mask absolute.status % 8 +
            mask absolute.status / 16 * 16 == absoluteFlags &&
          squaresValue.matches squares.value && mask squares.status % 8 +
            mask squares.status / 16 * 16 == squaresFlags)
        (describe "sumAbs, sumSquare" a b)
      let scaled := Model.scaledProd Small #[x, y]
      let (value, scale, flags) := scaledReference [x, y]
      products := products.record
        (value.matches scaled.product && scaled.scaleFactor == scale && mask scaled.status == flags)
        (describe "scaledProd" a b)
  let mut payloads : Tally := {}
  for bits in [0:1024] do
    payloads := payloads.record (payloadHolds bits) (describe "payload operations" bits 0)
  return #[("augmentedAddition", addition), ("augmentedSubtraction", subtraction),
    ("augmentedMultiplication", multiplication), ("magnitude extrema", extrema),
    ("sumAbs and sumSquare", sums), ("scaledProd", products),
    ("getPayload, setPayload, setPayloadSignaling", payloads)]

/-! ## The formatOf operations -/

def directions : Array Model.IEEERoundingMode :=
  #[.nearest, .nearestAway, .towardZero, .up, .down, .away]

def sameOutcome {format : FloatFormat} (left right : Model.IEEEOutcome format) : Bool :=
  left.value.toNatBits == right.value.toNatBits && mask left.status == mask right.status &&
    left.ternary == right.ternary

/-- What a formatOf operation must deliver, from the rules of the standard. -/
inductive Delivery where
  | nan (invalid : Bool)
  | infinity (negative divideByZero : Bool)
  | zero (negative : Bool)
  | rounded (exact : Rat)

def Delivery.matches {destination : FloatFormat} (expected : Delivery)
    (mode : Model.IEEERoundingMode) (actual : Model.IEEEOutcome destination) : Bool :=
  match expected with
  | .nan invalid =>
      Model.isNaN actual.value && !Model.isSignaling actual.value &&
        mask actual.status == (if invalid then 1 else 0)
  | .infinity negative divideByZero =>
      Model.isInfinite actual.value && Model.signBit actual.value == negative &&
        mask actual.status == (if divideByZero then 2 else 0) && actual.ternary == .eq
  | .zero negative =>
      Model.isZero actual.value && Model.signBit actual.value == negative &&
        mask actual.status == 0 && actual.ternary == .eq
  | .rounded exact =>
      sameOutcome actual (Model.ofRat destination exact (mode := mode) (status := true))

/-- The sign of an exact zero sum of terms with the signs `left` and `right`. -/
def zeroSumSign (mode : Model.IEEERoundingMode) (left right : Bool) : Bool :=
  if mode == .down then left || right else left && right

/-- A term of a sum: a rational, or an infinity with its sign. -/
def sumDelivery (mode : Model.IEEERoundingMode) (left right : Option Rat)
    (leftSign rightSign : Bool) : Delivery :=
  match left, right with
  | some p, some q =>
      if p + q == 0 then .zero (zeroSumSign mode leftSign rightSign) else .rounded (p + q)
  | none, none => if leftSign == rightSign then .infinity leftSign false else .nan true
  | none, some _ => .infinity leftSign false
  | some _, none => .infinity rightSign false

/-- Sum, product (`operation` 1), quotient (2) or `x * y + z` (3) of operands of any formats. -/
def formatOfReference {left right addend : FloatFormat} (operation : Nat)
    (mode : Model.IEEERoundingMode) (x : Model left) (y : Model right) (z : Model addend) :
    Delivery :=
  let sign := Model.signBit x != Model.signBit y
  let signaling := Model.isSignaling x || Model.isSignaling y ||
    (operation == 3 && Model.isSignaling z)
  let zeroTimesInfinity :=
    (Model.isZero x && Model.isInfinite y) || (Model.isInfinite x && Model.isZero y)
  if Model.isNaN x || Model.isNaN y then .nan signaling
  else if operation == 3 && Model.isNaN z then .nan (signaling || zeroTimesInfinity)
  else
    match operation with
    | 0 => sumDelivery mode (Model.toRat? x) (Model.toRat? y) (Model.signBit x) (Model.signBit y)
    | 2 =>
        match Model.toRat? x, Model.toRat? y with
        | some p, some q =>
            if q == 0 then (if p == 0 then .nan true else .infinity sign true)
            else if p == 0 then .zero sign else .rounded (p / q)
        | none, none => .nan true
        | none, some _ => .infinity sign false
        | some _, none => .zero sign
    | _ =>
        if zeroTimesInfinity then .nan true
        else
          let product : Option Rat := do
            let p ← Model.toRat? x
            let q ← Model.toRat? y
            pure (p * q)
          if operation == 1 then
            match product with
            | some exact => if exact == 0 then .zero sign else .rounded exact
            | none => .infinity sign false
          else sumDelivery mode product (Model.toRat? z) sign (Model.signBit z)

/--
A rational that rounds like the square root of the positive rational `q` in every direction,
into a format of far fewer than `bits` bits: the root truncated to `bits` bits after the binary
point by an integer square root, with half a unit more when the truncation is not exact.
-/
def sqrtRepresentative (q : Rat) (bits : Nat := 96) : Rat :=
  let scaled := q * 4 ^ bits
  let root := scaled.floor.toNat.sqrt
  if (root : Rat) * root == scaled then (root : Rat) / 2 ^ bits
  else ((root : Rat) + 1 / 2) / 2 ^ bits

/-- What the formatOf square root must deliver, from the rules of the standard. -/
def squareRootReference {source : FloatFormat} (x : Model source) : Delivery :=
  if Model.isNaN x then .nan (Model.isSignaling x)
  else if Model.isZero x then .zero (Model.signBit x)
  else if Model.signBit x then .nan true
  else
    match Model.toRat? x with
    | some q => .rounded (sqrtRepresentative q)
    | none => .infinity false false

/-- An operand format of eight bits and the three destinations. -/
abbrev Byte : FloatFormat := FloatFormat.ieee 4 3
abbrev Narrow : FloatFormat := FloatFormat.ieee 3 1
abbrev Wide : FloatFormat := FloatFormat.ieee 5 6

/-- The addends of the fused multiply-add: zeros, finite values, infinities, NaNs. -/
def addends : Array Nat := #[0x00, 0x20, 0x01, 0x0D, 0x33, 0x1C, 0x3C, 0x1E, 0x1D]

def formatOf : IO (Array (String × Tally)) := do
  let mut same : Tally := {}
  let mut fused : Tally := {}
  for mode in directions do
    for a in [0:64] do
      for b in [0:64] do
        let x := small a
        let y := small b
        same := same.record
          (sameOutcome (Model.formatOfAddition Small x y mode)
              (Model.add x y (mode := mode) (status := true)) &&
            sameOutcome (Model.formatOfSubtraction Small x y mode)
              (Model.sub x y (mode := mode) (status := true)) &&
            sameOutcome (Model.formatOfMultiplication Small x y mode)
              (Model.mul x y (mode := mode) (status := true)) &&
            sameOutcome (Model.formatOfDivision Small x y mode)
              (Model.div x y (mode := mode) (status := true)))
          fun _ => s!"one format, direction {repr mode}: {a} {b}"
        for c in addends do
          fused := fused.record
            (sameOutcome (Model.formatOfFusedMultiplyAdd Small x y (small c) mode)
              (Model.fma x y (small c) (mode := mode) (status := true)))
            fun _ => s!"one format, direction {repr mode}: fma {a} {b} {c}"
  let mut mixed : Tally := {}
  let mut mixedFused : Tally := {}
  for mode in directions do
    for a in [0:64] do
      for b in [0:256] do
        let x := small a
        let y : Model Byte := Model.ofNatBits b
        let holds (destination : FloatFormat) : Bool :=
          (formatOfReference 0 mode x y x).matches mode
              (Model.formatOfAddition destination x y mode) &&
            (formatOfReference 0 mode x (Model.neg y) x).matches mode
              (Model.formatOfSubtraction destination x y mode) &&
            (formatOfReference 1 mode x y x).matches mode
              (Model.formatOfMultiplication destination x y mode) &&
            (formatOfReference 2 mode x y x).matches mode
                (Model.formatOfDivision destination x y mode)
        mixed := mixed.record (holds Narrow && holds Byte && holds Wide)
          fun _ => s!"three formats, direction {repr mode}: {a} {b}"
        for c in addends do
          let z := small c
          let holds (destination : FloatFormat) : Bool :=
            (formatOfReference 3 mode x y z).matches mode
              (Model.formatOfFusedMultiplyAdd destination x y z mode)
          mixedFused := mixedFused.record (holds Narrow && holds Byte && holds Wide)
            fun _ => s!"three formats, direction {repr mode}: fma {a} {b} {c}"
  let mut roots : Tally := {}
  let mut mixedRoots : Tally := {}
  for mode in directions do
    for a in [0:64] do
      let x := small a
      roots := roots.record
        (sameOutcome (Model.formatOfSquareRoot Small x mode)
          (Model.sqrt x (mode := mode) (status := true)))
        fun _ => s!"one format, direction {repr mode}: sqrt {a}"
    for b in [0:256] do
      let y : Model Byte := Model.ofNatBits b
      roots := roots.record
        (sameOutcome (Model.formatOfSquareRoot Byte y mode)
          (Model.sqrt y (mode := mode) (status := true)))
        fun _ => s!"one format of eight bits, direction {repr mode}: sqrt {b}"
      let holds (destination : FloatFormat) : Bool :=
        (squareRootReference y).matches mode (Model.formatOfSquareRoot destination y mode)
      mixedRoots := mixedRoots.record (holds Narrow && holds Small && holds Wide)
        fun _ => s!"three formats, direction {repr mode}: sqrt {b}"
  return #[("formatOf addition, subtraction, multiplication, division with one format", same),
    ("formatOf fusedMultiplyAdd with one format", fused),
    ("formatOf addition, subtraction, multiplication, division across formats", mixed),
    ("formatOf fusedMultiplyAdd across formats", mixedFused),
    ("formatOf squareRoot with one format", roots),
    ("formatOf squareRoot across formats", mixedRoots)]

/-! ## Cases computed by other implementations -/

def parseHex? (text : String) : Option Nat :=
  text.foldl
    (fun value character =>
      value.bind fun value =>
        if character.isDigit then some (16 * value + (character.toNat - '0'.toNat))
        else if 'a' ≤ character && character ≤ 'f' then
          some (16 * value + (character.toNat - 'a'.toNat + 10))
        else none)
    (some 0)

def parseInt? (text : String) : Option Int :=
  if text.startsWith "-" then (text.drop 1).toNat?.map fun n => -(n : Int)
  else text.toNat?.map fun n => (n : Int)

/-- A decimal datum: `f,SIGN,COEFFICIENT,EXPONENT`, `i,SIGN` or `n,SIGN,SIGNALING,PAYLOAD`. -/
def parseDatum? (text : String) : Option DecimalInterchange.Datum :=
  match text.splitOn "," with
  | ["f", sign, coefficient, exponent] => do
      some (.finite (sign == "1") (← coefficient.toNat?) (← parseInt? exponent))
  | ["i", sign] => some (.infinity (sign == "1"))
  | ["n", sign, signaling, payload] => do
      some (.nan (sign == "1") (signaling == "1") (← payload.toNat?))
  | _ => none

def decimalFormat? : String → Option DecimalInterchange.Format
  | "7" => some .decimal32
  | "16" => some .decimal64
  | "34" => some .decimal128
  | _ => none

def decimalMode? : String → Option DecimalInterchange.RoundingMode
  | "E" => some .nearest
  | "A" => some .nearestAway
  | "Z" => some .towardZero
  | "U" => some .up
  | "D" => some .down
  | _ => none

def binary64 (word : Nat) : Model FloatFormat.binary64 := Model.ofNatBits word

open Model.Transcendentals in
/-- The functions of one operand of §9.2 by their names. -/
def functions : List (String × CorrectlyRounded.Function) :=
  [("exp2", .exp2), ("exp2m1", .exp2m1), ("exp10", .exp10), ("exp10m1", .exp10m1),
    ("log2", .log2), ("log10", .log10), ("log2p1", .log2p1), ("log10p1", .log10p1),
    ("sin", .sin), ("cos", .cos), ("tan", .tan), ("sinPi", .sinPi), ("cosPi", .cosPi),
    ("tanPi", .tanPi), ("asin", .asin), ("acos", .acos), ("atan", .atan), ("asinPi", .asinPi),
    ("acosPi", .acosPi), ("atanPi", .atanPi), ("sinh", .sinh), ("cosh", .cosh), ("tanh", .tanh),
    ("asinh", .asinh), ("acosh", .acosh), ("atanh", .atanh)]

open Model.Transcendentals in
/--
One case of a function of §9.2 in the format `fmt` and the rounding direction `direction`
(`E`, `A`, `Z`, `U` or `D`): `y` is `-`, the encoding of a second operand, or the integer
of `compound`, `rootn` or `pown`. The expected value is an encoding or `nan` for any quiet NaN,
and the flags are compared as their sum.
-/
def checkFunction (fmt : FloatFormat) (name direction x y expected flags : String) :
    Option Bool := do
  let mode : Model.IEEERoundingMode ←
    match direction with
    | "E" => some .nearest
    | "A" => some .nearestAway
    | "Z" => some .towardZero
    | "U" => some .up
    | "D" => some .down
    | _ => none
  let x : Model fmt := Model.ofNatBits (← parseHex? x)
  let outcome ←
    match name with
    | "atan2" => (parseHex? y).map fun y => CorrectlyRounded.atan2 x (Model.ofNatBits y) mode
    | "atan2Pi" => (parseHex? y).map fun y => CorrectlyRounded.atan2Pi x (Model.ofNatBits y) mode
    | "powr" => (parseHex? y).map fun y => CorrectlyRounded.powr x (Model.ofNatBits y) mode
    | "pow" => (parseHex? y).map fun y => CorrectlyRounded.pow x (Model.ofNatBits y) mode
    | "compound" => (parseInt? y).map fun n => CorrectlyRounded.compound x n mode
    | "exp" => some (Directed.exp x mode)
    | "expm1" => some (Directed.expm1 x mode)
    | "log" => some (Directed.log x mode)
    | "logp1" => some (Directed.logp1 x mode)
    | "rSqrt" => some (Model.Algebraic.Directed.rSqrt x mode)
    | "cbrt" => some (Model.Algebraic.Directed.cbrt x mode)
    | "hypot" =>
        (parseHex? y).map fun y => Model.Algebraic.Directed.hypot x (Model.ofNatBits y) mode
    | "rootn" => (parseInt? y).map fun n => Model.Algebraic.Directed.rootn x n mode
    | "pown" => (parseInt? y).map fun n => Model.Algebraic.Directed.pown x n mode
    | _ => (functions.lookup name).map fun function => function.apply x mode
  let valueHolds ←
    if expected == "nan" then
      some (Model.isNaN outcome.value && !Model.isSignaling outcome.value)
    else (parseHex? expected).map fun bits => outcome.value.toNatBits == bits
  some (valueHolds && mask outcome.status == (← flags.toNat?))

/-- Whether FloatLib agrees with one case, or `none` for a line that does not parse. -/
def checkLine (fields : List String) : Option Bool :=
  open DecimalInterchange in
  match fields with
  | ["fun", name, format, direction, x, y, expected, flags] =>
      match format with
      | "e3f2" => checkFunction (FloatFormat.ieee 3 2) name direction x y expected flags
      | "e4f3" => checkFunction (FloatFormat.ieee 4 3) name direction x y expected flags
      | "e5m2" => checkFunction FloatFormat.e5m2 name direction x y expected flags
      | "e4m3" => checkFunction FloatFormat.e4m3 name direction x y expected flags
      | "e4m3fnuz" => checkFunction FloatFormat.e4m3fnuz name direction x y expected flags
      | "e5m2fnuz" => checkFunction FloatFormat.e5m2fnuz name direction x y expected flags
      | "e2m1" => checkFunction FloatFormat.e2m1 name direction x y expected flags
      | "binary16" => checkFunction FloatFormat.binary16 name direction x y expected flags
      | "binary32" => checkFunction FloatFormat.binary32 name direction x y expected flags
      | "binary64" => checkFunction FloatFormat.binary64 name direction x y expected flags
      | _ => none
  | ["dec", operation, precision, mode, x, y, result, flags] => do
      let f ← decimalFormat? precision
      let mode ← decimalMode? mode
      let x ← parseDatum? x
      let y ← parseDatum? y
      let result ← parseDatum? result
      let flags ← flags.toNat?
      let (specification, kernel) ←
        match operation with
        | "add" => some (Arithmetic.add f mode x y, KernelPath.add f mode x y)
        | "sub" => some (Arithmetic.sub f mode x y, KernelPath.sub f mode x y)
        | "mul" => some (Arithmetic.mul f mode x y, KernelPath.mul f mode x y)
        | _ => none
      some (specification.value == result && mask specification.status == flags &&
        kernel == specification)
  | ["dtot", name, precision, mode, x, y, expected, flags] => do
      let f ← decimalFormat? precision
      let mode ← decimalMode? mode
      let x ← parseDatum? x
      let expected ← parseDatum? expected
      let outcome ←
        match name with
        | "exp" => some (Transcendentals.CorrectlyRounded.exp f mode x)
        | "expm1" => some (Transcendentals.CorrectlyRounded.expm1 f mode x)
        | "log" => some (Transcendentals.CorrectlyRounded.log f mode x)
        | "logp1" => some (Transcendentals.CorrectlyRounded.logp1 f mode x)
        | "powr" => (parseDatum? y).map fun y => Transcendentals.CorrectlyRounded.powr f mode x y
        | "pow" => (parseDatum? y).map fun y => Transcendentals.CorrectlyRounded.pow f mode x y
        | "atan2" =>
            (parseDatum? y).map fun y => Transcendentals.CorrectlyRounded.atan2 f mode x y
        | "atan2Pi" =>
            (parseDatum? y).map fun y => Transcendentals.CorrectlyRounded.atan2Pi f mode x y
        | "compound" =>
            (parseInt? y).map fun n => Transcendentals.CorrectlyRounded.compound f mode x n
        | _ =>
            (functions.lookup name).map fun function =>
              Transcendentals.CorrectlyRounded.apply f function mode x
      some (outcome.value == expected && mask outcome.status == (← flags.toNat?))
  | "dred" :: operation :: precision :: mode :: count :: rest => do
      let f ← decimalFormat? precision
      let mode ← decimalMode? mode
      let count ← count.toNat?
      let xs ← (rest.take count).mapM parseDatum?
      let agrees (outcome : Outcome) (result flags : String) : Option Bool := do
        some (outcome.value == (← parseDatum? result) && mask outcome.status == (← flags.toNat?))
      match operation, rest.drop count with
      | "sum", [result, flags] => agrees (Arithmetic.sum f mode xs.toArray) result flags
      | "sumabs", [result, flags] => agrees (Arithmetic.sumAbs f mode xs.toArray) result flags
      | "sumsq", [result, flags] => agrees (Arithmetic.sumSquare f mode xs.toArray) result flags
      | "dot", more => do
          let ys ← (more.take count).mapM parseDatum?
          match Arithmetic.dot f mode xs.toArray ys.toArray, more.drop count with
          | .ok outcome, [result, flags] => agrees outcome result flags
          | _, _ => none
      | _, _ => none
  | "dsp" :: operation :: precision :: mode :: count :: rest => do
      let f ← decimalFormat? precision
      let mode ← decimalMode? mode
      let count ← count.toNat?
      let xs ← (rest.take count).mapM parseDatum?
      let agrees (outcome : ScaledProduct Datum) (result scale flags : String) : Option Bool := do
        some (outcome.product == (← parseDatum? result) &&
          outcome.scaleFactor == (← parseInt? scale) && mask outcome.status == (← flags.toNat?))
      let paired (operation : Array Datum → Array Datum →
          Except FloatLib.Numerics.ReductionError (ScaledProduct Datum)) (more : List String) :
          Option Bool := do
        let ys ← (more.take count).mapM parseDatum?
        match operation xs.toArray ys.toArray, more.drop count with
        | .ok outcome, [result, scale, flags] => agrees outcome result scale flags
        | _, _ => none
      match operation, rest.drop count with
      | "scaledprod", [result, scale, flags] =>
          agrees (Arithmetic.scaledProd f mode xs.toArray) result scale flags
      | "scaledprodsum", more => paired (Arithmetic.scaledProdSum f mode) more
      | "scaledproddiff", more => paired (Arithmetic.scaledProdDiff f mode) more
      | _, _ => none
  | "dord" :: operation :: accumulator :: precision :: mode :: count :: rest => do
      let acc ← decimalFormat? accumulator
      let out ← decimalFormat? precision
      let mode ← decimalMode? mode
      let count ← count.toNat?
      let xs ← (rest.take count).mapM parseDatum?
      let agrees (outcome : Outcome) (result flags : String) : Option Bool := do
        some (outcome.value == (← parseDatum? result) && mask outcome.status == (← flags.toNat?))
      let inOrder (term : Datum → Outcome) : Outcome :=
        Arithmetic.reduceInOrder acc out mode term xs
      match operation, rest.drop count with
      | "sum", [result, flags] =>
          agrees (inOrder (Arithmetic.Reduction.sumTerm acc mode)) result flags
      | "sumabs", [result, flags] =>
          agrees (inOrder (Arithmetic.Reduction.sumAbsTerm acc mode)) result flags
      | "sumsq", [result, flags] =>
          agrees (inOrder (Arithmetic.Reduction.sumSquareTerm acc mode)) result flags
      | "dot", more => do
          let ys ← (more.take count).mapM parseDatum?
          match more.drop count with
          | [result, flags] =>
              agrees (Arithmetic.reduceInOrder acc out mode (Arithmetic.Reduction.dotTerm acc mode)
                (xs.zip ys)) result flags
          | _ => none
      | _, _ => none
  | ["ext", operation, precision, x, y, result] => do
      let f ← decimalFormat? precision
      let x ← parseDatum? x
      let y ← parseDatum? y
      let result ← parseDatum? result
      let outcome ←
        match operation with
        | "max" => some (Arithmetic.maximumNumber f x y)
        | "min" => some (Arithmetic.minimumNumber f x y)
        | "maxmag" => some (Arithmetic.maximumMagnitudeNumber f x y)
        | "minmag" => some (Arithmetic.minimumMagnitudeNumber f x y)
        | _ => none
      some (outcome.value == result)
  | ["aug", operation, x, y, head, tail, flags] => do
      let x := binary64 (← parseHex? x)
      let y := binary64 (← parseHex? y)
      let outcome ←
        match operation with
        | "add" => some (Model.augmentedAddition x y)
        | "sub" => some (Model.augmentedSubtraction x y)
        | "mul" => some (Model.augmentedMultiplication x y)
        | _ => none
      some (outcome.head.toNatBits == (← parseHex? head) &&
        outcome.tail.toNatBits == (← parseHex? tail) && mask outcome.status == (← flags.toNat?))
  | "red" :: operation :: count :: rest => do
      let count ← count.toNat?
      let values ← (rest.take count).mapM fun word => (parseHex? word).map binary64
      match operation, rest.drop count with
      | "sumabs", [result] =>
          some ((Model.sumAbs FloatFormat.binary64 values.toArray).toNatBits ==
              (← parseHex? result))
      | "sumsq", [result] =>
          some ((Model.sumSquare FloatFormat.binary64 values.toArray).toNatBits ==
            (← parseHex? result))
      | "scaledprod", [product, scale] =>
          let outcome := Model.scaledProd FloatFormat.binary64 values.toArray
          some (outcome.product.toNatBits == (← parseHex? product) &&
            outcome.scaleFactor == (← parseInt? scale))
      | _, _ => none
  | ["pay", operation, width, x, result] => do
      let x ← parseHex? x
      let result ← parseHex? result
      match width with
      | "64" =>
          let x : Model FloatFormat.binary64 := Model.ofNatBits x
          match operation with
          | "get" => some ((Model.getPayload x).toNatBits == result)
          | "set" => some ((Model.setPayload x).toNatBits == result)
          | "setsig" => some ((Model.setPayloadSignaling x).toNatBits == result)
          | _ => none
      | "32" =>
          let x : Model FloatFormat.binary32 := Model.ofNatBits x
          match operation with
          | "get" => some ((Model.getPayload x).toNatBits == result)
          | "set" => some ((Model.setPayload x).toNatBits == result)
          | "setsig" => some ((Model.setPayloadSignaling x).toNatBits == result)
          | _ => none
      | _ => none
  | _ => none

/--
A certified decimal function at one operand: whether a result was returned, and whether a
returned result has the expected value.
-/
def checkDecimalFunction (name precision x expected : String) : Option (Bool × Bool) := do
  let f ← decimalFormat? precision
  let x ← parseDatum? x
  let expected ← parseDatum? expected
  let result ←
    match name with
    | "exp" => some (DecimalInterchange.Transcendentals.Certified.exp f x)
    | "log" => some (DecimalInterchange.Transcendentals.Certified.log f x)
    | _ =>
        (functions.lookup name).map fun function =>
          DecimalInterchange.Transcendentals.Certified.apply f function x
  match result with
  | some result => some (true, result.toRat? == expected.toRat?)
  | none => some (false, true)

/-- Compare FloatLib with every case on standard input, one tally for each kind of line. A
certified decimal function that returns no result is counted under `dfun-unsettled`. -/
partial def checkStream (stream : IO.FS.Stream) (tallies : Std.HashMap String Tally) :
    IO (Std.HashMap String Tally) := do
  let raw ← stream.getLine
  if raw.isEmpty then return tallies
  let line := raw.trimAscii.copy
  let fields := (line.splitOn " ").filter fun field => !field.isEmpty
  match fields with
  | [] => checkStream stream tallies
  | ["dfun", name, precision, x, expected] =>
      let (settled, holds) := (checkDecimalFunction name precision x expected).getD (true, false)
      let key := if settled then s!"dfun {name}" else s!"dfun-unsettled {name}"
      checkStream stream (tallies.insert key ((tallies.getD key {}).record holds fun _ => line))
  | kind :: operation :: _ =>
      let key := s!"{kind} {operation}"
      let holds := (checkLine fields).getD false
      let tally := (tallies.getD key {}).record holds fun _ => line
      checkStream stream (tallies.insert key tally)
  | _ => checkStream stream (tallies.insert "unparsed" ((tallies.getD "unparsed" {}).record false
      fun _ => line))

def report (groups : Array (String × Tally)) : IO UInt32 := do
  let mut failed := false
  for (name, tally) in groups do
    IO.println s!"RESULT ieee2019 {name}: cases={tally.cases} failures={tally.failures}"
    for description in tally.reports do
      IO.println s!"  first failures: {description}"
    if tally.failures != 0 then failed := true
  return if failed then 1 else 0

/-- `oracle ieee2019 exhaustive`, `formatOf` or `check` (cases on standard input). -/
public def run (args : List String) : IO UInt32 := do
  match args with
  | ["exhaustive"] => report (← exhaustive)
  | ["formatOf"] => report (← formatOf)
  | ["check"] =>
      let tallies ← checkStream (← IO.getStdin) {}
      report (tallies.toArray.qsort fun left right => left.1 < right.1)
  | _ =>
      IO.eprintln "usage: oracle ieee2019 exhaustive | formatOf | check < CASES"
      return 2

end FloatLibTests.Oracle.IEEE2019
