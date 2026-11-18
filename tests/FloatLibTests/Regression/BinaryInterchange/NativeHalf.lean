/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured
public import FloatLib.Floats.Formats.IEEE754.Native
public import FloatLib.Floats.Formats.IEEE754.Native.Half

/-!
# Native binary16 and bfloat16 carriers against the software models

`Native.Half` and `Native.BFloat16` round on interchange words, while `Binary16` and `BFloat16`
(`ExecFloat.Binary 5 10` and `ExecFloat.Binary 8 7`) round exact values. These checks compare the
two:
* every 16-bit word decodes to the model's value and encodes back to itself;
* conversions from binary64 and binary32 agree on subnormal, halfway, overflow, NaN, and random
  inputs;
* addition, subtraction, multiplication, division, square root, negation and the comparisons
  `<`, `≤` and `==` agree on random operands;
* the four arithmetic operations agree on every pair of bfloat16 words of the two lowest
  exponent fields, where binary32 itself is subnormal, and on those words against words spread
  over the whole format.

The widening of both carriers is proved (`Native.Carrier.val_eq_spec`); the arithmetic is host
binary32 arithmetic, which these runs test and no theorem covers.

Each check returns its number of disagreements.
`word_boundaries` also checks exact midpoint, adjacent binary64, signed-zero and negative-NaN
words by kernel reduction, without host floating-point evaluation.
-/

@[expose] public section

namespace FloatLibTests.Regression.BinaryInterchange.NativeHalf

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

/-- Direct binary64 rounding distinguishes a midpoint from its next neighbour, preserves negative
zero and normalizes a negative NaN, for both native layouts. -/
theorem word_boundaries :
    ([(Native.halfFormat, 0x3ff0020000000000, 0x3c00),
      (Native.halfFormat, 0x3ff0020000000001, 0x3c01),
      (Native.halfFormat, 0x8000000000000000, 0x8000),
      (Native.halfFormat, 0xfff0000000000001, 0x7e00),
      (Native.bfloat16Format, 0x3ff0100000000000, 0x3f80),
      (Native.bfloat16Format, 0x3ff0100000000001, 0x3f81),
      (Native.bfloat16Format, 0x8000000000000000, 0x8000),
      (Native.bfloat16Format, 0xfff0000000000001, 0x7fc0)] :
        List (Native.Format × UInt64 × UInt16)).all (fun (format, bits, expected) =>
          (Native.Carrier.ofWord (format := format) FloatFormat.binary64 bits).toBits ==
            expected) = true := by
  decide +kernel

/-- Widening a binary16 carrier value is the nearest-even reference cast of its word to
binary32. -/
example (x : Native.Half) :
    x.val = Float32.ofBits (Model.cast Native.halfFormat.model FloatFormat.binary32
      (Model.ofNatBits x.toBits.toNat) .nearest).toNatBits.toUInt32 :=
  Native.Carrier.val_eq_spec x

/-- The same for bfloat16, whose widening places the word in the high half of binary32. -/
example (x : Native.BFloat16) :
    x.val = Float32.ofBits (Model.cast Native.bfloat16Format.model FloatFormat.binary32
      (Model.ofNatBits x.toBits.toNat) .nearest).toNatBits.toUInt32 :=
  Native.Carrier.val_eq_spec x

/-- NaN normalization keeps the class of every word: the stored word of a carrier value is a
NaN word exactly when the word it was built from is. -/
example (bits : UInt16) :
    Native.halfFormat.infinity < (Native.Half.ofBits bits).toBits &&& 0x7FFF ↔
      Native.halfFormat.infinity < bits &&& 0x7FFF :=
  Native.Carrier.isNaNWord_ofBits_iff bits

/-- A binary32 value as the model, outside the section below, whose generic codec would hide the
binary32 instance. -/
def model32 (x : Float32) : Model FloatFormat.binary32 :=
  ExecFloat.Binary.toModel (ExecFloat.Binary.ofFloat32 x : FloatLib.Floats.Binary32)

/-- A binary64 value as the model. -/
def model64 (x : Float) : Model FloatFormat.binary64 :=
  ExecFloat.Binary.toModel (ExecFloat.Binary.ofFloat x : FloatLib.Floats.Binary64)

section Reference

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" => ExecFloat (Configured.Family format code plan)

/-- The exact binary64 value of a format that binary64 contains. -/
def exactFloat (x : Value) : Float :=
  ExecFloat.Binary.toFloat (ExecFloat.Binary.ofModel (Model.cast format FloatFormat.binary64
    (ExecFloat.Binary.toModel x)) : FloatLib.Floats.Binary64)

/-- The model's rounding of a binary32 value. -/
def ofFloat32 (x : Float32) : Value :=
  ExecFloat.Binary.ofModel (Model.cast FloatFormat.binary32 format (model32 x))

/-- The model's rounding of a binary64 value, once, from its exact value. -/
def ofFloat64 (x : Float) : Value :=
  ExecFloat.Binary.ofModel (Model.cast FloatFormat.binary64 format (model64 x))

end Reference

/-- A 16-bit carrier under test. -/
structure Carrier (α : Type) where
  ofBits : UInt16 → α
  toBits : α → UInt16
  ofFloat : Float → α
  ofFloat32 : Float32 → α
  toFloat : α → Float
  isNaN : α → Bool
  /-- The canonical NaN word. -/
  nan : UInt16
  /-- The largest finite positive word. -/
  largest : UInt16
  add : α → α → α
  sub : α → α → α
  mul : α → α → α
  div : α → α → α
  sqrt : α → α
  neg : α → α
  lt : α → α → Bool
  le : α → α → Bool
  beq : α → α → Bool

/-- The software model with the same words. -/
structure Reference (β : Type) where
  ofNatBits : Nat → β
  toNatBits : β → Nat
  isNaN : β → Bool
  ofFloat : Float → β
  ofFloat32 : Float32 → β
  add : β → β → β
  sub : β → β → β
  mul : β → β → β
  div : β → β → β
  sqrt : β → β
  neg : β → β
  /-- The IEEE comparison of two values; `none` when a NaN makes them unordered. -/
  compare : β → β → Option Ordering

/-- The binary16 carrier. -/
def half : Carrier Native.Half :=
  { ofBits := Native.Half.ofBits, toBits := Native.Half.toBits
    ofFloat := Native.Half.ofFloat, ofFloat32 := Native.Half.ofFloat32
    toFloat := Native.Half.toFloat, isNaN := Native.Half.isNaN, nan := 0x7E00
    largest := 0x7BFF, add := (· + ·), sub := (· - ·), mul := (· * ·), div := (· / ·)
    sqrt := FloatLib.Numerics.MathFunctions.sqrt, neg := (- ·), lt := fun x y => decide (x < y)
    le := fun x y => decide (x ≤ y), beq := (· == ·) }

/-- The bfloat16 carrier. -/
def bfloat : Carrier Native.BFloat16 :=
  { ofBits := Native.BFloat16.ofBits, toBits := Native.BFloat16.toBits
    ofFloat := Native.BFloat16.ofFloat, ofFloat32 := Native.BFloat16.ofFloat32
    toFloat := Native.BFloat16.toFloat, isNaN := Native.BFloat16.isNaN, nan := 0x7FC0
    largest := 0x7F7F, add := (· + ·), sub := (· - ·), mul := (· * ·), div := (· / ·)
    sqrt := FloatLib.Numerics.MathFunctions.sqrt, neg := (- ·), lt := fun x y => decide (x < y)
    le := fun x y => decide (x ≤ y), beq := (· == ·) }

/-- The binary16 model, the reference for `half`. -/
def binary16 : Reference Binary16 :=
  { ofNatBits := ExecFloat.Binary.ofNatBits, toNatBits := ExecFloat.Binary.toNatBits
    isNaN := ExecFloat.Binary.isNaN, ofFloat := ofFloat64, ofFloat32 := ofFloat32
    add := (· + ·), sub := (· - ·), mul := (· * ·), div := (· / ·)
    sqrt := fun x => ExecFloat.Binary.ofModel (Model.sqrt (ExecFloat.Binary.toModel x))
    neg := fun x => ExecFloat.Binary.ofModel (Model.neg (ExecFloat.Binary.toModel x))
    compare := fun x y =>
      Model.compare (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y) }

/-- The bfloat16 model, the reference for `bfloat`. -/
def brain16 : Reference BFloat16 :=
  { ofNatBits := ExecFloat.Binary.ofNatBits, toNatBits := ExecFloat.Binary.toNatBits
    isNaN := ExecFloat.Binary.isNaN, ofFloat := ofFloat64, ofFloat32 := ofFloat32
    add := (· + ·), sub := (· - ·), mul := (· * ·), div := (· / ·)
    sqrt := fun x => ExecFloat.Binary.ofModel (Model.sqrt (ExecFloat.Binary.toModel x))
    neg := fun x => ExecFloat.Binary.ofModel (Model.neg (ExecFloat.Binary.toModel x))
    compare := fun x y =>
      Model.compare (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y) }

/-- SplitMix64's output function. -/
def splitmix64 (z : UInt64) : UInt64 :=
  let z := z + 0x9e3779b97f4a7c15
  let z := (z ^^^ (z >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  z ^^^ (z >>> 31)

/-- `count` pseudorandom 64-bit words from `seed`. -/
def randomWords (seed : UInt64) (count : Nat) : Array UInt64 :=
  (Array.range count).map fun i => splitmix64 (seed + i.toUInt64 * 0x632be59bd9b4e019)

/-- The carrier's word agrees with the model's: equal, or both NaN. -/
def agrees {α β : Type} (carrier : Carrier α) (reference : Reference β) (x : α) (y : β) :
    Bool :=
  if reference.isNaN y then carrier.isNaN x && carrier.toBits x == carrier.nan
  else carrier.toBits x == (reference.toNatBits y).toUInt16

/-- Words that do not decode to the model's value of the same word, or do not encode back. -/
def wordFailures {α β : Type} (carrier : Carrier α) (reference : Reference β)
    (exact : β → Float) : Nat := Id.run do
  let mut failures := 0
  for w in [0:65536] do
    let x := carrier.ofBits w.toUInt16
    let y := reference.ofNatBits w
    let ok :=
      if reference.isNaN y then carrier.isNaN x && carrier.toBits x == carrier.nan
      else carrier.toBits x == w.toUInt16 && (carrier.toFloat x).toBits == (exact y).toBits
    unless ok do failures := failures + 1
  return failures

/-- Binary64 inputs around every `stride`-th positive finite word: the midpoint to the next word,
one binary64 step on either side of it, and the word itself, with both signs. One step above a
midpoint must round up, which rounding through binary32 first gets wrong when the lower word is
even. -/
def boundaryInputs {α : Type} (carrier : Carrier α) (stride : Nat) : Array Float := Id.run do
  let mut inputs := #[]
  for i in [0:carrier.largest.toNat / stride + 1] do
    let w := i * stride
    let low := carrier.toFloat (carrier.ofBits w.toUInt16)
    let high := carrier.toFloat (carrier.ofBits (w + 1).toUInt16)
    let middle := if high.isFinite then (low + high) / 2 else low
    for x in [low, middle, Float.ofBits (middle.toBits + 1), Float.ofBits (middle.toBits - 1)] do
      inputs := inputs.push x |>.push (-x)
  return inputs

/-- Values every conversion must handle: zeros, infinities, NaN, the binary64 extremes, overflow
boundaries of both formats, and the binary16 subnormal range. -/
def specialInputs : Array Float :=
  let inf := Float.ofBits 0x7ff0000000000000
  #[0.0, -0.0, inf, -inf, Float.ofBits 0x7ff8000000000000,
    Float.ofBits 0xfff0000000000001, Float.ofBits 0xfff8123456789abc,
    Float.ofBits 0x7fefffffffffffff,
    Float.ofBits 1, -Float.ofBits 1, 1e-8, 1e-6, 1e5, 65504.0, 65519.99, 65520.0, 65536.0,
    -65520.0, 5.960464477539063e-8, 2.9802322387695312e-8, 2.9802322387695316e-8, 4.5e-8,
    6.103515625e-5, 6.1e-5, 1.0 / 3.0, 0.1, -0.1, 3.14159265358979323846, 3.3895313892515355e38,
    3.3961775292304465e38, 3.40e38, 1.1754943508222875e-38, 9.183549615799121e-41, 1e-45,
    -1e-40]

/-- Random binary64 values with exponents from `low` to `high`. -/
def randomInputs (seed : UInt64) (count : Nat) (low high : Int) : Array Float :=
  (randomWords seed count).map fun (word : UInt64) =>
    let span := (high - low + 1).toNat
    let exponent : Int := low + ((word >>> 52).toNat % span : Nat)
    let biased : UInt64 := (exponent + 1023).toNat.toUInt64 &&& 0x7ff
    let kept : UInt64 := word &&& 0x800fffffffffffff
    Float.ofBits (kept ||| (biased <<< 52))

/-- Conversions from binary64 and from binary32 (the nearest binary32 value and its two
neighbours) that do not round as the model's exact conversions do. -/
def conversionFailures {α β : Type} (carrier : Carrier α) (reference : Reference β)
    (inputs : Array Float) : Nat := Id.run do
  let mut failures := 0
  for x in inputs do
    unless agrees carrier reference (carrier.ofFloat x) (reference.ofFloat x) do
      failures := failures + 1
    let single := x.toFloat32
    for y in [single, Float32.ofBits (single.toBits + 1), Float32.ofBits (single.toBits - 1)] do
      unless agrees carrier reference (carrier.ofFloat32 y) (reference.ofFloat32 y) do
        failures := failures + 1
  return failures

/-- Operations on random words, including NaN, infinite, and subnormal operands, that disagree
with the model's nearest-even arithmetic. -/
def arithmeticFailures {α β : Type} (carrier : Carrier α) (reference : Reference β)
    (seed : UInt64) (count : Nat) : Nat := Id.run do
  let mut failures := 0
  for word in randomWords seed count do
    let a := (word &&& 0xffff).toUInt16
    let b := ((word >>> 16) &&& 0xffff).toUInt16
    -- Every fourth pair takes operands of similar magnitude, where cancellation happens.
    let b := if (word >>> 32) % 4 == 0 then (a ^^^ ((word >>> 34) &&& 0x3f).toUInt16) else b
    let x := carrier.ofBits a
    let y := carrier.ofBits b
    let x' := reference.ofNatBits a.toNat
    let y' := reference.ofNatBits b.toNat
    for (op, op') in [(carrier.add, reference.add), (carrier.sub, reference.sub),
        (carrier.mul, reference.mul), (carrier.div, reference.div)] do
      unless agrees carrier reference (op x y) (op' x' y') do failures := failures + 1
  return failures

/-- Square roots, negations and comparisons on random words that disagree with the model: the
root and the negation as words, and `<`, `≤`, `==` as the IEEE comparison, which is false on
unordered operands and equates the two zeros. -/
def unaryAndOrderFailures {α β : Type} (carrier : Carrier α) (reference : Reference β)
    (seed : UInt64) (count : Nat) : Nat := Id.run do
  let mut failures := 0
  for word in randomWords seed count do
    let a := (word &&& 0xffff).toUInt16
    let b := ((word >>> 16) &&& 0xffff).toUInt16
    -- Every fourth pair compares a word with itself or a neighbour, where the order is tight.
    let b := if (word >>> 32) % 4 == 0 then (a ^^^ ((word >>> 34) &&& 0x3).toUInt16) else b
    let x := carrier.ofBits a
    let y := carrier.ofBits b
    let x' := reference.ofNatBits a.toNat
    let y' := reference.ofNatBits b.toNat
    unless agrees carrier reference (carrier.sqrt x) (reference.sqrt x') do
      failures := failures + 1
    unless agrees carrier reference (carrier.neg x) (reference.neg x') do
      failures := failures + 1
    let order := reference.compare x' y'
    unless carrier.lt x y == (order == some .lt) do failures := failures + 1
    unless carrier.le x y == (order == some .lt || order == some .eq) do failures := failures + 1
    unless carrier.beq x y == (order == some .eq) do failures := failures + 1
  return failures

/-- The four arithmetic operations on the words of the two lowest exponent fields of a format
with `fraction` stored bits, both signs, against each other and against every `stride`-th word of
the format. In bfloat16 these are the values below `2 ^ -125`, where the binary32 intermediate
is subnormal and carries fewer than 24 bits. -/
def tinyFailures {α β : Type} (carrier : Carrier α) (reference : Reference β)
    (fraction stride : Nat) : Nat := Id.run do
  let mut failures := 0
  let tiny : Array UInt16 := Id.run do
    let mut words := #[]
    for w in [0:2 ^ (fraction + 1)] do
      words := words.push w.toUInt16 |>.push (w + 0x8000).toUInt16
    return words
  let spread : Array UInt16 := (Array.range (65536 / stride + 1)).map fun i => (i * stride).toUInt16
  for a in tiny do
    let x := carrier.ofBits a
    let x' := reference.ofNatBits a.toNat
    for b in tiny ++ spread do
      let y := carrier.ofBits b
      let y' := reference.ofNatBits b.toNat
      for (op, op') in [(carrier.add, reference.add), (carrier.sub, reference.sub),
          (carrier.mul, reference.mul), (carrier.div, reference.div)] do
        unless agrees carrier reference (op x y) (op' x' y') do failures := failures + 1
        unless agrees carrier reference (op y x) (op' y' x') do failures := failures + 1
  return failures

/-- Every disagreement of both carriers with their models. -/
def totalFailures : Nat :=
  wordFailures half binary16 exactFloat + wordFailures bfloat brain16 exactFloat +
    conversionFailures half binary16
      (specialInputs ++ boundaryInputs half 3 ++ randomInputs 11 4000 (-30) 17) +
    conversionFailures bfloat brain16
      (specialInputs ++ boundaryInputs bfloat 37 ++ randomInputs 13 4000 (-140) 130) +
    arithmeticFailures half binary16 17 5000 + arithmeticFailures bfloat brain16 19 5000 +
    unaryAndOrderFailures half binary16 23 5000 + unaryAndOrderFailures bfloat brain16 29 5000 +
    tinyFailures bfloat brain16 7 97

end FloatLibTests.Regression.BinaryInterchange.NativeHalf
