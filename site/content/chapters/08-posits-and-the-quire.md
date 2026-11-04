---
number: "08"
slug: posits-and-the-quire
title: Posits and the quire
summary: A posit is a number format that keeps the most digits for numbers near one, and its quire adds up products exactly, within a proved capacity, so a dot product rounds once.
phases: [posits]
---

A posit stores a real number in a fixed number of bits, as an IEEE float does, but it splits them differently between the number's size and its digits, the significand bits. In binary32, the usual 32-bit float, a number near one and a number near $2^{64}$ get the same 24 significand bits. Ask a 32-bit posit for the number right after one and it says $1 + 2^{-27}$, where binary32 says $1 + 2^{-23}$, so near one the posit's grid is sixteen times finer. Near $2^{64}$ the posit has 12 significand bits left, half of binary32's 24.

It's like a city map that spends its ink on fine detail downtown, near one, and rougher strokes the farther out you go, toward huge numbers or tiny ones. Same 32 bits, spent differently. The trick is the regime, a run of identical bits that holds part of the exponent, the power of two that sets the size. The farther a value is from one, the longer the run and the fewer bits are left for the fraction, which holds the digits.

The 2022 Standard for Posit Arithmetic [@positStandard2022] fixes the rest, and it's a short list: one width parameter, one rounding rule, one exceptional value called NaR (not a real), no signed zero, no infinities, and an exact accumulator called the quire. The quire adds up products without rounding, so a whole dot product, a sum like $a_1 b_1 + a_2 b_2 + a_3 b_3$, rounds once, as long as its running sum stays in range.

## How to create a posit

In FloatLib a format is a Lean type, and a posit is one more `ExecFloat` type, used like the binary formats of [the IEEE chapter](#/chapter/ieee-binary-formats). `Posit32` is short for `ExecFloat.Posit (bits := 32)`, and `Posit8`, `Posit16` and `Posit64` name the other standard widths. `toRat?` reads a result as an exact rational, wrapped in `some` for a reason we'll come to, and the comment under each `#eval` is what Lean prints. If you start with this:

```lean
open FloatLib.Floats

def x : Posit32 := 1.5
def y : Posit32 := 2.25
def z : Posit32 := x * y + (x + y)

#eval ExecFloat.Posit.toRat? z
-- some (57 / 8)

#eval ExecFloat.Posit.toRat? (.ofRat (1 / 3) : Posit8)
-- some (11 / 32)
```

you get $57/8$ for `z`. Every intermediate fits, so $1.5 \cdot 2.25 + (1.5 + 2.25) = 7.125 = 57/8$ comes out exactly. A literal, or `.ofRat` for any rational, rounds once from the exact value, so in eight bits the last line's one third lands on $11/32$.

## How much precision does a posit have?

Let's measure the map, starting downtown. `ExecFloat.Posit.next` gives the next posit up, so the gap shows how fine the grid is. Near one the regime run is a single bit and the fraction gets most of the word:

```lean
def one : Posit32 := 1

#eval ExecFloat.Posit.toRat? one
-- some 1
#eval ExecFloat.Posit.toRat? (ExecFloat.Posit.next one)
-- some (134217729 / 134217728)
```

That's $1 + 2^{-27}$, 28 significand bits where binary32 has 24. At the two ends of the range, `next 0` is the smallest positive posit, and `prior nar`, one word below NaR, is the largest:

```lean
#eval ExecFloat.Posit.toRat? (ExecFloat.Posit.next (0 : Posit32))
-- some (1 / 1329227995784915872903807060280344576)
#eval ExecFloat.Posit.toRat? (ExecFloat.Posit.prior (ExecFloat.Posit.nar : Posit32))
-- some 1329227995784915872903807060280344576
```

The answers are reciprocals, $2^{\pm 120}$, and out here the regime has eaten nearly everything. If you count up through the words one at a time, wrapping around at the end, NaR comes right after the largest positive posit, which is why `prior nar` lands on it. Binary32 reaches about $2^{128}$ and, through subnormals (its extra-small numbers near zero), $2^{-149}$.

[Figure 8.1](#/chapter/posits-and-the-quire/figure-ch14-tapered-precision) follows that trade across every binade, the stretch between two neighbouring powers of two. Near the extremes the regime leaves too few exponent bits to reach every binade, so gaps mark binades with no positive posit and isolated ticks those with just one.

![Significand bits available to a 32-bit posit and to binary32, computed from the two formats' parameters; gaps mark binades with no positive posit, and isolated ticks mark binades containing just one](assets/ch14-tapered-precision.png "Significand bits by magnitude, with gaps for empty binades and isolated ticks for single-posit ones.")

In 16 bits the taper, the way precision thins out away from one, shows at ordinary sizes: the posit after 4096 is 4112, a spacing of 16, or 8 fraction bits where binary16, the 16-bit IEEE float, has 10.

```lean
#eval ExecFloat.Posit.toRat? (ExecFloat.Posit.next (4096 : Posit16))
-- some 4112
```

De Dinechin, Forget, Muller, and Uguen discuss this dependence on magnitude [@deDinechinPosits2019]. It has a practical side: a change of units changes your precision. Store 4096 meters in a `Posit16` and the spacing is 16 meters. Store the same distance as 4.096 kilometers and the regime run is back to a single bit, with 11 fraction bits and a spacing under two meters.

## What does the width decide?

Where does the taper come from? To find out we'll read the bits, but first let's name a format. Gustafson and Yonemoto's 2017 proposal [@gustafsonYonemoto2017] wrote formats as `posit<n, es>`, with `es`, for exponent size, the maximum exponent width. The 2022 standard allows at most two exponent bits, so the width alone names a format. Our posit descriptor [[FloatLib.Floats.Formats.Posit.Format]], the record of a format's parameters, is one natural number with a proof that it's at least 2, the smallest width where zero, one, NaR and minus one all exist. `decide` supplies the proof for a numeral, and `{ bits := 1 }` fails with `a posit format requires bits ≥ 2`. You can ask a descriptor for the rest:

```lean
example : (ExecFloat.Posit.descriptor 32).payloadBits = 31 := rfl
example : (ExecFloat.Posit.descriptor 32).exponentBits = 2 := rfl
example : (ExecFloat.Posit.descriptor 32).regimeExponentStep = 4 := rfl
example : (ExecFloat.Posit.descriptor 32).oneCodeNat = 0x40000000 := by decide
```

Everything else in the [posit descriptor](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Descriptor.lean) follows from the width. A regime step is worth 4 in the binary exponent, so a factor of 16 in value. The posit for one is `0x40000000`: sign 0, regime `10`, exponent `00` and a zero fraction. The width picks the storage too, from a `UInt8` to two `UInt64` limbs, the pieces a wide number is split into, through 128 bits, with the exact-width model beyond.

Each format comes in two forms. The model, [[FloatLib.Floats.Formats.Posit.Model]], is a `BitVec` of the format's width that the proofs reason about, and the configured type, like `Posit32`, is the one you compute with. Every operation on every storage type is proved equal to the same model, and `#float_info Posit32` tells you which kernel, the code doing the arithmetic, you got.

## How to read the bits of a posit

Now let's take a word apart the way the decoder does. A word is the raw bit pattern, written here in hexadecimal, one digit for every four bits. The top bit is the sign, and a negative value is stored as the two's complement of the whole word, the usual way computers store negative integers, so our [posit decoder](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Model/Decode.lean) first gets the magnitude back:

$$
m = \begin{cases} w & \text{if the sign bit is } 0, \\ 2^n - w & \text{otherwise.} \end{cases}
$$

The low $n - 1$ bits of $m$ start with the regime, a run of identical bits that stops at the first opposite bit, the terminator, or at the end of the word. Think of it as a tally. A run of $r$ ones counts up, $k = r - 1$, a run of $r$ zeros counts down, $k = -r$, and each mark moves the value by a factor of 16. Like any tally it's cheap for small counts and expensive for big ones, and that's where the taper comes from. Then come up to two exponent bits $e$ (missing ones count as zero) and an $f$-bit fraction $F$, and the word means

$$
(-1)^s \cdot (2^{f} + F) \cdot 2^{4k + e - f},
$$

with $s$ the sign bit of $w$. `decodeExact` sorts every model word into zero, NaR, or finite with its fields. Take the 8-bit word `0x6C`. Its payload, the bits after the sign, is `1101100`: two regime ones and a terminator ($k = 1$), exponent `11` ($e = 3$) and fraction `00`. If you run

```lean
open FloatLib.Floats.Formats.Posit in
#eval (Model.ofNatBits (format := ExecFloat.Posit.descriptor 8) 0x6C).decodeExact
-- FloatLib.Floats.Formats.Posit.Model.ExactValue.finite
--   { negative := false,
--     regimeBit := true,
--     regimeRunLength := 2,
--     regimeValue := 1,
--     usedExponentBits := 2,
--     exponentField := 3,
--     fractionBits := 2,
--     fractionField := 0,
--     significand := 4,
--     scale := 5 }
```

you get each field back, and `0x6C` is $4 \cdot 2^5 = 128$. [Figure 8.2](#/chapter/posits-and-the-quire/figure-ch14-posit-layout) sets it beside one, `0x40`, and the extreme words `0x01` and `0x7F`, which are nothing but regime. Decoding those two gives the ends of the range, so an 8-bit posit runs from $2^{-24}$ to $2^{24}$. And `0x80`, the sign bit on its own, is NaR, which has no dyadic value, no integer times a power of two for `toDyadic?` to report.

![Four 8-bit posit words with their sign, regime, terminator, exponent and fraction fields, ordered by value, so that the regime run lengthens and the fraction shrinks toward both ends of the range](assets/ch14-posit-layout.png "Four posit8 encodings: longer regimes leave fewer exponent and fraction bits.")

```lean
open FloatLib.Floats.Formats.Posit in
#eval (Model.ofNatBits (format := ExecFloat.Posit.descriptor 8) 0x01).toDyadic?
-- some { negative := false, significand := 1, exponent := -24 }
open FloatLib.Floats.Formats.Posit in
#eval (Model.ofNatBits (format := ExecFloat.Posit.descriptor 8) 0x7F).toDyadic?
-- some { negative := false, significand := 1, exponent := 24 }
open FloatLib.Floats.Formats.Posit in
#eval (Model.ofNatBits (format := ExecFloat.Posit.descriptor 8) 0x80).toDyadic?
-- none
```

## How to print, widen and convert a posit

### How to print and parse decimal text

A finite posit's denominator is a power of two, so its decimal expansion terminates: $3\cdot2^{-3}=375\cdot10^{-3}$ prints as `0.375`. `Model.display` and the configured `ToString` print that exact decimal, and parsing reads a decimal exactly and rounds once. We prove every word at every valid width comes back from its text, NaR included, and on the configured type for any lawful codec, any way of packing words into storage that obeys the codec laws. The text is exact, not shortest, so a redundant zero can survive :)

### How to move to a wider posit

Widening, moving to a posit with more bits, appends zeros: the 8-bit `0x6c` becomes `0x6c00` in 16 bits, which is 128 too. We prove this for every source width and every wider destination, NaR included, and for a finite source we prove it agrees with exact decoding followed by rounding. On the configured type both hold for every lawful storage codec.

### How to convert a posit to an integer

Integers come with one catch, and it isn't the rounding. Integer conversion rounds to nearest with ties to even, so $1.5$ and $2.5$ both go to 2. The standard signals failure with a sentinel, a special result word: the one with only its most significant bit set. But a signed minimum or an unsigned $2^{w-1}$ is that same word as a successful result. Our sentinel theorems describe both cases, and the word alone can't tell you whether the conversion failed. `floor`, `ceil` and `nearestInt` return representable integers with exact values proved at every width, and `nearestInt_spec` adds the half-unit error bound and the even tie rule.

## How does a posit round?

A result that lands between two posits has to round, and there's one rounding mode, an odd one. Between adjacent $n$-bit posits $U$ and $W$, Section 4.1 of the standard puts the boundary at the $(n+1)$-bit posit encoded as $U$ followed by a one bit, with ties going to the even low bit. If the extra bit lands in the fraction, that's the midpoint. If it lands in the exponent field, it isn't, so [[FloatLib.Floats.Formats.Posit.Model.roundRat]] takes the boundary from `nextPrecision`, the format with one more bit, and never averages.

The two largest positive 8-bit posits show how odd it gets. Code `0x7e` is `0 111111 0`, with no room for an exponent, so its value is $2^{4\cdot5}=2^{20}$, and `0x7f` is $2^{24}$. Append a one to the lower word and read it as a 9-bit posit:

$$
\underbrace{0}_{\text{sign}}\;
\underbrace{111111}_{k=5}\;
\underbrace{0}_{\text{terminator}}\;
\underbrace{1}_{\text{exponent prefix}}
\quad\longmapsto\quad 2^{4\cdot5+2}=2^{22}.
$$

The extra one is the high exponent bit, so the threshold is $2^{22}$, not the midpoint $17\cdot2^{19}$. Now round $2^{23}$. It's above the threshold and goes to `0x7f`, though its distances to the lower and upper neighbours are $7\cdot2^{20}$ and $8\cdot2^{20}$. The rounding picked the neighbour farther away :)

**Note:** Agreeing with `roundRat` guarantees the standard's boundary rule, not nearest-value rounding, so an IEEE half-ulp argument, which bounds the error by half the gap between neighbours, doesn't carry over as is.

## What happens to huge and tiny results?

Nothing overflows to infinity or underflows to zero: nonzero magnitudes beyond either end round to the smallest or largest positive posit. This is saturation, and you can watch it by starting from $10^{39}$:

```lean
def big : Posit32 := 1000000000000000000000000000000000000000

#eval ExecFloat.Posit.toRat? big
-- some 1329227995784915872903807060280344576
#eval ExecFloat.Posit.toRat? (big * big)
-- some 1329227995784915872903807060280344576
#eval ExecFloat.Posit.toRat? ((1 : Posit32) / big / big)
-- some (1 / 1329227995784915872903807060280344576)
```

Every answer is $2^{\pm 120}$. The literal saturates, squaring stays put, and dividing one by it twice stops at the smallest positive word, never zero.

## What is NaR?

Some results, like a division by zero, have no real value. Posits get by with two special words. The all-zero word is the only zero, and the word with only the sign bit set is NaR, "not a real". There's no negative zero, infinity, NaN payload or subnormal. NaR is the `notAReal` value of `NumericalValue Rat`, FloatLib's type for what a word means, and `toRat?` returns `none` for NaR alone:

```lean
#eval ExecFloat.Posit.toNatBits (ExecFloat.Posit.nar : Posit32)
-- 2147483648
#eval ExecFloat.Posit.toRat? (ExecFloat.Posit.nar : Posit32)
-- none
```

NaR spreads through arithmetic, and division by zero and the square root of a negative number produce it. `isNaR` tests for it:

```lean
#eval ExecFloat.Posit.isNaR (x / 0)
-- true
#eval ExecFloat.Posit.isNaR (ExecFloat.sqrt (0 - x))
-- true
#eval ExecFloat.Posit.isNaR (x + ExecFloat.Posit.nar)
-- true
```

What about an IEEE infinity or NaN coming in? Section 6.5 of the standard converts IEEE infinities and NaNs to NaR and both signed zeros to zero. Our default [conversion context](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Configured/Conversion/Runtime.lean), the policies a conversion follows, does the same, using `toNaR` for both `InfinityPolicy` and `ExceptionalPolicy` and setting `mappedSpecial := true` whenever it maps an infinity or NaN. If you'd rather have a number for an infinity, `saturate` clamps to signed `maxPos` and sets `inexact`, `overflow`, `saturated` and `mappedSpecial`. And to make infinity or NaN fail, pass a rejection context to `cast` as its `context` option:

```lean
example : ExecFloat.Posit.Conversion.Context :=
  { infinity := .reject, exceptional := .reject }
```

## How do you know the arithmetic is right?

Correct arithmetic means computing the exact result and rounding it once, and that's what our [reference definitions](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Arithmetic/Spec.lean) do. [[FloatLib.Floats.Formats.Posit.Model.Spec.add]] adds the operands as `Rat` and calls `roundRat`, `div` returns NaR for a zero divisor, and `fma`, the fused multiply-add, rounds the exact $a \cdot b + c$. `roundSqrtRat` compares the radicand, the number under the root, with squared posit boundaries, since a square root needn't be rational. Host `Float`, your processor's floating point, appears nowhere. The public theorems say the operations you run equal their specifications:

```lean
example (a b : Posit32) :
    ExecFloat.add a b = ExecFloat.Spec.add a b :=
  ExecFloat.Proof.add_eq_spec a b

example (a : Posit32) :
    ExecFloat.sqrt a = ExecFloat.Spec.sqrt a :=
  ExecFloat.Proof.sqrt_eq_spec a

example (a b c : Posit32) :
    ExecFloat.fma a b c = ExecFloat.Spec.fma a b c :=
  ExecFloat.Proof.fma_eq_spec a b c
```

Behind those three examples, [[FloatLib.Floats.ExecFloat.Proof.add_eq_spec]] and its companions tie the specifications to certified kernels that work in integers and dyadics, never `Rat`. Division uses one integer division and an exact remainder test for the sticky bit, the record of nonzero discarded bits, which [[FloatLib.Floats.Formats.Posit.Model.DirectDyadicQuotient.round_eq_reference]] proves agrees with the specification, and square root works the same way.

## How to compare and step through posits

Comparison comes straight from the encoding. Read a posit word as a two's-complement integer and you get the numerical order, with NaR least. The [`LinearOrder` instance](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Comparison.lean), which tells Lean that any two posits can be compared, is defined through `signedCode`, and `compareLess_eq_true_iff` says the executable comparison agrees with it, so NaR is ordered without a rational value. Both of these come out `true`:

```lean
#eval decide ((ExecFloat.Posit.nar : Posit32) < 0)
-- true
#eval decide (x < y)
-- true
```

`next` and `prior` step the word by one, wrapping around, and `prior_next` proves they undo each other. Words and values match one to one, so `Model format` gets a `FinEnum` instance listing all $2^n$ elements. An exhaustive round-trip check covers widths 2 through 8: every word other than NaR decodes and rounds back to itself, and NaR has its own closed theorems. In Lean they look like this:

```lean
example (a : Posit32) : ExecFloat.Posit.prior (ExecFloat.Posit.next a) = a :=
  ExecFloat.Posit.prior_next a

open FloatLib.Floats.Formats.Posit in
example : FinEnum.card (Model (ExecFloat.Posit.descriptor 8)) = 256 :=
  Model.finEnum_card _
```

## What is a quire?

Each arithmetic operation so far rounds once, so a dot product summed in a posit rounds at every step. The quire is the fix: a ledger kept in the smallest unit any product can have. Its least significant bit, the lowest one, is worth the square of the smallest positive posit, so every posit and every product of two posits is a whole number of units. Entries go in exactly and nothing rounds until you close the books, so a dot product rounds once.

For an $n$-bit posit the standard fixes a two's-complement word of $16n$ bits whose least significant bit is worth $2^{16 - 8n}$, 512 bits at a scale of $2^{-240}$ for `Posit32`. The most negative word is quire NaR, and the bits above the largest product in [Figure 8.3](#/chapter/posits-and-the-quire/figure-ch14-quire) are headroom for carries.

![The 512-bit posit32 quire as a fixed-point word, with landmark weights 2^240 at bit 480, 1 at bit 240, and 2^-240 at bit 0, plus thirty carry bits and the sign bit](assets/ch14-quire.png "From zero, the quire accumulates strictly fewer than 2^31 finite posit32 products exactly.")

```lean
open FloatLib.Floats.Formats.Posit in
example : Quire.width (ExecFloat.Posit.descriptor 32) = 512 := rfl
open FloatLib.Floats.Formats.Posit in
example : Quire.scaleExponent (ExecFloat.Posit.descriptor 32) = -240 := by decide
```

### How to add products in a quire

Let's put a product into a quire. The model quire is [[FloatLib.Floats.Formats.Posit.Quire.Model]], a `FixedInt` (a signed integer of fixed width), and the configured `ExecFloat.Posit.Quire (bits := n)`, `Quire32` for `Posit32` and so on, shares the posit's width, so mixing widths is a type error. The names say what they do. `qMulAdd`, quire multiply-add, adds the exact product of two posits, and `qToP`, quire to posit, rounds back to a posit. Start from the empty quire with `x` and `y` from the first example:

```lean
def q0 : Quire32 := ExecFloat.Posit.Quire.zero
def q1 : Quire32 := ExecFloat.Posit.Quire.qMulAdd q0 x y
def rounded : Posit32 := ExecFloat.Posit.Quire.qToP q1

#eval ExecFloat.Posit.Quire.toRat? q1
-- some (27 / 8)
#eval ExecFloat.Posit.toRat? rounded
-- some (27 / 8)
```

You get $27/8$ both times. It goes in exactly and, being a posit itself, comes back unchanged.

### Why does a quire give a better answer?

Say you're adding up the 16-bit products $4096 \cdot 1$, $1 \cdot \tfrac{1}{2}$, and $4096 \cdot (-1)$, which come to $\tfrac{1}{2}$. Accumulate them with fused multiply-adds in the posit and the partial sum $4096.5$ rounds to 4096, where the spacing is 16, so the answer is 0. In the quire nothing rounds until the end:

```lean
def a1 : Posit16 := 4096
def b1 : Posit16 := 1
def a2 : Posit16 := 1
def b2 : Posit16 := 0.5
def a3 : Posit16 := 4096
def b3 : Posit16 := -1

def naive : Posit16 := ExecFloat.fma a3 b3 (ExecFloat.fma a2 b2 (a1 * b1))
#eval ExecFloat.Posit.toRat? naive
-- some 0

def exact : Quire16 :=
  ExecFloat.Posit.Quire.qMulAdd
    (ExecFloat.Posit.Quire.qMulAdd
      (ExecFloat.Posit.Quire.qMulAdd ExecFloat.Posit.Quire.zero a1 b1) a2 b2) a3 b3
#eval ExecFloat.Posit.Quire.toRat? exact
-- some (1 / 2)
#eval ExecFloat.Posit.toRat? (ExecFloat.Posit.Quire.qToP exact : Posit16)
-- some (1 / 2)
```

Let's open the ledger and see why. At width 16 the quire has 256 bits and scale $2^{-112}$, and dividing each product by the scale gives

$$
4096 \longmapsto 2^{124},\qquad
\tfrac12 \longmapsto 2^{111},\qquad
-4096 \longmapsto -2^{124}.
$$

After the second product the coefficient, the integer the quire stores, is $2^{124}+2^{111}$, the third cancels bit 124, and $2^{111}$ decodes to $\tfrac12$. The `Posit16` partial sum, with eight fraction bits at 4096, loses the half for good (cancelling the large products first would have saved it). The quire saves it in either order, provided the coefficient stays in range.

### What is proved about the quire?

Here's what we prove in general. Conversion into the quire is exact for every posit at every valid width, with no side conditions. [[FloatLib.Floats.Formats.Posit.Quire.Model.toRat?_pToQ]] says `(pToQ v).toRat? = v.toRat?`, and `toRat?_pToQ` says the same on the public type:

```lean
example (v : Posit32) :
    ExecFloat.Posit.Quire.toRat? (ExecFloat.Posit.Quire.pToQ v) = ExecFloat.Posit.toRat? v :=
  ExecFloat.Posit.Quire.toRat?_pToQ v
```

Adding a product is exact while the sum stays in range. Take ordinary operands and an ordinary accumulator, none of them NaR. If the new coefficient is an `OrdinaryCoefficient`, one that fits without reaching the NaR word, the quire denotes the old value plus the exact product ([[FloatLib.Floats.Formats.Posit.Quire.Model.toRat?_qMulAdd_of_ordinary]]), and if it isn't, you get quire NaR ([[FloatLib.Floats.Formats.Posit.Quire.Model.qMulAdd_eq_nar_of_not_ordinary]]). A NaR operand or accumulator gives quire NaR as well. Coming back out is one rounding: `qToP` of an ordinary quire is `roundRat` of its exact value, and quire NaR gives posit NaR ([[FloatLib.Floats.Formats.Posit.Quire.Model.qToP_eq_roundRat]]). So within range, the only rounding error in a dot product is the one at the end.

```lean
open FloatLib.Floats.Formats.Posit in
example (q : Quire.Model (ExecFloat.Posit.descriptor 32)) :
    Quire.Model.qToP q =
      match q.toRat? with
      | some rational => Model.roundRat _ rational
      | none => Model.nar _ :=
  Quire.Model.qToP_eq_roundRat q
```

### How many products fit in a quire?

How many entries fit before the ledger overflows? Let's count products first. The largest posit squared, $2^{240}$, sits at bit 480 of the 512-bit word, under the figure's thirty carry bits, and $2^{31}$ copies of it come to $2^{16n - 1}$ units, one past the largest ordinary coefficient. So fewer than $2^{31}$ exact products fit, and that bound is tight. The standard reads two ways here, though, "at most $2^{31}$ terms" in Section 3.2 and "length less than $2^{31}$" in Section 4.2, and the proof takes the second.

For posit addends the limit is $2^{23 + 4n}$, the standard's quire sum limit, the least number of additions that can overflow, so fewer is safe. In Lean they're `productSumTermLimit` and `positSumTermLimit`, the standard's term limits, both exclusive. Our [capacity proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Quire/Capacity.lean) bounds what one posit or product can contribute, and the [accumulation proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Quire/Accumulation.lean) carries those bounds through a loop, giving both.

Below those limits, [[FloatLib.Floats.Formats.Posit.Quire.Model.toRat?_foldMulAdd_zero]] and `toRat?_foldAddP_zero` prove that folding from the zero quire, adding the terms one at a time, never produces NaR and denotes the exact sum. On the public type `toRat?_foldl_qMulAdd_zero` needs only the length bound and `exactProducts?` returning `some`, which says no input is NaR:

```lean
open FloatLib.Floats.Formats.Posit in
example (pairs : List (Posit32 × Posit32)) (products : List Rat)
    (hproducts : ExecFloat.Posit.Quire.exactProducts? pairs = some products)
    (hlength : pairs.length < Quire.Model.productSumTermLimit) :
    ExecFloat.Posit.Quire.toRat?
        (pairs.foldl (fun quire pair => ExecFloat.Posit.Quire.qMulAdd quire pair.1 pair.2)
          ExecFloat.Posit.Quire.zero) =
      some products.sum :=
  ExecFloat.Posit.Quire.toRat?_foldl_qMulAdd_zero pairs products hproducts hlength

open FloatLib.Floats.Formats.Posit in
example : Quire.Model.productSumTermLimit = 2 ^ 31 := rfl
```

A longer loop needs a tighter coefficient bound or an `isNaR` check on the result. Exact accumulators aren't special to posits, either. Kulisch [@kulisch2013] argued for one for IEEE formats for decades, so a benchmark that gives only one format a quire can't credit the difference to the formats alone.

## How to compute roots and powers

Beyond the basic operations the rule is the same: keep the intermediate exact and round once. Our [algebraic API](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/Posit/Algebraic) has `rSqrt`, the reciprocal square root, `hypot`, the fused triple product `fMM`, and integer roots and powers. Take `hypot`, named for the hypotenuse it computes: it rounds neither square of $x^2+y^2$. `fMM` earns its keep at the edges of `Posit32`. With $M$ the largest positive value and $m=1/M$ the smallest, two ordinary multiplications saturate $M \cdot M$ to $M$ and then give $M \cdot m=1$, off by a factor of $2^{120}$, while `fMM` rounds the exact product once, to $M$.

Roots first, since they're the easy part. `rootN` takes positive and negative integer degrees, with the same boundary and tie rules as everything else. Degree zero gives NaR, and a negative input has a real root only for an odd degree.

Powers are trickier. `powInt` computes an integer power exactly, and `compound` forms $(1+x)^n$ without rounding $1+x$ first. Integer exponent zero is the constant-one operation on every finite input, so `compound (-1) 0` and `powInt 0 0` return one, as our [integer-power theorems](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Algebraic/Power/Proof.lean) state, and NaR propagates even then. Two-posit `pow` also takes nonintegral exponents, but a negative base needs an integral exponent, and zero with a nonpositive exponent gives NaR. Our proofs connect `pow`'s in-domain results to `Model.RealRounding.round`, the standard's rounding rule with nonzero saturation.

**Note:** `pow 0 0` is NaR while `powInt 0 0` is one, so swapping one API for the other can change a program's result.

## How to compute exponentials and logarithms

The boundary comparisons behind `pow` also give proved $2^x$, $10^x$ and their minus-one variants. For every finite input the [rational-power theorems](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Algebraic/RationalPower/Proof.lean) identify the result with one rounding of the exact real expression, so $2^x-1$ and $10^x-1$ subtract before rounding. We have no independent external comparison for these, though, so those theorems are their whole guarantee. The [base-two and base-ten logarithms](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/Posit/Logarithm) have real-rounding proofs too, `log2Plus1` and `log10Plus1` included.

The [natural-function API](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/Posit/Elementary) adds `exp`, `expMinus1`, `log` and `logPlus1`, whose [configured proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Configured/Elementary/Proof.lean) show each one equals the real function followed by posit rounding. For `x` decoding to a rational $q>-1$, `logPlus1_eq_real` says the output decodes to

$$
\operatorname{RealRounding.round}\bigl(\log(1+q)\bigr).
$$

Why not just take the logarithm of `1 + x`? At 32 bits $x=2^{-30}$ is representable, but `1 + x` rounds to one, whose logarithm is zero. `logPlus1 x` rounds the logarithm of the exact $1+2^{-30}$, and nonzero saturation keeps it nonzero. `expMinus1` likewise subtracts before rounding.

How far do the real-rounding proofs reach? Every finite input in the domain, extreme magnitudes and saturation included. `log` requires a positive input, `logPlus1` an input greater than $-1$, and invalid inputs or NaR give NaR.

### How to round a number you can't write down

How do you round $\exp(1/2)$ when you can never write it down? You trap it between rationals, a pair of bounds called an enclosure. `Numerics.Enclosure.exp` computes rational bounds, `Numerics.Enclosure.contains_exp` proves the real exponential lies between them, and at degree five both endpoints select the same eight-bit posit:

```lean standalone
import FloatLib.Floats.Formats.Posit.Rounding.Enclosure.Proof

open FloatLib.Numerics
open FloatLib.Floats.Formats.Posit

def format8 : Format := { bits := 8 }

#eval (Model.Enclosure.roundPositive? format8
  (Enclosure.exp (1 / 2) 5)).map Model.toNatBits
-- some 69
```

Decimal `69` is `0x45`, which decodes to $13/8 = 1.625$, the eight-bit posit nearest $\exp(1/2) \approx 1.6487$. Rounding is monotone, so the whole enclosure rounds to that word, and we prove this for any accepted exponential enclosure at any supported width. If the endpoints disagree, the check returns `none` and you need tighter bounds. The logarithm comparator doubles the degree until the boundary falls outside the enclosure, but if the value equalled a boundary, the trap would shrink around it forever.

So we prove it can't. Our [transcendence proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Numerics/Enclosure/Elementary/Transcendental.lean) shows that the exponential of a nonzero rational is transcendental, a root of no nonzero integer polynomial, building on Mathlib's Lindemann-Weierstrass analysis with no extra axioms. The [irrationality proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Numerics/Enclosure/Elementary/Irrational.lean) derive irrationality of that exponential and of the logarithm of a positive rational other than one ($\log 1=0$ is handled on its own), the [termination proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Numerics/Enclosure/Elementary/Termination.lean) shows that a separating enclosure exists, and the [comparison algorithm](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Numerics/Exact/Elementary/Runtime.lean) uses it to define total comparisons.

Cached Taylor enclosures for nonzero arguments in $[-8,8]$ are proved equal to the originals by the [cache theorem](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Numerics/Enclosure/Comparison/Cache.lean). Speed is another matter. We proved that the search terminates, not that it's fast, and a hard comparison can need large rational calculations. These aren't the approximate [binary transcendental kernels](#/chapter/elementary-functions/how-to-compute-exp-log-and-sine) that our testing chapter measures.

## How to compute sines, cosines and tangents

Trigonometry has a wrinkle of its own, and it's $\pi$. Argument reduction, subtracting whole turns $2k\pi$ to bring an angle near zero, is the tricky part. If the stand-in for $\pi$ has $|\pi-p|\leq\varepsilon$, replacing $x-2k\pi$ by $x-2kp$ can add an error as large as $2|k|\varepsilon$, so our sine and cosine enclosures carry that error into their bounds, and their convergence proofs don't assume the period count settles down.

The [trigonometric API](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/Posit/Trigonometric) gives you `sin`, `cos` and `tan` in radians and their principal inverses `arcSin`, `arcCos` and `arcTan`. Model and configured `*_eq_real` theorems identify the result with one posit rounding of the real function, and the [comparison proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Numerics/Exact/Trigonometric/Proof.lean) establish which side of each rational boundary the real value lies on.

Inverse sine and cosine accept $[-1,1]$ and return NaR outside it, and before rounding their real branches range over $[-\pi/2,\pi/2]$ and $[0,\pi]$. Inverse tangent takes every finite input, and its real branch ranges over $(-\pi/2,\pi/2)$. All six propagate NaR. And tangent never meets a pole, where it blows up, because a finite posit is rational and the poles aren't.

## How to measure angles in half-turns

Never meeting a pole has a flip side. Hand ordinary `tan` a posit near $\pi/2$ and it can't know you meant the pole. The [pi-scaled API](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/Posit/Trigonometric/Pi) measures angles in half-turns instead: `sinPi`, `cosPi`, `tanPi`, `arcSinPi`, `arcCosPi` and `arcTanPi`, with model and configured real-rounding proofs. Direct functions multiply the exact input by $\pi$ before rounding, and inverses divide the exact principal angle by $\pi$.

At $x=1/2$, `sinPi x` is one, `cosPi x` zero, and `tanPi x` NaR, because $x\pi=\pi/2$ is a pole. Inverse sine and cosine require inputs in $[-1,1]$, `tanPi` rejects every half-integer input, and like the radian versions, all six propagate NaR. The inverse tangent has a two-argument version too. `arcTan2 x y` gives the angle of $x+iy$ in $(-\pi,\pi]$, real coordinate first as in the Posit Standard, and NaR at the origin. `arcTan2Pi` divides the exact angle by pi, so `arcTan2Pi 1 1` is exactly one quarter. Both have real-rounding proofs for every finite pair except the origin.

## How to compute hyperbolic functions

The [hyperbolic API](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/Posit/Hyperbolic) has `sinH`, `cosH`, `tanH`, `arcSinH`, `arcCosH` and `arcTanH`, and for the model and the configured type alike we prove each result is one rounding of the exact real function. The first four accept every finite input, so only two need watching: `arcCosH` requires $x\geq1$ and `arcTanH` requires $-1<x<1$. NaR or an out-of-domain input gives NaR.

## What does the posit decoder trust about the compiler?

The posit decoder is the one place in the library where we swap in compiled code with `implemented_by`, which tells Lean's compiler to run another function in place of a definition. Every other kernel runs the definition Lean checked or a replacement justified by a proved `csimp` equation, a theorem that lets the compiler swap in an equal function, as [the chapter on running code and proofs](#/chapter/the-numerical-models) explains.

Every theorem about [[FloatLib.Floats.Formats.Posit.Model.toDyadic?]] uses its definition through `decodeExact`. Its compiled code is a private one-pass `Internal.toDyadic?`, and the private theorem `Internal.toDyadic?_eq` in the [posit decoder](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Model/Decode.lean) proves the two equal on every word. But Lean's kernel never sees the substitution, and `Lean.collectAxioms`, which lists a theorem's axioms, shows no trace of it. So we trust the compiler to substitute that function and no other, which matters because this decoder runs in every posit operation and quire conversion. In return, execution gets one pass and proofs keep the transparent field decoder.

## How we compare posits with Universal and SoftPosit

The last kind of evidence here isn't a proof. A proof connects our code to our specification, so it can't check how we read the standard, but a comparison with an independent implementation can. The benchmark runner times Stillwater's Universal library [@stillwaterUniversal] only on workloads where the two agree bit for bit on every output.

Our first comparison with SoftPosit [@softPosit], revision `17d5628`, found 7,562 differences, all from two problems in that version. First, SoftPosit disagreed with itself. Its generic variable-width path, pX2, and its dedicated p32 functions differed on three 32-bit boundary examples, repeated across 7,560 sampled cases, and there the dedicated functions agreed with FloatLib. The other two are 16-bit fused multiply-adds, one on each side of zero, whose exact answers sit just past a tie, such as $52800 + 2^{-56}$. SoftPosit lost the tiny addend from its sticky bit and rounded as if it were a tie.

Another 9,175,040 comparisons over widths 9 through 15 turned up two more FMA inputs, at 14 and 15 bits, with the same lost sticky bit. On all seven distinct inputs, exact rational evaluation agrees with FloatLib. [The testing chapter follows the calculation and source diagnosis](#/chapter/external-validation/why-did-softposit-disagree-with-floatlib), and [the performance chapter](#/chapter/performance) times FloatLib against Universal. These comparisons test software on the stated inputs. They aren't an official posit certification or a validation of a hardware posit unit.
