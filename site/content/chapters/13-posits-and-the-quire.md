---
number: "13"
slug: posits-and-the-quire
title: Posits and the quire
summary: Posits vary their precision with magnitude, while a quire keeps products and sums exact within a proved capacity bound.
phases: [posits]
---

Binary formats reserve the same number of exponent bits in every word, so binary32 has 24 significand bits near one and near $10^{30}$ alike. In a posit the split between exponent and fraction moves with the value. Part of the exponent is written as a run of identical bits whose length varies with the magnitude, which leaves values near one with more fraction bits than values at the extremes. The 2022 Standard for Posit Arithmetic [@positStandard2022] fixes the rest of the design: a single width parameter, one rounding rule, one exceptional value called NaR, no signed zero and no infinities. It also defines an exact fixed-point accumulator called the quire.

The arithmetic still uses the `ExecFloat` interface from [chapter 08](#/chapter/ieee-binary-formats). We write a 32-bit posit as `ExecFloat.Posit (bits := 32)`, or `Posit32`, and use ordinary literals and operators. `Posit8`, `Posit16` and `Posit64` name the other standard widths. Below, `toRat?` reads the result as an exact rational, so inspecting it adds no conversion error:

```lean
open FloatLib.Floats

def x : Posit32 := 1.5
def y : Posit32 := 2.25
def z : Posit32 := x * y + (x + y)

#eval ExecFloat.Posit.toRat? z
-- some (57 / 8)
```

We get $1.5 \cdot 2.25 + (1.5 + 2.25) = 7.125 = 57/8$ with no error at all, because every intermediate is a dyadic rational that fits in the posit's available fraction bits.

## Width fixes the standard posit format

Gustafson and Yonemoto's 2017 proposal [@gustafsonYonemoto2017] wrote posit formats as `posit<n, es>`, with `es` the maximum width of the exponent field, and in 2022 the standard dropped that second parameter. Every standard posit has at most two exponent bits, so the total width $n$ alone identifies a format. The descriptor [[FloatLib.Floats.Formats.Posit.Format]] holds one natural number and a proof that it is at least 2. That lower bound is the standard's own, since Section 2 defines $n$ as any integer greater than 1, and `bits_ge_two` carries the requirement into the type. Two bits is the smallest width at which zero, one, NaR and minus one, the four distinguished words, all exist.

```lean
example : (ExecFloat.Posit.format 32).payloadBits = 31 := rfl
example : (ExecFloat.Posit.format 32).exponentBits = 2 := rfl
example : (ExecFloat.Posit.format 32).regimeExponentStep = 4 := rfl
example : (ExecFloat.Posit.format 32).oneCodeNat = 0x40000000 := by decide
```

Everything else in the [posit descriptor](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Descriptor.lean) is derived from the width. Below the sign the payload has $n - 1$ bits, and the exponent field has at most two bits. One unit of regime is worth $2^2 = 4$ in the binary exponent, which is what `regimeExponentStep` records. The encoding of one is `0x40000000`: sign 0, regime `10`, exponent `00`, fraction zero. We also put `nextPrecision` in the descriptor, the same format with one more bit, because the standard defines the rounding boundary between two $n$-bit posits as an $(n+1)$-bit posit, and our rounding definition refers to that higher-precision format. The width lives in the type, so a `Posit32` value carries no format tag at runtime, and the width also picks the storage carrier. `forKnownWidth` is a chain of guards. Widths through 8 bits pack into a `UInt8`, through 16 into a `UInt16`, through 32 into a `UInt32` and through 64 into a `UInt64`, widths through 128 use two `UInt64` limbs, and anything wider uses the exact-width model itself. None of this changes what a posit means. Every operation on every carrier is proved equal to the same model, and `#float_info Posit32` prints which kernel was selected.

<a id="finding-the-posit-implementation"></a>

## Reading a posit word

Our [posit decoder](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Model/Decode.lean) starts by recovering the magnitude. A posit's top bit is the sign, and negative values are stored as the two's complement of the whole word, so we compute

$$
m = \begin{cases} w & \text{if the sign bit is } 0, \\ 2^n - w & \text{otherwise.} \end{cases}
$$

We read the low $n - 1$ bits of $m$ from highest to lowest. First comes the regime, a run of identical bits that ends at the opposite bit or at the end of the word. A run of length $r$ made of ones gives regime value $k = r - 1$, and a run made of zeros gives $k = -r$. After the terminator come up to two exponent bits $e$, if there's room, and whatever is left is the fraction $F$ with $f$ bits. Put together, the value is

$$
(-1)^s \cdot (2^{f} + F) \cdot 2^{4k + e - f},
$$

where $s$ is the sign bit of the original word $w$. The implicit leading one comes back just as it does in a binary format. If the word is too short to hold both exponent bits, the missing bits count as zero, and `decodeFields` records how many were really there. Our model type [[FloatLib.Floats.Formats.Posit.Model]] is a `BitVec` of the format's width, and `decodeExact` sorts every word into zero, NaR, or finite with its decoded fields. Let's take the 8-bit word `0x6C`. Its payload `1101100` splits into a regime of two ones, a terminator, exponent bits `11` and two fraction bits `00`, so the regime gives $k = 1$ and the exponent bits give $e = 3$.

```lean
open FloatLib.Floats.Formats.Posit in
#eval (Model.ofNatBits (format := ExecFloat.Posit.format 8) 0x6C).decodeExact
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

So `0x6C` is $4 \cdot 2^5 = 128$. The smallest and largest positive 8-bit words show how much of the word the regime can take. `0x01` is a regime of six zeros with no exponent bits and no fraction, and `0x7F` is a regime of seven ones. [Figure 13.1](#/chapter/posits-and-the-quire/figure-ch14-posit-layout) colours the fields of those two words next to `0x6C` and the encoding of one, `0x40`. Toward either end of the range the regime gets longer and the fraction disappears.

![Four 8-bit posit words with their sign, regime, terminator, exponent and fraction fields, ordered by value, so that the regime run lengthens and the fraction shrinks toward both ends of the range](assets/ch14-posit-layout.png "Four posit8 encodings: longer regimes leave fewer exponent and fraction bits.")

```lean
open FloatLib.Floats.Formats.Posit in
#eval (Model.ofNatBits (format := ExecFloat.Posit.format 8) 0x01).toDyadic?
-- some { negative := false, significand := 1, exponent := -24 }
open FloatLib.Floats.Formats.Posit in
#eval (Model.ofNatBits (format := ExecFloat.Posit.format 8) 0x7F).toDyadic?
-- some { negative := false, significand := 1, exponent := 24 }
open FloatLib.Floats.Formats.Posit in
#eval (Model.ofNatBits (format := ExecFloat.Posit.format 8) 0x80).toDyadic?
-- none
```

So an 8-bit posit runs from $2^{-24}$ to $2^{24}$. The word `0x80`, the sign bit alone, is NaR, which has no dyadic value at all.

<a id="exact-decimal-text"></a>

### Printing and parsing decimal text

Every finite posit has a terminating decimal expansion, because its denominator is a power of two. You can see the conversion in $3\cdot2^{-3}=375\cdot10^{-3}$, where we multiply the coefficient by $5^3$ and use decimal exponent $-3$. `Model.display` and the configured `ToString` instance apply this exact conversion and then drop fractional trailing zeros, so $3\cdot2^{-3}$ prints as `0.375`. When decimal `e` notation is shorter, as it is for very small magnitudes, they switch to it, and they print NaR as `NaR`. Parsing runs an ASCII decimal scanner and exact rational arithmetic, then rounds once into the posit format. `Model.parse_display`, `Model.parse_toString` and the configured `parse_toString` prove that every original word comes back, at every valid width, zero and NaR included, and the configured result holds for any lawful codec. What the printer promises is exact text. It doesn't promise the shortest spelling, so redundant coefficient zeros can remain :)

### Widening without rounding

To widen a posit, you just append zeros to its word. Our 8-bit `0x6c` from above becomes `0x6c00` in 16 bits and still denotes 128. In this case the extra bits extend the fraction with zeros. `Model.toRat?_widen` proves this for every source width and every wider destination, including negative values, zero, and NaR. For a finite source, `Model.roundRat_widen` adds that decoding it exactly and rounding into the destination gives that same extended word, so the two conversion routes agree, with no table of width pairs anywhere. On the configured type, `Conversion.run_default_widen` gives the same guarantee for every lawful storage codec. It returns the extended word, zero and NaR included, so changing the storage carrier doesn't change the conversion.

### Converting to integers

Posit-to-integer conversion uses ordinary nearest-integer rounding with even ties, which is a different grid from the tapered posit grid. $1.5$ rounds to 2, and $2.5$ also rounds to 2. Signed and unsigned destinations share one exact rational rounder, followed by a range check at the requested integer width. For an exceptional integer result, the standard uses the word with only its most significant bit set. But those bits also encode an ordinary integer, so a signed output equal to the minimum integer, or an unsigned output equal to $2^{w-1}$, can be a successful result. Our sentinel theorems describe both possibilities, and looking at that word alone, you can't tell whether conversion failed.

The rounding functions `floor`, `ceil`, and `nearestInt` return integers in the same posit format, and those integers are always representable. An input that is already integral comes back unchanged. Otherwise the format has enough fraction positions to represent both neighboring integers, even for a ceiling that crosses a power of two. We prove their exact rational values at every width, and `nearestInt_spec` also gives the half-unit error bound and the even-integer tie rule.

## How precision changes with magnitude

A number near one has the shortest possible regime and so the most fraction bits, while near the extremes the regime is long and leaves few fraction bits or none. Let's take the successor of one in 32 bits, which shows the spacing there.

```lean
def one : Posit32 := 1

#eval ExecFloat.Posit.toRat? one
-- some 1
#eval ExecFloat.Posit.toRat? (ExecFloat.Posit.next one)
-- some (134217729 / 134217728)
```

That's $1 + 2^{-27}$, so a 32-bit posit has 28 significand bits at one where binary32 has 24. Farther from one, the longer regime leaves fewer bits for the fraction, so let's look at the two ends.

```lean
#eval ExecFloat.Posit.toRat? (ExecFloat.Posit.next (0 : Posit32))
-- some (1 / 1329227995784915872903807060280344576)
#eval ExecFloat.Posit.toRat? (ExecFloat.Posit.prior (ExecFloat.Posit.nar : Posit32))
-- some 1329227995784915872903807060280344576
```

These two magnitudes are reciprocals, and $2^{120}$ is the larger. In the wrapping encoding order NaR comes right after the largest positive posit, which is why `prior nar` returns that largest value. So a 32-bit posit covers $[2^{-120}, 2^{120}]$, with precision falling toward each end. Binary32 reaches about $2^{128}$ at the top and, through subnormals, $2^{-149}$ at the bottom, and it has the same 24 bits everywhere in the normal range. At $2^{64}$ a 32-bit posit has 12 significand bits against binary32's 24. [Figure 13.2](#/chapter/posits-and-the-quire/figure-ch14-tapered-precision) follows that change across the range, with the precision computed from the two formats' parameters. The posit's fraction shrinks as the regime grows, while binary32 keeps its fraction width until the subnormal range. Near the extremes the regime leaves too few exponent bits to reach every binade, so in the figure, gaps mark binades with no positive posit and isolated ticks mark those with just one.

![Significand bits available to a 32-bit posit and to binary32, computed from the two formats' parameters; gaps mark binades with no positive posit, and isolated ticks mark binades containing just one](assets/ch14-tapered-precision.png "Significand bits by magnitude; gaps and isolated ticks mark empty and single-posit binades.")

In 16 bits you see the effect at quite ordinary magnitudes. Take, say, 4096. Its successor is 4112, a spacing of 16, which means 8 fraction bits where binary16 has 10.

```lean
#eval ExecFloat.Posit.toRat? (ExecFloat.Posit.next (4096 : Posit16))
-- some 4112
```

De Dinechin, Forget, Muller, and Uguen discuss this dependence on magnitude [@deDinechinPosits2019]. The extra precision near one decreases as the regime grows. Switch units from meters to kilometers, say, and the same computation moves into a different part of the taper, with a different number of fraction bits available.

## Rounding thresholds and exceptional values

Posits have just two special words. The all-zero word is the only zero, and the word with only the sign bit set is NaR, "not a real". There is no negative zero, infinity, or NaN payload. Precision falls off toward zero because the regime gets longer, so there's no separate subnormal class either, and each of the remaining $2^n - 2$ words is a finite dyadic rational. In FloatLib a posit denotes a `NumericalValue Rat` in which NaR is the exceptional value `notAReal`, and `toRat?` returns `none` for NaR and for no other word.

```lean
#eval ExecFloat.Posit.toNatBits (ExecFloat.Posit.nar : Posit32)
-- 2147483648
#eval ExecFloat.Posit.toRat? (ExecFloat.Posit.nar : Posit32)
-- none
```

Posits also have only one rounding mode. Take two adjacent $n$-bit posits $U$ and $W$. Section 4.1 of the standard [@positStandard2022] puts the boundary between them at the $(n+1)$-bit posit whose encoding is $U$ followed by a one bit, and a value sitting on that boundary goes to whichever of $U$ and $W$ has an even low bit. In general that boundary isn't the arithmetic midpoint of the two decoded values, which is why we defined it through `nextPrecision` and didn't average. `roundingThreshold` is that $(n+1)$-bit value. `roundPositiveCode` finds the lower code by bisection over the monotone positive encoding and applies the threshold test, and [[FloatLib.Floats.Formats.Posit.Model.roundRat]] adds the sign by two's-complement negation. Nothing overflows to infinity or underflows to zero. At the extremes, any nonzero magnitude below the smallest positive posit rounds to it, and any magnitude above the largest rounds to the largest. The two largest positive 8-bit posits show how unusual this boundary is. Code `0x7e` is `0 111111 0`, a sign, six regime ones and their terminator. No room is left for an exponent field, so its value is $2^{4\cdot5}=2^{20}$, and code `0x7f` has seven regime ones and value $2^{24}$. Now let's append a one to the lower word and read the result as a 9-bit posit.

$$
\underbrace{0}_{\text{sign}}\;
\underbrace{111111}_{k=5}\;
\underbrace{0}_{\text{terminator}}\;
\underbrace{1}_{\text{exponent prefix}}
\quad\longmapsto\quad 2^{4\cdot5+2}=2^{22}.
$$

That final one lands in the high position of the two-bit exponent field. The low position is absent and counts as zero, so the exponent contributes 2, and the extra bit has changed the exponent without extending any fraction. So the threshold is $2^{22}$, while the arithmetic midpoint of the neighbours is $17\cdot2^{19}$. A value right at the threshold goes to the lower code, because `0x7e` is even. Take a value above it, such as $2^{23}$. Posit rounding selects `0x7f`, yet the distances to the lower and upper neighbours are $7\cdot2^{20}$ and $8\cdot2^{20}$, so the selected value is the one farther away :) Agreement with `roundRat` guarantees this boundary rule as the standard specifies it. It doesn't make the operation nearest-value rounding on the ordinary real line, so you can't reuse an IEEE half-ulp argument for it as is. Now let's see what saturation does. The calculation below starts from the literal $10^{39}$, which is well above $2^{120}$.

```lean
def big : Posit32 := 1000000000000000000000000000000000000000

#eval ExecFloat.Posit.toRat? big
-- some 1329227995784915872903807060280344576
#eval ExecFloat.Posit.toRat? (big * big)
-- some 1329227995784915872903807060280344576
#eval ExecFloat.Posit.toRat? ((1 : Posit32) / big / big)
-- some (1 / 1329227995784915872903807060280344576)
```

Every answer is the largest or the smallest positive posit, $2^{\pm 120}$. The literal saturates on the way in, squaring it stays there, and dividing one by it twice stops at the smallest positive word and never reaches zero. NaR propagates through basic arithmetic, and division by zero and the square root of a negative value give NaR too.

```lean
#eval ExecFloat.Posit.isNaR (x / 0)
-- true
#eval ExecFloat.Posit.isNaR (ExecFloat.sqrt (0 - x))
-- true
#eval ExecFloat.Posit.isNaR (x + ExecFloat.Posit.nar)
-- true
```

Section 6.5 of the 2022 Posit Standard [@positStandard2022] converts every IEEE infinity and every NaN to NaR, and both signed zeros to the one posit zero. FloatLib does the same by default, since our [conversion context](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Configured/Conversion/Runtime.lean) selects `toNaR` for both `InfinityPolicy` and `ExceptionalPolicy`. A mapped infinity or NaN sets `mappedSpecial := true`. For infinities the context also offers a `saturate` policy, which clamps to signed `maxPos` and sets the inexact, overflow and saturation status. If your application needs a failure on infinity or NaN, pass a rejection context to `cast` as its `context` option.

```lean
example : ExecFloat.Posit.Conversion.Context :=
  { infinity := .reject, exceptional := .reject }
```

## Arithmetic correctness

Our [reference definitions](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Arithmetic/Spec.lean) compute the exact result and then apply posit rounding. [[FloatLib.Floats.Formats.Posit.Model.Spec.add]] decodes both operands to `Rat`, adds, and calls `roundRat`. `div` returns NaR for a zero divisor and otherwise rounds the exact quotient, and `fma` rounds the exact rational $a \cdot b + c$ once. An exact square root need not be rational, so the specification determines its rounding by comparing candidates. `roundSqrtRat` compares the rational radicand against the squares of exact posit boundaries, using the fact that for nonnegative $c$, $c \leq \sqrt{r}$ if and only if $c^2 \leq r$. Nowhere does the specification use host `Float` arithmetic. You can apply the same public theorems as for the other families, now at the configured posit type.

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

[[FloatLib.Floats.ExecFloat.Proof.add_eq_spec]] and its siblings connect the certified kernels to these specifications. Those kernels never touch `Rat` and work in integer and dyadic arithmetic instead. For addition, subtraction, multiplication and fused multiply-add, the kernel forms the exact result as a dyadic and passes it to `round`, and the theorem `round_eq_roundRat` says it agrees with `roundRat` on the dyadic's rational value. Division doesn't build the exact quotient, which need not be a dyadic. `DirectDyadicQuotient` does one integer division to get the leading quotient bits the destination width needs, then one exact remainder test to set the sticky bit and one packing pass, and [[FloatLib.Floats.Formats.Posit.Model.DirectDyadicQuotient.round_eq_reference]] proves it agrees with the specification. Square root works the same way in `DirectDyadicSquareRoot`, with one integer square root and the exact square remainder. Its theorem is `round_eq_reference_of_not_negative`. We also proved both direct kernels equal, on their shared domain, to the bisection kernels `DyadicQuotient.round` and `DyadicSquareRoot.round`. Those find the lower code by search with cross-multiplied and squared comparisons, and they're proved to implement the same rational rounding.

Up to 64 bits, the kernels decode the packed machine word with proved shifts and masks, and a masked `UInt64.log2` counts the regime. Widths 65 through 128 decode the stored pair of limbs. If the exact intermediate of a one-word multiply or fused multiply-add no longer fits one word, the kernel carries on into the shared two-limb rounder. The [product](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Arithmetic/Word/Packed/Product/Runtime.lean) and [signed-sum](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Arithmetic/Word/Packed/SignedSum/Runtime.lean) kernels test capacity, and the [word-to-limb adapters](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Arithmetic/WordLimb/Runtime.lean) zero-extend a `UInt64` significand into the two-limb carrier. All of these are execution choices, and each one is proved equal to the same exact model. Ordering also comes from the word. Read a posit word as a two's-complement integer and you get the numerical order of the finite values, with NaR as the least word. We define the [`LinearOrder` instance](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Comparison.lean) through `signedCode`, and `compareLess_eq_true_iff` says the executable comparison agrees with it. That orders every code, NaR included, without giving NaR a rational value.

```lean
#eval decide ((ExecFloat.Posit.nar : Posit32) < 0)
-- true
#eval decide (x < y)
-- true
```

The standard's `next` and `prior` functions increment and decrement the word, wrapping included, and `prior_next` proves they invert each other on every word. Words and values are in bijection, so the model also gets a `FinEnum` instance with $2^n$ elements. The second example states this for 8 bits.

```lean
example (a : Posit32) : ExecFloat.Posit.prior (ExecFloat.Posit.next a) = a :=
  ExecFloat.Posit.prior_next a

open FloatLib.Floats.Formats.Posit in
example : FinEnum.card (Model (ExecFloat.Posit.format 8)) = 256 :=
  Model.finEnum_card _
```

We derive the instance from `bitsEquiv`, so Mathlib code can enumerate `Model format` itself. An exhaustive round-trip check covers widths 2 through 8. Every word other than NaR decodes to a rational and rounds back to the same word, and NaR has its own closed theorems. If you work in Mathlib there's also a projective view, `toProjectiveRat`, which sends NaR to the added point of `OnePoint Rat`. `toProjectiveRat_eq_infty_iff` and `toProjectiveRat_eq_coe_iff` record what it preserves. It's a bridge to Mathlib, and the added point doesn't make NaR mean an infinity.

## Exact accumulation with a quire

A quire accumulates exact products in a fixed-point word. It has room for every product of two posits and for sums up to a stated capacity, so a dot product rounds once, when it's converted back to a posit. For an $n$-bit posit the standard fixes a signed two's-complement word of $16n$ bits, whose least significant bit is worth $2^{16 - 8n}$, the square of the smallest positive posit. For `Posit32` that's 512 bits with a scale of $2^{-240}$. The most negative word is reserved as quire NaR, and every other word denotes an exact dyadic. Every posit and every product of two posits lines up with that fixed scale and fits inside the word. Look at the bits above the largest product in [Figure 13.3](#/chapter/posits-and-the-quire/figure-ch14-quire), which are there so carries have room as more products are added.

![The 512-bit posit32 quire as a fixed-point word, with landmark weights 2^240 at bit 480, 1 at bit 240, and 2^-240 at bit 0, plus thirty carry bits and the sign bit](assets/ch14-quire.png "From zero, the quire accumulates strictly fewer than 2^31 finite posit32 products exactly.")

```lean
open FloatLib.Floats.Formats.Posit in
example : Quire.width (ExecFloat.Posit.format 32) = 512 := rfl
open FloatLib.Floats.Formats.Posit in
example : Quire.scaleExponent (ExecFloat.Posit.format 32) = -240 := by decide
```

In the model a quire is [[FloatLib.Floats.Formats.Posit.Quire.Model]], a `FixedInt` of width `width`. Its configured type is `ExecFloat.Posit.Quire (bits := n)`, named `Quire32` for `Posit32` and likewise for the other standard widths. It shares its width parameter with the posit, so mixing widths is a type error. To accumulate a product, `qMulAdd` decodes the operands to dyadics and aligns their exact product with the quire's integer coefficient, and `qToP` rounds that coefficient back to a posit. None of this arithmetic goes through `Rat`. For the inputs from the first example, `x * y` is $1.5 \cdot 2.25 = 27/8$, which lands in the quire with no error, and since $27/8$ is itself a 32-bit posit, `qToP` returns it unchanged.

```lean
def q0 : Quire32 := ExecFloat.Posit.Quire.zero
def q1 : Quire32 := ExecFloat.Posit.Quire.qMulAdd q0 x y
def rounded : Posit32 := ExecFloat.Posit.Quire.qToP q1

#eval ExecFloat.Posit.Quire.toRat? q1
-- some (27 / 8)
#eval ExecFloat.Posit.toRat? rounded
-- some (27 / 8)
```

Besides these, the [quire API](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Quire/Arithmetic/Runtime.lean) converts a posit exactly with `pToQ`, adds or subtracts posits with `qAddP` and `qSubP`, and combines quires with `qAddQ` and `qSubQ`. `qMulSub` subtracts an exact product, and `qNegate` and `qAbs` act on the accumulated coefficient. To see why the quire matters, three terms in 16 bits are enough to make the intermediate rounding visible. The products $4096 \cdot 1$, $1 \cdot \tfrac{1}{2}$, and $4096 \cdot (-1)$ add up to $\tfrac{1}{2}$. Accumulate them with fused multiply-adds in the posit itself and the first partial sum $4096.5$ rounds to 4096, since the spacing there is 16, so the final answer is 0. In the quire nothing rounds until the end.

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

You can follow the lost half through the quire's integer coefficient. At width 16 the quire has 256 bits and scale $2^{-112}$, and dividing each product by that scale gives

$$
4096 \longmapsto 2^{124},\qquad
\tfrac12 \longmapsto 2^{111},\qquad
-4096 \longmapsto -2^{124}.
$$

After the second product the stored coefficient is $2^{124}+2^{111}$, with both bits present. Adding the third cancels bit 124 and leaves $2^{111}$, which decodes to $\tfrac12$. The quire keeps the same scale throughout, so no shift ever discards the low bit. The posit accumulator is a different story. At 4096 it has only eight fraction bits, and the half sits thirteen bit positions below the leading bit, so it can't survive that intermediate rounding. Fusing the second multiplication and addition does compute their exact combined result before rounding. But the partial sum still has to be stored as a `Posit16`, and once it's 4096 the later subtraction can't bring the half back. A quire keeps the whole coefficient until `qToP`, so it never takes that intermediate loss. Cancelling the two large products first also preserves the half in the posit accumulator, while the quire preserves it in either order, provided the intermediate coefficient stays in range.

Conversion into the quire is exact for every posit at every valid width, with no side conditions. [[FloatLib.Floats.Formats.Posit.Quire.Model.toRat?_pToQ]] says `(pToQ v).toRat? = v.toRat?`, and `toRat?_pToQ` says the same on the public type. Two facts make this work. Call a posit ordinary if it is any word other than NaR. Every ordinary posit's dyadic exponent is at least the quire scale, by `scaleExponent_le_exponent_of_toDyadic?_eq_some`, so shifting into the quire loses no bits. And every ordinary posit's coefficient lies strictly inside the signed range, so the shift can't overflow or collide with the reserved NaR word. The two-bit format gets its own case in the proof, because its two nonzero words are $\pm 1$ at scale zero.

```lean
example (v : Posit32) :
    ExecFloat.Posit.Quire.toRat? (ExecFloat.Posit.Quire.pToQ v) = ExecFloat.Posit.toRat? v :=
  ExecFloat.Posit.Quire.toRat?_pToQ v
```

Accumulating products is exact while the sum stays in range, and it returns NaR when it doesn't. `scaleExponent_le_mul_exponent_of_toDyadic?_eq_some` shows that the exact product of two ordinary posits also lines up with the quire scale, and the capacity proofs below bound the coefficients and the number of terms that fit in the $16n$ bits. [[FloatLib.Floats.Formats.Posit.Quire.Model.toRat?_qMulAdd_of_ordinary]] says that when the resulting coefficient is an `OrdinaryCoefficient`, the quire denotes the old value plus the exact rational product. When it isn't, [[FloatLib.Floats.Formats.Posit.Quire.Model.qMulAdd_eq_nar_of_not_ordinary]] says the result is quire NaR, and together they pin down `qMulAdd` on ordinary inputs. The shared kernel `addDyadic` also returns NaR for an increment below the quire's least significant bit, so it never mis-scales one. That's `addDyadic_eq_nar_of_exponent_lt`, and the alignment theorems show the standard operations never reach that guard.

Converting back applies the standard's rounding rule. [[FloatLib.Floats.Formats.Posit.Quire.Model.qToP_eq_roundRat]] states that `qToP` of an ordinary quire is `roundRat` of its exact rational value, and `qToP` of quire NaR is posit NaR. So the only rounding error an exact dot product makes within the quire's range is the one on conversion.

```lean
open FloatLib.Floats.Formats.Posit in
example (q : Quire.Model (ExecFloat.Posit.format 32)) :
    Quire.Model.qToP q =
      match q.toRat? with
      | some rational => Model.roundRat _ rational
      | none => Model.nar _ :=
  Quire.Model.qToP_eq_roundRat q
```

Our [capacity proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Quire/Capacity.lean) bounds the coefficient contributed by one posit and by one product, and the [accumulation proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Quire/Accumulation.lean) folds those bounds through a loop. Together they give the standard's term limits: `productSumTermLimit`, fewer than $2^{31}$ exact products, and `positSumTermLimit`, fewer than $2^{23 + 4n}$ posit addends. Both bounds are exclusive. Take the 512-bit quire in [Figure 13.3](#/chapter/posits-and-the-quire/figure-ch14-quire). There the largest posit is $2^{120}$ and its square is $2^{240}$, which at scale $2^{-240}$ occupies coefficient bit 480. Bits 481 through 510 are the thirty extra carry positions in the drawing, and bit 511 is the sign. So the count depends on where that largest product sits inside the fixed-point word, and the posit's precision near one doesn't enter into it.

With products, $2^{31}$ copies of the largest posit squared come to $2^{16n - 1}$ coefficient units. That's one past the largest ordinary quire coefficient, so the theorem asks for strictly fewer. Honestly, the standard reads two ways on this point. It says "at most $2^{31}$ terms" in Section 3.2 and "length less than $2^{31}$" in Section 4.2, and the proof settles on the second reading. The addend bound is the standard's quire sum limit, which the standard defines as the least number of additions that can overflow the quire, so fewer than that many is what's safe.

Below those limits, [[FloatLib.Floats.Formats.Posit.Quire.Model.toRat?_foldMulAdd_zero]] and `toRat?_foldAddP_zero` prove that folding from the zero quire never produces NaR and denotes the exact sum. For the public type, the configured theorem `toRat?_foldl_qMulAdd_zero` states this over a `List.foldl`. Besides the length, its only hypothesis is that `exactProducts?` returns `some`, which says no input is NaR.

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

Past the term limit the quire can overflow, so a longer loop has to establish a tighter coefficient bound or check `isNaR` on the result. Exact accumulators aren't special to posits, either, and Kulisch [@kulisch2013] argued for one for IEEE formats for decades before posits existed. If a benchmark gives one format a quire and the other none, it has changed both the format and the accumulation method, so it can't attribute the difference to the formats alone.

## Roots, powers, and fused products

Beyond the six basic operations we follow the same rule: keep the intermediate exact and round once. The [algebraic API](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/Posit/Algebraic) implements reciprocal square root `rSqrt`, `hypot`, and the fused triple product `fMM`, along with integer roots and powers. For `hypot` the rational radicand is $x^2+y^2$, and comparing it with squared posit boundaries picks the rounded root without rounding either square first. `ExecFloat.Posit.square x` uses the certified multiplication backend selected for the posit width, and its `square_eq_mul` theorem identifies the complete result with `x * x`, NaR included. A fused triple product can avoid saturation of an intermediate in `Posit32`. Let $M$ be its largest positive value and $m=1/M$ its smallest. In exact arithmetic $M \cdot M \cdot m$ is $M$, but two ordinary multiplications first saturate $M \cdot M$ to $M$ and then produce $M \cdot m=1$. `fMM` keeps the whole rational product and rounds once, to $M$, so its intermediate can leave the posit range and the final answer still comes out right.

`rootN` handles positive and negative integer degrees. It compares candidate powers with the exact radicand, or with the reciprocal radicand for a negative degree, and those comparisons feed the shared `ComparisonRounding` search, so root rounding follows the same boundary and tie rules as the other comparison-based operations. Degree zero gives NaR, and a negative input has a real root only for an odd degree. `powInt` computes an integer power exactly, and `compound` forms $(1+x)^n$ without rounding $1+x$ first. At zero the fixed integer exponent matters. `compound (-1) 0` returns one even though its exact base is zero, because integer exponent zero is the constant-one operation on every finite input, and `powInt 0 0` returns one for the same reason. The [integer-power theorems](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Algebraic/Power/Proof.lean) `compound_exponent_zero` and `powInt_exponent_zero` state those rules. NaR still propagates, even with exponent zero.

Two-posit `pow` also accepts nonintegral exponents. A finite posit exponent is a dyadic rational $n/2^k$ in lowest terms, so for a positive base the power is rational only when the numerator and denominator of the base are perfect $2^k$-th powers. Our comparison checks this first. It decides equality with a boundary, ties included, by capped exponentiation, which stops as soon as a partial power exceeds the corresponding part of the boundary. Logarithm enclosures of increasing degree then separate every other boundary. A negative base needs an integral exponent, and zero with a nonpositive exponent gives NaR. The proofs connect the in-domain results to `Model.RealRounding.round`, which is the standard's appended-bit rounding rule with the nonzero saturation described above, and none of them treats a posit boundary as an arithmetic midpoint. So general `pow 0 0` returns NaR, unlike the fixed integer operation. Each function's contract decides that case, and swapping one API for the other can change a program's result.

## Exponentials and logarithms

With the same comparison method we get proved operations for $2^x$, $10^x$, and their minus-one variants. For every finite input, the [rational-power theorems](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Algebraic/RationalPower/Proof.lean) `exp2Minus1_eq_round` and `exp10Minus1_eq_round` identify the result with one rounding of the exact real expression $2^x-1$ or $10^x-1$. Subtraction happens before rounding, because the comparator tests the unrounded power against the candidate boundary plus one.

To compare these powers independently you'd need exact rational answers or directed MPFR intervals, and an interval only settles the answer if both endpoints round to the same posit under an independent decoder and rounder. Negative integer powers, tiny exponents, shifted cancellation, and the minus-one functions each need their own cases.

We have real-rounding proofs for the [base-two and base-ten logarithms](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/Posit/Logarithm) too, including `log2Plus1` and `log10Plus1`. To compare a logarithm with a rational boundary, they compare its argument with the corresponding power. The [natural-function API](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/Posit/Elementary) adds `exp`, `expMinus1`, `log`, and `logPlus1`, and their [configured proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Configured/Elementary/Proof.lean) state equality with the real function followed by posit rounding. When `x` decodes to a rational $q>-1$, for example, `logPlus1_eq_real` says the output decodes to the model word

$$
\operatorname{RealRounding.round}\bigl(\log(1+q)\bigr).
$$

So the addition happens inside the exact expression. At 32 bits, adjacent posits near one are $2^{-27}$ apart. Say we take the representable input $x=2^{-30}$. Ordinary posit `1 + x` rounds to one, so its logarithm comes out zero. `logPlus1 x` takes the logarithm of the exact rational $1+2^{-30}$ and rounds only the final, positive result, and the nonzero saturation rule keeps that result nonzero. `expMinus1` likewise subtracts one from the exact exponential before rounding. Round `exp x` first and a small difference like that could disappear. You can round $\exp(1/2)$ without ever computing its exact irrational value. `Numerics.Enclosure.exp` computes rational lower and upper bounds, and `Numerics.Enclosure.contains_exp` proves that the exact real exponential lies between them. At degree five the bounds are already narrow enough for both endpoints to select the same eight-bit posit.

```lean standalone
import FloatLib.Floats.Formats.Posit.Rounding.Enclosure.Proof

open FloatLib.Numerics
open FloatLib.Floats.Formats.Posit

def format8 : Format := ⟨8, by decide⟩

#eval (Model.Enclosure.roundPositive? format8
  (Enclosure.exp (1 / 2) 5)).map Model.toNatBits
-- some 69
```

That's decimal `69`, or hexadecimal `0x45`. By monotonicity every value in the enclosure rounds to that same word, and `Model.Enclosure.eq_roundPositive_exp_of_roundPositive?_eq_some` proves this for any accepted exponential enclosure and any supported posit width. If the endpoints disagree, the check returns `none` and you need tighter bounds. To build the exponential enclosure we reduce the argument by a power of two and bound the Taylor remainder on the smaller interval, and repeated interval squaring then gets back to the original argument. Our containment proof covers both the approximation and that range reduction. Logarithm bounds use their own reduction to a small series argument. Rounding only needs to know which side of each rational boundary the irrational value lies on. So the natural-logarithm comparator builds rational lower and upper bounds and doubles the approximation degree until the boundary falls outside the enclosure. Convergence alone wouldn't prove termination, though, because if the logarithm equalled the boundary, the search could keep narrowing forever.

Our [transcendence proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Numerics/Enclosure/Elementary/Transcendental.lean) shows something stronger: the exponential of a nonzero rational is transcendental, so it can't be a root of any nonzero polynomial with rational coefficients. It builds on Mathlib's Lindemann-Weierstrass analysis and adds no extra axioms. From there the [irrationality proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Numerics/Enclosure/Elementary/Irrational.lean) get irrationality of that exponential and of the logarithm of a positive rational other than one, which rules out the stuck case where the value equals a rational boundary. The one exact case, $\log 1=0$, is handled on its own. With that, the [termination proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Numerics/Enclosure/Elementary/Termination.lean) shows that a separating enclosure exists, and the [comparison algorithm](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Numerics/Exact/Elementary/Runtime.lean) uses that proof to define total adaptive comparisons. At zero, `prepareExp` just uses $e^0=1$. For nonzero arguments in $[-8,8]$ it builds direct Taylor enclosures and shares a lazily computed prefix across the rounding search, so comparing the same $e^x$ with several candidate boundaries can reuse bounds already computed for that input. `prepareLog` shares logarithm enclosures the same way.

Outside that interval the exponential comparison uses $e^x<b \iff x<\log b$ for positive $b$, and bounds on $\log b$ settle it without the large rational intermediates a direct exponential enclosure can need. Whichever algorithm runs, the function accepts the same inputs. The [cache theorem](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Numerics/Enclosure/Comparison/Cache.lean) `cacheIntervals_apply` proves that every cached interval equals the original one, and requests beyond the cached prefix still compute further bounds. Both routes are covered by the real-rounding proofs. Those real-rounding equations cover every finite input in the function's domain, extreme magnitudes and saturation included. `log` requires a positive input, `logPlus1` requires an input greater than $-1$, and invalid inputs or NaR produce NaR. We proved termination but not a small runtime bound, and hard comparisons can need large rational calculations. These are separate functions from the approximate [binary transcendental kernels](#/chapter/elementary-functions/calling-the-approximation-kernels) measured in the validation chapter.

<a id="ordinary-trigonometric-functions"></a>

## Trigonometric functions in radians

In the [trigonometric API](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/Posit/Trigonometric) you get the radian functions `sin`, `cos`, and `tan`, and their principal inverses `arcSin`, `arcCos`, and `arcTan`. Model and configured `*_eq_real` theorems identify each result with one standard posit rounding of the real function. Inverse sine and cosine accept $[-1,1]$ and return NaR outside it, and before rounding, their real principal branches have ranges $[-\pi/2,\pi/2]$ and $[0,\pi]$. Inverse tangent takes every finite input, and its real branch has range $(-\pi/2,\pi/2)$. All six propagate NaR. Since a finite posit is rational, it can never equal a radian tangent pole. Each call first decodes the input to its exact value and prepares an enclosure cache for that argument, then reuses the cache when comparing the result with each candidate rounding boundary. [Comparison proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Numerics/Exact/Trigonometric/Proof.lean) establish which side of a rational boundary the real value lies on, and the posit rounder uses those comparisons to apply the appended-bit rounding rule. Argument reduction has to account for uncertainty in the period. If $|\pi-p|\leq\varepsilon$, replacing $x-2k\pi$ by $x-2kp$ can introduce an error as large as $2|k|\varepsilon$, so at a large input a small error in the stored period can dominate the reduced argument. Our rational sine and cosine enclosures carry that reduction error into their final bounds, and their convergence proofs don't assume that the chosen period count eventually stops changing.

## Angles in units of pi

The [pi-scaled API](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/Posit/Trigonometric/Pi) adds `sinPi`, `cosPi`, `tanPi`, `arcSinPi`, `arcCosPi`, and `arcTanPi`, with model and configured real-rounding proofs. Each direct function multiplies the exact input by $\pi$, evaluates the real function, and rounds once. Each inverse divides the exact principal angle by $\pi$ before rounding, and never divides an already rounded posit angle. Take, say, $x=1/2$, which is representable at 32 bits. `sinPi x` returns one, `cosPi x` returns zero, and `tanPi x` returns NaR because $x\pi=\pi/2$ is a pole. If you formed a posit approximation to $\pi/2$ and passed it to ordinary `tan`, you'd hand it a finite rational angle and miss that pole. Working in units of pi keeps the exact angle relationship. Before refining any enclosure, the numerical comparator picks out the rational special values. Every other direct value is irrational, so a converging enclosure eventually separates it from a rational rounding boundary. Inverse comparisons use the monotone principal branches, whose endpoints are rational in units of pi. Inverse sine and cosine require inputs in $[-1,1]$, all six functions propagate NaR, and pi-scaled tangent rejects every half-integer input.

`arcTan2 x y` gives the angle of $x+iy$ in $(-\pi,\pi]$. Watch the argument order, because the Posit Standard takes the real coordinate first. The negative real axis has angle $\pi$, and the origin has no direction, so it produces NaR. `arcTan2Pi` divides the exact angle by pi before rounding, which makes `arcTan2Pi 1 1` exactly one quarter. Both operations have real-rounding proofs for every finite pair except the origin.

## Hyperbolic functions

Six functions live in the [hyperbolic API](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/Posit/Hyperbolic): `sinH`, `cosH`, `tanH`, `arcSinH`, `arcCosH`, and `arcTanH`. Their model and configured proofs identify the result with one rounding of the exact real function. The first four accept every finite input, while `arcCosH` requires $x\geq1$ and `arcTanH` requires $-1<x<1$. NaR propagates, and an input outside an inverse function's domain also gives NaR. Here too the implementation compares the exact result with a posit boundary. Deciding whether $\tanh x<1/2$, for example, reduces to deciding whether $2x<\log 3$, since $\operatorname{artanh}(1/2)=\tfrac12\log 3$, so we never construct either exponential in the formula for $\tanh x$. Hyperbolic sine and cosine settle large exponential comparisons with rational bounds first and refine an enclosure only when those bounds don't decide the ordering. Inverse functions share logarithm enclosures across rounding comparisons.

## What the decoder proof assumes about the compiler

In the whole library, the posit decoder is the one place where we replace compiled code through `implemented_by`. Every other kernel, as [chapter 05](#/chapter/why-execution-and-proofs-are-separate) explains, runs the definition Lean checked or uses a replacement justified by a proved `csimp` equation. [[FloatLib.Floats.Formats.Posit.Model.toDyadic?]] turns a word into `some` dyadic, or `none` for NaR. Its logical definition goes through `decodeExact` and the field-by-field decoder, and that's what every theorem about it uses. Its compiled code is a private one-pass function, `Internal.toDyadic?`, which tests for the NaR and zero codes and otherwise calls `decodeFiniteDyadicCode`. That compact decoder does sign restoration, the regime scan and the trailing field powers in one pass. `@[implemented_by Internal.toDyadic?]` connects the two, and the private theorem `Internal.toDyadic?_eq` in the [posit decoder](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Model/Decode.lean) proves them extensionally equal on every word.

That equality proof doesn't check what the compiler does with `implemented_by`. The attribute tells the compiler to substitute a function, and Lean's kernel never sees the substitution. Run `Lean.collectAxioms` on a theorem about `toDyadic?` and it reports the axioms of the logical definition, with no trace of the replacement. So the equality theorem settles the mathematics, but we still rely on the compiler to honour the attribute and substitute that function and no other. [Chapter 05](#/chapter/why-execution-and-proofs-are-separate) explains this distinction between a proved function and the code that executes it. This decoder runs in every posit operation and quire conversion. Its replacement gives execution a one-pass body, and proofs still get the transparent field decoder. `decodeFiniteDyadic_eq_decodeFields_toDyadic` closes the finite branch by `rfl`, so all the substitution theorem has to do is classify the two special words.

<a id="cross-checks-against-universal-and-softposit"></a>

## Comparing with Universal and SoftPosit

Proofs connect our executable arithmetic to our specification, and a comparison with Stillwater's independent Universal library [@stillwaterUniversal] also checks how we read the format. Before it compares execution times, the benchmark runner requires the two implementations to agree bit for bit on every output for the same inputs, and a workload where they disagree is left out of the timing comparison. [Chapter 19](#/chapter/external-validation) explains where the implementations agree and where they differ. Our first comparison with SoftPosit [@softPosit] found 7,562 differences. They came down to two problems in the version we tested, revision `17d5628`. Its generic variable-width path, called pX2, disagreed with its own dedicated p32 functions on three 32-bit boundary examples, repeated across 7,560 sampled cases, and on those, the dedicated functions and FloatLib agreed. The other two differences are in 16-bit fused multiply-add. In the first, the exact answer is $52800 + 2^{-56}$. Its neighbours are 52,736 and 52,864, so 52,800 sits halfway between them, and that tiny positive addend makes 52,864 the closer answer. SoftPosit lost the addend's contribution to its *sticky bit*, the record of nonzero discarded bits, so it treated the result as a tie and rounded down to 52,736. FloatLib rounded up. The second case is the same problem on the negative side.

Another 9,175,040 comparisons covered widths 9 through 15 and turned up two new inputs. Both are FMA differences, one at 14 bits and one at 15 bits, and both come from the same lost sticky information. With the three 32-bit examples and the two 16-bit ones, that makes seven distinct inputs, and exact rational evaluation agrees with FloatLib's executable result on all seven. [Chapter 19 follows the calculation and source diagnosis](#/chapter/external-validation/the-softposit-differences). These comparisons check software implementations on the stated inputs. They are not an official posit certification or a validation of a hardware posit unit. [Chapter 17](#/chapter/performance) compares the execution times of these software implementations on shared inputs.
