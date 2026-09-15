---
number: "11"
slug: posits-and-the-quire
title: Posits and the quire
summary: Posits vary their precision with magnitude, while a quire keeps products and sums exact within a proved capacity bound.
phases: [posits]
---

Binary formats reserve the same number of exponent bits in every word, so binary32 has 24 significand bits near one and near $10^{30}$ alike. Posits vary how many bits go to the exponent and fraction. The exponent is encoded partly as a run of identical bits whose length varies with the magnitude, so values near one get more fraction bits than values at the extremes. The 2022 Standard for Posit Arithmetic [@positStandard2022] fixes the rest of the design: a single width parameter, one rounding rule, one exceptional value called NaR, no signed zero, no infinities, and an exact fixed-point accumulator called the quire.

FloatLib exposes the standard's core arithmetic through the same `ExecFloat` interface as the binary formats of [chapter 08](#/chapter/ieee-binary-formats), with the same operation names, literal syntax, refinement theorems, and `#float_info` command. A 32-bit posit is `ExecFloat.Posit (bits := 32)`. Its `toRat?` decoder reads the stored value as an exact rational, so we can check the result of a calculation without converting it to another floating-point format.

We'll start with values whose products and sums we can verify by hand:

```lean
open FloatLib.Floats

abbrev Posit32 := ExecFloat.Posit (bits := 32)

def x : Posit32 := 1.5
def y : Posit32 := 2.25
def z : Posit32 := x * y + (x + y)

#eval ExecFloat.Posit.toRat? z
-- some (57 / 8)
```

The answer is $1.5 \cdot 2.25 + (1.5 + 2.25) = 7.125 = 57/8$, exact here because every intermediate is a dyadic rational that fits in the posit's available fraction bits.

## Width fixes the standard posit format

Gustafson and Yonemoto's 2017 proposal [@gustafsonYonemoto2017] wrote posit formats as `posit<n, es>`, with `es` the maximum width of the exponent field. The 2022 standard dropped that second parameter: every standard posit has at most two exponent bits, and a format is identified by its total width $n$ alone. The descriptor [[FloatLib.Floats.Formats.Posit.Format]] holds one natural number and a proof that it is at least 2. The lower bound is the standard's own: Section 2 defines $n$ as any integer greater than 1, and `bits_ge_two` carries that requirement into the type. Two bits is the smallest width at which the four distinguished words, zero, one, NaR, and minus one, all exist.

```lean
example : (ExecFloat.Posit.format 32).payloadBits = 31 := rfl
example : (ExecFloat.Posit.format 32).exponentBits = 2 := rfl
example : (ExecFloat.Posit.format 32).regimeExponentStep = 4 := rfl
example : (ExecFloat.Posit.format 32).oneCodeNat = 0x40000000 := by decide
```

The rest of the [posit descriptor](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Descriptor.lean) is derived. The payload below the sign is $n - 1$ bits, the exponent field is two bits, and one unit of regime is worth $2^2 = 4$ in the binary exponent, which `regimeExponentStep` records. The encoding of one is `0x40000000`: sign 0, regime `10`, exponent `00`, fraction zero. The descriptor also defines `nextPrecision`, the same format with one more bit, because the standard defines the rounding boundary between two $n$-bit posits as an $(n+1)$-bit posit. The rounding definition refers to that higher-precision format directly.

Because the width lives in the type, a `Posit32` value carries no format tag at runtime, and the width selects the storage carrier. `forKnownWidth` is a chain of guards: widths through 8 bits pack into a `UInt8`, through 16 into a `UInt16`, through 32 into a `UInt32`, through 64 into a `UInt64`, through 128 into two `UInt64` limbs, and anything wider uses the exact-width model directly. The carrier is a storage decision, not a semantic one; every operation on every carrier is proved equal to the same model, and `#float_info Posit32` prints which kernel was selected.

## Reading a posit word

To decode a posit, we first recover its magnitude. The top bit is the sign, and negative values are stored in two's complement of the whole word, so we compute

$$
m = \begin{cases} w & \text{if the sign bit is } 0, \\ 2^n - w & \text{otherwise.} \end{cases}
$$

Reading the low $n - 1$ bits of $m$ from highest to lowest, we start with the regime: a run of identical bits terminated by the opposite bit, or by the end of the word. If the run has length $r$ and consists of ones, the regime value is $k = r - 1$; if it consists of zeros, $k = -r$. After the terminator come up to two exponent bits $e$, if any room is left, and whatever remains is the fraction $F$ with $f$ bits. The value is

$$
(-1)^s \cdot (2^{f} + F) \cdot 2^{4k + e - f},
$$

where $s$ is the sign bit of the original word $w$ and the implicit leading one is restored exactly as in a binary format. If the word is too short to hold both exponent bits, the missing bits count as zero; `decodeFields` records how many were actually present.

The model type [[FloatLib.Floats.Formats.Posit.Model]] is a `BitVec` of the format's width, and `decodeExact` classifies every word as zero, NaR, or finite with its decoded fields. To decode the 8-bit word `0x6C`, we split its payload `1101100` into a regime of two ones (so $k = 1$), a terminator, exponent bits `11` (so $e = 3$), and two fraction bits `00`:

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

So `0x6C` is $4 \cdot 2^5 = 128$. The smallest and largest positive 8-bit words show how much of the word the regime can occupy: `0x01` is a regime of six zeros with no exponent bits and no fraction, and `0x7F` is a regime of seven ones. Compare those two words with `0x6C` and the encoding of one, `0x40`, in [Figure 11.1](#/chapter/posits-and-the-quire/figure-ch14-posit-layout), where the fields are coloured. Toward either end of the range, the regime lengthens and the fraction disappears.

![Four 8-bit posit words with their sign, regime, terminator, exponent and fraction fields, ordered by value, so that the regime run lengthens and the fraction shrinks toward both ends of the range](assets/ch14-posit-layout.png "Four posit8 encodings. Longer regime fields leave fewer explicit exponent and fraction bits at the ends of the range.")

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

An 8-bit posit runs from $2^{-24}$ to $2^{24}$, and the word `0x80`, the sign bit alone, is NaR and has no dyadic value.

<a id="exact-decimal-text"></a>

### Printing and parsing decimal text

Every finite posit has a terminating decimal expansion because its denominator is a power of two. The identity $3\cdot2^{-3}=375\cdot10^{-3}$ shows the conversion: multiply the coefficient by $5^3$ and use decimal exponent $-3$. `Model.display` and the configured `ToString` instance apply this exact conversion, using decimal `e` notation where needed. They print NaR as `NaR`.

Parsing goes through an ASCII decimal scanner and exact rational arithmetic, then rounds once into the posit format. The theorems `Model.parse_display`, `Model.parse_toString`, and configured `parse_toString` prove recovery of every original word at every valid width, including zero and NaR. The configured result holds for any lawful codec. The printer promises exact text, not the shortest spelling: redundant coefficient zeros can remain. [Chapter 16](#/chapter/external-validation/posit-decimal-text) checks both the emitted value and the parser's syntax against independent code.

<a id="more-bits-the-same-value"></a>

### Widening without rounding

To widen a posit, append zeros to its word. The 8-bit `0x6c` above becomes `0x6c00` in 16 bits and still denotes 128. In this example, the extra bits extend the fraction with zeros.

`Model.toRat?_widen` proves this for every source width and every wider destination, including negative values, zero, and NaR. For a finite source, `Model.roundRat_widen` also proves that decoding it exactly and rounding into the destination produces that same extended word. The two conversion routes agree without a table of width pairs.

The configured conversion has the same guarantee for every lawful storage codec: `Conversion.run_default_widen` returns the extended word, including for zero and NaR. Changing the storage carrier does not change the conversion.

### Converting to integers

Posit-to-integer conversion uses ordinary nearest-integer rounding with even ties. This is a different grid from the tapered posit grid: $1.5$ rounds to 2 and $2.5$ also rounds to 2. Signed and unsigned destinations use the same exact rational rounder, followed by a range check at the requested integer width.

The standard's exceptional integer word has only its most significant bit set. Those bits also encode an ordinary integer. A signed output equal to the minimum integer, or an unsigned output equal to $2^{w-1}$, can therefore be a successful result. The sentinel theorems describe both possibilities; inspecting that word alone cannot tell us whether conversion failed.

`floor`, `ceil`, and `nearestInt` return integers in the same posit format, and those integers are always representable. If the input is already integral, it stays unchanged. Otherwise, the format has enough fraction positions to represent both neighboring integers, including a ceiling that crosses a power of two. The proofs establish their exact rational values at every width; `nearestInt_spec` also gives the half-unit error bound and even-integer tie rule.

<a id="tapered-precision-in-numbers"></a>

## How precision changes with magnitude

A number near one has the shortest possible regime and therefore the most fraction bits; a number near the extremes has a long regime and few or no fraction bits. We can see the spacing near one by taking its successor in 32 bits.

```lean
def one : Posit32 := 1

#eval ExecFloat.Posit.toRat? one
-- some 1
#eval ExecFloat.Posit.toRat? (ExecFloat.Posit.next one)
-- some (134217729 / 134217728)
```

That is $1 + 2^{-27}$, so a 32-bit posit has 28 significand bits at one where binary32 has 24. Farther from one, the longer regime consumes bits that would otherwise hold the fraction.

```lean
#eval ExecFloat.Posit.toRat? (ExecFloat.Posit.next (0 : Posit32))
-- some (1 / 1329227995784915872903807060280344576)
#eval ExecFloat.Posit.toRat? (ExecFloat.Posit.prior (ExecFloat.Posit.nar : Posit32))
-- some 1329227995784915872903807060280344576
```

The two magnitudes are reciprocals, with $2^{120}$ as the larger. NaR immediately follows the largest positive posit in the wrapping encoding order, so `prior nar` returns that largest value. A 32-bit posit covers $[2^{-120}, 2^{120}]$ with precision falling toward each end. Binary32 reaches about $2^{128}$ at the top and, through subnormals, $2^{-149}$ at the bottom, with the same 24 bits everywhere in the normal range. At $2^{64}$ a 32-bit posit has 12 significand bits against binary32's 24. We can follow that change across the range in [Figure 11.2](#/chapter/posits-and-the-quire/figure-ch14-tapered-precision), which computes the precision from the two formats' parameters: the posit's fraction shrinks as the regime grows, while binary32 keeps its fraction width until the subnormal range.

Near the extremes, the regime leaves too few exponent bits to represent values in every binade. Gaps mark binades with no positive posit; isolated ticks mark those with just one.

![Significand bits available to a 32-bit posit and to binary32, computed from the two formats' parameters; gaps mark binades with no positive posit, and isolated ticks mark binades containing just one](assets/ch14-tapered-precision.png "Available significand bits by magnitude for posit32 and binary32. Gaps and isolated ticks distinguish empty binades from those containing a single posit.")

In 16 bits the effect shows at quite ordinary magnitudes: the successor of 4096 is 4112, a spacing of 16, which is 8 fraction bits where binary16 has 10.

```lean
abbrev Posit16 := ExecFloat.Posit (bits := 16)

#eval ExecFloat.Posit.toRat? (ExecFloat.Posit.next (4096 : Posit16))
-- some 4112
```

De Dinechin, Forget, Muller, and Uguen discuss this dependence on magnitude [@deDinechinPosits2019]. The accuracy advantage is local to values near one. Changing units from meters to kilometers moves the same computation into a different part of the taper, changing how many fraction bits are available.

## Rounding thresholds and exceptional values

Posits have exactly two special words. The all-zero word is the only zero, and the word with only the sign bit set is NaR, "not a real". There is no negative zero, no infinity, and no family of NaN payloads. Precision decreases toward zero through the changing regime length, with no separate subnormal class. Every one of the remaining $2^n - 2$ words is a finite dyadic rational. A posit denotes a `NumericalValue Rat` in which NaR is the exceptional value `notAReal`, and `toRat?` returns `none` exactly for it.

```lean
#eval ExecFloat.Posit.toNatBits (ExecFloat.Posit.nar : Posit32)
-- 2147483648
#eval ExecFloat.Posit.toRat? (ExecFloat.Posit.nar : Posit32)
-- none
```

There is exactly one rounding mode. Section 4.1 of the standard [@positStandard2022] says that between two adjacent $n$-bit posits $U$ and $W$ the boundary is the $(n+1)$-bit posit whose encoding is $U$ followed by a one bit, and a value exactly on that boundary goes to whichever of $U$ and $W$ has an even low bit. That boundary is not in general the arithmetic midpoint of the two decoded values, which is why we defined it through `nextPrecision` instead of averaging. `roundingThreshold` is that $(n+1)$-bit value, `roundPositiveCode` finds the lower code by bisection over the monotone positive encoding and applies the threshold test, and [[FloatLib.Floats.Formats.Posit.Model.roundRat]] adds the sign by two's-complement negation. At the extremes, any nonzero magnitude below the smallest positive posit rounds to it and any magnitude above the largest rounds to the largest; there is no overflow to infinity and no underflow to zero.

The two largest positive 8-bit posits make the unusual boundary visible. Code `0x7e` is `0 111111 0`: a sign, six regime ones, and their terminator. There is no exponent field left, so its value is $2^{4\cdot5}=2^{20}$. Code `0x7f` has seven regime ones and value $2^{24}$. Append a one to the lower word and read the result as a 9-bit posit:

$$
\underbrace{0}_{\text{sign}}\;
\underbrace{111111}_{k=5}\;
\underbrace{0}_{\text{terminator}}\;
\underbrace{1}_{\text{exponent prefix}}
\quad\longmapsto\quad 2^{4\cdot5+2}=2^{22}.
$$

That final one occupies the high position of the two-bit exponent field; the absent low position is zero, so the exponent contribution is 2. The extra bit therefore changes the exponent rather than extending a fraction. The threshold is $2^{22}$, whereas the arithmetic midpoint of the neighbours is $17\cdot2^{19}$. At the threshold the lower code wins because `0x7e` is even.

For a value above it, such as $2^{23}$, posit rounding selects `0x7f`. Yet the distances to the lower and upper neighbours are respectively $7\cdot2^{20}$ and $8\cdot2^{20}$: the selected value is farther away in absolute distance. Agreement with `roundRat` guarantees this specified boundary rule. It does not make the operation nearest-value rounding on the ordinary real line, so an IEEE half-ulp argument cannot simply be reused for it.

To see what saturation does to a calculation, we'll start with the literal below: $10^{39}$, well above $2^{120}$.

```lean
def big : Posit32 := 1000000000000000000000000000000000000000

#eval ExecFloat.Posit.toRat? big
-- some 1329227995784915872903807060280344576
#eval ExecFloat.Posit.toRat? (big * big)
-- some 1329227995784915872903807060280344576
#eval ExecFloat.Posit.toRat? ((1 : Posit32) / big / big)
-- some (1 / 1329227995784915872903807060280344576)
```

All three answers are the largest or the smallest positive posit, $2^{\pm 120}$: the literal saturates on the way in, squaring it stays there, and dividing one by it twice stops at the smallest positive word instead of reaching zero.

Basic arithmetic propagates NaR. Division by zero and the square root of a negative value also give NaR.

```lean
#eval ExecFloat.Posit.isNaR (x / 0)
-- true
#eval ExecFloat.Posit.isNaR (ExecFloat.sqrt (0 - x))
-- true
#eval ExecFloat.Posit.isNaR (x + ExecFloat.Posit.nar)
-- true
```

Section 6.5 of the Posit Standard (2022) [@positStandard2022] converts every IEEE infinity and every NaN to NaR, and both signed zeros to the one posit zero. FloatLib uses this mapping by default. The [conversion context](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Configured/Conversion/Runtime.lean) selects `toNaR` for both `InfinityPolicy` and `ExceptionalPolicy`; a mapped infinity or NaN sets `mappedSpecial := true`. For infinities it also offers an explicit `saturate` policy, which clamps to signed `maxPos` and sets the inexact, overflow, and saturation status.

Applications that require a failure on infinity or NaN can pass an explicit rejection context to `castWith`:

```lean
example : ExecFloat.Posit.Conversion.Context :=
  { infinity := .reject, exceptional := .reject }
```

<a id="what-is-proved-for-the-arithmetic"></a>

## Arithmetic correctness

The [reference definitions](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Arithmetic/Spec.lean) compute exactly and then apply posit rounding. [[FloatLib.Floats.Formats.Posit.Model.Spec.add]] decodes both operands to `Rat`, adds, and calls `roundRat`; `div` returns NaR for a zero divisor and otherwise rounds the exact quotient; `fma` rounds the exact rational $a \cdot b + c$ once. The exact square root need not be rational. To round it, `sqrt` avoids forming an approximate root: `roundSqrtRat` compares the rational radicand against the squares of exact posit boundaries, using, for nonnegative $c$, $c \leq \sqrt{r}$ if and only if $c^2 \leq r$. The specification uses no host `Float` arithmetic.

We can apply the same public theorems used by the other families, now at the configured posit type:

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

[[FloatLib.Floats.ExecFloat.Proof.add_eq_spec]] and its siblings connect the certified kernels to these specifications. The kernels work in integer and dyadic arithmetic, without `Rat`. Addition, subtraction, multiplication, and fused multiply-add form the exact result as a dyadic and pass it to `round`, whose theorem `round_eq_roundRat` says it agrees with `roundRat` on the dyadic's rational value.

Division does not construct the exact quotient, which need not be a dyadic. `DirectDyadicQuotient` performs one integer division to get the leading quotient bits the destination width needs, one exact remainder test to set the sticky bit, and one packing pass. [[FloatLib.Floats.Formats.Posit.Model.DirectDyadicQuotient.round_eq_reference]] proves agreement with the specification. Square root, in `DirectDyadicSquareRoot`, does the same with one integer square root and the exact square remainder; `round_eq_reference_of_not_negative` is its theorem.

Both direct kernels are also proved equal, on their shared domain, to the bisection kernels `DyadicQuotient.round` and `DyadicSquareRoot.round`. Those kernels find the lower code by search with cross-multiplied and squared comparisons and are proved to implement the same rational rounding.

Widths through 64 bits decode the packed machine word with proved shifts and masks, and a masked `UInt64.log2` counts the regime. Widths 65 through 128 decode the stored pair of limbs. When the exact intermediate of a one-word multiply or fused multiply-add no longer fits one word, the kernel continues into the shared two-limb rounder; the [product](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Arithmetic/Word/Packed/Product/Runtime.lean) and [signed-sum](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Arithmetic/Word/Packed/SignedSum/Runtime.lean) kernels test capacity, and the [word-to-limb adapters](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Arithmetic/WordLimb/Runtime.lean) zero-extend a `UInt64` significand into the two-limb carrier. These are execution choices, each proved equal to the same exact model.

Reading a posit word as a two's-complement integer gives the numerical order of the finite values, with NaR ordered as the least word. The [`LinearOrder` instance](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Comparison.lean) is defined through `signedCode`, and `compareLess_eq_true_iff` says the executable comparison agrees with it. This orders every code, including NaR, without assigning NaR a rational value.

```lean
#eval decide ((ExecFloat.Posit.nar : Posit32) < 0)
-- true
#eval decide (x < y)
-- true
```

The standard's `next` and `prior` functions increment and decrement the word, wrapping included, and `prior_next` proves they invert each other on every word. The bijection between words and values also gives the model a `FinEnum` instance with exactly $2^n$ elements, which the second example states for 8 bits.

```lean
example (a : Posit32) : ExecFloat.Posit.prior (ExecFloat.Posit.next a) = a :=
  ExecFloat.Posit.prior_next a

open FloatLib.Floats.Formats.Posit in
example : FinEnum.card (Model (ExecFloat.Posit.format 8)) = 256 :=
  Model.finEnum_card _
```

The `FinEnum` instance comes from `bitsEquiv`, the equivalence between the model and its bit vector, and `finEnum_card` gives the cardinality $2^n$. This lets a Mathlib user enumerate `Model format` itself. The exhaustive round-trip check covers widths 2 through 8: every word other than NaR decodes to a rational and rounds back to the same word. NaR has its own closed theorems.

For Mathlib users there is also a projective view, `toProjectiveRat`, sending NaR to the added point of `OnePoint Rat`, with `toProjectiveRat_eq_infty_iff` and `toProjectiveRat_eq_coe_iff` recording what it preserves. This view helps connect the type to Mathlib, but the added point does not give NaR the meaning of an infinity.

## Roots, powers, and fused products

The same principle extends beyond the six basic operations: keep the intermediate exact and round once. The [algebraic API](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/Posit/Algebraic) implements reciprocal square root `rSqrt`, `hypot`, and the fused triple product `fMM`, together with integer roots and powers. For `hypot`, the rational radicand is $x^2+y^2$; comparing it with squared posit boundaries chooses the rounded root without rounding either square first.

Consider a fused triple product using the largest and smallest values in `Posit32`. Let $M$ be its largest positive value and $m=1/M$ its smallest. The exact expression $M \cdot M \cdot m$ is $M$. Two ordinary multiplications first saturate $M \cdot M$ to $M$, then produce $M \cdot m=1$. `fMM` preserves the whole rational product and rounds to $M$ once. Its intermediate can exceed the posit range without losing the final answer.

`rootN` handles positive and negative integer degrees. It compares candidate powers with the exact radicand; a negative degree uses the reciprocal radicand. These comparisons feed the shared `ComparisonRounding` search, so root rounding uses the same boundary and tie rules as the other comparison-based operations. Degree zero gives NaR, and a negative input has a real root only for an odd degree. `powInt` computes an integer power exactly, while `compound` forms $(1+x)^n$ without first rounding $1+x$.

The fixed integer exponent matters at zero. `compound (-1) 0` returns one: its exact base is zero, but integer exponent zero is the constant-one operation on every finite input. `powInt 0 0` returns one for the same reason. The [integer-power theorems](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Algebraic/Power/Proof.lean) `compound_exponent_zero` and `powInt_exponent_zero` state those rules. NaR still propagates, even with exponent zero.

The two-posit `pow` operation also accepts nonintegral exponents. A finite posit exponent is a dyadic rational, so powers can be compared by exact integer-power inequalities. Logarithm enclosures can settle the comparison first; an exact algebraic fallback resolves cases too close to decide that way, including ties. A negative base requires an integral exponent; zero with a nonpositive exponent gives NaR. The proofs connect the in-domain results to `Model.RealRounding.round`, the standard's appended-bit rounding rule and nonzero saturation described above. They are not a claim that every posit boundary is an arithmetic midpoint.

Thus general `pow 0 0` returns NaR, unlike the fixed integer operation. The function's contract determines that case; substituting one API for the other can change a program's result.

## Exponentials and logarithms

The same comparison method gives us proved operations for $2^x$, $10^x$, and their minus-one variants. The [rational-power theorems](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Algebraic/RationalPower/Proof.lean) `exp2Minus1_eq_round` and `exp10Minus1_eq_round` identify the result with one rounding of the exact real expression $2^x-1$ or $10^x-1$ for every finite input. The subtraction happens before rounding: the comparator tests the unrounded power against the candidate boundary plus one.

Independent comparisons check powers using exact rational answers or directed MPFR intervals. For an interval to settle the answer, both endpoints must round to the same posit under an independent decoder and rounder. [Chapter 16](#/chapter/external-validation) describes these comparisons, which include negative integer powers, tiny exponents, shifted cancellation, and the minus-one functions.

The [base-two and base-ten logarithms](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/Posit/Logarithm), including `log2Plus1` and `log10Plus1`, have proofs of real rounding. They compare a logarithm with a rational boundary by comparing its argument with the corresponding power. The [natural-function API](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/Posit/Elementary) adds `exp`, `expMinus1`, `log`, and `logPlus1`. Their [configured proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Configured/Elementary/Proof.lean) state equality with the real function followed by posit rounding. For example, when `x` decodes to a rational $q>-1$, `logPlus1_eq_real` says the output decodes to the model word

$$
\operatorname{RealRounding.round}\bigl(\log(1+q)\bigr).
$$

The addition is inside the exact expression. At 32 bits, adjacent posits near one are $2^{-27}$ apart. Take the representable input $x=2^{-30}$. Computing ordinary posit `1 + x` rounds to one, so taking its logarithm returns zero. `logPlus1 x` instead evaluates the logarithm of the exact rational $1+2^{-30}$ and rounds only the final, positive result. The nonzero saturation rule keeps that result nonzero. `expMinus1` similarly subtracts one from the exact exponential before rounding, preserving a small difference that could disappear if `exp x` were rounded first.

We can round $\exp(1/2)$ without computing its exact irrational value. `Numerics.Enclosure.exp` computes rational lower and upper bounds, and `Numerics.Enclosure.contains_exp` proves that the exact real exponential lies between them. The degree-five bounds are already narrow enough for both endpoints to select the same eight-bit posit:

```lean standalone
import FloatLib.Floats.Formats.Posit.Rounding.Enclosure.Proof

open FloatLib.Numerics
open FloatLib.Floats.Formats.Posit

def format8 : Format := ⟨8, by decide⟩

#eval (Model.Enclosure.roundPositive? format8
  (Enclosure.exp (1 / 2) 5)).map Model.toNatBits
-- some 69
```

The word is decimal `69`, or hexadecimal `0x45`. Monotonicity forces every value in the enclosure to round to that same word. `Model.Enclosure.eq_roundPositive_exp_of_roundPositive?_eq_some` proves this connection for any accepted exponential enclosure and any supported posit width. If the endpoints disagree, the check returns `none` and we need tighter bounds.

For a closer look at that check, lower the degree in the example and inspect whether it still returns `some`. We accept a word only when both endpoints agree.

The exponential enclosure reduces the argument by a power of two, bounds the Taylor remainder on the smaller interval, then restores the original argument by repeated interval squaring. The containment proof covers both the approximation and that range reduction. Logarithm bounds use their own reduction to a small series argument.

For rounding, we only need to decide which side of each rational boundary the irrational value lies on. The natural-logarithm comparator builds rational lower and upper bounds, doubling the approximation degree until the boundary lies outside the enclosure. There is a catch: convergence alone would not establish termination. If the logarithm equalled the boundary, the search could keep narrowing forever.

The [transcendence proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Numerics/Enclosure/Elementary/Transcendental.lean) establishes the stronger fact that the exponential of a nonzero rational is transcendental: it cannot be a root of any nonzero polynomial with rational coefficients. The proof builds on Mathlib's Lindemann-Weierstrass analysis and introduces no extra axioms. The [irrationality proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Numerics/Enclosure/Elementary/Irrational.lean) derive irrationality of that exponential and of the logarithm of a positive rational other than one. These results rule out the unresolved equality with a rational boundary; the exact case $\log 1=0$ is handled directly.

The [termination proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Numerics/Enclosure/Elementary/Termination.lean) then establishes that a separating enclosure exists, and the [comparison algorithm](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Numerics/Exact/Elementary/Runtime.lean) uses that proof to define total adaptive comparisons. At zero, `prepareExp` uses $e^0=1$ directly. For nonzero arguments in $[-8,8]$, it builds direct Taylor enclosures and shares a lazily computed prefix across the rounding search. Comparing the same $e^x$ with several candidate boundaries can then reuse bounds already computed for that input. `prepareLog` shares logarithm enclosures in the same way.

Outside that interval, the exponential comparison uses $e^x<b \iff x<\log b$ for positive $b$. Bounds on $\log b$ settle the comparison without the large rational intermediates a direct exponential enclosure can require. The function accepts the same inputs whichever algorithm it uses. The [cache theorem](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Numerics/Enclosure/Comparison/Cache.lean) `cacheIntervals_apply` proves that every cached interval equals the original one; requests beyond the cached prefix still compute further bounds. The real-rounding proofs cover both routes.

The resulting real-rounding equations cover every finite input in the function's domain, including extreme magnitudes and saturation. `log` requires a positive input, `logPlus1` requires an input greater than $-1$, and invalid inputs or NaR produce NaR. Termination is proved; a small runtime bound is not. Difficult comparisons can require large rational calculations. These functions are separate from the approximate [binary transcendental kernels](#/chapter/ieee-binary-formats/transcendental-functions) measured in the validation chapter.

<a id="ordinary-trigonometric-functions"></a>

## Trigonometric functions in radians

The [trigonometric API](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/Posit/Trigonometric) supplies the radian functions `sin`, `cos`, and `tan`, and their principal inverses `arcSin`, `arcCos`, and `arcTan`. The model and configured `*_eq_real` theorems identify each result with one standard posit rounding of the real function. Inverse sine and cosine accept $[-1,1]$ and return NaR outside it. Before rounding, their real principal branches have ranges $[-\pi/2,\pi/2]$ and $[0,\pi]$. Inverse tangent takes every finite input; its real branch has range $(-\pi/2,\pi/2)$. All six propagate NaR. A finite posit is rational, so it cannot equal a radian tangent pole.

The implementation first decodes the input exactly and prepares an enclosure cache for that argument. It reuses this cache when comparing the result with each candidate rounding boundary. The [comparison proofs and oracle checks](#/chapter/external-validation/exact-trigonometric-comparisons) establish which side of a rational boundary the real value lies on. The posit rounder uses those comparisons to apply the appended-bit rounding rule.

Argument reduction must account for uncertainty in the period. If $|\pi-p|\leq\varepsilon$, replacing $x-2k\pi$ by $x-2kp$ can introduce an error as large as $2|k|\varepsilon$. At a large input, a small error in the stored period can therefore dominate the reduced argument. The rational sine and cosine enclosures carry that reduction error into their final bounds. Their convergence proofs do not assume that the chosen period count eventually stops changing.

## Angles in units of pi

The [pi-scaled API](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/Posit/Trigonometric/Pi) adds `sinPi`, `cosPi`, `tanPi`, `arcSinPi`, `arcCosPi`, and `arcTanPi`, with model and configured real-rounding proofs. The direct functions multiply the exact input by $\pi$ before evaluating the real function and rounding once. The inverse functions divide the exact principal angle by $\pi$ before rounding; they do not divide an already rounded posit angle.

At 32 bits, $x=1/2$ is exactly representable. `sinPi x` returns one and `cosPi x` returns zero. `tanPi x` returns NaR because $x\pi=\pi/2$ is a pole. Forming a posit approximation to $\pi/2$ and passing it to ordinary `tan` would give a finite rational angle, so it would miss that pole. The pi-scaled API preserves the exact angle relationship.

The numerical comparator classifies rational special values before refining enclosures. Every other direct value is irrational, so a converging enclosure eventually separates it from a rational rounding boundary. Inverse comparisons use the monotone principal branches, whose endpoints are rational in units of pi. Inverse sine and cosine require inputs in $[-1,1]$; all six functions propagate NaR, and pi-scaled tangent rejects every half-integer input.

`arcTan2 x y` gives the angle of $x+iy$ in $(-\pi,\pi]$. Watch the argument order: the Posit Standard takes the real coordinate first. The negative real axis has angle $\pi$; the origin has no direction and produces NaR. `arcTan2Pi` divides the exact angle by pi before rounding, so `arcTan2Pi 1 1` is exactly one quarter. Both operations have real-rounding proofs for every finite pair outside the origin.

## Hyperbolic functions

The [hyperbolic API](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/Posit/Hyperbolic) implements `sinH`, `cosH`, `tanH`, `arcSinH`, `arcCosH`, and `arcTanH`. Their model and configured proofs identify the result with one rounding of the exact real function. The first four accept every finite input; `arcCosH` requires $x\geq1$, and `arcTanH` requires $-1<x<1$. NaR propagates, and an input outside an inverse function's domain gives NaR.

The implementation compares the exact result with a posit boundary. For example, deciding whether $\tanh x<1/2$ reduces to deciding whether $2x<\log 3$, since $\operatorname{artanh}(1/2)=\tfrac12\log 3$. This avoids constructing either exponential in the formula for $\tanh x$. Hyperbolic sine and cosine use rational bounds to settle large exponential comparisons first and refine an enclosure only when those bounds do not decide the ordering. The inverse functions share logarithm enclosures across rounding comparisons. [The validation section](#/chapter/external-validation/posit-hyperbolic-functions) explains how independent enclosures can check these functions, including their domain and range boundaries.

<a id="the-quire"></a>

## Exact accumulation with a quire

A quire accumulates exact products in a fixed-point word. It has enough room for every product of two posits and for sums up to a stated capacity, so a dot product rounds once when converted back to a posit. For an $n$-bit posit the standard fixes a signed two's-complement word of $16n$ bits whose least significant bit is worth $2^{16 - 8n}$, the square of the smallest positive posit; for `Posit32` that is 512 bits with a scale of $2^{-240}$. Its most negative word is reserved as quire NaR, and every other word denotes an exact dyadic.

Every posit and every product of two posits aligns with that fixed scale and fits inside the word. In [Figure 11.3](#/chapter/posits-and-the-quire/figure-ch14-quire), look at the bits above the largest product: they provide room for carries as more products are added.

![The 512-bit quire of a 32-bit posit drawn to scale as a fixed-point word, with the weights of its landmark bits, the span of one posit and of one product, the 30 bits of headroom and the sign bit](assets/ch14-quire.png "The posit32 quire has 512 bits at scale 2^-240. Thirty carry positions above the largest product support exact accumulation within the stated capacity.")

```lean
open FloatLib.Floats.Formats.Posit in
example : Quire.width (ExecFloat.Posit.format 32) = 512 := rfl
open FloatLib.Floats.Formats.Posit in
example : Quire.scaleExponent (ExecFloat.Posit.format 32) = -240 := by decide
```

The model is [[FloatLib.Floats.Formats.Posit.Quire.Model]], a `FixedInt` of width `width`, and the configured type `ExecFloat.Posit.Quire (bits := n)` shares its width parameter with the posit so that mixing widths is a type error. The [quire operations](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Quire/Arithmetic/Runtime.lean) are the ones the standard names: `pToQ` converts a posit exactly, `qNegate` and `qAbs` negate and take the absolute value, `qAddP` and `qSubP` add or subtract a posit, `qAddQ` and `qSubQ` combine two quires, `qMulAdd` and `qMulSub` accumulate an exact product, and `qToP` rounds once on the way out. All of them work on the integer coefficient. A posit operand decodes to a dyadic and is shifted to the quire's fixed scale by `coefficientOfDyadic`; these operations need no conversion through `Rat`.

We can start with a single product to check conversion in and out of the quire. `x * y` is $1.5 \cdot 2.25 = 27/8$; it lands in the quire exactly, and because $27/8$ is itself a 32-bit posit, `qToP` returns it unchanged.

```lean
abbrev Quire32 := ExecFloat.Posit.Quire (bits := 32)

def q0 : Quire32 := ExecFloat.Posit.Quire.zero
def q1 : Quire32 := ExecFloat.Posit.Quire.qMulAdd q0 x y
def rounded : Posit32 := ExecFloat.Posit.Quire.qToP q1

#eval ExecFloat.Posit.Quire.toRat? q1
-- some (27 / 8)
#eval ExecFloat.Posit.toRat? rounded
-- some (27 / 8)
```

Now we can make the intermediate rounding visible with three terms in 16 bits. The products $4096 \cdot 1$, $1 \cdot \tfrac{1}{2}$, and $4096 \cdot (-1)$ sum exactly to $\tfrac{1}{2}$. Accumulated with fused multiply-adds in the posit itself, the first partial sum $4096.5$ rounds to 4096, since the spacing there is 16, and the final answer is 0. In the quire there is nothing to round until the end.

```lean
abbrev Quire16 := ExecFloat.Posit.Quire (bits := 16)

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

We can follow the lost half through the quire's integer coefficient. At width 16, the quire has 256 bits and scale $2^{-112}$. Dividing each product by that scale gives

$$
4096 \longmapsto 2^{124},\qquad
\tfrac12 \longmapsto 2^{111},\qquad
-4096 \longmapsto -2^{124}.
$$

After the second product the stored coefficient is $2^{124}+2^{111}$, with both bits present. Adding the third cancels bit 124 and leaves $2^{111}$, which decodes to $\tfrac12$. No shift discards the low bit because the quire keeps the same scale throughout.

The posit accumulator has only eight fraction bits at 4096. The half lies thirteen bit positions below the leading bit, so it cannot survive that intermediate rounding. Fusing the second multiplication and addition computes their exact combined result before rounding, but still has to store that partial sum as a `Posit16`. Once it becomes 4096, the later subtraction cannot recover the half. The quire avoids that intermediate loss by retaining the whole coefficient until `qToP`.

As another experiment, reorder the three products in both calculations. Before running them, identify which partial sum the posit accumulator will have to round; then compare the decoded answers again.

Conversion into the quire is exact for every posit at every valid width, with no side conditions: [[FloatLib.Floats.Formats.Posit.Quire.Model.toRat?_pToQ]] says `(pToQ v).toRat? = v.toRat?`, and `toRat?_pToQ` says the same on the public type. Two properties make this possible. Every ordinary posit's dyadic exponent (ordinary meaning any word other than NaR) is at least the quire scale, by `scaleExponent_le_exponent_of_toDyadic?_eq_some`, so shifting into the quire loses no bits. Every ordinary posit's coefficient also lies strictly inside the signed range, so the shift cannot overflow or collide with the reserved NaR word. The proof handles the two-bit format separately because its two nonzero words are $\pm 1$ at scale zero.

```lean
example (v : Posit32) :
    ExecFloat.Posit.Quire.toRat? (ExecFloat.Posit.Quire.pToQ v) = ExecFloat.Posit.toRat? v :=
  ExecFloat.Posit.Quire.toRat?_pToQ v
```

Product accumulation is exact while it stays in range and returns NaR when it does not. `scaleExponent_le_mul_exponent_of_toDyadic?_eq_some` shows that the exact product of two ordinary posits also aligns with the quire scale, which is the fact that makes the $16n$ width sufficient; [[FloatLib.Floats.Formats.Posit.Quire.Model.toRat?_qMulAdd_of_ordinary]] says that when the resulting coefficient is an `OrdinaryCoefficient` the quire denotes the old value plus the exact rational product; and [[FloatLib.Floats.Formats.Posit.Quire.Model.qMulAdd_eq_nar_of_not_ordinary]] says that when it is not, the result is quire NaR. Together they characterize `qMulAdd` on ordinary inputs. The shared kernel `addDyadic` also returns NaR for an increment below the quire's least significant bit rather than mis-scaling it (`addDyadic_eq_nar_of_exponent_lt`); the alignment theorems show the standard operations never reach that guard.

Converting back applies the standard's rounding rule. [[FloatLib.Floats.Formats.Posit.Quire.Model.qToP_eq_roundRat]] states that `qToP` of an ordinary quire is `roundRat` of its exact rational value and `qToP` of quire NaR is posit NaR. An exact dot product accumulated within the quire's range therefore incurs one rounding error on conversion.

```lean
open FloatLib.Floats.Formats.Posit in
example (q : Quire.Model (ExecFloat.Posit.format 32)) :
    Quire.Model.qToP q =
      match q.toRat? with
      | some rational => Model.roundRat _ rational
      | none => Model.nar _ :=
  Quire.Model.qToP_eq_roundRat q
```

The [capacity proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Quire/Capacity.lean) bounds the coefficient contributed by one posit and by one product, and the [accumulation proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Quire/Accumulation.lean) folds those bounds through a loop. The standard's term limits come out as `productSumTermLimit`, fewer than $2^{31}$ exact products, and `positSumTermLimit`, fewer than $2^{23 + 4n}$ posit addends. Both bounds are exclusive.

For the 512-bit quire in [Figure 11.3](#/chapter/posits-and-the-quire/figure-ch14-quire), the largest posit is $2^{120}$ and its square is $2^{240}$. At scale $2^{-240}$ that product occupies coefficient bit 480. Bits 481 through 510 are the thirty extra carry positions shown in the drawing; bit 511 is the sign. The count comes from where that largest product sits inside the fixed-point word, rather than from the posit's precision near one.

For products, $2^{31}$ products of the largest posit squared come to exactly $2^{16n - 1}$ coefficient units, one past the largest ordinary quire coefficient, so the theorem asks for strictly fewer. The standard itself says "at most $2^{31}$ terms" in Section 3.2 and "length less than $2^{31}$" in Section 4.2; the proof settles it on the second reading. The addend bound is the standard's quire sum limit, defined there as the least number of additions that can overflow the quire, so fewer than that many is exactly what is safe.

Below those limits, [[FloatLib.Floats.Formats.Posit.Quire.Model.toRat?_foldMulAdd_zero]] and `toRat?_foldAddP_zero` prove that folding from the zero quire never produces NaR and denotes the exact sum. The configured theorem `toRat?_foldl_qMulAdd_zero` states this over a `List.foldl` on the public type; the only hypothesis besides the length is that `exactProducts?` returns `some`, which says no input is NaR.

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

A loop that exceeds the term limit can overflow the quire. Exact accumulators can also serve other number formats. Kulisch [@kulisch2013] argued for an exact accumulator for IEEE formats for decades before posits existed. Giving one format a quire and the other none changes both the format and the accumulation method, so a benchmark cannot attribute the difference to the formats alone.

<a id="the-compiled-decoder-and-its-trust-boundary"></a>

## What the decoder proof assumes about the compiler

The posit decoder contains the library's one compiler replacement made through `implemented_by`. As [chapter 05](#/chapter/why-execution-and-proofs-are-separate) explains, the other kernels run the definition Lean checked or use a replacement justified by a proved `csimp` equation.

[[FloatLib.Floats.Formats.Posit.Model.toDyadic?]] turns a word into `some` dyadic or `none` for NaR. Its logical definition goes through `decodeExact` and the field-by-field decoder, which is what every theorem about it uses. Its compiled code is a private one-pass function, `toDyadicImpl?`, that tests for the NaR and zero codes and otherwise calls `decodeFiniteDyadicCode`, the compact decoder that does sign restoration, the regime scan, and the trailing field powers in one pass. The attribute connecting them is `@[implemented_by toDyadicImpl?]`, and the private theorem `toDyadicImpl?_eq_toDyadic?` in the [posit decoder](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Model/Decode.lean) proves the two functions extensionally equal on every word.

The equality proof does not check the compiler's use of `implemented_by`: the attribute instructs the compiler to substitute a function, but Lean's kernel does not see that substitution. `Lean.collectAxioms` on a theorem about `toDyadic?` reports the axioms of the logical definition and knows nothing about the replacement. The equality theorem settles the mathematics; the compiler must still honour the attribute and substitute exactly that function. [Chapter 05](#/chapter/why-execution-and-proofs-are-separate) explains this distinction between a proved function and the code that executes it.

The decoder runs in every posit operation and quire conversion. Its replacement supplies the one-pass body for execution while the transparent field decoder remains available in proofs. `decodeFiniteDyadic_eq_decodeFields_toDyadic` closes the finite branch by `rfl`, so the only content of the substitution theorem is the classification of the two special words.

<a id="cross-checks-against-universal-and-softposit"></a>

## Comparing with Universal and SoftPosit

Proofs connect our executable arithmetic to our specification. Comparing it with Stillwater's independent Universal library [@stillwaterUniversal] also checks our reading of the format. Before comparing execution times, the benchmark runner requires the two implementations to agree bit for bit on every output for the same inputs. If they disagree, that workload is excluded from the timing comparison. [Chapter 16](#/chapter/external-validation) explains where the implementations agree and where they differ.

The initial comparison with SoftPosit [@softPosit] found 7,562 differences.
They came down to two problems in the version tested, revision `17d5628`. Its generic
variable-width path, called pX2, disagreed with its own dedicated p32 functions on three
32-bit boundary examples repeated across 7,560 sampled cases. The dedicated functions
and FloatLib agreed.

The other two differences occur in 16-bit fused multiply-add. In the first,
the exact answer is $52800 + 2^{-56}$. The neighbours are 52,736 and 52,864, so 52,800 is
exactly halfway between them. That tiny positive addend makes 52,864 the closer answer.
SoftPosit lost the addend's contribution to its *sticky bit*, the record of nonzero
discarded bits. It consequently treated the result as a tie and rounded down to 52,736.
FloatLib rounded up. The second case has the same problem on the negative side.

Another 9,175,040 comparisons covered widths 9 through 15. They found two new inputs:
one FMA difference at 14 bits and one at 15 bits, both from the same lost sticky
information. Together with the three 32-bit examples and two 16-bit examples, these make
seven distinct inputs. Exact rational evaluation agrees with FloatLib's executable result
on all seven.
[Chapter 16 follows the calculation and source diagnosis](#/chapter/external-validation/the-softposit-differences).

These software comparisons establish agreement or explain disagreements on the tested
inputs. They do not constitute official posit certification, and no hardware posit unit
has been checked against this library.

[Chapter 15](#/chapter/performance) compares the execution times of these software implementations on shared inputs.

<a id="where-the-posit-work-stops"></a>

## Error bounds and quire limits

The roots, powers, exponentials, logarithms, ordinary and pi-scaled trigonometric functions, and hyperbolic functions have real-rounding proofs, but those equations do not supply the IEEE half-ulp and relative-error theory of [chapter 07](#/chapter/the-mathematics-of-rounding); posit spacing and boundary rules differ. The quire guarantees still require coefficients in range, so accumulation must respect its term limits or check `isNaR` on the way out.

## Finding the posit implementation

For a proof about a posit word, start with the [posit model](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/Posit/Model), which defines decoding, and the [arithmetic](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/Posit/Arithmetic) and [rounding](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/Posit/Rounding) proofs that connect the basic operations to their exact specifications. For accumulation, use the [quire proofs](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/Posit/Quire), where [[FloatLib.Floats.Formats.Posit.Quire.Model.toRat?_pToQ]] and [[FloatLib.Floats.Formats.Posit.Quire.Model.qToP_eq_roundRat]] prove exact conversion in and one rounding out.

The [algebraic](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/Posit/Algebraic), [logarithmic](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/Posit/Logarithm), and [natural-function](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/Posit/Elementary) APIs add roots, powers, fused products, and exponentials and logarithms with real-rounding proofs. To follow why the natural functions terminate, start with the [total adaptive comparator](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Numerics/Exact/Elementary). Its proof uses exp/log irrationality derived from the [proof of rational-argument exponential transcendence](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Numerics/Enclosure/Elementary). The [shared numerical algorithms](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Numerics) and [kernels](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Kernels) also serve binary formats.
