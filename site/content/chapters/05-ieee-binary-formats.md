---
number: "05"
slug: ieee-binary-formats
title: "IEEE 754 binary formats"
summary: "IEEE 754-2019 binary formats, arithmetic, rounding and exception flags, with a clause-by-clause guide to the implementations and their Lean theorems."
phases: [ieee-formats, binary-format, binary-arithmetic, status-and-directed, planner-and-configured]
---

IEEE 754 specifies both the value of an operation and the exceptions it signals. Dividing one by positive zero gives positive infinity and raises the division-by-zero flag. Dividing zero by zero gives a quiet NaN and raises the invalid-operation flag. FloatLib makes both parts of the result available in Lean for binary16, binary32, binary64 and binary128. The [operation table](#/chapter/ieee-binary-formats/where-is-each-operation-of-ieee-754-2019) maps the required operations of clause 5 and the recommended families of clause 9 to their implementations and theorems. [@ieee754_2019]

We checked the binary model against Berkeley TestFloat on 127,741,704 level-1 vectors. All 210 campaigns matched on the five exception flags. Non-NaN results matched bit for bit, and NaNs matched by quiet or signaling class. The campaigns cover arithmetic, comparisons and conversions in the four IEEE widths, plus conversions between binary32 and bfloat16. The [validation chapter](#/chapter/external-validation/how-do-we-test-the-wider-ieee-formats) gives the format and rounding coverage.

## What is a binary float?

Every binary float splits its bits into three fields. One bit holds the sign, and for a normal value the exponent field picks a power of two and the fraction field says where you are between that power and the next. In the ruler picture from earlier in the book, the exponent picks the ruler and the fraction picks the tick. Every ruler in the normal range (all but the tiniest values near zero) has the same number of ticks, so the ticks near a million are much wider than those near one. All the ticks together form the format's grid. More exponent bits mean more rulers, and more fraction bits mean finer ticks.

So how would you split sixteen bits? Binary16 spends ten on the fraction, which gives it eleven significant bits (we'll see where the extra bit comes from), but its largest value is 65504, so 70000 doesn't fit. Bfloat16, another sixteen-bit layout, moves three of those bits into the exponent. Where both are normal its ticks are eight times wider, and in return it reaches as far as binary32, past $10^{38}$. Training code for machine learning tends to care more about not overflowing than about the third digit, and that's the trade bfloat16 makes.

## How to describe a format

FloatLib records the field layout in a descriptor of type [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat]]. The record contains `expWidth`, `fracWidth`, the `exponentBias` subtracted from the stored exponent, and an `encoding` ([[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.Encoding]]) that says what the reserved bit patterns, such as an all-ones exponent, mean. This chapter uses `.ieee`, and [the chapter on small formats](#/chapter/low-precision-formats-for-machine-learning) covers the other three encodings.

A descriptor also has four [proof fields](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Format/Definition.lean), which hold proofs instead of data. They're checked when you build a descriptor, free at run time, and ask for at least two exponent bits, at least one fraction bit, a positive bias, and a bias no larger than the largest finite exponent code. One fraction bit is enough for quiet NaNs, and signaling NaNs need two. The `ieee` constructor takes the two widths and fills in the conventional bias and the `.ieee` encoding.

A format with $w_e$ exponent bits and $w_f$ fraction bits is $1 + w_e + w_f$ bits wide (`bitWidth`), and its conventional bias, precision (significant bits), exponent range and extreme values are

$$
\begin{aligned}
b &= 2^{w_e - 1} - 1, &\qquad p &= w_f + 1,\\
e_{\min} &= 1 - b, &\qquad e_{\max} &= b,\\
x^{\text{norm}}_{\min} &= 2^{e_{\min}}, &\qquad x^{\text{subn}}_{\min} &= 2^{e_{\min} - w_f},\\
x_{\max} &= (2 - 2^{-w_f}) \cdot 2^{e_{\max}}.
\end{aligned}
$$

Here's what those constants come to for the [named layouts](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Format/Catalog.lean). Bfloat16 isn't in IEEE 754, but it follows the same encoding conventions with its own field widths.

| Descriptor | $w_e$ | $w_f$ | bits | $b$ | $p$ | $e_{\min}$ | $e_{\max}$ | $x_{\max}$ |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.binary16]] | 5 | 10 | 16 | 15 | 11 | $-14$ | 15 | $(2 - 2^{-10}) \cdot 2^{15} = 65504$ |
| [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.bfloat16]] | 8 | 7 | 16 | 127 | 8 | $-126$ | 127 | $(2 - 2^{-7}) \cdot 2^{127}$ |
| [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.binary32]] | 8 | 23 | 32 | 127 | 24 | $-126$ | 127 | $(2 - 2^{-23}) \cdot 2^{127}$ |
| [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.binary64]] | 11 | 52 | 64 | 1023 | 53 | $-1022$ | 1023 | $(2 - 2^{-52}) \cdot 2^{1023}$ |
| [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.binary128]] | 15 | 112 | 128 | 16383 | 113 | $-16382$ | 16383 | $(2 - 2^{-112}) \cdot 2^{16383}$ |

[Figure 5.1](#/chapter/ieee-binary-formats/figure-ch12-bit-layouts) draws every bit at the same width. Look at binary128: nearly all of its storage goes to the fraction.

![Five horizontal strips on one scale, each split into a sign bit, an exponent field and a fraction field, with the field widths written inside: 5 and 10 bits for binary16, 8 and 7 for bfloat16, 8 and 23 for binary32, 11 and 52 for binary64, and 15 and 112 for binary128. The total, 16, 16, 32, 64 or 128 bits, follows each strip](assets/ch12-bit-layouts.png "The bit layouts of the five named binary formats, drawn to one scale with the most significant bit on the left. The number inside an exponent or fraction field is its width in bits, and every format has one sign bit.")

Every number in the table reads straight off the descriptors, so you can ask Lean for them:

```lean
open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

#eval (FloatFormat.binary16.bitWidth, FloatFormat.binary32.bitWidth,
       FloatFormat.binary64.bitWidth, FloatFormat.binary128.bitWidth)
-- (16, 32, 64, 128)

#eval (FloatFormat.binary16.exponentBias, FloatFormat.binary32.exponentBias,
       FloatFormat.binary64.exponentBias, FloatFormat.binary128.exponentBias)
-- (15, 127, 1023, 16383)

#eval (FloatFormat.binary16.minNormalExponent, FloatFormat.binary32.minNormalExponent,
       FloatFormat.binary64.minNormalExponent, FloatFormat.binary128.minNormalExponent)
-- (-14, -126, -1022, -16382)

#eval (FloatFormat.binary128.maxNormalExponent, FloatFormat.binary128.minSubnormalExponent)
-- (16383, -16494)
```

The last pair is binary128's $e_{\max}$ and the exponent of its least subnormal, its smallest positive value, $e_{\min} - w_f = -16382 - 112 = -16494$. [Figure 5.2](#/chapter/ieee-binary-formats/figure-ch12-range-precision) puts range and precision side by side.

![Two bar charts with one row for each format. Panel (a) draws a bar from the exponent of the least subnormal to the largest normal exponent on a symmetric logarithmic axis: −24 to 15 for binary16, −133 to 127 for bfloat16, −149 to 127 for binary32, −1,074 to 1,023 for binary64 and −16,494 to 16,383 for binary128, with the subnormal part in a second colour. Panel (b) draws the precision: 11, 8, 24, 53 and 113 bits](assets/ch12-range-precision.png "Exponent range and precision of the five named binary formats: (a) the exponents of subnormal and normal values on a symmetric logarithmic axis, (b) the precision p in bits. A normal value is m × 2^e with 1 ≤ m < 2. The numbers at the ends of a bar are the exponent of the least subnormal and the largest normal exponent, and the least normal exponent is one minus the largest. The precision counts the leading bit.")

[[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.isIEEE]] says a descriptor has the `.ieee` encoding with the conventional bias $2^{w_e-1}-1$. Nearly every real-number theorem below asks for it as a hypothesis `hfmt : fmt.isIEEE = true`, and `by simp` proves it for the named formats. Each theorem also lists the finiteness hypotheses it needs.

## How to run one addition in every width

Now let's compute with all five. The theorems are stated on [[FloatLib.Floats.Formats.BinaryInterchange.Model]], and a `Model fmt` value is a word, `fmt.bitWidth` bits and nothing else. If you add one to itself in each format and print the word in hexadecimal (base sixteen, and our little helper drops leading zeros), you get:

```lean
def hex (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

def twoBits (fmt : FloatFormat) : String :=
  hex (Model.toNatBits (Model.add (Model.posOne fmt) (Model.posOne fmt)))

#eval twoBits FloatFormat.binary16
-- "4000"
#eval twoBits FloatFormat.bfloat16
-- "4000"
#eval twoBits FloatFormat.binary32
-- "40000000"
#eval twoBits FloatFormat.binary64
-- "4000000000000000"
#eval twoBits FloatFormat.binary128
-- "40000000000000000000000000000000"
```

Every answer is the number two: sign zero, biased exponent $b + 1$, fraction zero. Binary16 and bfloat16 even print the same word, `0x4000`, because $b + 1$ is a one followed by zeros in a five-bit field and in an eight-bit one. So one definition of addition, [[FloatLib.Floats.Formats.BinaryInterchange.Model.add]], ran at five descriptors.

## How to read a word

Let's learn to read words like these by hand. Read as an unsigned number, a word $W$ of width $1 + w_e + w_f$ splits into the sign $s$, the biased exponent $E$ and the fraction $F$:

$$
s = \lfloor W / 2^{w_e + w_f} \rfloor, \qquad
E = \lfloor W / 2^{w_f} \rfloor \bmod 2^{w_e}, \qquad
F = W \bmod 2^{w_f}.
$$

When $1\le E\le2^{w_e}-2$, the word is normal and denotes $(-1)^s(1+F/2^{w_f})\cdot2^{E-b}$. The factor $1+F/2^{w_f}$ is the significand. Its leading one is implicit, so $w_f$ stored fraction bits provide $p=w_f+1$ bits of precision. When $E=0$ and $F\ne0$, the word is subnormal and denotes $(-1)^sF\cdot2^{e_{\min}-w_f}$, without an implicit leading one. When $E=0$ and $F=0$, the word is a signed zero. An all-ones exponent denotes an infinity when $F=0$ and a NaN otherwise.

In a program you'll normally use [[FloatLib.Floats.ExecFloat.Binary]], which takes the two widths and fills in the `.ieee` encoding and the conventional bias. It and its named types, `Binary16`, `BFloat16`, `Binary32`, `Binary64`, `Binary128` and a wider `Binary256`, make up what we call the configured API, and `toModel` lets the model theorems apply to their values. Here's the binary32 value nearest $\pi$, and the smallest positive one:

```lean
def piWord : Binary32 := ExecFloat.Binary.ofBits32 0x40490fdb

#eval piWord
-- 3.1415927
#eval ExecFloat.Binary.toRat? piWord
-- some (13176795 / 4194304)

def leastSubnormal : Binary32 := ExecFloat.Binary.ofBits32 0x00000001

#eval (ExecFloat.Binary.isSubnormal leastSubnormal, leastSubnormal)
-- (true, 1e-45)
```

Let's take `0x40490fdb` apart. Its fields are $s = 0$, $E = 128$ and $F = 4788187$. Counted as a whole number, the significand is $2^{23} + 4788187 = 13176795$, and the exponent is $128 - 127 - 23 = -22$. Its value, $13176795 \cdot 2^{-22} = 3.14159274\ldots$, is less than half a step ($2^{-22}$ there) from $\pi$, as correct rounding promises. And `0x00000001` is $2^{-149} = 2^{e_{\min} - w_f}$, the smallest positive binary32 number. [[FloatLib.Floats.ExecFloat.Binary.ofBits32]] and [[FloatLib.Floats.ExecFloat.Binary.toBits32]] carry a word across unchanged, NaN payload included.

### What happens at the bottom of the range?

Count up from the largest subnormal and the two decoding formulas join without a gap:

| Binary32 word | Exponent field | Fraction field | Exact value |
| --- | --- | --- | --- |
| `0x007fffff` | 0 | $2^{23}-1$ | $(2^{23}-1)\,2^{-149}$ |
| `0x00800000` | 1 | 0 | $2^{23}\,2^{-149}$ |
| `0x00800001` | 1 | 1 | $(2^{23}+1)\,2^{-149}$ |

The second word is the least normal number, $2^{-126}$, and the next is still only $2^{-149}$ away. The name changed and the spacing didn't. Below it the step stays $2^{-149}$ while the values shrink, until at the least positive subnormal the step is the whole value. Rounding there keeps an absolute half-step bound, but the normal range's relative bound, an error in proportion to the value, can't cover it.

## How to make your own width

What if you want a format of your own? A custom format needs no new arithmetic proofs, because the IEEE theorems apply to any descriptor with `isIEEE`. Here are two of them, a 24-bit layout with seven exponent bits and sixteen fraction bits, and a 71-bit one with eleven and fifty-nine:

```lean
abbrev binary24 : FloatFormat := FloatFormat.ieee 7 16
abbrev Binary24 := ExecFloat.Binary (exponentBits := 7) (fractionBits := 16)

def one24 : Binary24 := 1

#eval one24 + one24
-- 2
#eval (binary24.bitWidth, binary24.exponentBias,
       binary24.minNormalExponent, binary24.maxNormalExponent)
-- (24, 63, -62, 63)

example (x y : Model binary24)
    (hout : Model.isFinite (Model.add x y) = true) :
    Model.toReal (Model.add x y) =
      Model.roundAt binary24 (Model.toReal x + Model.toReal y) :=
  Model.toReal_add_eq_roundAt x y (by simp) hout

abbrev binary71 : FloatFormat := FloatFormat.ieee 11 59
abbrev Binary71 := ExecFloat.Binary (exponentBits := 11) (fractionBits := 59)

example : binary71.bitWidth = 71 := by decide

#eval ((1 : Binary71) / 3)
-- 0.3333333333333333335
```

Our 24-bit format has bias 63, normal exponents from $-62$ to $63$, and $p = 17$ significant bits. The first `example` says that a finite binary24 sum is `roundAt` of the real sum, that sum rounded once to nearest even on the binary24 grid. Its `by simp` proves `binary24.isIEEE = true`. At 71 bits there are 60 significant bits, and $1/3$ shows them off with nineteen significant digits.

## How NaNs and signed zeros behave

Now for the words that aren't ordinary numbers, and for zero, which comes in two signs. The top fraction bit of a NaN is called the quiet bit, because setting it makes the NaN quiet. A quiet NaN flows through arithmetic silently, while a signaling NaN is a tripwire that raises the invalid flag when used as an operand. Seven [classifiers](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Model/Carrier.lean), [[FloatLib.Floats.Formats.BinaryInterchange.Model.isZero]], `isSubnormal`, [[FloatLib.Floats.Formats.BinaryInterchange.Model.isFinite]], [[FloatLib.Floats.Formats.BinaryInterchange.Model.isInfinite]], [[FloatLib.Floats.Formats.BinaryInterchange.Model.isNaN]], `isSignaling` and `isQNaN`, test the stored fields, and `classify` sorts a value into the ten IEEE classes. One theorem matches `classify` to the exact value for every binary descriptor, whatever its bias and encoding, and the configured API inherits it through `toModel`.

A NaN can carry a small message in its fraction bits, called its payload. The standard leaves the choice of surviving payload to the implementation [@ieee754_2019], and ours is deterministic. An invalid operation with no NaN operand, such as $\infty - \infty$, returns `canonicalNaN`, positive with only the quiet bit set. With a NaN operand, `chooseNaN2` takes a signaling operand over a quiet one, then the left over the right, and quiets it, keeping the rest of the payload. Our [independent comparisons](#/chapter/external-validation) check NaN class and signaling behaviour, not this choice of payload.

[[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal]] reads a word as a real number. It has to give every word a value, and it sends NaNs, infinities and both zeros to $0$, so we state signed-zero facts on the bits. [[FloatLib.Floats.Formats.BinaryInterchange.Model.exactValue]] keeps what `toReal` loses. It returns an [[FloatLib.Floats.Formats.BinaryInterchange.Model.ExactValue]] with the sign of a zero or an infinity and a NaN's sign, class and payload ([how running code and proofs fit together](#/chapter/the-numerical-models)):

```lean
def posInf : Binary32 := ExecFloat.Binary.ofBits32 0x7f800000
def signaling : Binary32 := ExecFloat.Binary.ofBits32 0x7f800001
def negZero : Binary32 := ExecFloat.Binary.ofBits32 0x80000000

#eval ExecFloat.Binary.exactValue (posInf - posInf)
-- FloatLib.Floats.Formats.BinaryInterchange.Model.ExactValue.nan false false 4194304
#eval ExecFloat.Binary.exactValue (signaling + 1)
-- FloatLib.Floats.Formats.BinaryInterchange.Model.ExactValue.nan false false 4194305
#eval (negZero == (0 : Binary32), ExecFloat.Binary.toBits32 negZero == ExecFloat.Binary.toBits32 0)
-- (true, false)
#eval (1 : Binary32) / negZero
-- -inf
```

In `ExactValue.nan false false 4194304` the three fields are the sign, whether it's signaling, and the stored fraction, and $4194304 = 2^{22}$ is the quiet bit alone. The second result is `0x7f800001` quieted, and its fraction $4194305 = 2^{22} + 1$ keeps the original low bit. The two zeros are equal under `==`, IEEE numerical comparison, but their stored words differ. Dividing one by negative zero gives $-\infty$, so the zero sign affects subsequent arithmetic.

## How to read the status flags

IEEE 754 defines five exception flags: invalid operation, division by zero, overflow, underflow and inexact. FloatLib represents these as the five Boolean fields of [[FloatLib.Numerics.IEEEStatus]]. Pass `(status := true)` to an arithmetic operation or a conversion and you get an [[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEEOutcome]] with the value, its flags and the [ternary value](#/chapter/the-mathematics-of-rounding/how-to-choose-a-rounding-direction). The ternary value gets its name from its three possible answers: the result was rounded up, down or not at all. On the configured types you read a flag as a field:

```lean
def largest : Binary32 := ExecFloat.Binary.maxFinite

#eval ExecFloat.Binary.div (1 : Binary32) 0 (status := true)
-- { value := inf, status := { divideByZero := true }, ternary := Ordering.eq }
#eval ExecFloat.Binary.div (0 : Binary32) 0 (status := true)
-- { value := nan, status := { invalid := true }, ternary := Ordering.eq }
#eval ExecFloat.Binary.mul largest 2 (status := true)
-- { value := inf, status := { overflow := true, inexact := true }, ternary := Ordering.gt }
#eval ExecFloat.Binary.mul leastSubnormal 0.5 (status := true)
-- { value := 0, status := { underflow := true, inexact := true }, ternary := Ordering.lt }
#eval ExecFloat.Binary.div (1 : Binary32) 3 (status := true)
-- { value := 0.33333334, status := { inexact := true }, ternary := Ordering.gt }
#eval ExecFloat.Binary.sqrt (-4 : Binary32) (status := true)
-- { value := nan, status := { invalid := true }, ternary := Ordering.eq }

example (x : Model FloatFormat.binary64) (mode : Model.IEEERoundingMode)
    (hnan : Model.isNaN x = false) (hneg : Model.signBit x = true)
    (hnz : Model.isZero x = false) :
    (Model.sqrt x (mode := mode) (status := true)).status.invalid = true :=
  Model.sqrt_invalid_of_negative_nonzero hnan hneg hnz

example (x : Model FloatFormat.binary64) (mode : Model.IEEERoundingMode)
    (hfinite : Model.isFinite x = true) (hsign : Model.signBit x = false) :
    (Model.sqrt x (mode := mode) (status := true)).status.inexact = true ↔
      Model.toReal (Model.sqrt x (mode := mode) (status := true)).value ≠
        Real.sqrt (Model.toReal x) :=
  Model.sqrt_inexact_iff mode hfinite hsign
```

Dividing one by positive zero produces $\infty$ and raises `divideByZero`; $0/0$ produces a NaN and raises `invalid`. Overflow also raises `inexact`. The product $2^{-149}\cdot0.5$ is halfway between zero and the least positive subnormal. Nearest-even returns zero, and the inexact result below the normal range raises `underflow`. The ternary value is `Ordering.gt` for the overflow and the upward-rounded third, `Ordering.lt` for the product rounded to zero, and `Ordering.eq` for the exact infinity and the two NaN results.

**Note:** As in [how running code and proofs fit together](#/chapter/the-numerical-models/how-to-see-which-flags-an-operation-raised), overflow is decided on the result rounded with an unbounded exponent range. A nonzero result is tiny when, rounded to the destination precision with an unbounded exponent range, its magnitude is below the least normal number. That's what deciding tininess after rounding means. Underflow means tiny *and* inexact, so an exact subnormal result raises neither flag.

Each flag has a theorem saying exactly when it's set. An invalid square root ([[FloatLib.Floats.Formats.BinaryInterchange.Model.sqrt_invalid]]), for example, comes from a signaling NaN or a negative nonzero non-NaN input. For a finite input with a clear sign bit, [[FloatLib.Floats.Formats.BinaryInterchange.Model.sqrt_inexact_iff]] says square root raises inexact, in every direction, exactly when the delivered value isn't the real square root, and `value_sqrt` says asking for status never changes the value. The block's two examples apply a corollary of the invalid theorem and the inexactness theorem, both at binary64 and in every rounding direction at once.

## How to choose a rounding direction

The ternary value tells you which way a result was rounded, but sometimes you'd rather choose the direction yourself, say for a lower bound you can trust. The six directions of [the rounding chapter](#/chapter/the-mathematics-of-rounding/how-to-choose-a-rounding-direction) are the constructors of [[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEERoundingMode]]: `nearest` (ties to even), `nearestAway`, `towardZero`, `up`, `down` and `away`. On a configured type, plain `+`, `-`, `*`, `/`, `x.sqrt` and `x.fma y z` (fused multiply-add) round to nearest even. For any other direction you call a named operation such as [[FloatLib.Floats.ExecFloat.Binary.add]] or [[FloatLib.Floats.ExecFloat.Binary.div]] with a mode like `(mode := .up)`. After `open FloatLib.Rounding` the type is `IEEERoundingMode`, so a function can take a direction as a parameter:

```lean
open FloatLib.Rounding

def third (mode : IEEERoundingMode) : Binary32 :=
  ExecFloat.Binary.div 1 3 (mode := mode)

#eval third .nearest
-- 0.33333334
#eval third .towardZero
-- 0.3333333
#eval third .up
-- 0.33333334
#eval third .down
-- 0.3333333

#eval ExecFloat.Binary.add largest largest (mode := .nearest)
-- inf
#eval ExecFloat.Binary.add largest largest (mode := .up)
-- inf
#eval ExecFloat.Binary.add largest largest (mode := .towardZero)
-- 3.4028235e38
#eval ExecFloat.Binary.add largest largest (mode := .down)
-- 3.4028235e38

example (x y : Model FloatFormat.binary32)
    (hx : Model.isFinite x = true) (hy : Model.isFinite y = true) :
    Model.toEReal (Model.add x y (mode := .down)) ≤ ((Model.toReal x + Model.toReal y : ℝ) : EReal) :=
  Model.toEReal_add_down_le x y (by simp) hx hy
```

One third sits between two binary32 neighbours. Nearest-even and up pick the upper one, toward zero and down the lower, and those two agree only because one third is positive. The overflow lines follow IEEE 754-2019 Section 7.4 [@ieee754_2019]. A direction that pushes the magnitude away from zero overflows to infinity, while toward zero, or toward the infinity of the other sign, stops at the largest finite value, $16777215 \cdot 2^{104} = (2 - 2^{-23}) \cdot 2^{127}$.

Interval arithmetic, which carries a lower and an upper bound, is built on directed rounding, rounding in a chosen direction, so these theorems are inequalities in the extended reals (the reals with $\pm\infty$), through [[FloatLib.Floats.Formats.BinaryInterchange.Model.toEReal]]. For finite operands [[FloatLib.Floats.Formats.BinaryInterchange.Model.toEReal_add_down_le]] says the `.down` sum never lands above the exact sum, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.le_toEReal_add_up]] says the `.up` sum never lands below it. Our [other directed operations](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/BinaryInterchange/DirectedSemantics), subtraction, multiplication, division and square root, have bounds of the same shape with their finite-input and domain hypotheses.

## How to cast between widths

Say you have bfloat16 model weights and want them in binary32, or a binary64 result to store as binary32. Both are casts, written `value.cast (target := …)` ([[FloatLib.Floats.ExecFloat.cast]]). A cast runs through one conversion pipeline, shared with posits (another number system, with its own chapter) and the P3109 machine-learning formats. It decodes the source to an exact signed rational, keeping the sign of zero, and quantizes once, that is, rounds onto the destination grid. That's nearest-even unless you pass `(mode := ...)`, any [[FloatLib.Numerics.RoundingMode]]: one of the six directions or `.stochastic`, which rounds up or down at random. For a binary destination `(context := ...)` holds the overflow, underflow, infinity and NaN policies, such as saturation or rejecting infinities. You get back a `ConversionOutcome`: a success with the value and its conversion flags, or a reported failure.

Let's try four casts: two binary64 values that sit exactly halfway between binary32 neighbours, 65504 from binary16 up to binary32, and 70000 from binary32 down to binary16. You get:

```lean
def halfUlp64 : Binary64 := ExecFloat.Binary.ofBits64 0x3ff0000010000000
def threeHalfUlp64 : Binary64 := ExecFloat.Binary.ofBits64 0x3ff0000030000000

#eval ExecFloat.Binary.toRat? halfUlp64
-- some (16777217 / 16777216)
#eval halfUlp64.cast (target := Binary32)
-- .success 1 { inexact := true }
#eval threeHalfUlp64.cast (target := Binary32)
-- .success 1.0000002 { inexact := true }
#eval (65504 : Binary16).cast (target := Binary32)
-- .success 65504
#eval (70000 : Binary32).cast (target := Binary16)
-- .success inf { inexact := true, overflow := true }

example (x : Model FloatFormat.binary32)
    (hout : Model.isFinite (Model.cast FloatFormat.binary32 FloatFormat.binary64 x) = true) :
    Model.toReal (Model.cast FloatFormat.binary32 FloatFormat.binary64 x) = Model.toReal x :=
  Model.cast_exact_of_gridExtension x (by decide) (by decide) (by decide) hout

example (x : Model FloatFormat.binary64)
    (hout : Model.isFinite (Model.cast FloatFormat.binary64 FloatFormat.binary32 x) = true) :
    Model.toReal (Model.cast FloatFormat.binary64 FloatFormat.binary32 x) =
      Model.roundAt FloatFormat.binary32 (Model.toReal x) :=
  Model.cast_eq_roundAt (by simp) x hout
```

Widening 65504, the largest binary16 value, sets no flags, and 70000, which binary16 can't represent, becomes an infinity with `overflow` and `inexact` set. Now the ties. The first binary64 word is $1 + 2^{-24}$, halfway between the binary32 neighbours $1$ and $1 + 2^{-23}$, and the second, $1 + 3 \cdot 2^{-24}$, is halfway between $1 + 2^{-23}$ and $1 + 2^{-22}$. A tie goes to the neighbour whose last bit is even, so the first rounds down to $1$ and the second up to $1 + 2^{-22}$. You can't see that parity in the decimals, only on the destination grid.

### What the cast theorems say

The block's two theorems are about [[FloatLib.Floats.Formats.BinaryInterchange.Model.cast]], which the configured cast doesn't call. `Model.cast` rounds a finite source to nearest even in the destination, where it can overflow to a signed infinity or land among the subnormals, and keeps an infinity a same-sign infinity when the destination has one. Into an IEEE format a NaN comes out quiet with its sign, and a signaling NaN raises invalid, as Section 7.2 of [@ieee754_2019] requires. It keeps its payload when that fits in the destination's fraction without the quiet bit, and gets a zero payload otherwise. That's Section 6.2.3 of the same standard, so a quiet NaN survives a widen-and-narrow round trip.

The two casts line up through our [configured conversion theorem](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/Conversion/Proof.lean): with the default mode and context a finite value comes out as `Model.roundRat`, the model's rounding of a rational, and for an IEEE destination and a finite result [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_roundRatScaled_eq_roundAt]] makes it `roundAt`. Under the default NaN policy NaNs come out as `Model.cast` builds them. The flags aren't `IEEEStatus`, though, because the pipeline also reaches formats that saturate or wrap.

[[FloatLib.Floats.Formats.BinaryInterchange.Model.cast_eq_roundAt]] says a cast into an IEEE descriptor with a finite result is one nearest-even rounding in the destination, and only the destination needs the IEEE convention. Why the `hout` premise? It keeps overflow out. The cast of 70000 is an infinity whose `toReal` is zero, while `roundAt` rounds on a grid with no top, so equating the two would quietly erase the overflow.

[[FloatLib.Floats.Formats.BinaryInterchange.Model.cast_exact_of_gridExtension]] says the cast is exact when the destination grid contains the source grid. That means at least as many fraction bits and a subnormal exponent at least as low, which three `by decide` calls check along with the destination's IEEE contract. Exponent widths needn't match, so it covers binary16 to binary32, binary32 to binary64 and binary64 to binary128. A finer grid doesn't guarantee room at the top, though, so the finite-result premise stays, as IEEE 754-2019 §5.4.2 asks for range as well as precision [@ieee754_2019].

### How to widen without rounding

Some casts don't round at all. A finite value cast to its own format comes back unchanged. When the exponent width, bias and encoding agree and only the fraction grows, `widenExact` copies the fields. Bfloat16 to binary32 is one of these, and you can do it in your head: append sixteen zero bits, and the bfloat16 word `0x3fc0`, which is $1.5$, becomes `0x3fc00000`. The [widening proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Conversion/Cast/Widening.lean) covers the bit packing at arbitrary widths. For every finite source, subnormals and signed zeros included, compatible widening is exact in every rounding mode:

```lean
example {src dst : FloatFormat} (x : Model src) (mode : Model.IEEERoundingMode)
    (he : src.expWidth = dst.expWidth)
    (hb : src.exponentBias = dst.exponentBias)
    (hc : src.encoding = dst.encoding)
    (hf : src.fracWidth ≤ dst.fracWidth)
    (hx : Model.isFinite x = true) :
    Model.cast src dst x mode = Model.widenExact x he hb hc hf :=
  Model.cast_eq_widenExact_of_compatibleWidening x he hb hc hf hx mode
```

Its exactness theorem, [[FloatLib.Floats.Formats.BinaryInterchange.Model.cast_exact_of_compatibleWidening]], needs only a finite source, with no premise on the result.

## How to mix formats

What happens when a binary32 value meets a binary64 one? In FloatLib you name where the answer lands, because formats never promote implicitly: nothing is widened behind your back. The mixed operations `ExecFloat.Mixed.add`, `sub`, `mul`, `div` and `fma` take the same `target`, `mode` and `context` as `cast` and return a `ConversionOutcome` too. Here are some casts and a mixed product:

```lean standalone
import FloatLib

open FloatLib.Floats

#eval (1.5 : Binary32).cast (target := Binary64)
-- .success 1.5
#eval (-(0 : Binary32)).cast (target := Binary64)
-- .success (-0)
#eval (0.1 : Binary64).cast (target := Binary32)
-- .success 0.1 { inexact := true }
#eval (0.1 : Binary64).cast (target := Binary32) (mode := .down)
-- .success 0.099999994 { inexact := true }
#eval (0.1 : Binary64).cast (target := Binary32) (mode := .down)
    (context := ({ infinity := .reject } : ExecFloat.Binary.Conversion.Policy))
-- .success 0.099999994 { inexact := true }

def tenth : Binary32 := 0.1

#eval (1.5 : Binary32) * tenth
-- 0.15

def widenedProduct := ExecFloat.Mixed.mul (target := Binary64) (1.5 : Binary32) tenth

#eval widenedProduct
-- .success 0.15000000223517418
#eval (1.5 : Binary32).cast (target := Posit32)
-- .success 1.5
#eval ExecFloat.Binary.toFloat32 ((1.5 : Binary32) + 2.25)
-- 3.750000
```

A mixed operation works like a cast. It decodes its operands exactly, computes in the destination's exact domain, the exact numbers that destination rounds from, and rounds once. For binary destinations that domain is [[FloatLib.Numerics.SignedRat]], a rational with an IEEE sign bit attached. That's why the second cast delivers $-0$ where a plain rational would give $+0$. Binary64's $0.1$ doesn't fit in binary32's 24 significant bits, so narrowing it reports `inexact := true`, and rounding downward gives the binary32 neighbour below. The cast with a `context` rejects infinities and leaves the downward rounding alone, because a context has no direction of its own. A success prints only the flags that were raised.

Both products use the same operands. $1.5$ times the stored $0.1$ needs 26 significand bits, so `*` at binary32 rounds it to $5033165 \cdot 2^{-25}$, while `Mixed.mul` into binary64 returns the exact $40265319 \cdot 2^{-28}$ with no flag raised. That clear flag is about the stored inputs, though. `tenth` was rounded when we defined it, and a comparison with the original decimal data has to account for that literal conversion too.

Mixed operations need finite operands, and `Mixed.div` also needs a nonzero divisor. Otherwise they report a failure before destination conversion. So they're the finite part of IEEE 754's formatOf operations, the standard's mixed-format arithmetic, which would return an infinity or a NaN there. [[FloatLib.Floats.ExecFloat.spec_cast]] and `Mixed.preparedSpec_add` with its siblings spell out the steps: decode, embed, operate, round once.

The last line leaves FloatLib. [[FloatLib.Floats.ExecFloat.Binary.ofFloat32]] and [[FloatLib.Floats.ExecFloat.Binary.toFloat32]] cross to Lean's native `Float32` through the interchange word, the stored bits, and the line prints in Lean's six-decimal style. Conversions to `Float32` canonicalize NaNs, swapping them for a standard NaN ([the performance chapter](#/chapter/performance/host-arithmetic-as-a-reference)), and `Float32.ofBits` canonicalizes NaN payloads, so use `toBits32` when the payload matters.

### How to round a whole expression once

Mixed operations round once, but one operation at a time. Longer finite expressions can get one final rounding too. Let's look at one where it matters. Binary32's $0.1$ is exactly $13421773 \cdot 2^{-27}$, and `threeTenths`, the stored $0.3$, is $5033165 \cdot 2^{-24}$. So the exact value of `3 * tenth - threeTenths` is

$$3 \cdot 13421773 \cdot 2^{-27} - 5033165 \cdot 2^{-24} = (40265319 - 40265320) \cdot 2^{-27} = -2^{-27},$$

which is representable. Round twice and the answer changes. `3 * tenth` needs 26 bits and rounds up to `threeTenths` itself, so the subtraction gives $0$. `fma` and `roundOnce` round only at the end and keep the exact difference. [[FloatLib.Floats.ExecFloat.roundOnce]] evaluates a `do` block in the exact domain and quantizes the result once.

```lean standalone
import FloatLib

open FloatLib.Floats

def tenth : Binary32 := 0.1

def threeTenths : Binary32 := 0.3

#eval 3 * tenth - threeTenths
-- 0
#eval ExecFloat.fma 3 tenth (-threeTenths)
-- -7.450581e-9

def onceRounded : ExecFloat.ConversionOutcome Binary32 :=
  ExecFloat.roundOnce (Exact := FloatLib.Numerics.SignedRat) do
    let a ← ExecFloat.ExactExpression.operand 0 tenth
    let b ← ExecFloat.ExactExpression.operand 1 threeTenths
    let three ← ExecFloat.ExactExpression.operand 2 (3 : Binary32)
    pure (three * a - b)

#eval onceRounded
-- .success (-7.450581e-9)
```

In `onceRounded` the result type fixes the destination. `operand` decodes each input to an exact `SignedRat` value, so the arithmetic on `a`, `b` and `three` calls no binary32 operation, and `0`, `1` and `2` label the inputs for error reporting. `pure` hands the exact result to `roundOnce`, and rounding the exact $-2^{-27}$ gives it back unchanged, matching the `fma` line. The once in `roundOnce` is a theorem: [[FloatLib.Floats.ExecFloat.ConversionProof.preparedSpec_roundOnce]] states that a successful evaluation reaches the destination quantizer exactly once. A non-finite operand, or a checked division by zero through `ExactExpression.div`, fails without reaching the quantizer.

### Which zero do you get when terms cancel?

`roundOnce (mode := .down)` rounds only the final quantization downward. Plain `SignedRat` addition keeps the nearest-even rule for the sign of an exact zero. So if cancellation inside the expression has to follow the same direction, use `ExactExpression.add (target := Destination) x y (mode := .down)` or `ExactExpression.sub` inside the `do` block. Exact cancellation under rounding toward negative infinity then produces negative zero:

```lean standalone
import FloatLib

open FloatLib.Floats

def cancelledDownward : ExecFloat.ConversionOutcome Binary32 :=
  ExecFloat.roundOnce (mode := .down) do
    let a ← ExecFloat.ExactExpression.operand 0 (1 : Binary32)
    let b ← ExecFloat.ExactExpression.operand 1 (-1 : Binary32)
    ExecFloat.ExactExpression.add (target := Binary32) a b (mode := .down)

#eval cancelledDownward.map ExecFloat.Binary.toBits32
-- .success 2147483648
```

That word is `0x80000000`, the sign bit and nothing else, so this directed addition returns negative zero. `Mixed.add`, `Mixed.sub` and `Mixed.fma` take this cancellation rule from their own `mode`.

## How to work with complex numbers

A complex number has two parts, and multiplying two of them looks like one operation on paper:

$$
(a+bi)(c+di)=(ac-bd)+(ad+bc)i.
$$

With floating-point components that formula hides six rounding steps. `ExecComplex fmt` stores two `Model fmt` values, and its multiplication rounds each of the four products, then the subtraction and the addition. Writing $R$ for the format's nearest-even rounder, the computed components are

$$
R\bigl(R(ac)-R(bd)\bigr),\qquad
R\bigl(R(ad)+R(bc)\bigr).
$$

If $ac$ and $bd$ nearly cancel, errors in the two products can dominate their difference, so a proof about the implementation has to keep those inner roundings. We prove the multiplication theorem for any descriptor with conventional IEEE semantics:

```lean standalone
import FloatLib.Floats.Formats.BinaryInterchange.Complex.Semantics

open FloatLib.Floats.Formats.BinaryInterchange

example {fmt : FloatFormat} (x y : ExecComplex fmt)
    (hfmt : fmt.isIEEE = true) (h : ExecComplex.MulFinite x y) :
    ExecComplex.toComplex (x * y) =
      ExecComplex.roundedMul fmt
        (ExecComplex.toComplex x) (ExecComplex.toComplex y) :=
  ExecComplex.toComplex_mul_eq_roundedMul x y hfmt h
```

`MulFinite` asks for finite inputs, four finite rounded products and finite final components, because a product can overflow even when the exact complex answer would fit after cancellation. Componentwise addition and subtraction have matching theorems. Division sets a different trap. The familiar denominator $c^2+d^2$ can overflow while $c$ and $d$ are perfectly finite, so `ExecComplex.div` uses the ratio formula from [Robert L. Smith's Algorithm 116 (1962)](https://doi.org/10.1145/368637.368661), pivoting on the larger denominator component. `toComplex_div_eq_roundedDiv` records the selected branch and its nine rounding steps, under a `DivFinite` hypothesis that asks for a nonzero pivot and rounded denominator and for finite inputs, intermediates and results, since other intermediates can overflow too. Magnitude, the absolute value of a complex number, uses the same scaling idea. With $s=\max(|a|,|b|)$, it computes the rounded counterpart of

$$
s\sqrt{(a/s)^2+(b/s)^2}.
$$

A zero scale returns zero right away. Otherwise `toReal_magnitude_eq_roundedMagnitude` accounts for seven scalar roundings (two divisions, two squares, the addition, the square root and the final rescaling) under `MagnitudeFinite` conditions on the intermediate ranges and the square-root domain.

How far is the whole operation from the exact one? The arithmetic of `ExecComplex` rounds at every step: a product is four real products and two real sums, each rounded. For the real and imaginary parts taken one at a time there is no good answer. Take the real part, $ac - bd$: when the two products cancel, no bound relative to $|ac - bd|$ holds, only one relative to $|ac|+|bd|$. Measured as a complex number, though, the product is fine. With $u$ the unit roundoff and $\eta$ the underflow error of the format:

| Operation | Bound on the error | Premise |
| --- | --- | --- |
| `+`, `-` | $u\,\lVert\text{exact}\rVert$ | none beyond finiteness; no underflow term |
| `*` | $\sqrt5\,u\,\lVert xy\rVert + 5\eta$ | at least five bits of precision |
| `ExecComplex.mulFma` | $2u\,\lVert xy\rVert + 5\eta$ | none |
| `/` (Smith's ratio formula) | $\sqrt2\,\bigl((1+u)^4/(1-u)^3 - 1\bigr)\lVert x/y\rVert$ | no underflow in the six inner roundings (`DivNormal`) |
| `magnitude` (scaled) | $\bigl((1+u)^4 - 1\bigr)\,\lvert z\rvert + \eta$ | `MagnitudeNormal` |

```lean standalone
import FloatLib.Floats.Formats.BinaryInterchange.Complex.ErrorBounds

open FloatLib.Floats.Formats.BinaryInterchange

example (x y : ℂ) :
    ‖ExecComplex.roundedMul FloatFormat.binary32 x y - x * y‖ ≤
      √5 * Model.unitRoundoffAt FloatFormat.binary32 * ‖x * y‖ +
        5 * Model.underflowErrorAt FloatFormat.binary32 :=
  ExecComplex.norm_roundedMul_sub_le _ (by decide) x y
```

The product bound is that of [Brent, Percival and Zimmermann (2007)](https://doi.org/10.1090/S0025-5718-07-01931-X), with an underflow term they exclude, and the one with fused multiply-adds is the constant that [Jeannerod, Kornerup, Louvet and Muller (2017)](https://doi.org/10.1090/mcom/3123) prove without underflow. For the division and the magnitude we found no published proof in this form, so those two constants are what our proof gives. Our division constant is at most $\sqrt2\,\gamma_7$ with $\gamma_7=7u/(1-7u)$.

Each bound is a theorem for every binary descriptor and all operands under nearest-even rounding. It is stated for the rounded expression, and for the operation of `ExecComplex` on an IEEE descriptor under the finiteness premise of that operation ([[FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.norm_roundedDiv_sub_le]], [[FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.abs_roundedMagnitude_sub_le]] and their siblings). Why do division and magnitude take the absence of underflow as a premise, where the product has an $\eta$ term? An underflow error $\eta$ in the denominator's product is a relative error $\eta/|c|$, so near the subnormal range no bound of the form $Cu\lVert x/y\rVert + C'\eta$ is true.

With `import FloatLib.Floats.Formats.BinaryInterchange.Complex.Roundoff`, the [`roundoff`](#/chapter/proving-numerical-bounds) commands bound a component of any complex program, since that import tells them which scalar expression computes each component of `+`, `-`, `*`, `mulFma`, `/`, negation, conjugation, `normSq` and `magnitude`. The normwise bounds above are theorems about a complex number and aren't `roundoff` rules.

There are two limits, though. The finite theorem doesn't give you a correctly rounded hypotenuse, and it doesn't show that every intermediate stays finite. `normSq`, the squared norm, is a rounded sum of squares with no scaling.

### How to evaluate a complex elementary function

All of that arithmetic rounds at every step. An elementary function rounds once: each part of the result is the exact part, rounded in the direction you ask for. That is the contract of GNU MPC, and here it is a theorem. `ExecComplex.exp`, `log`, `sqrt`, `sin`, `cos`, `tan`, `sinh`, `cosh`, `tanh`, `asin`, `acos`, `atan`, `asinh`, `acosh` and `atanh` are C's `cexp`, `clog`, `csqrt` and the rest of `<complex.h>` (C23 7.3 and Annex G). `expm1` and `log1p` are $e^z-1$ and $\log(1+z)$ without the cancellation at a small $z$, `rsqrt` is $1/\sqrt z$, and `pow` is `cpow`. They aren't part of `import FloatLib`. Each family has a module under `FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary`, with its theorems in the module of the same name plus `Proof`:

```lean standalone
import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.ValueProof

open FloatLib.Floats.Formats.BinaryInterchange

example {fmt : FloatFormat} (hfmt : fmt.isIEEE = true) (z : ExecComplex fmt)
    (hz : ExecComplex.isFinite z = true) (mode : Model.IEEERoundingMode) :
    (ExecComplex.exp z mode).re =
      Model.roundReal fmt mode (Complex.exp (ExecComplex.toComplex z)).re
        (ExecComplex.expExact z).reZero := by
  rw [ExecComplex.exp_eq hfmt hz mode, ExecComplex.Exact.round, ExecComplex.expExact_value hz]
```

Read the statement from the inside out. `Complex.exp (toComplex z)` is Mathlib's exponential of the complex number that `z` stores. `Model.roundReal fmt mode x` is the rounding of the real number `x`: the grid value when that fits, and the overflow result of IEEE 754-2019, clause 7.4, when it doesn't ([[FloatLib.Floats.Formats.BinaryInterchange.Model.roundReal_roundsTo]]). The last argument is the sign of the zero you get when the part is exactly zero. Nothing in the theorem mentions a search budget or a set of hard cases. It holds for every finite `z`, in binary16 as in binary128 or a format of your own, and the definition is the same one for all of them. So $e^{a+ib}$ doesn't overflow through $e^a$ when $e^a\cos b$ fits.

How can a program round a transcendental number correctly for every input? Rounding only asks one kind of question, how the part compares with a rational, and each function answers that exactly. And the answer always comes, because a part is never a rational number unless we know which one. That is number theory: for rational $a$ and $b$, not both zero, $e^a\cos b$ is irrational, by the Lindemann-Weierstrass argument of Mathlib extended to Gaussian rational exponents ([[FloatLib.Numerics.Enclosure.gaussianInt_add_sum_exp_div_ne_zero]]). In practice one enclosure of the part settles nearly every comparison, and the exact comparison runs only for a rational inside it.

Here is what is proved and what is tested, since the two differ:

- **Every finite argument** of the eighteen functions of one argument has a theorem. That includes the poles and the signed zeros: `log` of a zero is $-\infty$ with the angle of that zero ([[FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.log_zero]]), `atanh (±1)` and `atan (±i)` are infinite, and `log1p` and `expm1` return a zero unchanged.
- **The symmetries** hold at every argument, NaNs and infinities included: each function commutes with conjugation, eight are odd and `cosh` and `cos` are even ([[FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.exp_conj]] and its siblings), in the four rounding directions that negation fixes, since rounding $-x$ upward is the negation of rounding $x$ downward.
- **The other values at a NaN or an infinite part** follow the tables of C23 Annex G. Those are tests, row by row, in four formats and six rounding directions, not theorems.
- **The sign of a zero picks the side of a branch cut**, so `sqrt (-4 + 0 i)` is `2 i` and `sqrt (-4 - 0 i)` is `-2 i`. Off the cut the value is Mathlib's own principal value ([[FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.exp_logExact_value]], [[FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.sinh_asinhExact_value]]). Mathlib has no complex `arcsin` or `arcosh`, so there the reference is Kahan's principal expressions written with Mathlib's logarithm and square root.

`pow` is different. Whether a part of $z^w$ is a rational number is a question we can't always answer, so `ExecComplex.powChecked` returns the power together with a certificate, and [[FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.pow_eq]] proves a certified power correctly rounded. A power is certified when it is exact for a reason we know, like an integer power of moderate size, $(-4)^{1/4}=1+i$ or an even power of a base on a diagonal such as $(1+i)^{2^{40}}$, when its exponent $\operatorname{Re}(w\log z)$ alone puts a part beyond the largest finite number or below half the least positive one ([[FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.powExtreme?_eq]]), at any size of that exponent, and whenever an enclosure of each part decides its rounding. For a base next to an axis the enclosure takes the angle from that axis: the real part of $(-1+2^{-100}i)^{3/2}$ is $-\tfrac32\,2^{-100}$ and a relative $2^{-200}$ more, and the power is certified in every direction. Our tests found no part on a rounding boundary outside the exact cases, but there is no proof that none exists: for a complex exponent that is a question of transcendence theory. An uncertified power is still within an enclosure of the exact one, but its last bit isn't proved.

We compared them with GNU MPC on 10,944 results in binary16, bfloat16, binary32 and binary64, in every rounding direction, and found no difference. A call takes 0.23 to 1.08 milliseconds in binary32 and 0.47 to 3.98 in binary64 at ordinary arguments.

A small argument needs its own enclosure. Where a function is the identity to first order, such as `sin` or `expm1` far below one, the result is the argument up to a correction that is small against $|z|$: of relative order $|z|^2$ for `sin`, and of order $|z|$ for `expm1`. So a part of the result can lie so close to a part of the argument, which is a representable number, that an enclosure at the working precision can't tell the two apart. There each part is enclosed by Taylor polynomials in exact rational arithmetic with their remainder bounds ([[FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.contains_smallProduct?]] and its siblings), with a remainder four orders of $|z|$ below the working precision. When that enclosure settles the rounding, nothing is compared exactly, and when it doesn't, the general enclosure takes over. At subnormal binary64 arguments a call takes 0.7 to 2.0 milliseconds for `cos`, `exp`, `log1p`, `sin`, `sinh` and `expm1`, 2.7 to 3.0 for `atan` and `atanh`, 3.2 to 4.8 for `asinh` and `asin`, and 5.4 to 5.6 for `tan` and `tanh` ([`oracle complex-timing functions`](https://github.com/lean-dojo/FloatLib/blob/main/tests/FloatLibTests/Oracle/ComplexTiming.lean)), and Lean's kernel evaluates one part in 0.08 to 0.17 seconds. A second comparison with GNU MPC, on 234,744 arguments with small, subnormal and mixed parts in binary16, binary32 and binary64, found no difference. A third, on 60,204 powers in the same formats and six rounding directions, with bases next to an axis, perturbed perfect powers, bases whose parts have the least ratio of the format and exponents up to $2^{90}$, found no difference and no power without a certificate.

You can evaluate all of this in Lean's kernel as well as in compiled code: `decide +kernel` proves `exp (1 + i)` in binary32 in under a second, with no trusted compiler in the proof.

## How to convert to integers and text

What's our binary32 $\pi$ as an 8-bit integer? And $300$? FloatLib has [integer conversions](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/BinaryInterchange/DType) between binary values and fixed-width two's-complement integers (the usual signed machine integers). `ExecDType.convertToIntegerExact` rounds a finite value to an integer in the requested direction and succeeds only if it fits the signed width, with inexact set when a fraction was thrown away. An infinity, a NaN or an out-of-range value is a reported failure, never some fixed integer, and the [integer conversion theorem](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/DType/Semantics.lean) and its out-of-range companion pin down both finite cases. Going the other way, `ExecDType.convertFromInt` rounds a `FixedInt width` once into the destination, with the five flags under `status := true`, and `convertFromInt_nearest_eq_round` proves that a finite nearest-even result is `roundAt` of the integer. The parse and format lines come up in the next section.

```lean
open FloatLib.Numerics.Representations

#eval (ExecDType.convertToIntegerExact (width := 8) (ExecFloat.Binary.toModel piWord) (mode := .nearest)).map FixedInt.toInt
-- .success 3 { inexact := true }
#eval (ExecDType.convertToIntegerExact (width := 8) (ExecFloat.Binary.toModel (300 : Binary32)) (mode := .nearest))
-- .failure .outOfRange
#eval let o := ExecDType.convertFromInt FloatFormat.binary16 (FixedInt.ofInt (width := 32) 2049)
        (status := true)
      ((ExecFloat.Binary.ofModel o.value : Binary16), o.status.inexact)
-- (2048, true)
#eval (ExecFloat.Binary.parse "0.1" : Except Model.ParseError Binary32)
-- Except.ok 0.1
#eval Model.format (Model.canonicalNaN FloatFormat.binary32)
-- "nan"

example {width : Nat} (x : FixedInt width)
    (hfin : Model.isFinite (ExecDType.convertFromInt FloatFormat.binary32 x) = true) :
    Model.toReal (ExecDType.convertFromInt FloatFormat.binary32 x) =
      Model.roundAt FloatFormat.binary32 (FixedInt.toInt x : ℝ) :=
  ExecDType.convertFromInt_nearest_eq_round x (by simp) hfin
```

Rounding the binary32 $\pi$ gives the 8-bit integer $3$ with inexact set. $300$ doesn't fit in eight signed bits, so it fails with `outOfRange`. And binary16 can't hold $2049$: its eleven significant bits cover every integer only up to $2048$, so nearest-even returns $2048$ and flags inexact.

### How to parse and print numbers

That `0.1` we parsed above isn't one tenth. It's the $13421773 \cdot 2^{-27}$ we met earlier, the familiar `0x3dcccccd`, whose exact decimal takes 27 digits after the point. So `#eval` and `toString` print a decimal that parses back to the same value, normally the shortest, here `0.1`. A value prints exactly when its exact decimal fits in the nine significant digits binary32 needs, so `3.75` stays `3.75`.

`ExecFloat.Binary.parse` reads decimal, hexadecimal and the compact dyadic syntax (an integer times a power of two), infinities and signed NaNs included. It rounds the exact value once, nearest-even unless you pass `mode`. `status := true` adds the five flags, `limits := some {}` checks input size and exponent bounds first, and malformed input gives a parse error. Here are some more examples:

```lean
#eval (ExecFloat.Binary.parse "0.1" (mode := .towardZero) :
    Except Model.ParseError Binary32)
-- Except.ok 0.099999994
#eval (ExecFloat.Binary.parse "-0" (limits := some { maxBytes := 128 }) :
    Except Model.ParseError Binary32).map
      (fun (value : Binary32) => value.format (style := .fixed (places := 3)))
-- Except.ok "-0.000"
#eval (ExecFloat.Binary.parse "0.1" (status := true)).map fun outcome =>
    ((outcome.value : Binary32), outcome.status.inexact, outcome.ternary)
-- Except.ok (0.1, true, Ordering.gt)
#eval (12.5 : Binary32).format (style := .fixed (places := 3))
-- "12.500"
#eval (12.5 : Binary32).format (style := .scientific (places := 3))
-- "1.250e1"
#eval (0.1 : Binary64) + 0.2
-- 0.30000000000000004
```

`.fixed (places := n)` and `.scientific (places := n)` count digits after the point, like C's `%.3f` and `%.3e`, and keep trailing zeros. Our proofs reach the printed characters: the digit count, the midpoint choice, an error of at most half the last printed unit under nearest-even, and inexact exactly when the printed value differs from the stored one. The round-trip theorems bring back every finite IEEE word from its text, sign of zero included: hexadecimal output for every input rounding mode, and exact decimal output and the shortest display for nearest-even input. The tests check every binary16 and bfloat16 word and find no shorter decimal that reads back for any display that isn't exact.

## How to compare two floats

Comparing two floats is easy right up until a NaN or a negative zero shows up. Is a NaN less than one? No, and it isn't equal or greater either. [[FloatLib.Floats.Formats.BinaryInterchange.Model.compare]] returns `none` when either operand is a NaN and `some` ordering otherwise, so "unordered" is an answer you can see, never a comparison that quietly says false. Its theorems match real order on finite values and extended-real order with infinities, and the two zeros compare equal.

```lean
example (x y : Model FloatFormat.binary16)
    (hx : Model.isFinite x = true) (hy : Model.isFinite y = true) :
    Model.compare x y = some .lt ↔ Model.toReal x < Model.toReal y :=
  Model.compare_eq_some_lt_iff_toReal_lt_of_isFinite x y hx hy

#eval Model.compare (Model.posZero FloatFormat.binary32) (Model.negZero FloatFormat.binary32)
-- some (Ordering.eq)
#eval Model.compare (Model.canonicalNaN FloatFormat.binary32) (Model.posOne FloatFormat.binary32)
-- none
```

## Can rounding to an integer overflow?

Yes. In the six-bit IEEE-style descriptor below, two exponent bits and three fraction bits, the largest finite value is $3.75$. Truncating, which rounds toward zero, gives three, but the nearest integer is four, and four doesn't exist here, so it overflows. Truncating toward zero never increases a magnitude (IEEE 754-2019 §4.3.2 and §5.9 [@ieee754_2019]), so [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_roundToIntegral_towardZero]] needs only a finite input and the IEEE encoding convention. Its finiteness and overflow companions hold even when a custom descriptor has more fraction bits than its upper exponent bound. The other integral directions keep the range condition `fmt.fracWidth ≤ fmt.maxNormalExponent`, which the standard's interchange formats all satisfy.

```lean
example {fmt : FloatFormat} (value : Model fmt)
    (hfmt : fmt.isIEEE = true) (hfinite : Model.isFinite value = true) :
    Model.isFinite (Model.roundToIntegral value (mode := .towardZero)) = true :=
  Model.isFinite_roundToIntegral_towardZero hfmt value hfinite

abbrev IntegralNarrow := FloatFormat.ieee 2 3
#eval (Model.roundToIntegral
  (Model.ofNatBits (fmt := IntegralNarrow) 23) (mode := .towardZero)).toNatBits
-- 20
#eval Model.isInfinite (Model.roundToIntegral
  (Model.ofNatBits (fmt := IntegralNarrow) 23) (mode := .nearest))
-- true
```

In the block, word `23` is $3.75$ and word `20` is three. `roundToIntegral` is one of a few operations with their own status and finite-value theorems, with `remainder`, `scale`, `nextUp`, `nextDown` and `logB`. That last one rounds $\lfloor\log_2|x|\rfloor$ into the source format, where a small format can lose accuracy, while `logBInt` returns it exactly.


## Where is each operation of IEEE 754-2019?

IEEE 754-2019 gives every operation a name, such as `roundToIntegralTiesToEven`, `compareQuietLess` or `augmentedAddition`, and you can call each operation FloatLib has by that name. For the binary formats look in `Model`, the reference model of this chapter, and in `ExecFloat.Binary`, the values you compute with. For the decimal formats look in `Arithmetic` and `Datum` ([the decimal chapter](#/chapter/decimal-arithmetic)).

Where the standard names every member of a family, as it does for the five rounding directions of `roundToIntegral…` and for the 22 comparisons, FloatLib defines the family once, with the direction or the predicate as an argument, and declares the members from it. So a member is its family at one argument by definition, and every theorem about the family applies to it:

```lean
example (x y : Model FloatFormat.binary64) :
    Model.compareQuietLess x y = Model.compareQuiet .less x y ∧
      Model.roundToIntegralTowardZero x = Model.roundToIntegral x (mode := .towardZero) :=
  ⟨rfl, rfl⟩
```

### What do the augmented operations return?

Clause 9.5 recommends augmented arithmetic for binary formats. Where the head is finite, `augmentedAddition` returns the sum rounded to nearest with ties toward zero, together with the exact rounding error. In binary16 the successor of one, plus half a unit in the last place, is such a tie: ordinary addition rounds it to the even neighbour `0x3C02`, and the augmented operation keeps `0x3C01` and hands you the half unit back.

```lean
def afterOne : Binary16 := ExecFloat.Binary.ofNatBits 0x3C01
def halfUnit : Binary16 := ExecFloat.Binary.ofNatBits 0x1000

#eval (afterOne + halfUnit).toNatBits
-- 15362
#eval (ExecFloat.Binary.augmentedAddition afterOne halfUnit).head.toNatBits
-- 15361
#eval (ExecFloat.Binary.augmentedAddition afterOne halfUnit).tail.toNatBits
-- 4096
```

[[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_augmentedAddition_add]] proves that in an IEEE descriptor the head and tail add up to the exact sum whenever the head is finite.

### Why isn't an operation in another format a cast afterwards?

In the standard, arithmetic is more general than `x + y` on one type. Its operations are formatOf operations: the operands and destination can have different formats of the same radix, and the exact result is rounded once into the destination. `Model.formatOfAddition`, `formatOfSubtraction`, `formatOfMultiplication`, `formatOfDivision` and `formatOfFusedMultiplyAdd` take the destination as their first argument and return the value with its flags. One rounding is not a cast after the operation. Take $1 + 2^{-24}$, which lies exactly between two binary32 values, and add $2^{-54}$ to it. In binary64 the sum rounds back to $1 + 2^{-24}$, and the cast then rounds that tie to its even neighbour, which is 1. But the exact sum lies above the tie, so one rounding gives the neighbour above 1:

```lean
def tie : Model FloatFormat.binary64 := Model.ofNatBits 0x3FF0000010000000
def small : Model FloatFormat.binary64 := Model.ofNatBits 0x3C90000000000000

#eval (Model.cast FloatFormat.binary64 FloatFormat.binary32 (Model.add tie small)).toNatBits
-- 1065353216
#eval (Model.formatOfAddition FloatFormat.binary32 tie small).value.toNatBits
-- 1065353217
```

[[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_formatOfAddition]] proves that finite operands of any two binary formats give the exact sum rounded once to nearest-even, provided the destination is an IEEE descriptor and the result is finite.

### Which sum does `sum` compute?

For the reductions of clause 9.4, the standard allows different association orders and wider intermediate formats. These choices can change the numerical result [@ieee754_2019]. `Model.sum` is the member of that family that adds without error and rounds once. `Model.sumInOrder acc out values` is the loop most programs run: the values are converted to the accumulator format `acc`, added from left to right with one rounding at each addition, and the result is converted to `out`. `Model.sumAlong acc out schedule` does the same along any association order, and `sumAbs`, `sumSquare` and `dot` have the same two forms. Three binary16 values show the difference. In a binary16 accumulator each $1 + 2^{-11}$ is a tie that rounds back to one, and a binary32 accumulator keeps both small terms:

```lean
def reductionOne : Model FloatFormat.binary16 := Model.ofNatBits 0x3C00
def reductionHalf : Model FloatFormat.binary16 := Model.ofNatBits 0x1000

#eval (Model.sumInOrder .binary16 .binary16 [reductionOne, reductionHalf, reductionHalf]).toNatBits
-- 15360
#eval (Model.sumInOrder .binary32 .binary16 [reductionOne, reductionHalf, reductionHalf]).toNatBits
-- 15361
#eval (Model.sum FloatFormat.binary16 #[reductionOne, reductionHalf, reductionHalf]).toNatBits
-- 15361
```

The import `FloatLib.Floats.Formats.BinaryInterchange.Reduction.Schedule.Proof` bounds the error of every member: `Model.abs_toReal_reduceAlong_sub_le` covers every association order, `abs_toReal_reduceAlong_sub_le_depth` bounds it by the depth of the order, which is about $\log_2 n$ for an order that pairs its $n$ terms, and four theorems (`Model.sumInOrder_mixedError` and its siblings) cover the loop for a list of any length, with the source, accumulator and destination formats as parameters. The [`roundoff` command](#/chapter/proving-numerical-bounds) derives these four bounds from the loop definitions.

### Which mathematical functions are correctly rounded?

Clause 9.2 recommends mathematical functions and asks that they be correctly rounded. You get them for every binary format with the import `FloatLib.Floats.Formats.BinaryInterchange.Configured.CorrectlyRounded`: `exp2`, `exp10`, `log2`, `log10` with their `m1` and `p1` forms, the trigonometric functions in radians and in half-turns (`sinPi x` is the sine of π times `x`) with their inverses, the hyperbolic functions with their inverses, `atan2`, `powr`, `pow` and `compound`. Each returns the value with its flags and takes the rounding direction as an optional argument:

```lean standalone
import FloatLib
import FloatLib.Floats.Formats.BinaryInterchange.Configured.CorrectlyRounded

open FloatLib.Floats

def half : Binary64 := 0.5

#eval (ExecFloat.Binary.CorrectlyRounded.sinPi half).value
-- 1
#eval (ExecFloat.Binary.CorrectlyRounded.exp2 half).value
-- 1.4142135623730951
#eval (ExecFloat.Binary.CorrectlyRounded.exp2 half).status.inexact
-- true
#eval (ExecFloat.Binary.CorrectlyRounded.atanh (1 : Binary64)).status.divideByZero
-- true
#eval (ExecFloat.Binary.CorrectlyRounded.exp2 half .up).value
-- 1.4142135623730951
#eval (ExecFloat.Binary.CorrectlyRounded.exp2 half .down).value
-- 1.414213562373095
```

The result is proved correctly rounded in every direction, for every format descriptor: a finite operand in the domain, at which the real function is not zero, gives the real function rounded once in the direction you asked for. The result is the rounding of the real value on the grid of the format when that is in range and the overflow result of the direction otherwise, and in a format with signed zeros it has the sign of the real value ([[FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals.CorrectlyRounded.Function.apply_roundsTo]]). Where the real function is zero, the result is a zero (`Function.isZero_apply`). In a conventional IEEE format the results toward negative and toward positive infinity are then the closest representable values on their side, an infinity included, so they can serve as interval endpoints (`Function.apply_encloses`). That takes the infinities: E4M3 has none, and there $2^{16}$ rounded up is its NaN. The flags are proved as well: `inexact` is raised exactly when a finite result is not the real value (`Function.inexact_apply_iff`), and where the real value is not zero, `overflow` exactly when the rounding with an unbounded exponent range exceeds the largest finite value, which is the rule of clause 7.4 (`Function.overflow_apply_iff`), and `underflow` exactly when the result is inexact and the real value is tiny after rounding in the direction, which is the rule of clause 7.5 with tininess detected after rounding (`Function.underflow_apply_iff`); `invalid` and `divideByZero` stay clear (`Function.invalid_divideByZero_apply`). `pow` has the same theorem for a positive base and for a negative base with an integral exponent, and no search has to settle for it ([[FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals.CorrectlyRounded.pow_roundsTo_of_pos]]). The other functions of clause 9.2 have this form too: `exp`, `expm1`, `log` and `logp1` in `Model.Transcendentals.Directed`, and `rSqrt`, `hypot`, `rootn`, `cbrt` and `pown` in `Model.Algebraic.Directed`, each with its flags and its theorem in every direction. Speed depends on the direction. To nearest-even the functions round an enclosure, which takes about a millisecond for a binary64 result. With directed rounding, and for a result on a rounding boundary, they decide by one exact comparison per bit, at 1 to 200 milliseconds for binary64. Both grow quickly with the width of the format.

The functions take any binary format, so they also run on the eight-bit formats of machine learning. OCP E5M2 is an IEEE format. E4M3 has no infinity: a result beyond its largest value 448 is its NaN when the direction rounds away from zero and 448 otherwise, with `overflow` raised, and the theorem above holds for it as it does for binary64. It holds for the ONNX formats E4M3FNUZ and E5M2FNUZ too, which have one zero: there a negative value that rounds to zero gives that zero.

```lean standalone
import FloatLib
import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals

open FloatLib.Floats.Formats.BinaryInterchange

-- 1.0 in E4M3
def e4m3One : Model FloatFormat.e4m3 := Model.ofNatBits 0x38

#eval (Model.Transcendentals.Directed.exp e4m3One).value.toNatBits
-- 67
#eval (Model.Transcendentals.Directed.exp e4m3One .down).value.toNatBits
-- 66
#eval (Model.Algebraic.Directed.cbrt (Model.ofNatBits 0xD0 : Model FloatFormat.e4m3)).value.toNatBits
-- 192
```

The words 67 and 66 are 2.75 and 2.5, the two neighbours of $e$ in E4M3, and 192 is $-2$, the cube root of $-8$.

Separately, we checked 30 recommended functions against high-precision `mpmath` evaluations rounded to the target format. All 259,720 cases agreed on the value and flags across the five IEEE rounding directions. The [campaign record](https://github.com/lean-dojo/FloatLib/blob/main/tests/results/differential/ieee2019.csv) gives the cases by function. The same script, `tests/oracles/ieee2019.sh`, compares the other functions of clause 9.2 as well, and every encoding of the eight-bit formats E4M3, E5M2, E4M3FNUZ and E5M2FNUZ in the five directions.

For the decimal formats the functions are total too. With the import `FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.CorrectlyRounded.Proof`, `Transcendentals.CorrectlyRounded.exp2 f mode x` and the others return the datum with its flags in each of the five rounding directions, for decimal32, decimal64, decimal128 and every other decimal format, with `atan2`, `atan2Pi` and `pow` among them. Each is proved correctly rounded with its flags ([[FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.CorrectlyRounded.apply_roundsTo]]). The certified functions of `Transcendentals.Certified` return the correctly rounded datum to nearest-even when an enclosure settles the rounding, and `none` otherwise.

### Can the kernel check these operations?

Yes, nearly all of them. `float_decide` rewrites an operation to a computation on the encodings. That covers the arithmetic, the comparisons, the integral roundings, `nextUp`, `nextDown`, `remainder`, the classification, `abs`, `copySign`, `scale`, `logB`, the payload operations, the conversions to integers and to and from character sequences, the formatOf values, the minimum and maximum operations, the augmented operations, the reductions, the scaled products, `pown`, `rootn`, `rSqrt` and `hypot`. For most of them such a check costs a fraction of a millisecond:

```lean
example : (ExecFloat.Binary.compareQuietLess (1 : Binary64) 2).value = true ∧
    ExecFloat.Binary.minimumMagnitude (-1.5 : Binary64) 2.25 = -1.5 ∧
    ExecFloat.Binary.roundToIntegralTiesToEven (2.5 : Binary64) = 2 := by
  float_decide
```

For binary64, `compareQuietLess` takes 115 microseconds with its rule where the operation as written takes 2,233, and `roundToIntegralTiesToEven` 115 where it takes 4,472 ([Figure 5.3](#/chapter/ieee-binary-formats/figure-kernel-ieee2019)). Decimal formats have a kernel form for most of their operations, which take 51 to 3,929 microseconds for decimal64 where the specification takes 149 to 64,016 ([the decimal chapter](#/chapter/decimal-arithmetic/can-leans-kernel-check-a-decimal-computation) has an example). The certified functions of clause 9.2, `exp` to `compound`, have no kernel rule, and the kernel evaluates them as they are defined. The same goes for `pow`, for the forms with flags in every direction, for the formatOf square root, and for the flags of the formatOf operations across formats.

![16 small panels of lines, one per family of operations of the standard: kernel time against format width from 8 to 4,096 bits, with a dashed line and band for the operation as written and a solid line and band for the same operation with the kernel rules.](assets/kernel-ieee2019.png "Kernel time of the operations of IEEE 754-2019 on binary formats, by family and format width, as written and with FloatLib's kernel rules. A line is the median over the operations of a family of the time Lean's kernel takes for one evaluation, at the widths at which every one of them has a time, and the band is their range; where the two lines coincide the family has no kernel rule. Both axes are logarithmic, and lower is faster. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-20).")

### Which names differ?

A few. Addition, subtraction, multiplication and division are `+`, `-`, `*` and `/`, and `negate` is the unary minus. `squareRoot` is `sqrt`, `fusedMultiplyAdd` is `fma`, `scaleB` is `scale`, `convertFormat` is `cast`, `isSignMinus` is `signBit`, and `class` is `classify`, since `class` is a keyword of Lean. FloatLib exposes exception flags as data. Callers can handle them in Lean code. Clause 8 also describes alternate exception-handling attributes, which FloatLib does not implement. And the conformance predicates `is754version1985`, `is754version2008` and `is754version2019` answer `false`, because FloatLib is a library of operations with proofs and doesn't claim that an environment built on it conforms to the standard as a whole.

We used the IEEE working group's notes on the 2019 revision [@ieee754_2019_changes], the C binding in Annex F, Table F.2 [@iso9899_2024], and the C extension for reductions [@iso18661_4] to relate the operation names to the standard. The augmented operations follow Riedy and Demmel [@riedyDemmel2018] and Boldo, Lauter and Muller [@boldoLauterMuller2021], and the decimal minimum and maximum follow the rule of the General Decimal Arithmetic Specification for equal operands [@cowlishawDecarith]. The table groups related operations and gives the corresponding declarations and theorems. A missing entry identifies an operation with no implementation for that format family. Timings for the operations we measured are in the [benchmark results](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/ieee2019/README.md).

<!-- clause map of IEEE 754-2019 -->

| Clause | Operation | Binary formats | Decimal formats | What is proved |
| --- | --- | --- | --- | --- |
| 5.3.1 | `roundToIntegral…` (five directions: `TiesToEven`, `TiesToAway`, `TowardZero`, `TowardPositive`, `TowardNegative`) | `Model.roundToIntegral…`, `ExecFloat.Binary.roundToIntegral…` (generated members of `roundToIntegral`) | `Arithmetic.roundToIntegral…` | binary: `toReal_roundToIntegral`, `exists_int_toReal_roundToIntegral`, `roundToIntegral_overflow_eq_false`; decimal: `roundToIntegral_value`, `roundToIntegral_valid`; kernel rule: binary: the member is unfolded to its family, which had a rule; decimal `KernelPath.roundToIntegral_eq` |
| 5.3.1 | `roundToIntegralExact` | `Model.roundToIntegralExact`, `ExecFloat.Binary.roundToIntegralExact` (`roundToIntegral` with `status := true`) | `Arithmetic.roundToIntegralExact` | binary: `roundToIntegral_status_of_finite`, `roundToIntegral_inexact_iff`; decimal: `roundToIntegralExact_inexact_iff`, `roundToIntegralExact_error_le_half`; kernel rule: binary: the member is unfolded to its family, which had a rule; decimal `KernelPath.roundToIntegralExact_eq` |
| 5.3.1 | `nextUp` | `Model.nextUp`, `ExecFloat.Binary.nextUp` | `Arithmetic.nextUp` | binary: `no_value_between_nextUp`, `nextUp_status_eq`; decimal: `nextUp_adjacent`, `nextUp_quantum_minimal`; kernel rule: binary `Configured.liftUnary_nextUp_eq`, `nextUp_outcome_eq` (`KernelPath.nextUp_eq_spec`), decimal `KernelPath.nextUp_eq` |
| 5.3.1 | `nextDown` | `Model.nextDown`, `ExecFloat.Binary.nextDown` | `Arithmetic.nextDown` | binary: `no_value_between_nextDown`, `nextDown_status_eq`; decimal: `nextDown_adjacent`, `nextDown_quantum_minimal`; kernel rule: binary `Configured.liftUnary_nextDown_eq`, `nextDown_outcome_eq` (`KernelPath.nextDown_eq_spec`), decimal `KernelPath.nextUp_eq` (`nextDown` is unfolded to `nextUp`) |
| 5.3.1 | `remainder` | `Model.remainder`, `ExecFloat.Binary.remainder` | `Arithmetic.remainder` | binary: `remainder_exact`, `abs_toReal_remainder_le`; decimal: `remainder_value`, `remainder_error_le_half_divisor`; kernel rule: binary `Configured.liftBinary_remainder_eq`, `remainder_outcome_eq` (`KernelPath.remainder_eq_spec`, `remainder_status_eq`), decimal `KernelPath.remainder_eq` (`remainderFinite_eq`) |
| 5.3.2 | `quantize` | not applicable (decimal only) | `Arithmetic.quantize` | `quantize_same_quantum`, `quantize_error_le_half`, `quantize_inexact_iff`; kernel rule: decimal `KernelPath.quantize_eq` |
| 5.3.2 | `quantum` | not applicable (decimal only) | `Arithmetic.quantum` | `sameQuantum_quantum`, `toRat?_quantum` |
| 5.3.3 | `scaleB` | `Model.scale`, `ExecFloat.Binary.scale` | `Arithmetic.scale` | binary: `toReal_scale_eq_roundAt`, `toReal_scale_exact`; decimal: `scale_exact_value`, `scale_inexact_iff`; kernel rule: binary `Configured.liftUnary_scale_eq` (`KernelPath.scale_eq_spec`), decimal `KernelPath.scale_eq` |
| 5.3.3 | `logB` | `Model.logB`, `Model.logBInt`, `ExecFloat.Binary.logB` | `Arithmetic.logB` | binary: `logBInt_of_finite_nonzero`, `logBInt_bounds`, `logB_status_of_zero`; decimal: `logB_finite`, `logB_bounds`; kernel rule: binary `Configured.liftUnary_logB_eq` (`KernelPath.logB_eq_spec`), decimal `KernelPath.logB_eq` |
| 5.4.1 | `addition` | `Model.add`, `x + y` on `ExecFloat.Binary` (a Lean operator) | `Arithmetic.add`, kernel path `KernelPath.add` | binary: `toReal_add_eq_roundAt`, `add_invalid`; decimal: `add_error_le_half`, `add_inexact_iff`, `KernelPath.add_eq` |
| 5.4.1 | `subtraction` | `Model.sub`, `x - y` on `ExecFloat.Binary` (a Lean operator) | `Arithmetic.sub`, kernel path `KernelPath.sub` | binary: `toReal_sub_eq_roundAt`, `add_invalid`; decimal: `sub_error_le_half`, `sub_inexact_iff`, `KernelPath.sub_eq` |
| 5.4.1 | `multiplication` | `Model.mul`, `x * y` on `ExecFloat.Binary` (a Lean operator) | `Arithmetic.mul`, kernel path `KernelPath.mul` | binary: `toReal_mul_eq_roundAt`, `mul_invalid`; decimal: `mul_error_le_half`, `mul_inexact_iff`, `KernelPath.mul_eq` |
| 5.4.1 | `division` | `Model.div`, `x / y` on `ExecFloat.Binary` (a Lean operator) | `Arithmetic.div` | binary: `toReal_div_eq_roundAt`, `div_invalid`; decimal: `div_error_le_half`, `div_inexact_iff`; kernel rule: decimal `KernelPath.div_eq` (`projectRatio_eq`) |
| 5.4.1 | `squareRoot` | `Model.sqrt`, `ExecFloat.sqrt` | `Arithmetic.sqrt` | binary: `toReal_sqrt_eq_roundAt`, `isFinite_sqrt_of_isFinite`; decimal: `sqrt_valid`, `sqrt_quantum_closest`; kernel rule: decimal `KernelPath.sqrt_eq` (`sqrtRatio_eq`) |
| 5.4.1 | `fusedMultiplyAdd` | `Model.fma`, `ExecFloat.fma` | `Arithmetic.fma` | binary: `toReal_fma_eq_roundAt`; decimal: `fma_error_le_half`, `fma_inexact_iff`; kernel rule: decimal `KernelPath.fma_eq` |
| 5.4.1 | `convertFromInt` | `ExecDType.convertFromInt` | `Conversion.Integer.convertFromInt` | binary: `value_convertFromInt`, `convertFromInt_nearest_eq_round`; decimal: `convertFromInt_exact`, `convertFromInt_error_le_half`; kernel rule: binary `Configured.convertFromInt_eq` (`KernelPath.Value.ofInteger_eq_lift`), decimal `KernelPath.convertFromInt_eq` |
| 5.4.1 | `convertToInteger…` (five directions) | `ExecDType.convertToInteger…` (generated member of `convertToInteger`), `ExecFloat.Binary.convertToInteger…` (member of `toInt?`) | `Conversion.Integer.convertToInteger…` | binary: `convertToInteger_of_convertToIntegerExact_eq_success`, `convertToInteger_of_convertToIntegerExact_eq_failure`; decimal: `convertToInteger_exact`, `convertToInteger_error_le_half`; kernel rule: binary: the member is unfolded to its family, which had a rule; decimal `KernelPath.convertToInteger_eq` |
| 5.4.1 | `convertToIntegerExact…` (five directions) | `ExecDType.convertToIntegerExact…` (generated member of `convertToIntegerExact`) | `Conversion.Integer.convertToIntegerExact…` | binary: `convertToIntegerExact_of_exactValue_eq_finite_of_inRange`, `toInt_of_convertToIntegerExact_finite`; decimal: `convertToInteger_exact`; kernel rule: binary `Configured.convertToIntegerExact_eq` (`KernelPath.convertToIntegerExact_eq_spec`), decimal `KernelPath.convertToInteger_eq` |
| 5.4.1 (formatOf) | formatOf-addition, -subtraction, -multiplication, -division, -fusedMultiplyAdd (operands and result in different formats) | `Model.formatOfAddition`, `formatOfSubtraction`, `formatOfMultiplication`, `formatOfDivision`, `formatOfFusedMultiplyAdd` (any three formats, six directions, NaNs, infinities, flags); `ExecFloat.Mixed.add`, `sub`, `mul`, `div`, `fma` (any two families, finite operands only) | `Arithmetic.add`, `sub`, `mul`, `div`, `fma` (a `Datum` carries no format: operands of any formats, one rounding into the format argument) | binary: `toReal_formatOfAddition` and its four siblings (nearest-even, finite operands: one rounding of the exact result), `formatOfAddition_finite_roundAt` and its siblings for subtraction, multiplication and fusedMultiplyAdd (every direction, an exact result in the range of the destination), `formatOfAddition_of_toDyadic?_eq_some` and its siblings (every direction), `formatOfAddition_eq_add` and its four siblings (in one format the whole outcome, value, flags and ternary value, is that of `add`, `sub`, `mul`, `div`, `fma` in the same direction, for every operand, NaNs and infinities included, and every descriptor); decimal: `add_error_le_half` and its siblings; kernel rule: binary `Configured.formatOfAddition_eq` and its four siblings (`KernelPath.formatOfAddition_eq_spec` and its siblings, every direction) |
| 5.4.1 (formatOf) | formatOf-squareRoot | `Model.formatOfSquareRoot` (any two formats, six directions, NaNs, infinities, flags and ternary value) | `Arithmetic.sqrt` (operands of any formats) | binary: `formatOfSquareRoot_roundsTo` (correctly rounded in every direction for a finite positive operand of any format and a destination with signed zeros, overflow result included), `formatOfSquareRoot_inexact_iff`, `formatOfSquareRoot_of_isZero`, `formatOfSquareRoot_of_isNaN`, `formatOfSquareRoot_of_isInfinite`, `formatOfSquareRoot_of_negative`, `formatOfSquareRoot_eq_sqrt` (in one format the outcome at a NaN, a zero, an infinity and a negative number is that of `Model.sqrt`), `formatOfSquareRoot_value_eq_sqrt` (in one IEEE format the value to nearest-even is `Model.sqrt`); decimal: see squareRoot |
| 5.4.1 (formatOf) | formatOf-convertFromInt | `ExecDType.convertFromInt` (any destination) | `Conversion.Integer.convertFromInt` | see convertFromInt |
| 5.4.2 | `convertFormat` | `Model.cast` | `Conversion.convertFormat` | binary: `cast_eq_roundAt`, `cast_exact_of_gridExtension`; decimal: `convertFormat_error_le_half`, `convertFormat_exact`; kernel rule: decimal `KernelPath.convertFormat_eq` |
| 5.4.2 | `convertFromDecimalCharacter` | `Model.parse`, `ExecFloat.Binary.parse` | `Formatting.parse` | binary: `toReal_parse_decimal_nearest`, `parse_format_of_isFinite`; decimal: `parse_error_le_half`, `parse_formatExact`; kernel rule: binary `Configured.parse_eq` (`KernelPath.parseCharacters_eq`, `decimalWord_eq`), decimal `KernelPath.parse_eq` |
| 5.4.2 | `convertToDecimalCharacter` | `Model.format`, `ExecFloat.Binary.format` | `Formatting.formatExact`, `Formatting.format` | binary: `parse_format_of_isFinite`, `format_status`; decimal: `formatExact_injective`, `parse_formatExact`; kernel rule: binary `Configured.format_eq` (`KernelPath.ofList_formatCharacters`), decimal `KernelPath.formatExact_eq` |
| 5.4.3 | `convertFromHexCharacter` | `Model.parse` (hexadecimal text) | not applicable (binary only) | `parse_format_hex_of_isFinite`; kernel rule: binary `Configured.parse_eq` (`KernelPath.parseCharacters_eq`) |
| 5.4.3 | `convertToHexCharacter` | `Model.format` with `.hex` | not applicable (binary only) | `parse_format_hex_of_isFinite`; kernel rule: binary `Configured.format_eq` (`KernelPath.ofList_formatCharacters`) |
| 5.5.1 | `copy` | `Model.copy`, `ExecFloat.Binary.copy` | `Datum.copy` | definitional (`copy x = x`) |
| 5.5.1 | `negate` | `Model.neg`, `-x` (a Lean operator) | `Datum.negate` | decimal: `negate_negate`, `negate_valid` |
| 5.5.1 | `abs` | `Model.abs`, `ExecFloat.Binary.abs` | `Datum.abs` | decimal: `finiteValue_abs`; kernel rule: binary `Configured.liftUnary_abs_eq` (`KernelPath.abs_eq_spec`) |
| 5.5.1 | `copySign` | `Model.copySign`, `ExecFloat.Binary.copySign` | `Datum.copySign` | decimal: `decode_copySign`; kernel rule: binary `Configured.liftBinary_copySign_eq` (`KernelPath.copySign_eq_spec`) |
| 5.5.2 | `encodeDecimal` | not applicable (decimal only) | `encodeDecimal` (`Encoding.encode?` at `.dpd`) | `decodeDecimal_of_encodeDecimal_eq_some`, `decode_transcode`; kernel rule: `KernelPath.encodeDecimal_eq` (`KernelPath.encode?_eq`) |
| 5.5.2 | `decodeDecimal` | not applicable (decimal only) | `decodeDecimal` (`Encoding.decode` at `.dpd`) | `decodeDecimal_of_encodeDecimal_eq_some`, `decode_transcode`; kernel rule: `KernelPath.decodeDecimal_eq` (`KernelPath.decode_eq`) |
| 5.5.2 | `encodeBinary` | not applicable (decimal only) | `encodeBinary` (`Encoding.encode?` at `.bid`) | `decodeBinary_of_encodeBinary_eq_some`, `decode_transcode`; kernel rule: `KernelPath.encodeBinary_eq` (`KernelPath.encode?_eq`) |
| 5.5.2 | `decodeBinary` | not applicable (decimal only) | `decodeBinary` (`Encoding.decode` at `.bid`) | `decodeBinary_of_encodeBinary_eq_some`, `decode_transcode`; kernel rule: `KernelPath.decodeBinary_eq` (`KernelPath.decode_eq`) |
| 5.6.1, 5.11 | `compareQuiet…` (twelve predicates: `Equal`, `NotEqual`, `Greater`, `GreaterEqual`, `Less`, `LessEqual`, `Unordered`, `Ordered`, `LessUnordered`, `NotGreater`, `NotLess`, `GreaterUnordered`) | `Model.compareQuiet…`, `ExecFloat.Binary.compareQuiet…` (generated members of `compareQuiet`) | `Datum.compareQuiet…` (generated member of `Datum.compareQuiet`) | binary: `compareQuiet_value_of_toEReal?`, `compareQuiet_invalid_iff`; decimal: `compareQuiet_invalid_iff`, `compareQuiet_value_iff`; kernel rule: binary `Configured.compareQuiet_eq`, decimal `KernelPath.compareQuiet_eq` |
| 5.6.1, 5.11 | `compareSignaling…` (ten predicates: the twelve without `Unordered` and `Ordered`) | `Model.compareSignaling…`, `ExecFloat.Binary.compareSignaling…` (generated members of `compareSignaling`) | `Datum.compareSignaling…` (generated member of `Datum.compareSignaling`) | binary: `compareSignaling_value_of_toEReal?`, `compareSignaling_invalid_iff`; decimal: `compareSignaling_invalid_iff`, `compareQuiet_value_iff`; kernel rule: binary `Configured.compareSignaling_eq`, decimal `KernelPath.compareSignaling_eq` |
| 5.7.1 | `is754version…` (`1985`, `2008`, `2019`) | `IEEE754.is754version…` (`false`: no conformance claim) | the same declaration | definitional (`conformsTo`) |
| 5.7.2 | `class` | `Model.classify`, `ExecFloat.Binary.classify` (`class` is a keyword of Lean) | `Datum.classify` | binary: `classify_eq_match_exactValue`; decimal: `classify_normal_iff`, `classify_zero_iff`; kernel rule: binary `Configured.classify_eq` (`KernelPath.classOf_eq`), decimal `KernelPath.classify_eq` |
| 5.7.2 | `isSignMinus` | `Model.signBit`, `ExecFloat.Binary.signBit` | `Datum.isSignMinus` | decimal: `isSignMinus_withSign` |
| 5.7.2 | `isNormal` | `Model.isNormal`, `ExecFloat.Binary.isNormal` | `Datum.isNormal` | decimal: `isNormal_iff`; kernel rule: binary `Configured.isNormal_eq`, decimal `KernelPath.isNormal_eq` |
| 5.7.2 | `isFinite` | `Model.isFinite`, `ExecFloat.Binary.isFinite` | `Datum.isFinite` | binary: `isFinite_of_isFinite_add` |
| 5.7.2 | `isZero` | `Model.isZero`, `ExecFloat.Binary.isZero` | `Datum.isZero` | decimal: `isZero_iff` |
| 5.7.2 | `isSubnormal` | `Model.isSubnormal`, `ExecFloat.Binary.isSubnormal` | `Datum.isSubnormal` | decimal: `isSubnormal_iff`; kernel rule: binary `Configured.isSubnormal_eq`, decimal `KernelPath.isSubnormal_eq` |
| 5.7.2 | `isInfinite` | `Model.isInfinite`, `ExecFloat.Binary.isInfinite` | `Datum.isInfinite` | binary: `nextUp_of_isInfinite_of_signBit_eq_false` |
| 5.7.2 | `isNaN` | `Model.isNaN`, `ExecFloat.Binary.isNaN` | `Datum.isNaN` | binary: `compare_eq_none_iff`; decimal: `numericValue?_eq_none_iff` |
| 5.7.2 | `isSignaling` | `Model.isSignaling`, `ExecFloat.Binary.isSignaling` | `Datum.isSignaling` | binary: `compareQuiet_invalid_iff`; decimal: `withSign_isSignaling`; kernel rule: binary `Configured.isSignaling_eq` |
| 5.7.2 | `isCanonical` | `Model.isCanonical`, `ExecFloat.Binary.isCanonical` | `Encoding.isCanonical` | decimal: `isCanonical_canonicalize` |
| 5.7.2 | `radix` | `Model.radix`, `ExecFloat.Binary.radix` | `Datum.radix` | definitional |
| 5.7.2, 5.10 | `totalOrder` | `Model.totalOrder`, `ExecFloat.Binary.totalOrder` | `Datum.totalOrder` | binary: `totalOrder_total`, `totalOrder_trans`, `totalOrder_antisymm`; decimal: `totalOrder_total`, `totalOrder_antisymm_iff`; kernel rule: decimal `KernelPath.totalOrder_eq` |
| 5.7.2, 5.10 | `totalOrderMag` | `Model.totalOrderMag`, `ExecFloat.Binary.totalOrderMag` | `Datum.totalOrderMag` | binary: `totalOrderMag_trans`; decimal: `totalOrderMag_total`, `totalOrderMag_antisymm_iff`; kernel rule: binary `Configured.totalOrderMag_eq`, decimal `KernelPath.totalOrder_eq` |
| 5.7.3 | `sameQuantum` | not applicable (decimal only) | `Datum.sameQuantum` | `sameQuantum_comm`, `sameQuantum_trans`, `quantize_same_quantum` |
| 5.7.4 | `lowerFlags` | `Numerics.IEEEStatus.lowerFlags` | `Numerics.IEEEStatus.lowerFlags`, `Environment.lowerFlags` | definitional on the record of five flags |
| 5.7.4 | `raiseFlags` | `Numerics.IEEEStatus.raiseFlags` | `Numerics.IEEEStatus.raiseFlags`, `Environment.raiseFlags` | definitional on the record of five flags |
| 5.7.4 | `testFlags` | `Numerics.IEEEStatus.testFlags` | `Numerics.IEEEStatus.testFlags`, `Environment.testFlags` | definitional on the record of five flags |
| 5.7.4 | `testSavedFlags` | `Numerics.IEEEStatus.testSavedFlags` | `Numerics.IEEEStatus.testSavedFlags` | definitional on the record of five flags |
| 5.7.4 | `restoreFlags` | `Numerics.IEEEStatus.restoreFlags` | `Numerics.IEEEStatus.restoreFlags`, `Environment.restoreFlags` | definitional on the record of five flags |
| 5.7.4 | `saveAllFlags` | `Numerics.IEEEStatus.saveAllFlags` | `Numerics.IEEEStatus.saveAllFlags`, `Environment.saveAllFlags` | definitional on the record of five flags |
| 7.2 to 7.6 | invalid, divideByZero, overflow, underflow, inexact (default handling) | `IEEEOutcome` (for operations supporting `status := true`), `Numerics.IEEEStatus` | `Outcome` | binary: `add_invalid`, `div_divideByZero`, `dyadicRoundingStatus_overflow`, `dyadicRoundingStatus_inexact_of_underflow`; decimal: `add_inexact_iff`, `scale_underflow_iff` |
| 8 | alternate exception handling attributes | none: an operation returns its flags as a value, and a caller handles them in ordinary code (`IEEEOutcome.bind`) | none (`Environment.accept`) | none |
| 9.2 | `exp` | `Model.Transcendentals.Directed.exp` (value and flags, every rounding direction); `ExecFloat.Binary.CorrectlyRounded.exp`, `Model.Transcendentals.CorrectlyRounded.exp`: an enclosure search, then exact comparisons; nearest-even, value only | `Transcendentals.CorrectlyRounded.exp` (every operand, value and flags, five directions); `Transcendentals.Certified.exp` (a result when an enclosure settles) | binary: `Directed.exp_roundsTo` (correctly rounded in every direction for every finite operand, overflow result included, every format descriptor), `Directed.exp_inexact_iff`, `Directed.exp_overflow_iff` (`overflow` exactly when the rounding with an unbounded exponent range exceeds the largest finite value), `exp_correctlyRoundedCertificateOn`, `toReal_exp_eq_roundAt`; decimal: `CorrectlyRounded.exp_roundsTo` (value and flags in five directions, every format), `toReal_of_exp_eq_some` |
| 9.2 | `expm1` | `Model.Transcendentals.Directed.expm1` (value and flags, every rounding direction); `ExecFloat.Binary.CorrectlyRounded.expm1`, `Model.Transcendentals.CorrectlyRounded.expm1`: an enclosure search, then exact comparisons; nearest-even, value only | `Transcendentals.CorrectlyRounded.expm1` (every operand, value and flags, five directions); `Transcendentals.Certified.expm1` (a result when the certified search settles) | binary: `Directed.expm1_roundsTo` (correctly rounded in every direction for every finite nonzero operand, every format descriptor), `Directed.expm1_inexact_iff`, `Directed.expm1_overflow_iff`, `expm1_correctlyRoundedCertificateOn`, `expm1_eq_of_certified_expm1_eq_ok`; decimal: `CorrectlyRounded.expm1_roundsTo` |
| 9.2 | `log` | `Model.Transcendentals.Directed.log` (value and flags, every rounding direction); `ExecFloat.Binary.CorrectlyRounded.log`, `Model.Transcendentals.CorrectlyRounded.log`: an enclosure search, then exact comparisons; nearest-even, value only | `Transcendentals.CorrectlyRounded.log` (every operand, value and flags, five directions); `Transcendentals.Certified.log` (a result when an enclosure settles) | binary: `Directed.log_roundsTo` (correctly rounded in every direction for every finite positive operand other than one, every format descriptor), `Directed.log_inexact_iff`, `Directed.log_overflow_iff`, `log_correctlyRoundedCertificateOn`, `log_eq_of_certified_log_eq_ok`; decimal: `CorrectlyRounded.log_roundsTo`, `toReal_of_log_eq_some` |
| 9.2 | `logp1` | `Model.Transcendentals.Directed.logp1` (value and flags, every rounding direction); `ExecFloat.Binary.CorrectlyRounded.logp1`, `Model.Transcendentals.CorrectlyRounded.logp1`: an enclosure search, then exact comparisons; nearest-even, value only | `Transcendentals.CorrectlyRounded.logp1` (every operand, value and flags, five directions); `Transcendentals.Certified.logp1` (a result when the certified search settles) | binary: `Directed.logp1_roundsTo` (correctly rounded in every direction for every finite nonzero operand above -1, every format descriptor), `Directed.logp1_inexact_iff`, `Directed.logp1_overflow_iff`, `logp1_correctlyRoundedCertificateOn`, `logp1_eq_of_certified_logp1_eq_ok`; decimal: `CorrectlyRounded.logp1_roundsTo` |
| 9.2 | `rSqrt` | `Model.Algebraic.Directed.rSqrt` (value and flags, every rounding direction); `Model.rSqrt`, `ExecFloat.Binary.rSqrt`: one rounding of the exact value to nearest-even | `Arithmetic.rSqrt` (five directions) | binary: `Algebraic.Directed.rSqrt_roundsTo` (correctly rounded in every direction, every format descriptor), `rSqrt_inexact_iff`, `rSqrt_overflow_iff`, `toReal_rSqrt_eq_roundAt`, `rSqrt_of_isZero`; decimal: `rSqrt_error_le_half`; kernel rule: binary `Configured.liftUnary_rSqrt_eq` (`KernelPath.rSqrt_eq_spec`, `rootRatio_eq`), decimal `KernelPath.rSqrt_eq` (`sqrtRatio_eq`) |
| 9.2 | `hypot` | `Model.Algebraic.Directed.hypot` (value and flags, every rounding direction); `Model.hypot`, `ExecFloat.Binary.hypot`: one rounding of the exact value to nearest-even | `Arithmetic.hypot` (five directions) | binary: `Algebraic.Directed.hypot_roundsTo` (correctly rounded in every direction, every format descriptor), `hypot_inexact_iff`, `hypot_overflow_iff`, `toReal_hypot_eq_roundAt`; decimal: `hypot_error_le_half`, `hypot_inexact_iff`; kernel rule: binary `Configured.liftBinary_hypot_eq` (`KernelPath.hypot_eq_spec`, `sqrtDyadic_eq`), decimal `KernelPath.hypot_eq` (`sqrtRatio_eq`) |
| 9.2 | `pown` | `Model.Algebraic.Directed.pown` (value and flags, every rounding direction); `Model.pown`, `ExecFloat.Binary.pown`: one rounding of the exact value to nearest-even | `Arithmetic.pown` (five directions) | binary: `Algebraic.Directed.pown_roundsTo` (correctly rounded in every direction, every format descriptor), `pown_inexact_iff`, `pown_overflow_iff`, `toReal_pown_eq_roundAt`, `pown_of_isSignaling`; decimal: `pown_error_le_half`; kernel rule: binary `Configured.liftUnary_pown_eq` (`KernelPath.pown_eq_spec`), decimal `KernelPath.pown_eq` (`project_eq`, `projectRatio_eq`) |
| 9.2 | `rootn` | `Model.Algebraic.Directed.rootn` and its degree three `cbrt` (value and flags, every rounding direction); `Model.rootn`, `ExecFloat.Binary.rootn`: one rounding of the exact value to nearest-even | `Arithmetic.rootn` (five directions) | binary: `Algebraic.Directed.rootn_roundsTo_of_pos`, `rootn_roundsTo_of_neg` (correctly rounded in every direction, every format descriptor), `rootn_overflow_iff_of_pos`, `rootn_overflow_iff_of_neg`, `toReal_rootn_eq_roundAt`, `rootn_of_isNaN`; decimal: `rootn_error_le_half`, `rootn_inexact_iff`; kernel rule: binary `Configured.liftUnary_rootn_eq` (`KernelPath.rootn_eq_spec`, `rootRatio_eq`), decimal `KernelPath.rootn_eq` (`rootRatio_eq`) |
| 9.2 | `pow` | `CorrectlyRounded.pow` in `Model.Transcendentals` and `ExecFloat.Binary` (every operand, value and flags, every rounding direction, the special cases of §9.2.1); `Model.pow`, `ExecFloat.Binary.Certified.pow` | `Transcendentals.CorrectlyRounded.pow` (every operand, value and flags, five directions) | binary: `pow_roundsTo_of_pos` (a finite positive base and a finite exponent), `pow_roundsTo_of_neg` (a finite negative base and an integral exponent): correctly rounded in every direction, overflow result included, every format descriptor, with no search that has to settle; `pow_overflow_iff_of_pos`, `pow_overflow_iff_of_neg`; `toReal_pow_of_eq_intCast`; `Certified.pow` returns the correctly rounded value or a failure. Decimal: `CorrectlyRounded.pow_roundsTo_of_pos`, `pow_roundsTo_of_neg` |
| 9.2 | `exp2`, `exp2m1`, `exp10`, `exp10m1`, `log2`, `log10`, `log2p1`, `log10p1`, `sin`, `cos`, `tan`, `sinPi`, `cosPi`, `tanPi`, `asin`, `acos`, `atan`, `asinPi`, `acosPi`, `atanPi`, `sinh`, `cosh`, `tanh`, `asinh`, `acosh`, `atanh` | `CorrectlyRounded.<name>` in `Model.Transcendentals` and `ExecFloat.Binary` (value and flags, every rounding direction; an enclosure to nearest-even, exact comparisons otherwise) | `Transcendentals.CorrectlyRounded.<name>` (every operand, value and flags, five directions); `Transcendentals.Certified.<name>` (a result when an enclosure settles, nearest-even, no flags) | binary: `Function.apply_roundsTo` (correctly rounded in every rounding direction for finite operands in the domain, overflow result and sign included, every format descriptor), `Function.toReal_apply`, `Function.overflow_apply_iff` (`overflow` exactly when the rounding with an unbounded exponent range exceeds the largest finite value), `Function.inexact_apply_iff` (every direction), `Function.isZero_apply`. Decimal: `CorrectlyRounded.apply_roundsTo` (value and flags in five directions for every finite operand in the domain, every format), `toReal_of_apply_eq_some` |
| 9.2 | `atan2` | `CorrectlyRounded.atan2` in `Model.Transcendentals` and `ExecFloat.Binary` (value and flags, every rounding direction; an enclosure to nearest-even, exact comparisons otherwise) | `Transcendentals.CorrectlyRounded.atan2` (every operand, value and flags, five directions) | binary: `atan2_roundsTo` (correctly rounded in every direction at finite operands with a nonzero `y`, every format descriptor), `atan2_overflow_iff`, `toReal_atan2`; decimal: `CorrectlyRounded.atan2_roundsTo` |
| 9.2 | `atan2Pi` | `CorrectlyRounded.atan2Pi` in `Model.Transcendentals` and `ExecFloat.Binary` (value and flags, every rounding direction; an enclosure to nearest-even, exact comparisons otherwise) | `Transcendentals.CorrectlyRounded.atan2Pi` (every operand, value and flags, five directions) | binary: `atan2Pi_roundsTo` (correctly rounded in every direction at finite operands with a nonzero `y`, every format descriptor), `toReal_atan2Pi`; decimal: `CorrectlyRounded.atan2Pi_roundsTo` |
| 9.2 | `powr` | `CorrectlyRounded.powr` in `Model.Transcendentals` and `ExecFloat.Binary` (value and flags, every rounding direction; an enclosure to nearest-even, exact comparisons otherwise) | `Transcendentals.CorrectlyRounded.powr` (every operand, value and flags, five directions); `Transcendentals.Certified.powr` (a result when an enclosure settles) | binary: `powr_roundsTo` (correctly rounded in every direction at finite operands with a positive base, every format descriptor), `powr_overflow_iff`, `toReal_powr`; decimal: `CorrectlyRounded.powr_roundsTo`, `toReal_of_powr_eq_some` |
| 9.2 | `compound` | `CorrectlyRounded.compound` in `Model.Transcendentals` and `ExecFloat.Binary` (value and flags, every rounding direction; an enclosure to nearest-even, exact comparisons otherwise) | `Transcendentals.CorrectlyRounded.compound` (every operand, value and flags, five directions); `Transcendentals.Certified.compound` (a result when an enclosure settles) | binary: `compound_roundsTo` (correctly rounded in every direction at finite operands above -1, every format descriptor), `compound_overflow_iff`, `toReal_compound`; decimal: `CorrectlyRounded.compound_roundsTo`, `toReal_of_compound_eq_some` |
| 9.3 | `getBinaryRoundingDirection` | `IEEE754.Modes.getBinaryRoundingDirection` | the same declaration | `getBinaryRoundingDirection_setBinaryRoundingDirection` |
| 9.3 | `setBinaryRoundingDirection` | `IEEE754.Modes.setBinaryRoundingDirection` | the same declaration | `getBinaryRoundingDirection_setBinaryRoundingDirection`, `getDecimalRoundingDirection_setBinaryRoundingDirection` |
| 9.3 | `getDecimalRoundingDirection` | `IEEE754.Modes.getDecimalRoundingDirection` | the same declaration | `getDecimalRoundingDirection_setDecimalRoundingDirection` |
| 9.3 | `setDecimalRoundingDirection` | `IEEE754.Modes.setDecimalRoundingDirection` | the same declaration | `getDecimalRoundingDirection_setDecimalRoundingDirection`, `getBinaryRoundingDirection_setDecimalRoundingDirection` |
| 9.3 | `saveModes` | `IEEE754.Modes.saveModes` | the same declaration | `restoreModes_saveModes` |
| 9.3 | `restoreModes` | `IEEE754.Modes.restoreModes` | the same declaration | `restoreModes_saveModes` |
| 9.3 | `defaultModes` | `IEEE754.Modes.defaultModes` | the same declaration | `getBinaryRoundingDirection_defaultModes`, `getDecimalRoundingDirection_defaultModes` |
| 9.4 | `sum` | `Model.sum`, `ExecFloat.Binary.sum` | `Arithmetic.sum` | binary: `sum_status_value_toReal_eq_roundAt_of_finite`, `sum_status_eq_zero_of_finite`; decimal: `sum_eq_project` (one rounding of the exact sum, five directions), `sum_error_le_half`, `sum_inexact_iff`, `sum_valid`; kernel rule: binary `Configured.sum_eq` (`KernelPath.sum_eq_spec`), decimal `KernelPath.sum_eq` (`sumLoop_eq`, `deliverSum_eq`) |
| 9.4 | `dot` | `Model.dot`, `ExecFloat.Binary.dot` | `Arithmetic.dot` | binary: `dot_status_value_toReal_eq_roundAt_of_finite`; decimal: `dot_eq_project`; kernel rule: binary `Configured.dot_eq` (`KernelPath.dot_eq_spec`), decimal `KernelPath.dot_eq` (`sumLoop_eq`, `deliverSum_eq`) |
| 9.4 | `sumSquare` | `Model.sumSquare`, `ExecFloat.Binary.sumSquare` | `Arithmetic.sumSquare` | binary: `toReal_sumSquare`, `sumSquare_status_of_decidingInfinity?`, `toModel_sumSquare`; decimal: `sumSquare_eq_project`, `sumSquare_valid`; kernel rule: binary `Configured.sumSquare_eq` (`KernelPath.sumSquare_eq_spec`), decimal `KernelPath.sumSquare_eq` (`sumLoop_eq`, `deliverSum_eq`) |
| 9.4 | `sumAbs` | `Model.sumAbs`, `ExecFloat.Binary.sumAbs` | `Arithmetic.sumAbs` | binary: `toReal_sumAbs`, `sumAbs_status_of_decidingInfinity?`, `toModel_sumAbs`; decimal: `sumAbs_eq_project`, `sumAbs_valid`; kernel rule: binary `Configured.sumAbs_eq` (`KernelPath.sumAbs_eq_spec`), decimal `KernelPath.sumAbs_eq` (`sumLoop_eq`, `deliverSum_eq`) |
| 9.4 | `scaledProd` | `Model.scaledProd`, `ExecFloat.Binary.scaledProd` | `Arithmetic.scaledProd` (five directions, `pr × 10 ^ sf`) | binary: `toReal_scaledProd_product` (one rounding of the scaled exact product, of magnitude in [1, 2)), `mixedError_scaledProd`; decimal: `scaledProd_eq_project` (one rounding of the exact product scaled by the power of ten of its leading digit, of magnitude in [1, 10)), `scaledProd_inexact_iff`, `scaledProd_status` (no overflow or underflow), `scaledProd_valid`; kernel rule: binary `Configured.scaledProd_eq` (`KernelPath.scaledProd_eq_spec`) |
| 9.4 | `scaledProdSum` | `Model.scaledProdSum`, `ExecFloat.Binary.scaledProdSum` | `Arithmetic.scaledProdSum` (five directions) | binary: `toReal_scaledProdOfSums_product`, `map_toModel_scaledProdSum`; decimal: `scaledProdSum_eq_project`, `scaledProdSum_valid`; kernel rule: binary `Configured.scaledProdSum_eq` (`KernelPath.scaledProdOfSums_eq_spec`) |
| 9.4 | `scaledProdDiff` | `Model.scaledProdDiff`, `ExecFloat.Binary.scaledProdDiff` | `Arithmetic.scaledProdDiff` (five directions) | binary: `toReal_scaledProdOfSums_product`, `map_toModel_scaledProdDiff`; decimal: `scaledProdDiff_eq_project`, `scaledProdDiff_valid`; kernel rule: binary `Configured.scaledProdDiff_eq` (`KernelPath.scaledProdOfSums_eq_spec`) |
| 9.4 | sum, from left to right in an accumulator format | `Model.sumInOrder` (`reduceInOrder` at the term of `sum`) | `Arithmetic.reduceInOrder` at `Reduction.sumTerm` (five directions, the flags of every step) | binary: `sumInOrder_mixedError` (generated by `roundoff`: mixed error against the exact real reduction, any length, any source, accumulator and destination descriptors with the accumulator grid containing the source grid), `reduceInOrder_eq_reduceAlong`; decimal: `reduceInOrder_eq_reduceAlong`, `reduceInOrder_valid`; kernel rule: binary `KernelPath.toNatBits_reduceInOrder` (`foldAdd_eq`) |
| 9.4 | sumAbs, from left to right in an accumulator format | `Model.sumAbsInOrder` (`reduceInOrder` at the term of `sumAbs`) | `Arithmetic.reduceInOrder` at `Reduction.sumAbsTerm` (five directions, the flags of every step) | binary: `sumAbsInOrder_mixedError` (generated by `roundoff`: mixed error against the exact real reduction, any length, any source, accumulator and destination descriptors with the accumulator grid containing the source grid), `reduceInOrder_eq_reduceAlong`; decimal: `reduceInOrder_eq_reduceAlong`, `reduceInOrder_valid`; kernel rule: binary `KernelPath.toNatBits_reduceInOrder` (`foldAdd_eq`) |
| 9.4 | sumSquare, from left to right in an accumulator format | `Model.sumSquareInOrder` (`reduceInOrder` at the term of `sumSquare`) | `Arithmetic.reduceInOrder` at `Reduction.sumSquareTerm` (five directions, the flags of every step) | binary: `sumSquareInOrder_mixedError` (generated by `roundoff`: mixed error against the exact real reduction, any length, any source, accumulator and destination descriptors with the accumulator grid containing the source grid), `reduceInOrder_eq_reduceAlong`; decimal: `reduceInOrder_eq_reduceAlong`, `reduceInOrder_valid`; kernel rule: binary `KernelPath.toNatBits_reduceInOrder` (`foldAdd_eq`) |
| 9.4 | dot, from left to right in an accumulator format | `Model.dotInOrder` (`reduceInOrder` at the term of `dot`) | `Arithmetic.reduceInOrder` at `Reduction.dotTerm` (five directions, the flags of every step) | binary: `dotInOrder_mixedError` (generated by `roundoff`: mixed error against the exact real reduction, any length, any source, accumulator and destination descriptors with the accumulator grid containing the source grid), `reduceInOrder_eq_reduceAlong`; decimal: `reduceInOrder_eq_reduceAlong`, `reduceInOrder_valid`; kernel rule: binary `KernelPath.toNatBits_reduceInOrder` (`foldAdd_eq`) |
| 9.4 | sum, sumAbs, sumSquare, dot in any association order and accumulator format | `Model.reduceAlong`, `Model.sumAlong`, `Model.sumAbsAlong`, `Model.sumSquareAlong`, `Model.dotAlong` | `Arithmetic.reduceAlong` at `Reduction.sumTerm`, `sumAbsTerm`, `sumSquareTerm`, `dotTerm` (five directions, the flags of every step) | binary: `abs_toReal_reduceAlong_sub_le` (every association order, IEEE accumulator and destination, finite evaluation: error at most $((1+u)^n-1)\sum_i \lvert t_i\rvert$ plus the final half-ulp allowance, where $n$ counts the additions); decimal: `abs_reduceAlong_sub_le` (every association order, accumulator, destination and direction, finite terms and no `overflow` flag: the mixed budget of the order with $10^{1-p}$ relative and $10^{q_{\min}}$ absolute allowance at each addition, plus one unit of the destination grid), `reduceAlong_valid`; kernel rule: binary `KernelPath.toNatBits_reduceAlong` (`evalWord_eq`) |
| 9.5 | `augmentedAddition` | `Model.augmentedAddition`, `ExecFloat.Binary.augmentedAddition` | not applicable (binary only) | `toReal_augmentedAddition_head`, `toReal_augmentedAddition_add`, `augmentedAddition_of_isFinite_head_eq_false`; kernel rule: `Configured.augmentedAddition_eq` (`KernelPath.augmentedAddition_eq_spec`) |
| 9.5 | `augmentedSubtraction` | `Model.augmentedSubtraction`, `ExecFloat.Binary.augmentedSubtraction` | not applicable (binary only) | `toReal_augmentedSubtraction_sub`; kernel rule: `Configured.augmentedSubtraction_eq` (`KernelPath.augmentedSubtraction_eq_spec`) |
| 9.5 | `augmentedMultiplication` | `Model.augmentedMultiplication`, `ExecFloat.Binary.augmentedMultiplication` | not applicable (binary only) | `toReal_augmentedMultiplication_head`, `toReal_augmentedMultiplication_tail`, `augmentedMultiplication_inexact_iff`; kernel rule: `Configured.augmentedMultiplication_eq` (`KernelPath.augmentedMultiplication_eq_spec`) |
| 9.6 | `minimum` | `Model.minimum`, `ExecFloat.Binary.minimum` | `Arithmetic.minimum` (generated member of `extremum`) | binary: `isNaN_minimum_eq_false_of_isNaN_eq_false`; decimal: `extremum_status`, `extremum_value_eq_or`, `numericValue?_selectExtremum`; kernel rule: binary `Configured.liftBinary_minimum_eq`, `minimum_outcome_eq` (`KernelPath.extremum_eq_spec`, `extremumNumber_eq_spec`, `magnitudeExtremum_eq_spec`), decimal `KernelPath.extremum_eq` |
| 9.6 | `minimumNumber` | `Model.minimumNumber`, `ExecFloat.Binary.minimumNumber` | `Arithmetic.minimumNumber` (generated member of `extremum`) | binary: `isNaN_minimumNumber`; decimal: `extremum_status`, `extremum_value_eq_or`, `numericValue?_selectExtremum`; kernel rule: binary `Configured.liftBinary_minimumNumber_eq`, `minimumNumber_outcome_eq` (`KernelPath.extremum_eq_spec`, `extremumNumber_eq_spec`, `magnitudeExtremum_eq_spec`), decimal `KernelPath.extremum_eq` |
| 9.6 | `maximum` | `Model.maximum`, `ExecFloat.Binary.maximum` | `Arithmetic.maximum` (generated member of `extremum`) | binary: `isNaN_maximum_eq_false_of_isNaN_eq_false`; decimal: `extremum_status`, `extremum_value_eq_or`, `numericValue?_selectExtremum`; kernel rule: binary `Configured.liftBinary_maximum_eq`, `maximum_outcome_eq` (`KernelPath.extremum_eq_spec`, `extremumNumber_eq_spec`, `magnitudeExtremum_eq_spec`), decimal `KernelPath.extremum_eq` |
| 9.6 | `maximumNumber` | `Model.maximumNumber`, `ExecFloat.Binary.maximumNumber` | `Arithmetic.maximumNumber` (generated member of `extremum`) | binary: `isNaN_maximumNumber`; decimal: `extremum_status`, `extremum_value_eq_or`, `numericValue?_selectExtremum`; kernel rule: binary `Configured.liftBinary_maximumNumber_eq`, `maximumNumber_outcome_eq` (`KernelPath.extremum_eq_spec`, `extremumNumber_eq_spec`, `magnitudeExtremum_eq_spec`), decimal `KernelPath.extremum_eq` |
| 9.6 | `minimumMagnitude` | `Model.minimumMagnitude`, `ExecFloat.Binary.minimumMagnitude` | `Arithmetic.minimumMagnitude` (generated member of `extremum`) | binary: `abs_toReal_minimumMagnitude`, `magnitudeExtremum_status`, `toModel_magnitudeExtremum`; decimal: `extremum_status`, `extremum_value_eq_or`, `numericValue?_selectExtremum`, `numericValue?_abs_selectByMagnitude`; kernel rule: binary `Configured.liftBinary_minimumMagnitude_eq`, `minimumMagnitude_outcome_eq` (`KernelPath.extremum_eq_spec`, `extremumNumber_eq_spec`, `magnitudeExtremum_eq_spec`), decimal `KernelPath.extremum_eq` |
| 9.6 | `minimumMagnitudeNumber` | `Model.minimumMagnitudeNumber`, `ExecFloat.Binary.minimumMagnitudeNumber` | `Arithmetic.minimumMagnitudeNumber` (generated member of `extremum`) | binary: `abs_toReal_minimumMagnitudeNumber`, `magnitudeExtremum_status`, `toModel_magnitudeExtremum`; decimal: `extremum_status`, `extremum_value_eq_or`, `numericValue?_selectExtremum`, `numericValue?_abs_selectByMagnitude`; kernel rule: binary `Configured.liftBinary_minimumMagnitudeNumber_eq`, `minimumMagnitudeNumber_outcome_eq` (`KernelPath.extremum_eq_spec`, `extremumNumber_eq_spec`, `magnitudeExtremum_eq_spec`), decimal `KernelPath.extremum_eq` |
| 9.6 | `maximumMagnitude` | `Model.maximumMagnitude`, `ExecFloat.Binary.maximumMagnitude` | `Arithmetic.maximumMagnitude` (generated member of `extremum`) | binary: `abs_toReal_maximumMagnitude`, `magnitudeExtremum_status`, `toModel_magnitudeExtremum`; decimal: `extremum_status`, `extremum_value_eq_or`, `numericValue?_selectExtremum`, `numericValue?_abs_selectByMagnitude`; kernel rule: binary `Configured.liftBinary_maximumMagnitude_eq`, `maximumMagnitude_outcome_eq` (`KernelPath.extremum_eq_spec`, `extremumNumber_eq_spec`, `magnitudeExtremum_eq_spec`), decimal `KernelPath.extremum_eq` |
| 9.6 | `maximumMagnitudeNumber` | `Model.maximumMagnitudeNumber`, `ExecFloat.Binary.maximumMagnitudeNumber` | `Arithmetic.maximumMagnitudeNumber` (generated member of `extremum`) | binary: `abs_toReal_maximumMagnitudeNumber`, `magnitudeExtremum_status`, `toModel_magnitudeExtremum`; decimal: `extremum_status`, `extremum_value_eq_or`, `numericValue?_selectExtremum`, `numericValue?_abs_selectByMagnitude`; kernel rule: binary `Configured.liftBinary_maximumMagnitudeNumber_eq`, `maximumMagnitudeNumber_outcome_eq` (`KernelPath.extremum_eq_spec`, `extremumNumber_eq_spec`, `magnitudeExtremum_eq_spec`), decimal `KernelPath.extremum_eq` |
| 9.7 | `getPayload` | `Model.getPayload`, `ExecFloat.Binary.getPayload` | `Datum.getPayload` | binary: `toReal_getPayload`, `getPayload_setPayload`; decimal: `getPayload_setPayload`, `getPayload_of_isNaN_eq_false`; kernel rule: binary `Configured.liftUnary_getPayload_eq` (`KernelPath.getPayload_eq_spec`) |
| 9.7 | `setPayload` | `Model.setPayload`, `ExecFloat.Binary.setPayload` | `Datum.setPayload` | binary: `isNaN_setPayload`, `setPayload_getPayload`, `signBit_setPayload`; decimal: `setPayload_getPayload`, `setPayload_valid`, `isNaN_setPayload`; kernel rule: binary `Configured.liftUnary_setPayload_eq` (`KernelPath.setPayload_eq_spec`) |
| 9.7 | `setPayloadSignaling` | `Model.setPayloadSignaling`, `ExecFloat.Binary.setPayloadSignaling` | `Datum.setPayloadSignaling` | binary: `isSignaling_setPayloadSignaling`, `getPayload_setPayloadSignaling`; decimal: `setPayloadSignaling_getPayload`; kernel rule: binary `Configured.liftUnary_setPayloadSignaling_eq` (`KernelPath.setPayloadSignaling_eq_spec`) |

<!-- end of the clause map -->

## What the theorems give you

We've quoted theorems all chapter, so here's the chain behind the arithmetic ones. First, [[FloatLib.Floats.ExecFloat.Proof.add_eq_spec]], [[FloatLib.Floats.ExecFloat.Proof.sub_eq_spec]], [[FloatLib.Floats.ExecFloat.Proof.mul_eq_spec]], [[FloatLib.Floats.ExecFloat.Proof.div_eq_spec]], [[FloatLib.Floats.ExecFloat.Proof.sqrt_eq_spec]] and [[FloatLib.Floats.ExecFloat.Proof.fma_eq_spec]] show that the code that runs computes the format's reference definition, whichever kernel FloatLib's planner picked. They hold for every `FloatFormat` with no IEEE hypothesis, because the reference definitions follow the descriptor's own exceptional-value policy ([the performance chapter](#/chapter/performance)). The processor's own floating-point instructions sit behind the [unchecked native-FPU import](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/NativeFPU/Unchecked.lean), and certified modules don't import it.

Second, under `fmt.isIEEE = true` the reference definitions meet the reals through [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt]]. That's nearest-even rounding in the style of the Coq library Flocq, onto the grid with precision $w_f + 1$ and gradual underflow (the subnormals) at $e_{\min} - w_f$. The grid has no top, which is where the finite-result premises come from. For addition, subtraction, multiplication and FMA you show the result is finite, which forces finite operands, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt]], [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_sub_eq_roundAt]], [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_mul_eq_roundAt]] and [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_fma_eq_roundAt]] give you the exact real operation rounded once. Division, [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_div_eq_roundAt]], also wants a finite divisor, because a finite value over an infinity is a finite zero. [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_sqrt_eq_roundAt]] asks only for a finite input that's zero or has a clear sign bit, since [[FloatLib.Floats.Formats.BinaryInterchange.Model.isFinite_sqrt_of_isFinite]] proves a square root can't overflow. The first example ties binary32 `+` to its executable specification, the next two are rounding equations, and the last keeps a square root finite:

```lean
example (a b : Binary32) : a + b = ExecFloat.Spec.add a b :=
  ExecFloat.Proof.add_eq_spec a b

example (x y : Model FloatFormat.binary64)
    (hout : Model.isFinite (Model.mul x y) = true) :
    Model.toReal (Model.mul x y) =
      Model.roundAt FloatFormat.binary64 (Model.toReal x * Model.toReal y) :=
  Model.toReal_mul_eq_roundAt x y (by simp) hout

example (x y z : Model FloatFormat.binary128)
    (hout : Model.isFinite (Model.fma x y z) = true) :
    Model.toReal (Model.fma x y z) =
      Model.roundAt FloatFormat.binary128 (Model.toReal x * Model.toReal y + Model.toReal z) :=
  Model.toReal_fma_eq_roundAt x y z (by simp) hout

example (x : Model FloatFormat.binary32)
    (hx : Model.isFinite x = true) (hpos : Model.signBit x = false) :
    Model.isFinite (Model.sqrt x) = true :=
  Model.isFinite_sqrt_of_isFinite x (by simp) hx (Or.inr hpos)
```

Once you have a rounding equation, the [general rounding theory](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/Flocq/Theory) of [the rounding chapter](#/chapter/the-mathematics-of-rounding) takes over. [[FloatLib.Floats.Formats.BinaryInterchange.Model.abs_roundAt_sub_le]] and [[FloatLib.Floats.Formats.BinaryInterchange.Model.abs_toReal_add_sub_le]] give the half-ulp bound, half the gap between neighbouring values (ulp is short for unit in the last place), and in the normal range [[FloatLib.Floats.Formats.BinaryInterchange.Model.relativeError_roundAt_le_of_normal]] gives the relative bound $u = 2^{-p}$. `Model.mixedError_roundAt` bounds the error everywhere by $u|x| + \eta$, with $\eta = 2^{e_{\min} - w_f - 1}$ half the subnormal spacing, $2^{-150}$ for binary32, and the `mixedError_toReal_*` theorems carry that through each operation. Sometimes there's no error at all. Sterbenz's lemma, [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_sub_eq_of_sterbenz_of_same_sign]], says two finite values of the same sign within a factor of two subtract exactly, with no finite-output premise.
