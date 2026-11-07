---
number: "05"
slug: ieee-binary-formats
title: "IEEE binary formats"
summary: "How binary16, binary32, binary64, binary128 and widths of your own store a number in bits, and how to read, round, convert, print and prove things about them."
phases: [ieee-formats, binary-format, binary-arithmetic, status-and-directed, planner-and-configured]
---

IEEE 754, the floating-point standard, names its binary formats by width: binary16 takes sixteen bits, and binary32, binary64 and binary128 take 32, 64 and 128. In this chapter we'll take values apart bit by bit, meet NaNs ("not a number"), signed zeros and status flags, move values between widths, and see what FloatLib proves at each step.

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

![The five layouts of the table drawn to one scale, sign bit, exponent field, and fraction field from left to right, with the width of each field in bits](assets/ch12-bit-layouts.png "Five binary layouts on the same bit scale.")

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

![Table of normal exponent intervals and least subnormal values for binary16, bfloat16, binary32, binary64, and binary128, with a separate bar chart of significand precision in bits including the leading bit](assets/ch12-range-precision.png "Exact exponent limits and significand precision for five binary formats.")

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

Now for the words that aren't ordinary numbers, and for zero, which comes in two signs. The top fraction bit of a NaN is called the quiet bit, because setting it makes the NaN quiet. A quiet NaN flows through arithmetic silently, while a signaling NaN is a tripwire that raises the invalid flag when used as an operand. Seven [classifiers](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Model/Carrier.lean), [[FloatLib.Floats.Formats.BinaryInterchange.Model.isZero]], `isSubnormal`, [[FloatLib.Floats.Formats.BinaryInterchange.Model.isFinite]], [[FloatLib.Floats.Formats.BinaryInterchange.Model.isInf]], [[FloatLib.Floats.Formats.BinaryInterchange.Model.isNaN]], `isSNaN` and `isQNaN`, test the stored fields, and `classify` sorts a value into the ten IEEE classes. One theorem matches `classify` to the exact value for every binary descriptor, whatever its bias and encoding, and the configured API inherits it through `toModel`.

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

There are two limits, though. The finite theorem doesn't give you a correctly rounded hypotenuse, and it doesn't show that every intermediate stays finite. Complex support covers basic arithmetic, conjugation, squared norm and magnitude, and `normSq`, the squared norm, is a rounded sum of squares with no scaling. Complex exponential, logarithm and trigonometric functions aren't implemented, and the scalar transcendental APIs don't supply them.

## How to convert to integers and text

What's our binary32 $\pi$ as an 8-bit integer? And $300$? FloatLib has [integer conversions](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/BinaryInterchange/DType) between binary values and fixed-width two's-complement integers (the usual signed machine integers). `ExecDType.floatToInt` rounds a finite value to an integer in the requested direction and succeeds only if it fits the signed width, with inexact set when a fraction was thrown away. An infinity, a NaN or an out-of-range value is a reported failure, never some fixed integer, and the [integer conversion theorem](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/DType/Semantics.lean) and its out-of-range companion pin down both finite cases. Going the other way, `ExecDType.intToFloat` rounds a `FixedInt width` once into the destination, with the five flags under `status := true`, and `intToFloat_nearest_eq_round` proves that a finite nearest-even result is `roundAt` of the integer. The parse and format lines come up in the next section.

```lean
open FloatLib.Numerics.Representations

#eval (ExecDType.floatToInt (width := 8) (ExecFloat.Binary.toModel piWord) (mode := .nearest)).map FixedInt.toInt
-- .success 3 { inexact := true }
#eval (ExecDType.floatToInt (width := 8) (ExecFloat.Binary.toModel (300 : Binary32)) (mode := .nearest))
-- .failure .outOfRange
#eval let o := ExecDType.intToFloat FloatFormat.binary16 (FixedInt.ofInt (width := 32) 2049)
        (status := true)
      ((ExecFloat.Binary.ofModel o.value : Binary16), o.status.inexact)
-- (2048, true)
#eval (ExecFloat.Binary.parse "0.1" : Except Model.ParseError Binary32)
-- Except.ok 0.1
#eval Model.format (Model.canonicalNaN FloatFormat.binary32)
-- "nan"

example {width : Nat} (x : FixedInt width)
    (hfin : Model.isFinite (ExecDType.intToFloat FloatFormat.binary32 x) = true) :
    Model.toReal (ExecDType.intToFloat FloatFormat.binary32 x) =
      Model.roundAt FloatFormat.binary32 (FixedInt.toInt x : ℝ) :=
  ExecDType.intToFloat_nearest_eq_round x (by simp) hfin
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
#eval Model.isInf (Model.roundToIntegral
  (Model.ofNatBits (fmt := IntegralNarrow) 23) (mode := .nearest))
-- true
```

In the block, word `23` is $3.75$ and word `20` is three. `roundToIntegral` is one of a few operations with their own status and finite-value theorems, with `remainder`, `scale`, `nextUp`, `nextDown` and `binaryExponent`. That last one rounds $\lfloor\log_2|x|\rfloor$ into the source format, where a small format can lose accuracy, while `binaryExponentInt` returns it exactly.

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
