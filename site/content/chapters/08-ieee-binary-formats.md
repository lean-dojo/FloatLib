---
number: "08"
slug: ieee-binary-formats
title: "IEEE binary formats"
summary: "Standard and custom binary layouts share arithmetic kernels and proofs, and their descriptors and finite-value hypotheses determine how those proofs apply."
phases: [ieee-formats, binary-format, binary-arithmetic, status-and-directed]
---

Binary16, binary32, binary64 and binary128 divide a stored word into a sign bit, a biased exponent field and a fraction field. A wider exponent extends the range; a wider fraction places representable values closer together. Binary16 and bfloat16 both occupy sixteen bits, but binary16 keeps eleven significant bits and stops at 65504. Bfloat16 gives three of those significant bits to the exponent, so its values are farther apart but its normal exponent range reaches as far as binary32's.

In FloatLib we describe that choice with [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat]], which specifies the field widths, the bias and the exceptional encodings, and its indexed type [[FloatLib.Floats.Formats.BinaryInterchange.Model]] stores the bits. The same arithmetic definitions work at each descriptor, custom widths included, and the real-valued theorems state which descriptor and finiteness hypotheses they need.

## One descriptor, many widths

A `FloatFormat` stores four pieces of data: `expWidth`, `fracWidth`, `exponentBias`, and `encoding`. The last is a value of [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.Encoding]], which says what the reserved bit patterns mean. The binary examples in this chapter all use `.ieee`. The other three encodings are finite-max-NaN, finite-unsigned-zero, and fully finite, and [chapter 11](#/chapter/low-precision-formats-for-machine-learning) explains them. The structure also has four [proof fields](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Format/Definition.lean). They require at least two exponent bits, at least one fraction bit, a positive bias, and a bias no larger than the largest finite exponent code. They're propositions, so they cost nothing at run time. In the structure the two width conditions default to `by decide`, and for literal arguments `FloatFormat.custom` defaults all four.

These minimums leave room for zeros, subnormals, normal numbers, infinities, and quiet NaNs. With one exponent bit the field has only two values, one reserved for zeros and subnormals and the other for infinity and NaN, so nothing is left for normal numbers. With two bits the codes 00, 01, 10, 11 become subnormals, two normal binades, and the infinity-NaN class. One fraction bit is enough to tell a quiet NaN from an infinity, but signaling NaNs need at least two fraction bits. The two bias conditions put the exponent code used to encode $1$ inside the finite range.

The `ieee` constructor takes only the two widths and fills in the conventional bias and the `.ieee` encoding, while the more general [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.custom]] accepts any validated bias with any encoding. With $w_e$ exponent bits and $w_f$ fraction bits, the total width from `bitWidth` is $1 + w_e + w_f$, and the conventional constants are

$$
\begin{aligned}
b &= 2^{w_e - 1} - 1, &\qquad p &= w_f + 1,\\
e_{\min} &= 1 - b, &\qquad e_{\max} &= b,\\
x^{\text{norm}}_{\min} &= 2^{e_{\min}}, &\qquad x^{\text{subn}}_{\min} &= 2^{e_{\min} - w_f},\\
x_{\max} &= (2 - 2^{-w_f}) \cdot 2^{e_{\max}}.
\end{aligned}
$$

Here are the constants of the [named layouts](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Format/Catalog.lean). Binary16, binary32, binary64, and binary128 are IEEE 754 interchange formats, and bfloat16 shares their encoding conventions but has its own field widths.

| Descriptor | $w_e$ | $w_f$ | bits | $b$ | $p$ | $e_{\min}$ | $e_{\max}$ | $x_{\max}$ |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.binary16]] | 5 | 10 | 16 | 15 | 11 | $-14$ | 15 | $(2 - 2^{-10}) \cdot 2^{15} = 65504$ |
| [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.bfloat16]] | 8 | 7 | 16 | 127 | 8 | $-126$ | 127 | $(2 - 2^{-7}) \cdot 2^{127}$ |
| [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.binary32]] | 8 | 23 | 32 | 127 | 24 | $-126$ | 127 | $(2 - 2^{-23}) \cdot 2^{127}$ |
| [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.binary64]] | 11 | 52 | 64 | 1023 | 53 | $-1022$ | 1023 | $(2 - 2^{-52}) \cdot 2^{1023}$ |
| [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.binary128]] | 15 | 112 | 128 | 16383 | 113 | $-16382$ | 16383 | $(2 - 2^{-112}) \cdot 2^{16383}$ |

[Figure 8.1](#/chapter/ieee-binary-formats/figure-ch12-bit-layouts) draws every bit at the same width, so you can compare how much storage each field takes. Exponent fields range from five bits to fifteen and fractions from seven to one hundred and twelve, while the sign takes one bit in all five.

![The five layouts of the table drawn to one scale, sign bit, exponent field, and fraction field from left to right, with the width of each field in bits](assets/ch12-bit-layouts.png "Five binary layouts on the same bit scale.")

That file also defines the wider `binary256` layout, with 19 exponent and 236 fraction bits. You can read the constants in the table straight from the descriptors:

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

For binary128, the last pair is $e_{\max}$ and the exponent of the least subnormal, $e_{\min} - w_f = -16382 - 112 = -16494$. In [Figure 8.2](#/chapter/ieee-binary-formats/figure-ch12-range-precision), the table gives each format's normal exponent interval and its least subnormal as a power of two, and the *Significand precision* panel gives $p$ in bits. That count includes the leading bit, and it corresponds to $p \log_{10} 2$ decimal digits. Look at the two sixteen-bit formats, which differ in both columns: bfloat16 shares binary32's normal exponent range and has fewer significant bits than binary16.

![Table of normal exponent intervals and least subnormal values for binary16, bfloat16, binary32, binary64, and binary128, with a separate bar chart of significand precision in bits including the leading bit](assets/ch12-range-precision.png "Exact exponent limits and significand precision for five binary formats.")

[[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.isIEEE]] holds when a descriptor has the `.ieee` encoding and the conventional bias $2^{w_e-1}-1$. You'll see it in nearly every theorem below as the hypothesis `hfmt : fmt.isIEEE = true`. The catalog provides `simp` lemmas such as `isIEEE_binary32`, so `by simp` discharges it for the named formats. It's a hypothesis on the theorems and stays out of the type, because the executable operations are meaningful for every encoding while the real-number theorems use the IEEE reading of the reserved patterns.

## The same value in five layouts

A `Model fmt` stores exactly `fmt.bitWidth` bits, and the helper below prints their natural-number value in hexadecimal, without leading zeroes. So let's add one to itself in each format and print the result:

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

Every result encodes two, with sign zero, biased exponent $b + 1$ and fraction zero. Binary16 and bfloat16 agree on `0x4000` even though their field boundaries differ, because $b + 1$ is a one followed by zeros in both a five-bit and an eight-bit field. We used one Lean addition definition, [[FloatLib.Floats.Formats.BinaryInterchange.Model.add]], at all five descriptors.

## Reading a word

A stored word $W$ of width $1 + w_e + w_f$ splits into the sign $s$, the biased exponent $E$, and the fraction $F$:

$$
s = \lfloor W / 2^{w_e + w_f} \rfloor, \qquad
E = \lfloor W / 2^{w_f} \rfloor \bmod 2^{w_e}, \qquad
F = W \bmod 2^{w_f}.
$$

When $1 \le E \le 2^{w_e} - 2$ the word is normal and denotes $(-1)^s (1 + F/2^{w_f}) \cdot 2^{E - b}$. Its leading one is implicit, and that's where the extra bit of precision $p = w_f + 1$ comes from. When $E = 0$ and $F \ne 0$ the word is subnormal and denotes $(-1)^s F \cdot 2^{e_{\min} - w_f}$, with no implicit bit. So the representable values keep going in equal steps down to $\pm 2^{e_{\min} - w_f}$ and don't stop at $2^{e_{\min}}$. When $E = 0$ and $F = 0$ the word is a signed zero, and when $E = 2^{w_e} - 1$ it's an infinity if $F = 0$ and a NaN otherwise.

[[FloatLib.Floats.Formats.BinaryInterchange.Model.toDyadic?]] decodes a finite word to an exact dyadic rational without normalizing it. A normal word decodes to significand $2^{w_f} + F$ and exponent $E - b - w_f$, and a subnormal word to significand $F$ and exponent $e_{\min} - w_f$. Because the decoder keeps that form, you can still see the fields in the decoded value: the fraction supplies the low significand bits, and the exponent accounts for their scale. The [IEEE decoding rule](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Dyadic/Core.lean) is `ieeeToDyadic?`, and the [general decoder](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Dyadic/Decode.lean) `toDyadic?` dispatches to it for IEEE descriptors and reads the declared bias for the other encodings.

Application code normally uses `ExecFloat.Binary`. Given the two widths, it builds a descriptor with the `.ieee` encoding and the conventional bias as defaults. It selects its storage and kernels statically, which is the subject of [chapter 16](#/chapter/backends-and-the-planner). Its `toModel` conversion lets us apply the model theorems to these executable values. Each descriptor in the table above has an executable type named after it: `Binary16`, `BFloat16`, `Binary32`, `Binary64`, and `Binary128`, each an `ExecFloat.Binary` with the table's widths. `Binary256` uses nineteen exponent bits and 236 fraction bits. Here's the nearest binary32 value to $\pi$, and the smallest positive one:

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

Take the word `0x40490fdb`. It has $s = 0$, $E = 128$, and $F = 4788187$, so the significand is $2^{23} + 4788187 = 13176795$ and the exponent is $128 - 127 - 23 = -22$. Its value, $13176795 \cdot 2^{-22} = 3.14159274\ldots$, differs from $\pi$ by less than half the spacing $2^{-22}$ in that binade, as correct rounding demands. The word `0x00000001` is the least positive subnormal, $2^{-149} = 2^{e_{\min} - w_f}$ for binary32. [[FloatLib.Floats.ExecFloat.Binary.ofBits32]] and [[FloatLib.Floats.ExecFloat.Binary.toBits32]] carry the 32-bit word across unchanged in both directions, NaN payload included. The conversions to Lean's native `Float32` in the same file canonicalize NaNs, and that's why we keep the two boundaries apart ([chapter 17](#/chapter/performance/host-arithmetic-as-a-reference)). Where subnormal meets normal, the two decoding formulas join without a gap. Let's watch it happen by incrementing the largest positive subnormal word twice:

| Binary32 word | Exponent field | Fraction field | Exact value |
| --- | --- | --- | --- |
| `0x007fffff` | 0 | $2^{23}-1$ | $(2^{23}-1)\,2^{-149}$ |
| `0x00800000` | 1 | 0 | $2^{23}\,2^{-149}$ |
| `0x00800001` | 1 | 1 | $(2^{23}+1)\,2^{-149}$ |

The carry out of the fraction changes the exponent field from zero to one, and at the same time the decoder restores the implicit leading bit. Both decoder branches use the scale $2^{-149}$ here, so the coefficient just advances from 8388607 to 8388608. The second value is the least normal, $2^{-126}$, and the next normal is still only $2^{-149}$ away. So a change in classification doesn't by itself change the spacing.

As subnormal values get smaller, the absolute step stays the same and fewer significant bits are left. At the least normal, the step divided by the value is $2^{-23}$, and at the least positive subnormal it's 1, so the next positive value is twice as large. In the table of [Figure 8.2](#/chapter/ieee-binary-formats/figure-ch12-range-precision), this region runs from the least subnormal up to the bottom of the normal exponent interval. It's a fixed grid whose relative precision gets worse toward zero. With the exponent fixed in this region, a smaller value has to use a smaller coefficient. So an absolute half-step error bound can still describe rounding there, but a uniform normal-range relative error bound can't.

You can inspect a stored value through the three readings from [chapter 06](#/chapter/the-numerical-models). For exact rational arithmetic, `toRat?` gives the stored rational and returns `none` for infinities and NaNs. When the exceptional details matter, [[FloatLib.Floats.Formats.BinaryInterchange.Model.exactValue]] returns an [[FloatLib.Floats.Formats.BinaryInterchange.Model.ExactValue]], which keeps the sign of zero, the sign of an infinity, and the sign, signaling class and payload of a NaN. For real-number proofs, [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal]] is total and sends NaNs and infinities to $0$. Any map into $\mathbb{R}$ also has to send both zeros to $0$, so we state signed-zero facts on the bits.

## Custom widths

The IEEE theorems apply to any descriptor with `isIEEE`, so a custom format needs no new arithmetic proofs. Say we want a 24-bit layout with seven exponent bits and sixteen fraction bits, and a 71-bit layout with eleven exponent bits and fifty-nine fraction bits.

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
    (hx : Model.isFinite x = true) (hy : Model.isFinite y = true)
    (hout : Model.isFinite (Model.add x y) = true) :
    Model.toReal (Model.add x y) =
      Model.roundAt binary24 (Model.toReal x + Model.toReal y) :=
  Model.toReal_add_eq_roundAt x y (by simp) hx hy hout

abbrev binary71 : FloatFormat := FloatFormat.ieee 11 59
abbrev Binary71 := ExecFloat.Binary (exponentBits := 11) (fractionBits := 59)

example : binary71.bitWidth = 71 := by decide

#eval ((1 : Binary71) / 3)
-- 0.3333333333333333335
```

The 24-bit format has bias 63, normal exponents from $-62$ to $63$, and $p = 17$ significant bits. A layout with eight exponent bits and fifteen fraction bits would occupy the same 24 bits with more range and one bit less precision. So "a 24-bit float" isn't a specification until you give the split. The addition theorem applies with `by simp` discharging `binary24.isIEEE = true` through the lemma `isIEEE_ieee`, and nothing else in the proof mentions the width. The 71-bit format has 60 significant bits, and its quotient $1/3$ shows them: the display needs nineteen significant digits, and the stored significand $768614336404564651$ lies between $2^{59}$ and $2^{60}$. For 71 significant bits you'd take `fracWidth := 70` and occupy 82 stored bits with the same exponent field. [Chapter 11](#/chapter/low-precision-formats-for-machine-learning) goes the other way, down to eight and four bits, and changes what the reserved patterns mean. Programs normally use [[FloatLib.Floats.ExecFloat.Binary]] or [[FloatLib.Floats.ExecFloat.BinaryLimbs]], whose [[FloatLib.Floats.Formats.BinaryInterchange.Configured.StoragePlan]] chooses a carrier. `Binary` uses machine words through 64 bits, two native words for eligible layouts from 65 through 128 bits, and `Model format` itself otherwise. Above 128 bits, `BinaryLimbs` uses an array of 32-bit limbs. Both have the same descriptor and reference semantics.

## NaN propagation and signed zero

The [classifiers](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Model/Carrier.lean) [[FloatLib.Floats.Formats.BinaryInterchange.Model.isZero]], `isSubnormal`, [[FloatLib.Floats.Formats.BinaryInterchange.Model.isFinite]], [[FloatLib.Floats.Formats.BinaryInterchange.Model.isInf]], [[FloatLib.Floats.Formats.BinaryInterchange.Model.isNaN]], `isSNaN`, and `isQNaN` test the stored fields. All but `isSubnormal` are defined by a case split on the encoding, and under `.ieee` they're the field tests above. `isSubnormal` is the same field test in every encoding, a zero exponent with a nonzero fraction. The quiet bit is the most significant fraction bit. A NaN with that bit set is quiet and propagates silently, while a NaN with it clear is signaling and raises the invalid flag when it's an operand.

`classify` gathers these answers into the ten IEEE classes. Its semantic theorem reads the complete exact value: a finite nonzero magnitude below $2^{e_{\min}}$ is subnormal, and one at or above that threshold is normal. The sign distinguishes the two versions of each finite class and of infinity, and NaNs are quiet or signaling. One proof covers every binary descriptor, using its declared bias and encoding policy, and the configured API inherits it through its codec.

When several inputs carry NaN payloads, the standard leaves the choice among them to the implementation [@ieee754_2019], and we use two deterministic rules. When an operation is invalid and no operand is a NaN, `invalidResult` returns the format's `canonicalNaN`, which has a positive sign, an all-ones exponent, and only the quiet bit set. When at least one operand is a NaN, `chooseNaN2` prefers a signaling operand over a quiet one, and otherwise the left operand over the right. It then sets the quiet bit and keeps the rest of the payload. So a signaling operand's payload survives whenever there is one, and otherwise operand order settles the choice, without comparing payloads. Our [independent comparisons](#/chapter/external-validation) check NaN class and signaling behaviour, but they don't independently validate this choice of payload. At binary32, an invalid subtraction and an addition with a signaling NaN produce different payloads, and the two zero encodings stay distinguishable:

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

In `ExactValue.nan false false 4194304` the three fields are the sign, whether it is signaling, and the complete stored fraction field. Here $4194304 = 2^{22}$ is the quiet bit alone, the canonical NaN that $\infty - \infty$ produces. The second result is the signaling NaN `0x7f800001`, quieted. Its fraction field $4194305 = 2^{22} + 1$ keeps the original low bit, and the middle `false` records that the result is no longer signaling. In the common `NumericalValue` view these two results have diagnostic payloads $0$ and $1$, with the quiet bit removed. The two zeros compare equal under the configured type's `==`, which is IEEE numerical comparison, even though their words differ :) Dividing one by negative zero gives $-\infty$, so the sign shows up in arithmetic as well as in casts and reductions.

## Status flags

IEEE 754 asks each operation to report five exceptions: invalid operation, division by zero, overflow, underflow, and inexact. We represent them as the five Booleans of [[FloatLib.Numerics.IEEEStatus]]. Arithmetic operations and conversions take the option `(status := true)`, and then they return an [[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEEOutcome]] holding the value, its flags and the [ternary value](#/chapter/the-mathematics-of-rounding/rounding-directions-and-the-ternary-value). Leave the option off and the same call computes neither flags nor ternary value. [[FloatLib.Floats.Formats.BinaryInterchange.Model.add]] and its siblings for subtraction, multiplication and fused multiply-add classify the exact dyadic result and the delivered value, as [chapter 06](#/chapter/the-numerical-models/status-flags-as-data) describes. We decide overflow on the result rounded with an unbounded exponent range, and we detect tininess after rounding. Underflow is raised exactly when the result is both tiny and inexact, so an exact subnormal result raises neither flag, as the examples in [chapter 06](#/chapter/the-numerical-models) show. Invalid and division by zero are decided from the operand classes.

Division and square root work out their flags without forming an exact dyadic result. With status, division rounds the exact rational quotient and classifies it with `rationalRoundingStatusScaled`. Square root never forms an exact result at all. With status, it compares the exact square of the delivered root with the radicand, and that comparison gives the ternary value and decides inexact. It decides tininess by [comparing the radicand with the squared underflow boundary](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Status/Runtime.lean), and both tests use exact integer arithmetic. [[FloatLib.Floats.Formats.BinaryInterchange.Model.sqrt_inexact_eq_ternary_bne_eq]] says that, on every input, square root raises inexact exactly when its ternary value is not `Ordering.eq`. On a positive finite input and in every direction, [[FloatLib.Floats.Formats.BinaryInterchange.Model.sqrt_inexact_iff]] says this happens exactly when the delivered value is not the real square root. As with the other operations, `value_sqrt` states that the option doesn't change the value. On the configured type the operations take the rounding direction as a named argument. They return the value with its flags and ternary value, so application code reads a flag as a field and never inspects a bit pattern:

```lean
def largest : Binary32 := ExecFloat.Binary.maxFinite false

#eval ExecFloat.Binary.div (1 : Binary32) 0 (status := true)
-- { value := inf,
--   status := { invalid := false, divideByZero := true, overflow := false, underflow := false, inexact := false },
--   ternary := Ordering.eq }
#eval ExecFloat.Binary.div (0 : Binary32) 0 (status := true)
-- { value := nan,
--   status := { invalid := true, divideByZero := false, overflow := false, underflow := false, inexact := false },
--   ternary := Ordering.eq }
#eval ExecFloat.Binary.mul largest 2 (status := true)
-- { value := inf,
--   status := { invalid := false, divideByZero := false, overflow := true, underflow := false, inexact := true },
--   ternary := Ordering.gt }
#eval ExecFloat.Binary.mul leastSubnormal 0.5 (status := true)
-- { value := 0,
--   status := { invalid := false, divideByZero := false, overflow := false, underflow := true, inexact := true },
--   ternary := Ordering.lt }
#eval ExecFloat.Binary.div (1 : Binary32) 3 (status := true)
-- { value := 0.33333334,
--   status := { invalid := false, divideByZero := false, overflow := false, underflow := false, inexact := true },
--   ternary := Ordering.gt }
#eval ExecFloat.Binary.sqrt (-4 : Binary32) (status := true)
-- { value := nan,
--   status := { invalid := true, divideByZero := false, overflow := false, underflow := false, inexact := false },
--   ternary := Ordering.eq }

example (x : Model FloatFormat.binary64) (mode : Model.IEEERoundingMode)
    (hnan : Model.isNaN x = false) (hneg : Model.signBit x = true)
    (hnz : Model.isZero x = false) :
    (Model.sqrt x (mode := mode) (status := true)).status.invalid = true :=
  Model.sqrt_invalid_of_negative_nonzero hnan hneg hnz

example (x : Model FloatFormat.binary64) (mode : Model.IEEERoundingMode)
    (hfinite : Model.isFinite x = true) (hzero : Model.isZero x = false)
    (hsign : Model.signBit x = false) :
    (Model.sqrt x (mode := mode) (status := true)).status.inexact = true ↔
      Model.toReal (Model.sqrt x (mode := mode) (status := true)).value ≠
        Real.sqrt (Model.toReal x) :=
  Model.sqrt_inexact_iff mode hfinite hzero hsign
```

The first two lines show the standard's distinction between division by zero and invalid. With a positive zero denominator, $1/0$ returns $\infty$ with the divide-by-zero flag, while $0/0$ returns a NaN with the invalid flag. Overflow always comes with inexact. The product $2^{-149} \cdot 0.5$ lies exactly halfway between $0$ and the least subnormal, and ties to even selects $0$. That result is both tiny and inexact, so the underflow flag is raised. The ternary value is `Ordering.eq` for the exact infinity and for both NaNs, `Ordering.gt` for the overflow and for one third rounded up, and `Ordering.lt` for the product rounded down to zero. Our flag theorems state the conditions for each exception. [[FloatLib.Floats.Formats.BinaryInterchange.Model.div_divideByZero]] says the flag is set exactly when a finite nonzero numerator meets a finite zero denominator. [[FloatLib.Floats.Formats.BinaryInterchange.Model.sqrt_invalid]] says invalid is set exactly for a signaling NaN or a negative nonzero non-NaN input. [[FloatLib.Floats.Formats.BinaryInterchange.Model.dyadicRoundingStatus_overflow]] says the overflow flag is set exactly when rounding the exact result crosses the format's overflow threshold or the delivered result is an infinity. Once the result is known to be finite, `dyadicRoundingStatus_overflow_of_isFinite` drops the second case. The two examples above apply a corollary of the square-root invalid theorem and the inexactness theorem at binary64, for every rounding direction at once.

## Directed rounding

In Lean, the six directions of [chapter 07](#/chapter/the-mathematics-of-rounding/rounding-directions-and-the-ternary-value) are the constructors of [[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEERoundingMode]]: `nearest` with ties to even, `nearestAway`, `towardZero`, `up`, `down`, and `away`. Ordinary `+`, `-`, `*`, `/`, `x.sqrt`, and `x.fma y z` on a configured type round to nearest even. Named operations, including [[FloatLib.Floats.ExecFloat.Binary.add]] and [[FloatLib.Floats.ExecFloat.Binary.div]], take a direction as the option `(mode := .up)` and default to nearest-even. After `open FloatLib.Rounding` you can write the six modes without the leading dot, as in `(mode := up)`, and the type is available as `IEEERoundingMode`. For one third, say, we can locate both binary32 neighbours exactly and compare the rounding directions:

```lean
open FloatLib.Rounding

def third (mode : IEEERoundingMode) : Binary32 :=
  ExecFloat.Binary.div 1 3 (mode := mode)

#eval third nearest
-- 0.33333334
#eval third towardZero
-- 0.3333333
#eval third up
-- 0.33333334
#eval third down
-- 0.3333333

#eval ExecFloat.Binary.add largest largest (mode := nearest)
-- inf
#eval ExecFloat.Binary.add largest largest (mode := up)
-- inf
#eval ExecFloat.Binary.add largest largest (mode := towardZero)
-- 3.4028235e38
#eval ExecFloat.Binary.add largest largest (mode := down)
-- 3.4028235e38

example (x y : Model FloatFormat.binary32)
    (hx : Model.isFinite x = true) (hy : Model.isFinite y = true) :
    Model.toEReal (Model.add x y (mode := .down)) ≤ ((Model.toReal x + Model.toReal y : ℝ) : EReal) :=
  Model.toEReal_add_down_le x y (by simp) hx hy
```

One third lies between the binary32 neighbours $5592405 \cdot 2^{-24}$ below and $11184811 \cdot 2^{-25}$ above. Nearest-even and toward $+\infty$ pick the upper one. Toward zero and toward $-\infty$ pick the lower one, and those two agree because the value is positive. For a negative numerator, toward zero agrees with upward rounding instead, because the direction is defined by order on the number line and changing the sign exchanges the upward and downward cases. The overflow lines show the rule of IEEE 754-2019 Section 7.4 [@ieee754_2019] as `directedOverflow` implements it. A direction that carries the magnitude away from zero overflows to infinity. Rounding toward zero, or toward the infinity of the other sign, returns the largest finite value, here $16777215 \cdot 2^{104} = (2 - 2^{-23}) \cdot 2^{127}$.

Directed operations are the basis of interval arithmetic, so their theorems are bounds rather than equations. They're stated in the extended reals through [[FloatLib.Floats.Formats.BinaryInterchange.Model.toEReal]], for the reason [chapter 06](#/chapter/the-numerical-models) gives. For finite operands, [[FloatLib.Floats.Formats.BinaryInterchange.Model.toEReal_add_down_le]] says that `add x y (mode := .down)`, addition toward $-\infty$, never exceeds the exact real sum. For the same operands, [[FloatLib.Floats.Formats.BinaryInterchange.Model.le_toEReal_add_up]] says that `add x y (mode := .up)`, addition toward $+\infty$, never falls below it. Our [other directed operations](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/BinaryInterchange/DirectedSemantics) for subtraction, multiplication, division, and square root have bounds of the same shape, with their finite-input and domain hypotheses.

## Casting between widths

[[FloatLib.Floats.Formats.BinaryInterchange.Model.cast]] is the descriptor-level operation, and it converts a `Model src` into a `Model dst`. A finite source is decoded to its exact dyadic and packed into the destination with nearest-even rounding, which may overflow to a signed infinity or land in the subnormal range. An infinity becomes the same-sign infinity when the destination has one. NaNs need a little more care. Cast a NaN to its own format and it's quieted with its payload kept. Cast it to a different IEEE format and it keeps its sign and becomes quiet. It keeps its payload when the payload fits in the destination's fraction without the quiet bit, and a payload that doesn't fit becomes zero. Section 6.2.3 of [@ieee754_2019] asks for this propagation, and it makes a widen-and-narrow round trip return the original quiet NaN. Casting a signaling NaN raises invalid, as Section 7.2 requires.

Cast a finite value to its own format and it comes back unchanged. When the exponent width, bias, and encoding agree and only the fraction widens, `widenExact` copies the fields without decoding the value. Bfloat16 to binary32 is such a case, and we like it because you can do it in your head. Both exponent fields have eight bits and bias 127, and the fraction grows from seven bits to twenty-three. Appending sixteen zero bits to the stored word puts its sign, exponent, and fraction in the right destination positions, so the bfloat16 word `0x3fc0`, which represents $1.5$, becomes the binary32 word `0x3fc00000`. In compiled code this widening is one shift of the complete stored word. In the [widening proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Conversion/Cast/Widening.lean), `widenBits_eq_ofFields` proves the bit-packing identity for arbitrary widths, and its destination-width proof removes a redundant modulus from execution. NaNs and infinities are handled before the cast takes this path. For every finite source, subnormals and signed zeros included, the compatible widening is exact in every rounding mode:

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

At the descriptor level, [[FloatLib.Floats.Formats.BinaryInterchange.Model.cast_eq_roundAt_of_isIEEE_destination]] also covers finite source values from custom-bias and finite-only encodings. Only the destination needs the IEEE encoding convention, and the result must stay finite. [[FloatLib.Floats.Formats.BinaryInterchange.Model.cast_exact_of_gridExtension_of_isIEEE_destination]] makes the cast exact when the destination has at least the source precision and reaches its smallest subnormal exponent. Grid inclusion alone doesn't guarantee enough upper range, though, so that exactness theorem keeps the finite-result premise. IEEE 754-2019 §5.4.2 likewise requires both sufficient precision and sufficient range for exact widening conversions [@ieee754_2019].

In the configured API you spell a cast `value.cast (target := …)`. It returns a `ConversionOutcome`, either a success carrying the value and conversion flags or a reported failure, and it doesn't call `Model.cast`. Instead it goes through the general conversion pipeline shared with posits and P3109. There the source is decoded to an exact signed rational that keeps the sign of zero, mapped into the destination's exact domain, and quantized once. Our [configured conversion theorem](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/Conversion/Proof.lean) `ExecFloat.Binary.Conversion.run_default_finite` says that for a finite value this quantization is `Model.roundRat`. For an IEEE destination and a finite result, [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_roundRatScaled_eq_roundAt_of_isFinite]] identifies its real value with `roundAt`, including a zero numerator, and the denominator must stay nonzero. The executable converter preserves signed zero even though its real denotation is zero. On NaNs the two paths follow the same rule. Inside the pipeline a NaN carries its sign, signaling class, and diagnostic payload. The source decoder removes the quiet bit from the stored fraction field, and the generic payload leaves out encoding markers. The pipeline's default policy `propagateNaN` builds the destination NaN with `Model.propagatedNaN`, the same construction `Model.cast` uses. A signaling source sets the `invalid` flag of the conversion status, and these flags differ from `IEEEStatus` because the same pipeline reaches destinations that saturate or wrap. The evaluations below use the configured path, and the theorems after them state the guarantees about `Model.cast` underneath.

```lean
def halfUlp64 : Binary64 := ExecFloat.Binary.ofBits64 0x3ff0000010000000
def threeHalfUlp64 : Binary64 := ExecFloat.Binary.ofBits64 0x3ff0000030000000

#eval ExecFloat.Binary.toRat? halfUlp64
-- some (16777217 / 16777216)
#eval (halfUlp64.cast (target := Binary32)).value?
-- some 1
#eval (threeHalfUlp64.cast (target := Binary32)).value?
-- some 1.0000002
#eval ((65504 : Binary16).cast (target := Binary32)).value?
-- some 65504
#eval (70000 : Binary32).cast (target := Binary16)
-- FloatLib.Floats.ExecFloat.ConversionOutcome.success
--   inf
--   { inexact := true,
--     overflow := true,
--     underflow := false,
--     saturated := false,
--     wrapped := false,
--     mappedSpecial := false,
--     invalid := false }

example (x : Model FloatFormat.binary32)
    (hx : Model.isFinite x = true)
    (hout : Model.isFinite (Model.cast FloatFormat.binary32 FloatFormat.binary64 x) = true) :
    Model.toReal (Model.cast FloatFormat.binary32 FloatFormat.binary64 x) = Model.toReal x :=
  Model.cast_exact_of_gridExtension x (by decide) (by decide) (by decide) (by decide) hx hout

example (x : Model FloatFormat.binary64)
    (hx : Model.isFinite x = true)
    (hout : Model.isFinite (Model.cast FloatFormat.binary64 FloatFormat.binary32 x) = true) :
    Model.toReal (Model.cast FloatFormat.binary64 FloatFormat.binary32 x) =
      Model.roundAt FloatFormat.binary32 (Model.toReal x) :=
  Model.cast_eq_roundAt (by simp) (by simp) x hx hout
```

The easy lines first. Widening 65504, the largest binary16 value, to binary32 leaves every flag clear, and 70000 has no binary16 representation and overflows to $\infty$, with both `overflow` and `inexact` set. The two ties are more interesting. In binary64, `0x3ff0000010000000` is $1 + 2^{-24}$, exactly halfway between the binary32 neighbours $1$ and $1 + 2^{-23}$, and ties to even picks $1$. The second word, $1 + 3 \cdot 2^{-24}$, is halfway between $1 + 2^{-23}$ and $1 + 2^{-22}$. There ties to even picks the latter, $4194305 \cdot 2^{-22}$, whose fraction field is even. In both ties, “even” refers to the retained binary32 significand. Measured in steps of $2^{-23}$, the first input has coefficient $2^{23}+\tfrac12$, so it rounds down to the even integer $2^{23}$, and the second has coefficient $2^{23}+\tfrac32$, so it rounds up to $2^{23}+2$. You can't see that parity in the decimal values on either side, but the destination grid shows it.

The two Lean examples are the general theorems at two named formats. [[FloatLib.Floats.Formats.BinaryInterchange.Model.cast_eq_roundAt]] says that a finite cast between IEEE descriptors whose result is finite is one nearest-even rounding in the destination. [[FloatLib.Floats.Formats.BinaryInterchange.Model.cast_exact_of_gridExtension]] says the cast is exact when the destination has at least as many fraction bits and a subnormal exponent at least as low, which is what "the destination grid contains the source grid" means. The four `by decide` calls check the two IEEE contracts and those two inequalities. Equal exponent widths aren't required, so the theorem covers binary16 to binary32, binary32 to binary64, and binary64 to binary128 alike. The field-copy case is [[FloatLib.Floats.Formats.BinaryInterchange.Model.cast_exact_of_compatibleWidening]]. The identity case, sign of zero included, is `cast_self_of_finite`, and `abs_toReal_cast_sub_le` bounds a rounded narrowing by half a destination ulp. In `cast_exact_of_gridExtension`, output finiteness stays a hypothesis because its conditions allow different exponent ranges, while compatible field widening preserves finiteness by itself, so its theorem needs only a finite source.

The `hout` hypothesis excludes overflow for a reason: cast 70000 to binary16 and the delivered infinity has `toReal` equal to zero. But `roundAt` rounds on a real grid with no upper exponent cutoff, so equating the two would erase the overflow. The status-bearing result above describes that case, and the finite-result theorem describes the cases where decoding does recover the rounded real number.

## Integers and text

Our [integer conversion modules](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/BinaryInterchange/DType) convert between binary-interchange values and fixed-width two's-complement integers. `ExecDType.intToFloat` decodes a `FixedInt width` exactly to a dyadic and rounds it once into the destination, and under `status := true` it reports the usual five flags. The theorem `intToFloat_nearest_eq_round` says that a finite nearest-even result is `roundAt` of the integer, the same equation the arithmetic satisfies.

In the other direction, `ExecDType.floatToInt` rounds a finite value to an unbounded integer in the requested direction, and it succeeds only when that integer fits the signed width. It reports inexact when a fraction was discarded, and an infinity or NaN source comes back as a failure that keeps its class. Our [integer conversion theorem](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/DType/Semantics.lean) `floatToInt_of_exactValue_eq_finite_of_inRange` and its out-of-range companion pin down the two finite cases. For an invalid conversion the API reports a failure and doesn't pick some fixed integer result.

```lean
open FloatLib.Numerics.Representations

#eval (ExecDType.floatToInt (width := 8) (ExecFloat.Binary.toModel piWord) (mode := .nearest)).value?.map FixedInt.toInt
-- some 3
#eval (ExecDType.floatToInt (width := 8) (ExecFloat.Binary.toModel (300 : Binary32)) (mode := .nearest))
-- FloatLib.Floats.ExecFloat.ConversionOutcome.failure (FloatLib.Floats.ExecFloat.ConversionFailure.outOfRange)
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

Rounding the nearest binary32 value to $\pi$ gives the 8-bit integer $3$ with inexact set, while the integer $300$ doesn't fit in eight signed bits and fails with `outOfRange`. Binary16 can't represent $2049$, because its precision covers every integer only up to $2048$, so nearest-even returns $2048$ and flags inexact.

### Parsing and printing

Parsing `0.1` into binary32 gives $13421773 \cdot 2^{-27}$, the familiar `0x3dcccccd`. Printing that value exactly takes 27 digits after the point, because the stored binary fraction is slightly larger than $1/10$. `#eval` and `toString` print a decimal that parses back to the same value, normally the shortest one, here `0.1`. A value prints exactly if its exact decimal has no more significant digits than the format needs to identify a value, which is nine for binary32. So `16777216` stays `16777216` and `3.75` stays `3.75`. `ExecFloat.Binary.format` writes the other forms through its `style` option. With `.exact` it gives the exact decimal expansion, and with `.hex` an exact hexadecimal significand and binary exponent.

`ExecFloat.Binary.parse` accepts decimal, hexadecimal, and the compact dyadic syntax. We read the exact value and round once into the destination. Nearest-even is the default, and `mode := .towardZero` selects another direction. Set `status := true` to return the five exception flags with the value, and `limits := some {}` to check input size and exponent bounds before conversion. A record such as `some { maxBytes := 128 }` changes one bound and keeps the other's default, and we prove that accepted input keeps the same value and flags. Malformed input gives a parse error. Special spellings include infinity and signed quiet or signaling NaNs, and the diagnostic NaN suffix records the complete fraction field.

```lean
#eval (ExecFloat.Binary.parse "0.1" (mode := .towardZero) :
    Except Model.ParseError Binary32)
-- Except.ok 0.099999994
#eval (ExecFloat.Binary.parse "-0" (limits := some { maxBytes := 128 }) :
    Except Model.ParseError Binary32).map
      (fun value => ExecFloat.Binary.format value (style := .fixed 3))
-- Except.ok "-0.000"
#eval (ExecFloat.Binary.parse "0.1" (status := true)).map fun outcome =>
    ((outcome.value : Binary32), outcome.status.inexact, outcome.ternary)
-- Except.ok (0.1, true, Ordering.gt)
#eval ExecFloat.Binary.format (12.5 : Binary32) (style := .fixed 3)
-- "12.500"
#eval ExecFloat.Binary.format (12.5 : Binary32) (style := .scientific 3)
-- "1.250e1"
#eval (0.1 : Binary64) + 0.2
-- 0.30000000000000004
```

For fixed and scientific notation, `style := .fixed places` and `style := .scientific places` take the number of digits after the decimal point. Both keep trailing zeros and round nearest-even. Pass `mode` to select any other rounding direction, and `status := true` to report inexactness. Our proofs connect the actual printed characters to the rounded decimal value, and with nearest-even rounding the error is at most half the last requested decimal unit. For a fixed number of significant digits, `style := .significant digits` and `style := .hex (.significant digits)` accept any positive count and round in `mode`. The exponent of the output stays unbounded. We prove the requested digit count, nearest-even midpoint selection, the half-grid error bound, directed output inequalities in both radices, and inexactness exactly when the printed value changes. Decimal interchange shares the positional scanner, digit-grid selection, and rounding algorithms. To use a parsed binary64 value as Lean's native `Float`, map `ExecFloat.Binary.toFloat` over the result.

Our round-trip theorems recover every finite IEEE word, including the sign of zero. Hexadecimal output works with every input rounding mode, while exact decimal output and the shortest display have nearest-even input theorems. For the display, the round trip holds by construction. Its digits come from exact integer arithmetic on the interval of decimals that round to the value. They're printed only after the parser's own conversion has returned the value, with the exact expansion as the fallback. In the tests we check the round trip for every binary16 and bfloat16 word, and for every display that isn't exact we find no shorter decimal that also reads back.

<a id="formats-encodings-and-their-meaning"></a>

## From executable arithmetic to real rounding

To reason about any of the six arithmetic operations, we first connect the kernel a program runs to the format's reference definition. The theorems [[FloatLib.Floats.ExecFloat.Proof.add_eq_spec]], [[FloatLib.Floats.ExecFloat.Proof.sub_eq_spec]], [[FloatLib.Floats.ExecFloat.Proof.mul_eq_spec]], [[FloatLib.Floats.ExecFloat.Proof.div_eq_spec]], [[FloatLib.Floats.ExecFloat.Proof.sqrt_eq_spec]], and [[FloatLib.Floats.ExecFloat.Proof.fma_eq_spec]] give that equality, whichever fixed-word or limb kernel the planner selected. They hold for every `FloatFormat` with no IEEE hypothesis, because the reference definitions follow the descriptor's own exceptional-value policy, and [Chapter 16](#/chapter/backends-and-the-planner) explains the proofs required of each kernel. Our configured interface exposes the same choices, including the `mode` and `status` options of [[FloatLib.Floats.ExecFloat.Binary.add]] and casts through exact signed rationals. Its [configured word kernels](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/Core/Runtime.lean) adapt software arithmetic to the chosen format and carrier, with certificates such as [[FloatLib.Floats.Formats.BinaryInterchange.Configured.Backend.wordAdd_eq_spec]]. To call the processor's floating-point instructions you need the [unchecked native-FPU import](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/NativeFPU/Unchecked.lean) that [chapter 17](#/chapter/performance/host-arithmetic-as-a-reference) discusses, and certified modules don't import it.

Then we relate the reference definitions to real-number operations under `fmt.isIEEE = true`, as [chapter 06](#/chapter/the-numerical-models) explains. [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt]] is Flocq-style nearest-even rounding onto the grid with precision $w_f + 1$ and gradual underflow at $e_{\min} - w_f$. That grid has no upper exponent bound, so the theorem has to require a finite result to exclude overflow.

For addition, subtraction, multiplication, and FMA, the rounding equations require finite operands and a finite executable result, and under those hypotheses decoding gives the exact real operation rounded once. Theorem names follow the operations: [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt]], [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_sub_eq_roundAt]], [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_mul_eq_roundAt]], and [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_fma_eq_roundAt]]. The division theorem [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_div_eq_roundAt]] also requires a nonzero divisor. For a finite square-root input, [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_sqrt_eq_roundAt]] asks that it be zero or have a clear sign bit, which admits both signed zeros. It needs no output-finiteness premise, because [[FloatLib.Floats.Formats.BinaryInterchange.Model.isFinite_sqrt_of_isFinite]] proves that a square root can't overflow. These examples expose the hypotheses at three widths. The first connects an ordinary binary32 call to its executable specification, and the next two apply real rounding equations.

```lean
example (a b : Binary32) : a + b = ExecFloat.Spec.add a b :=
  ExecFloat.Proof.add_eq_spec a b

example (x y : Model FloatFormat.binary64)
    (hx : Model.isFinite x = true) (hy : Model.isFinite y = true)
    (hout : Model.isFinite (Model.mul x y) = true) :
    Model.toReal (Model.mul x y) =
      Model.roundAt FloatFormat.binary64 (Model.toReal x * Model.toReal y) :=
  Model.toReal_mul_eq_roundAt x y (by simp) hx hy hout

example (x y z : Model FloatFormat.binary128)
    (hx : Model.isFinite x = true) (hy : Model.isFinite y = true) (hz : Model.isFinite z = true)
    (hout : Model.isFinite (Model.fma x y z) = true) :
    Model.toReal (Model.fma x y z) =
      Model.roundAt FloatFormat.binary128 (Model.toReal x * Model.toReal y + Model.toReal z) :=
  Model.toReal_fma_eq_roundAt x y z (by simp) hx hy hz hout

example (x : Model FloatFormat.binary32)
    (hx : Model.isFinite x = true) (hpos : Model.signBit x = false) :
    Model.isFinite (Model.sqrt x) = true :=
  Model.isFinite_sqrt_of_isFinite x (by simp) hx (Or.inr hpos)
```

If evaluating a result first is inconvenient, `isFinite_add_of_abs_add_le_posMaxFinite`, `isFinite_mul_of_abs_mul_le_posMaxFinite`, and `isFinite_div_of_abs_div_le_posMaxFinite` derive its finiteness from symbolic bounds on the operands. Those premises matter because `Model.toReal` assigns zero to a nonfinite word, and [Chapter 21](#/chapter/further-examples/the-result-as-a-real-number) works through the bridge from a configured value to `Model` and its real value. Once a rounding equation is established, we can apply the [general rounding theory](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/Flocq/Theory) developed in [chapter 07](#/chapter/the-mathematics-of-rounding). The half-ulp bound comes from [[FloatLib.Floats.Formats.BinaryInterchange.Model.abs_roundAt_sub_le]] and [[FloatLib.Floats.Formats.BinaryInterchange.Model.abs_toReal_add_sub_le]], and [[FloatLib.Floats.Formats.BinaryInterchange.Model.relativeError_roundAt_le_of_normal]] gives $u = 2^{-p}$ in the normal range. Exact subtraction comes from [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_sub_eq_of_sterbenz_of_same_sign]], which covers finite values of the same sign whose magnitudes lie within a factor of two, and output finiteness follows from those hypotheses.

## Comparisons and neighbouring values

Comparison is an operation of its own, with its own contract. [[FloatLib.Floats.Formats.BinaryInterchange.Model.compare]] returns `none` when either operand is a NaN and `some` ordering otherwise, so unordered comes back as a value and never as a silently false answer. The theorems `compare_eq_some_lt_iff_toReal_lt_of_isFinite` and `compare_eq_some_eq_iff_toReal_eq_of_isFinite` identify the finite comparison with real order. The infinities are covered by `compare_eq_some_lt_iff_toEReal_lt`, and `compare_zero_false_true` records that the two zeros compare equal. Below we apply the finite comparison theorem at binary16, and the binary32 evaluations show equal zeros and an unordered NaN.

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

For minimum and maximum we implement the IEEE 754-2019 operations [[FloatLib.Floats.Formats.BinaryInterchange.Model.minimum]] and `maximum`. They treat $-0$ as below $+0$ and agree with the real `min` on finite inputs, as `minimum_posZero_negZero_of_supportsSignedZero` and `toReal_minimum_eq_min_of_isFinite` prove. The 2019 [[FloatLib.Floats.Formats.BinaryInterchange.Model.minimumNumber]] and `maximumNumber` skip a NaN operand, and the deprecated 2008 [[FloatLib.Floats.Formats.BinaryInterchange.Model.minNum]] and `maxNum` differ from them on signaling NaNs.

Other scalar operations have their own status and finite-value theorems, and each takes the `status := true` option. They are `remainder`, `roundToIntegral`, `scale`, `binaryExponent`, `nextUp`, and `nextDown`. For an IEEE descriptor, finite operands and a nonzero divisor, `remainder_exact` proves that the remainder is exactly representable. Scaling, the binary form of IEEE's `scaleB`, multiplies by $2^k$ and rounds once. The integer form `binaryExponentInt` returns $\lfloor\log_2|x|\rfloor$ exactly, with IEEE `logB` exception handling. The same-format convenience operation `binaryExponent` rounds that integer into the source format, and small formats can lose accuracy in this extra rounding.

For an exact normalized rational, [[FloatLib.Floats.Formats.BinaryInterchange.Model.toEReal_ofRat_down_le]] and [[FloatLib.Floats.Formats.BinaryInterchange.Model.le_toEReal_ofRat_up]] bound the input between its downward and upward conversions. Their extended-real conclusions admit overflow to infinity and include zero and subnormals without a nonzero-input premise.

Truncation toward zero can't increase the input magnitude. That's how IEEE 754-2019 defines the direction in §4.3.2 and the integral operation in §5.9 [@ieee754_2019], so [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_roundToIntegral_towardZero_of_isFinite]] needs only a finite input and the IEEE encoding convention. It computes floor for nonnegative values and ceiling for negative values. Its companion finiteness and overflow theorems apply even when a custom descriptor has more fraction bits than its upper exponent bound. Other integral rounding directions keep the range condition `fmt.fracWidth ≤ fmt.maxNormalExponent`, which IEEE 754's standard binary interchange formats satisfy. Below is a six-bit descriptor with two exponent bits and three fraction bits. It follows the IEEE encoding convention but isn't one of IEEE 754's defined interchange formats. Its largest finite positive value is $3.75$. Truncating it delivers three, but rounding to the nearest integer would need four, which overflows this descriptor :)

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

Quiet and signaling comparisons share one truth table across binary and decimal formats. They agree about order and differ on invalid: a quiet comparison raises it for a signaling NaN, and a signaling comparison raises it for either kind of NaN. Sometimes you want to sort representations, NaNs included. `totalOrder` places negative zero before positive zero and distinguishes NaN signs, signaling classes, and payloads, and `totalOrderMag` compares the corresponding magnitudes. Their proofs cover every binary descriptor and connect the executable comparison to an exact ordering specification, and neither operation raises an exception. Decimal operations also have to choose a representation within a cohort, and [Decimal arithmetic](#/chapter/decimal-arithmetic) follows that choice from exact arithmetic to encoded words. [Elementary functions](#/chapter/elementary-functions) develops powers, roots, and the different accuracy guarantees available for transcendental calls.