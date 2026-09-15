---
number: "08"
slug: ieee-binary-formats
title: "IEEE binary and decimal formats"
summary: "Binary formats share one arithmetic model, while decimal formats preserve a quantum that distinguishes representations of equal values."
phases: [ieee-formats, binary-format, binary-arithmetic, status-and-directed]
---

Binary16, binary32, binary64, and binary128 divide a stored word into a sign bit, a biased exponent field, and a fraction field. Increasing the exponent width extends the range; increasing the fraction width places representable values closer together. The reserved patterns keep the meanings introduced in [chapter 02](#/chapter/from-reals-to-machine-numbers): an all-ones exponent identifies infinities and NaNs, and an all-zeros exponent identifies zeros and subnormals. The arithmetic computes an exact result followed by one rounding into the chosen format.

FloatLib expresses that common structure with one descriptor, [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat]], and one bit-level model indexed by it, [[FloatLib.Floats.Formats.BinaryInterchange.Model]]. We can change the widths without rewriting the arithmetic or its proofs. The real-number theorems require a conventional IEEE descriptor and, where needed, bounds on its exponent range; their remaining hypotheses concern the operands and result. The four interchange formats, bfloat16, and custom 24-bit or 71-bit layouts all fit this model.

## One descriptor, many widths

A `FloatFormat` has four data fields: `expWidth`, `fracWidth`, `exponentBias`, and `encoding`. The encoding is a value of [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.Encoding]] and says what the reserved bit patterns mean; everything in this chapter uses `.ieee`, and the three other encodings (finite-max-NaN, finite-unsigned-zero, and fully finite) are the subject of [chapter 09](#/chapter/low-precision-formats-for-machine-learning). The structure also carries four [proof fields](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Format/Definition.lean): at least two exponent bits, at least one fraction bit, a positive bias, and a bias no larger than the largest finite exponent code. They are propositions, so they cost nothing at run time. The two width conditions default to `by decide` in the structure, and `FloatFormat.custom` defaults all four for literal arguments.

These minimums leave room for zeros, subnormals, normal numbers, infinities, and quiet NaNs. With one exponent bit the field has only two values, one reserved for zeros and subnormals and one for infinity and NaN, leaving no normal numbers. With two bits the codes 00, 01, 10, 11 become subnormals, two normal binades, and the infinity-NaN class. One fraction bit is enough to tell a quiet NaN from an infinity; signaling NaNs need at least two fraction bits. The two bias conditions ensure that the exponent code equal to the bias, used to encode $1$, exists and is finite.

The constructor `ieee` takes only the two widths and fills in the conventional bias and the `.ieee` encoding; [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.custom]] accepts any validated bias with any encoding. With $w_e$ exponent bits and $w_f$ fraction bits, the total width from `bitWidth` is $1 + w_e + w_f$, and the conventional constants are

$$
\begin{aligned}
b &= 2^{w_e - 1} - 1, &\qquad p &= w_f + 1,\\
e_{\min} &= 1 - b, &\qquad e_{\max} &= b,\\
x^{\text{norm}}_{\min} &= 2^{e_{\min}}, &\qquad x^{\text{subn}}_{\min} &= 2^{e_{\min} - w_f},\\
x_{\max} &= (2 - 2^{-w_f}) \cdot 2^{e_{\max}}.
\end{aligned}
$$

The [named layouts](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Format/Catalog.lean) have the following constants. Binary16, binary32, binary64, and binary128 are IEEE 754 interchange formats. Bfloat16 shares their encoding conventions but has its own field widths.

| Descriptor | $w_e$ | $w_f$ | bits | $b$ | $p$ | $e_{\min}$ | $e_{\max}$ | $x_{\max}$ |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.binary16]] | 5 | 10 | 16 | 15 | 11 | $-14$ | 15 | $(2 - 2^{-10}) \cdot 2^{15} = 65504$ |
| [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.bfloat16]] | 8 | 7 | 16 | 127 | 8 | $-126$ | 127 | $(2 - 2^{-7}) \cdot 2^{127}$ |
| [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.binary32]] | 8 | 23 | 32 | 127 | 24 | $-126$ | 127 | $(2 - 2^{-23}) \cdot 2^{127}$ |
| [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.binary64]] | 11 | 52 | 64 | 1023 | 53 | $-1022$ | 1023 | $(2 - 2^{-52}) \cdot 2^{1023}$ |
| [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.binary128]] | 15 | 112 | 128 | 16383 | 113 | $-16382$ | 16383 | $(2 - 2^{-112}) \cdot 2^{16383}$ |

With every bit drawn at the same width in [Figure 8.1](#/chapter/ieee-binary-formats/figure-ch12-bit-layouts), we can compare how much storage each field takes. The exponent field ranges from five bits to fifteen, the fraction from seven to one hundred and twelve, and the sign bit stays one.

![The five layouts of the table drawn to one scale, sign bit, exponent field, and fraction field from left to right, with the width of each field in bits](assets/ch12-bit-layouts.png "Five binary layouts on the same bit scale. Wider formats devote additional bits to both exponent range and precision.")

The same file defines the wider `binary256` layout with 19 exponent and 236 fraction bits. We can read the constants in the table straight from the descriptors:

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

The last pair is $e_{\max}$ and the exponent of the least subnormal, $e_{\min} - w_f = -16382 - 112 = -16494$, for binary128. In [Figure 8.2](#/chapter/ieee-binary-formats/figure-ch12-range-precision), the three boundaries of each format, the least subnormal, the least normal, and the largest finite value, share one logarithmic axis. Beside them is the number of decimal digits the precision $p$ amounts to, $p \log_{10} 2$. Look especially at the two sixteen-bit formats: bfloat16 reaches binary32's range with fewer digits than binary16.

![The least subnormal, least normal, and largest finite value of the five formats on one logarithmic axis, with the decimal digits of precision each carries](assets/ch12-range-precision.png "Finite range and precision of five binary formats. The range axis distinguishes the least subnormal from the least normal value; its extreme ends use a compressed scale.")

The predicate [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.isIEEE]] holds when a descriptor has the `.ieee` encoding and the conventional bias $2^{w_e-1}-1$. It appears in nearly every theorem below as the hypothesis `hfmt : fmt.isIEEE = true`, and the catalog provides `simp` lemmas such as `isIEEE_binary32` so that `by simp` discharges it for the named formats. The condition is a hypothesis rather than a type index: the executable operations are meaningful for every encoding, while the real-number theorems use the IEEE reading of the reserved patterns.

## The same value in five layouts

The model type `Model fmt` stores exactly `fmt.bitWidth` bits. The helper below prints their natural-number value in hexadecimal, without leading zeroes. We add one to itself in each format and print the result:

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

Every result encodes two: sign zero, biased exponent $b + 1$, fraction zero. Binary16 and bfloat16 agree on `0x4000` even though their field boundaries differ, because $b + 1$ is a one followed by zeros in both a five-bit and an eight-bit field. The addition that produced these words is the same Lean definition, [[FloatLib.Floats.Formats.BinaryInterchange.Model.add]], applied at five descriptors.

## Reading a word

A stored word $W$ of width $1 + w_e + w_f$ splits into the sign $s$, the biased exponent $E$, and the fraction $F$:

$$
s = \lfloor W / 2^{w_e + w_f} \rfloor, \qquad
E = \lfloor W / 2^{w_f} \rfloor \bmod 2^{w_e}, \qquad
F = W \bmod 2^{w_f}.
$$

When $1 \le E \le 2^{w_e} - 2$ the word is normal and denotes $(-1)^s (1 + F/2^{w_f}) \cdot 2^{E - b}$; the leading one is implicit, which is where the extra bit of precision $p = w_f + 1$ comes from. When $E = 0$ and $F \ne 0$ the word is subnormal and denotes $(-1)^s F \cdot 2^{e_{\min} - w_f}$ with no implicit bit, so the representable values continue in equal steps down to $\pm 2^{e_{\min} - w_f}$ instead of stopping at $2^{e_{\min}}$. When $E = 0$ and $F = 0$ the word is a signed zero. When $E = 2^{w_e} - 1$ the word is an infinity if $F = 0$ and a NaN otherwise.

[[FloatLib.Floats.Formats.BinaryInterchange.Model.toDyadic?]] decodes a finite word to an exact dyadic rational without normalizing it. A normal word decodes to significand $2^{w_f} + F$ and exponent $E - b - w_f$, a subnormal word to significand $F$ and exponent $e_{\min} - w_f$. Keeping that form makes the fields visible in the decoded value: the fraction supplies the low significand bits, and the exponent accounts for their scale. The [IEEE decoding rule](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Dyadic/Core.lean) is `ieeeToDyadic?`; the [general decoder](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Dyadic/Decode.lean) `toDyadic?` dispatches to it for IEEE descriptors and reads the declared bias for the other encodings.

Application code normally uses `ExecFloat.Binary`. Given the two widths, it builds a descriptor with the `.ieee` encoding and conventional bias as defaults, then selects its storage and kernels statically ([chapter 14](#/chapter/backends-and-the-planner)). Its `toModel` conversion lets us apply the model theorems to these executable values. We abbreviate the three configured types used here, then read the nearest binary32 value to $\pi$:

```lean
abbrev Binary16 := ExecFloat.Binary (exponentBits := 5) (fractionBits := 10)
abbrev Binary32 := ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)
abbrev Binary64 := ExecFloat.Binary (exponentBits := 11) (fractionBits := 52)

def piWord : Binary32 := ExecFloat.Binary.ofBits32 0x40490fdb

#eval piWord
-- 13176795 * 2^-22
#eval ExecFloat.Binary.toRat? piWord
-- some (13176795 / 4194304)

def leastSubnormal : Binary32 := ExecFloat.Binary.ofBits32 0x00000001

#eval (ExecFloat.Binary.isSubnormal leastSubnormal, leastSubnormal)
-- (true, 1 * 2^-149)
```

The word `0x40490fdb` has $s = 0$, $E = 128$, and $F = 4788187$, so the significand is $2^{23} + 4788187 = 13176795$ and the exponent is $128 - 127 - 23 = -22$. The value $13176795 \cdot 2^{-22} = 3.14159274\ldots$ differs from $\pi$ by less than half of the spacing $2^{-22}$ in that binade, as correct rounding demands. The word `0x00000001` is the least positive subnormal, $2^{-149} = 2^{e_{\min} - w_f}$ for binary32. [[FloatLib.Floats.ExecFloat.Binary.ofBits32]] and [[FloatLib.Floats.ExecFloat.Binary.toBits32]] transport the 32-bit word exactly in both directions, NaN payload included; the conversions to Lean's native `Float32` in the same file canonicalize NaNs, which is why we keep the two boundaries separate ([chapter 15](#/chapter/performance/comparing-with-leans-native-floats)).

At the boundary between subnormal and normal, the two decoding formulas meet without a gap. We can see it by incrementing the largest positive subnormal word twice:

| Binary32 word | Exponent field | Fraction field | Exact value |
| --- | --- | --- | --- |
| `0x007fffff` | 0 | $2^{23}-1$ | $(2^{23}-1)\,2^{-149}$ |
| `0x00800000` | 1 | 0 | $2^{23}\,2^{-149}$ |
| `0x00800001` | 1 | 1 | $(2^{23}+1)\,2^{-149}$ |

The carry out of the fraction changes the exponent field from zero to one. At the same time, the decoder restores the implicit leading bit. Both decoder branches use the scale $2^{-149}$ here, so the coefficient simply advances from 8388607 to 8388608. The second value is the least normal, $2^{-126}$; the next normal is still only $2^{-149}$ away. A change in classification does not itself change the spacing.

As subnormal values get smaller, the absolute step stays the same and fewer significant bits remain. At the least normal, the step divided by the value is $2^{-23}$. At the least positive subnormal it is 1: the next positive value is twice as large. This is the small interval between the open circle and the square in the range figure, a fixed grid whose relative precision deteriorates toward zero. The exponent is fixed in this region, so a smaller value must use a smaller coefficient. An absolute half-step error bound can still describe rounding there; a uniform normal-range relative error bound cannot.

We can inspect this value through the three readings from [chapter 06](#/chapter/the-numerical-models). For exact rational arithmetic, `toRat?` gives the stored rational and returns `none` for infinities and NaNs. When the exceptional details matter, [[FloatLib.Floats.Formats.BinaryInterchange.Model.exactValue]] returns an [[FloatLib.Floats.Formats.BinaryInterchange.Model.ExactValue]] that keeps the sign of zero, the sign of an infinity, and the sign, signaling class, and payload of a NaN. For real-number proofs, [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal]] is total and sends NaNs and infinities to $0$. A map into $\mathbb{R}$ also necessarily sends both zeros to $0$, so signed-zero facts are stated on the bits instead.

<a id="exceptional-classes-and-how-nans-travel"></a>

## NaN propagation and signed zero

The [classifiers](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Model/Carrier.lean) [[FloatLib.Floats.Formats.BinaryInterchange.Model.isZero]], `isSubnormal`, [[FloatLib.Floats.Formats.BinaryInterchange.Model.isFinite]], [[FloatLib.Floats.Formats.BinaryInterchange.Model.isInf]], [[FloatLib.Floats.Formats.BinaryInterchange.Model.isNaN]], `isSNaN`, and `isQNaN` test the stored fields. All but `isSubnormal` are defined by a case split on the encoding, and under `.ieee` they are the field tests above; `isSubnormal` is the same field test, zero exponent and nonzero fraction, in every encoding. The quiet bit is the most significant fraction bit: a NaN with that bit set is quiet and propagates silently, a NaN with it clear is signaling and raises the invalid flag when it is an operand.

`classify` gathers these answers into the ten IEEE classes. Its semantic theorem reads the complete exact value: a finite nonzero magnitude below $2^{e_{\min}}$ is subnormal, and one at or above that threshold is normal. The sign distinguishes the two versions of each finite class and of infinity; NaNs are quiet or signaling. The same proof applies to every binary descriptor using its declared bias and encoding policy, and the configured API inherits it through its codec.

The standard leaves NaN selection to the implementation. FloatLib uses two deterministic rules. When an operation is invalid and no operand is a NaN, `invalidResult` returns the format's `canonicalNaN`: positive sign, all-ones exponent, and only the quiet bit set. When at least one operand is a NaN, `chooseNaN2` prefers a signaling operand over a quiet one and otherwise the left operand over the right. It then sets the quiet bit and preserves the remaining payload. Selection therefore retains the signaling operand's payload when one is present; otherwise operand order resolves the choice without comparing payloads. The Arm architecture's default NaN propagation makes the same two choices.

The [independent comparisons](#/chapter/external-validation) check NaN class and signaling behaviour, but do not independently validate this choice of payload. At binary32, an invalid subtraction and an addition with a signaling NaN produce different payloads. The two zero encodings also remain distinguishable:

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

In `ExactValue.nan false false 4194304` the three fields are the sign, the signaling bit, and the payload. The payload $4194304 = 2^{22}$ is the quiet bit alone, the canonical NaN produced by $\infty - \infty$. The second result shows the signaling NaN `0x7f800001` quieted: its payload $4194305 = 2^{22} + 1$ keeps the original low bit, and the middle `false` records that the result is no longer signaling. The two zeros compare equal under the `==` of the configured type, which is IEEE numerical comparison, while their words differ; dividing one by negative zero gives $-\infty$, so the sign is observable in arithmetic as well as in casts and reductions.

## Status flags

IEEE 754 asks each operation to report five exceptions: invalid operation, division by zero, overflow, underflow, and inexact. We represent them as the five Booleans of [[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEEStatus]], and a status-bearing operation returns an [[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEEOutcome]], the value paired with its flags. [[FloatLib.Floats.Formats.BinaryInterchange.Model.addWithStatus]] and its siblings for subtraction, multiplication, and fused multiply-add compute the exact dyadic result, call the value-only operation, and derive the flags from the pair with [[FloatLib.Floats.Formats.BinaryInterchange.Model.dyadicRoundingStatus]].

Division and square root determine their flags without forming an exact dyadic result. `divWithStatus` rounds the exact rational quotient and classifies it with `rationalRoundingStatusScaled`. Square root never forms an exact result: `sqrtWithStatus` decides inexact with `dyadicSquareRootIsExact` and tininess by [comparing the radicand with the squared underflow boundary](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Status/Runtime.lean), so no approximate root enters the test. The theorem [[FloatLib.Floats.Formats.BinaryInterchange.Model.addWithStatus_value]] and its five siblings state that the delivered value is the value-only result, so the two APIs cannot disagree.

Overflow is decided on the result rounded with an unbounded exponent range. Tininess is detected after rounding, and underflow is raised exactly when the result is both tiny and inexact. Thus an exact subnormal result raises neither flag, as the examples in [chapter 06](#/chapter/the-numerical-models) show. Invalid and division by zero are decided from the operand classes.

On the configured type the operations take the rounding direction as a named argument and return the value paired with its flags, so application code reads a flag as a field and never inspects a bit pattern:

```lean
def largest : Binary32 := ExecFloat.Binary.maxFinite false

#eval ExecFloat.Binary.divWithStatus (1 : Binary32) 0 (rounding := .nearestEven)
-- (inf, { invalid := false, divideByZero := true, overflow := false, underflow := false, inexact := false })
#eval ExecFloat.Binary.divWithStatus (0 : Binary32) 0 (rounding := .nearestEven)
-- (nan, { invalid := true, divideByZero := false, overflow := false, underflow := false, inexact := false })
#eval ExecFloat.Binary.mulWithStatus largest 2 (rounding := .nearestEven)
-- (inf, { invalid := false, divideByZero := false, overflow := true, underflow := false, inexact := true })
#eval ExecFloat.Binary.mulWithStatus leastSubnormal 0.5 (rounding := .nearestEven)
-- (0, { invalid := false, divideByZero := false, overflow := false, underflow := true, inexact := true })
#eval ExecFloat.Binary.divWithStatus (1 : Binary32) 3 (rounding := .nearestEven)
-- (11184811 * 2^-25, { invalid := false, divideByZero := false, overflow := false, underflow := false, inexact := true })
#eval ExecFloat.Binary.sqrtWithStatus (-4 : Binary32) (rounding := .nearestEven)
-- (nan, { invalid := true, divideByZero := false, overflow := false, underflow := false, inexact := false })

example (x : Model FloatFormat.binary64) (mode : Model.IEEERoundingMode)
    (hnan : Model.isNaN x = false) (hneg : Model.signBit x = true)
    (hnz : Model.isZero x = false) :
    (Model.sqrtWithStatus x mode).status.invalid = true :=
  Model.sqrtWithStatus_invalid_of_negative_nonzero hnan hneg hnz
```

The first two lines show the standard's distinction between division by zero and invalid: $1/0$ with a positive zero denominator returns $\infty$ with the divide-by-zero flag, while $0/0$ returns a NaN with the invalid flag. Overflow always comes with inexact. The product $2^{-149} \cdot 0.5$ lies exactly halfway between $0$ and the least subnormal, ties to even selects $0$, and since the result is both tiny and inexact the underflow flag is raised.

The flag theorems state the conditions for each exception: [[FloatLib.Floats.Formats.BinaryInterchange.Model.divWithStatus_divideByZero]] says the flag is set exactly when a finite nonzero numerator meets a finite zero denominator, [[FloatLib.Floats.Formats.BinaryInterchange.Model.sqrtWithStatus_invalid]] says invalid is set exactly for a signaling NaN or a negative nonzero non-NaN input, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.dyadicRoundingStatus_overflow]] says the overflow flag is set exactly when rounding the exact result crosses the format's overflow threshold or the delivered result is an infinity; `dyadicRoundingStatus_overflow_of_isFinite` drops the second case once the result is known to be finite. The example above applies a corollary of the square-root theorem at binary64, for every rounding direction at once.

## Directed rounding

The type [[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEERoundingMode]] has the four IEEE attributes: `nearestEven`, `towardZero`, `towardPositiveInfinity`, and `towardNegativeInfinity`. Ordinary `+`, `-`, `*`, and `/` on a configured type round to nearest even, as the default arithmetic convention. The named operations [[FloatLib.Floats.ExecFloat.Binary.add]], `sub`, `mul`, [[FloatLib.Floats.ExecFloat.Binary.div]], `fma`, and `sqrt` take the direction as a required argument, and after `open scoped FloatLib.IEEERounding` the two infinite directions may be written `+∞` and `-∞`. The notation is scoped to keep it separate from the meaning of $\infty$ in a file about extended reals.

One third is a useful value to try: it needs rounding, but we can still locate both neighbours exactly.

```lean
open scoped FloatLib.IEEERounding

def third (rounding : Model.IEEERoundingMode) : Binary32 :=
  ExecFloat.Binary.div 1 3 (rounding := rounding)

#eval third .nearestEven
-- 11184811 * 2^-25
#eval third .towardZero
-- 5592405 * 2^-24
#eval third +∞
-- 11184811 * 2^-25
#eval third -∞
-- 5592405 * 2^-24

#eval ExecFloat.Binary.add largest largest (rounding := .nearestEven)
-- inf
#eval ExecFloat.Binary.add largest largest (rounding := +∞)
-- inf
#eval ExecFloat.Binary.add largest largest (rounding := .towardZero)
-- 16777215 * 2^104
#eval ExecFloat.Binary.add largest largest (rounding := -∞)
-- 16777215 * 2^104

example (x y : Model FloatFormat.binary32)
    (hx : Model.isFinite x = true) (hy : Model.isFinite y = true) :
    Model.toEReal (Model.addDown x y) ≤ ((Model.toReal x + Model.toReal y : ℝ) : EReal) :=
  Model.toEReal_addDown_le x y (by simp) hx hy
```

One third lies between the binary32 neighbours $5592405 \cdot 2^{-24}$ below and $11184811 \cdot 2^{-25}$ above. Nearest-even and toward $+\infty$ pick the upper one, toward zero and toward $-\infty$ pick the lower one, and the last two agree because the value is positive. The overflow lines show the rule of IEEE 754-2019 Section 7.4 [@ieee754_2019] as implemented by `directedOverflow`: a direction that carries the magnitude away from zero overflows to infinity, while toward zero, or toward the infinity of the other sign, returns the largest finite value, here $16777215 \cdot 2^{104} = (2 - 2^{-23}) \cdot 2^{127}$.

A useful variation is to make the numerator in `third` negative. Before rerunning the four evaluations, work out which rounding directions should agree.

Directed operations are the basis of interval arithmetic, so their theorems are bounds rather than equations, stated in the extended reals through [[FloatLib.Floats.Formats.BinaryInterchange.Model.toEReal]] for the reason [chapter 06](#/chapter/the-numerical-models) gives: [[FloatLib.Floats.Formats.BinaryInterchange.Model.toEReal_addDown_le]] and [[FloatLib.Floats.Formats.BinaryInterchange.Model.le_toEReal_addUp]] say that `addDown`, addition toward $-\infty$, never exceeds the exact real sum and that `addUp`, addition toward $+\infty$, never falls below it, with the same shape for the [other directed operations](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/BinaryInterchange/DirectedSemantics): subtraction, multiplication, division, and square root.

## Casting between widths

[[FloatLib.Floats.Formats.BinaryInterchange.Model.cast]] is the descriptor-level operation: it converts a `Model src` into a `Model dst`. Its docstring is the specification. A finite source is decoded to its exact dyadic and packed into the destination with nearest-even rounding, which may overflow to a signed infinity or land in the subnormal range. An infinity becomes the same-sign infinity when the destination has one. A NaN cast to its own format is quieted with its payload kept, and a NaN cast to a different format becomes the destination's canonical NaN. We do not remap payloads across formats: the standard only recommends preserving a payload through a widen-and-narrow round trip (Section 6.2.3 of [@ieee754_2019]) and gives no rule for the bits themselves. We chose canonicalization so callers have one documented result when the source and destination payload widths differ. A finite value cast to its own format comes back unchanged. When the exponent width, bias, and encoding agree and the fraction only widens, the cast takes the field-copy path `widenExact`, which shifts the fraction into the wider field without decoding.

The configured API spells a cast as `value.cast (target := …)` and returns a `ConversionOutcome`, a success carrying the value and conversion flags or an explicit failure. It does not call `Model.cast`. It goes through the general conversion pipeline shared with posits and P3109: the source is decoded to an exact rational, mapped into the destination's exact domain, and quantized once there. The [configured conversion theorem](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/Conversion/Proof.lean) `ExecFloat.Binary.Conversion.run_default_finite` says that for a finite value this quantization is `Model.roundRat`, the same nearest-even rounding that `toReal_roundRatScaled_eq_roundAt` ties to `roundAt`, so on finite values the two paths agree.

On NaNs they follow different policies: the pipeline delivers the destination's canonical NaN even at the same format and reports it in the `mappedSpecial` flag, while `Model.cast` keeps a same-format payload. The flags differ from `IEEEStatus` because the same pipeline reaches destinations that saturate or wrap. We'll use the configured path for the evaluations, then state the guarantees about `Model.cast` underneath.

```lean
def halfUlp64 : Binary64 := ExecFloat.Binary.ofBits64 0x3ff0000010000000
def threeHalfUlp64 : Binary64 := ExecFloat.Binary.ofBits64 0x3ff0000030000000

#eval ExecFloat.Binary.toRat? halfUlp64
-- some (16777217 / 16777216)
#eval (halfUlp64.cast (target := Binary32)).value?
-- some 1
#eval (threeHalfUlp64.cast (target := Binary32)).value?
-- some 4194305 * 2^-22
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
--     mappedSpecial := false }

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

The binary64 word `0x3ff0000010000000` is $1 + 2^{-24}$, exactly halfway between the binary32 neighbours $1$ and $1 + 2^{-23}$; ties to even picks $1$. The second word, $1 + 3 \cdot 2^{-24}$, is halfway between $1 + 2^{-23}$ and $1 + 2^{-22}$, and ties to even picks the latter, $4194305 \cdot 2^{-22}$, whose fraction field is even. The largest binary16 value, 65504, widens to binary32 with every flag clear, while 70000 has no binary16 representation and overflows to $\infty$ with both `overflow` and `inexact` set.

In the two ties, “even” refers to the retained binary32 significand. Measured in steps of $2^{-23}$, the first input has coefficient $2^{23}+\tfrac12$, so it rounds down to the even integer $2^{23}$. The second has coefficient $2^{23}+\tfrac32$, so it rounds up to $2^{23}+2$. The decimal values on either side do not reveal that parity; the destination grid does.

The two examples are the general theorems at two named formats. [[FloatLib.Floats.Formats.BinaryInterchange.Model.cast_eq_roundAt]] says that a finite cast between IEEE descriptors whose result is finite is one nearest-even rounding in the destination. [[FloatLib.Floats.Formats.BinaryInterchange.Model.cast_exact_of_gridExtension]] says the cast is exact when the destination has at least as many fraction bits and a subnormal exponent at least as low, which is what "the destination grid contains the source grid" means; the four `by decide` calls check the two IEEE contracts and those two inequalities. It does not require equal exponent widths, so it covers binary16 to binary32, binary32 to binary64, and binary64 to binary128 alike. [[FloatLib.Floats.Formats.BinaryInterchange.Model.cast_exact_of_compatibleWidening]] is the field-copy case, `cast_self_of_finite` states the identity case including the sign of zero, and `abs_toReal_cast_sub_le` bounds a rounded narrowing by half a destination ulp. Output finiteness stays an explicit hypothesis in the exact-widening theorem: it is decidable on the result and lets one theorem cover the different exponent ranges.

The `hout` hypothesis also keeps an overflowing cast out of the real-valued rounding equation. For the cast of 70000 to binary16, the delivered infinity has `toReal` equal to zero, while `roundAt` rounds on a real grid with no upper exponent cutoff. Equating those two would erase the overflow. The status-bearing result above describes that case, and the finite-result theorem describes the cases where decoding really does recover the rounded real number.

## Integers and text

The [integer conversion modules](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/BinaryInterchange/DType) convert between binary-interchange values and fixed-width two's-complement integers. `ExecDType.intToFloatWithStatus` decodes a `FixedInt width` exactly to a dyadic and rounds it once into the destination with the usual five flags. `intToFloat_nearestEven_eq_round` says that a finite nearest-even result is `roundAt` of the integer, the same equation the arithmetic satisfies.

In the other direction, `ExecDType.floatToInt` rounds a finite value to an unbounded integer in the requested direction and succeeds only when that integer fits the signed width. It reports inexact when a fraction was discarded; an infinity or NaN source is an explicit failure that keeps its class. The [integer conversion theorem](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/DType/Semantics.lean) `floatToInt_of_exactValue_eq_finite_of_inRange` and its out-of-range companion state the two finite cases exactly. The API reports a failure rather than choosing a fixed integer result for an invalid conversion.

```lean
open FloatLib.Numerics.Representations

#eval (ExecDType.floatToInt (width := 8) (ExecFloat.Binary.toModel piWord) .nearestEven).value?.map FixedInt.toInt
-- some 3
#eval (ExecDType.floatToInt (width := 8) (ExecFloat.Binary.toModel (300 : Binary32)) .nearestEven)
-- FloatLib.Floats.ExecFloat.ConversionOutcome.failure (FloatLib.Floats.ExecFloat.ConversionFailure.outOfRange)
#eval let o := ExecDType.intToFloatWithStatus FloatFormat.binary16 (FixedInt.ofInt (width := 32) 2049) .nearestEven
      ((ExecFloat.Binary.ofModel o.value : Binary16), o.status.inexact)
-- (2048, true)
#eval (ExecFloat.Binary.parseNearest "0.1" : Except Model.ParseError Binary32)
-- Except.ok 13421773 * 2^-27
#eval Model.format (Model.canonicalNaN FloatFormat.binary32)
-- "nan"

example {width : Nat} (x : FixedInt width)
    (hfin : Model.isFinite (ExecDType.intToFloat FloatFormat.binary32 x .nearestEven) = true) :
    Model.toReal (ExecDType.intToFloat FloatFormat.binary32 x .nearestEven) =
      Model.roundAt FloatFormat.binary32 (FixedInt.toInt x : ℝ) :=
  ExecDType.intToFloat_nearestEven_eq_round x (by simp) hfin
```

The nearest binary32 value to $\pi$ rounds to the 8-bit integer $3$ with inexact set. The integer $300$ does not fit in eight signed bits and fails with `outOfRange`. And $2049$ has no binary16 representation: its precision covers every integer only up to $2048$, so nearest-even returns $2048$ and flags inexact.

<a id="text-you-can-read-back"></a>

### Exact and rounded text output

Parsing `0.1` into binary32 gives $13421773 \cdot 2^{-27}$, the familiar `0x3dcccccd`. Printing that value exactly takes more than one decimal digit, because the stored binary fraction is slightly larger than $1/10$. `formatDecimal` writes its exact decimal expansion; `formatHex` writes an exact hexadecimal significand and binary exponent. Ordinary `#eval` display stays compact, using the significand-times-power-of-two form seen above.

`ExecFloat.Binary.parse` and `parseNearest` accept decimal, hexadecimal, and the compact dyadic syntax. They read an exact value and round once into the destination. `parseWithStatus` also returns the five exception flags. Malformed input is an explicit parse error. Special spellings include infinity and signed quiet or signaling NaNs; the diagnostic NaN suffix records the complete fraction field.

The round-trip theorems recover every finite IEEE word, including the sign of zero: hexadecimal output works with every input rounding mode, and exact decimal output has a nearest-even input theorem. The output is exact, so these are representation guarantees rather than promises to produce a short string.

For a shorter decimal or hexadecimal string, `formatWithStatus` accepts any positive significant-digit count and a rounding direction. Its exponent remains unbounded. The proofs establish the requested digit count, nearest-even midpoint selection, the half-grid error bound, and inexactness exactly when the printed value changes. The positional scanner, digit-grid selection, and rounding algorithms are shared with decimal interchange.

## What is proved for each operation

To reason about any of the six arithmetic operations, we first connect the kernel a program runs to the format's reference definition. [[FloatLib.Floats.ExecFloat.Proof.add_eq_spec]], [[FloatLib.Floats.ExecFloat.Proof.sub_eq_spec]], [[FloatLib.Floats.ExecFloat.Proof.mul_eq_spec]], [[FloatLib.Floats.ExecFloat.Proof.div_eq_spec]], [[FloatLib.Floats.ExecFloat.Proof.sqrt_eq_spec]], and [[FloatLib.Floats.ExecFloat.Proof.fma_eq_spec]] give that equality, whichever fixed-word or limb kernel the planner selected. They hold for every `FloatFormat` with no IEEE hypothesis, because the reference definitions follow the descriptor's own exceptional-value policy. [Chapter 14](#/chapter/backends-and-the-planner) explains the proofs required of each kernel.

We can then relate the reference definitions to real-number operations under `fmt.isIEEE = true`, as explained in [chapter 06](#/chapter/the-numerical-models). [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt]] is Flocq-style nearest-even rounding onto the grid with precision $w_f + 1$ and gradual underflow at $e_{\min} - w_f$; the grid has no upper exponent bound, so the theorem must require a finite result to exclude overflow.

With that, [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt]], [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_sub_eq_roundAt]], [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_mul_eq_roundAt]], and [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_fma_eq_roundAt]] each say: for finite operands whose executable result is finite, decoding the result gives the exact real operation rounded once. [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_div_eq_roundAt]] adds the hypothesis that the divisor is not zero. [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_sqrt_eq_roundAt]] asks that the input be zero or have a clear sign bit, which admits both signed zeros, and needs no output-finiteness premise because [[FloatLib.Floats.Formats.BinaryInterchange.Model.isFinite_sqrt_of_isFinite]] proves that a square root cannot overflow. When evaluating the result first is inconvenient, the variants `isFinite_add_of_abs_add_le_posMaxFinite`, `isFinite_mul_of_abs_mul_le_posMaxFinite`, and `isFinite_div_of_abs_div_le_posMaxFinite` derive finiteness from a symbolic bound on the operands. The execution equation applies directly at binary32. The real-number examples below instantiate the rounding equations for multiplication at binary64 and fused multiply-add at binary128, and the square root finiteness lemma at binary32.

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

Once we have a rounding equation, we can reuse the error bounds from the grid theory. [[FloatLib.Floats.Formats.BinaryInterchange.Model.abs_roundAt_sub_le]] bounds nearest-even rounding by half an ulp of the input, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.abs_toReal_add_sub_le]] and its siblings transfer that bound to one finite operation. In the normal range, [[FloatLib.Floats.Formats.BinaryInterchange.Model.relativeError_roundAt_le_of_normal]] gives the relative bound $u = 2^{-p}$. Sometimes the error is zero: [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_sub_eq_of_sterbenz]] proves that two positive values within a factor of two subtract exactly, with the result's finiteness following from the hypotheses. [Chapter 07](#/chapter/the-mathematics-of-rounding) develops that theory.

Comparison is a separate operation with its own contract. [[FloatLib.Floats.Formats.BinaryInterchange.Model.compare]] returns `none` when either operand is a NaN and `some` ordering otherwise, so unordered is a value rather than a silently false answer. `compare_eq_some_lt_iff_toReal_lt_of_isFinite` and `compare_eq_some_eq_iff_toReal_eq_of_isFinite` identify the finite comparison with real order, `compare_eq_some_lt_iff_toEReal_lt` extends that to infinities, and `compare_zero_false_true` records that the two zeros compare equal. The finite comparison theorem applies at binary16; the binary32 evaluations show equal zeros and an unordered NaN.

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

For minimum and maximum we implement the IEEE 754-2019 operations [[FloatLib.Floats.Formats.BinaryInterchange.Model.minimum]] and `maximum`. They treat $-0$ as below $+0$ (`minimum_posZero_negZero_of_supportsSignedZero`) and agree with the real `min` on finite inputs (`toReal_minimum_eq_min_of_isFinite`). The 2019 [[FloatLib.Floats.Formats.BinaryInterchange.Model.minimumNumber]] and `maximumNumber` skip a NaN operand; the deprecated 2008 [[FloatLib.Floats.Formats.BinaryInterchange.Model.minNum]] and `maxNum` differ from them on signaling NaNs. The standard's remaining scalar operations are implemented with their own status and finite-value theorems: `remainderWithStatus`, whose result `remainderWithStatus_exact` proves exactly representable, `roundToIntegral`, `scaleB`, `logB`, `nextUp`, and `nextDown`.

Quiet and signaling comparisons share one truth table across binary and decimal formats. They agree about order. A quiet comparison raises invalid for a signaling NaN; a signaling comparison raises it for either kind of NaN.

Sometimes we want to sort representations, including NaNs. `totalOrder` places negative zero before positive zero and distinguishes NaN signs, signaling classes, and payloads. `totalOrderMag` compares the corresponding magnitudes. Their proofs cover every binary descriptor and connect the executable comparison to an exact ordering specification. Neither operation raises an exception. Quantum operations concern decimal representations, which we turn to next. The host-FPU path is described in [chapter 15](#/chapter/performance/comparing-with-leans-native-floats).

## Decimal interchange

With decimal, we need to keep track of more than the numerical value of a datum. The amounts $1.20 = 120 \cdot 10^{-2}$ and $1.2 = 12 \cdot 10^{-1}$ are equal as rationals, but their coefficients and exponents differ. They belong to the same *cohort*: different representations of one value. A codec that silently removes the trailing zero has changed the datum even though a rational equality test would pass.

The [decimal codec proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/DecimalInterchange/Basic.lean) establish exact datum round trips for decimal32, decimal64, and decimal128 in both binary integer decimal (BID) and densely packed decimal (DPD). BID stores the coefficient as a binary integer; DPD packs groups of decimal digits. Changing between them preserves the coefficient and its decimal exponent. It also preserves the sign of zero, infinity sign, and NaN sign, signaling bit, and payload.

The theorem `decode_transcode` states this directly: decoding a converted word in the destination encoding gives the same datum as decoding the original word in its source encoding. Thus BID $120 \cdot 10^{-2}$ becomes DPD $120 \cdot 10^{-2}$, with the exponent still $-2$. The conversion does not normalize it to $12 \cdot 10^{-1}$.

Some bit patterns are redundant. Every word decodes to a valid datum, but encoding that datum again returns its canonical word, as `Encoding.encode?_decode` proves. Converting to the other encoding and back can therefore change the bits while preserving every component of the datum. This is different from rounding: `encode?` rejects a datum that does not fit the destination rather than rounding it to a nearby one.

The three standard formats are presets of one descriptor. A layout chooses the number of declets, the exponent continuation width, and the exponent bias; its precision is three digits per declet plus one leading digit. The algorithms and codec proofs also work for custom layouts with arbitrary bias. A theorem that needs quantum zero to be available says so explicitly. Custom layouts let us study other choices of precision and range; the IEEE names still refer to their specified parameters.

<a id="arithmetic-keeps-track-of-the-cohort"></a>

### Arithmetic and preferred exponents

The [decimal arithmetic API](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/DecimalInterchange/Arithmetic/Basic.lean) provides addition, subtraction, multiplication, division, fused multiply-add, and square root for decimal32, decimal64, and decimal128. The operations consume decoded `Datum` values and return an `Outcome`, pairing the result with five exception flags. BID or DPD is chosen when reading or writing the bits. All six operations accept the five decimal rounding modes: nearest with ties to even or away, toward zero, toward positive infinity, and toward negative infinity.

We can see the preferred exponent at work in $1.20+0.30$. Both operands have quantum exponent $-2$, so their exact sum is

$$
(120+30)\cdot10^{-2}=150\cdot10^{-2}.
$$

The preferred exponent for addition is the smaller input exponent, here $-2$. The runtime therefore returns $1.50$, preserving that exponent, with no exception flags. Multiplication adds the input exponents: $1.2\cdot3.0$ has preferred exponent $-2$ and returns $3.60$. Removing a trailing zero would preserve each numerical result but change its cohort member. `preferredCohort` moves toward the preferred exponent by removing only exact trailing coefficient zeros, within the destination's limits.

When precision is insufficient, the rounding mode decides the numerical result first. Decimal32 has seven significant digits. The exact sum $1.000000+0.0000005=1.0000005$ lies halfway between $1.000000$ and $1.000001$. Nearest-even chooses the former because coefficient 1000000 is even; nearest-away chooses the latter. Both results report inexact. Finite addition, subtraction, multiplication, division, and FMA form the exact rational expression before this projection. FMA therefore never rounds or signals overflow on its intermediate product alone.

Square root uses an integer square root to locate adjacent candidates, then compares the radicand with their squared midpoint. This decides the rounding without approximating the real root. Its preferred exponent is the floor of half the input exponent. Square root preserves negative zero, while a negative nonzero input returns a quiet NaN and raises invalid.

The [arithmetic proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/DecimalInterchange/Arithmetic/Proof.lean) establish destination validity for the rational operations; the [square-root proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/DecimalInterchange/Sqrt/Proof.lean) do so for square root. With finite operands and no overflow, the nearest-mode error is at most half the selected decimal grid step; division requires a nonzero denominator and square root a nonnegative input. Directed-rounding theorems place the result on the required side of the exact value, and midpoint theorems resolve ties. Every representable rational projects to its exact numerical value. The inexactness theorems detect a numerical change, so choosing another cohort member does not itself raise inexact.

Signs and flags distinguish cases that rational equality cannot. Exact cancellation in $1.20-1.20$ returns a zero with exponent $-2$: negative under rounding toward negative infinity, positive under the other four modes. A signaling NaN raises invalid and is quieted; the first NaN operand supplies the sign and payload when that payload fits the destination. The five returned flags are invalid, divide-by-zero, overflow, underflow, and inexact. Decimal tininess is tested **before rounding**, and underflow requires both a tiny exact result and inexactness. The binary kernels earlier in this chapter test tininess after rounding.

Cohort selection has a stronger guarantee than preserving the numerical value. For an exact result, the projection and square-root theorems compare its exponent with every valid representation of that value and prove that it is closest to the preferred exponent. An inexact finite result uses the smallest quantum exponent in its cohort, including when the exact square root is irrational. The [preferred-cohort proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/DecimalInterchange/Projection/Cohort.lean), [minimal-quantum proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/DecimalInterchange/Projection/Minimal.lean), and their square-root counterparts establish these results.

<a id="remembering-exceptions-across-a-calculation"></a>

### Accumulating exception flags

An `Outcome` tells us what happened in one operation. A longer calculation needs to remember earlier exceptions too. Suppose decimal32 division rounds $1/3$ to $0.3333333$, raising inexact, and the next operation divides $1$ by zero. The second operation raises divide-by-zero; it must not erase the earlier inexact flag.

`Environment.run` supplies the current rounding direction and accumulates the returned flags. The environment is an ordinary Lean value, so a function's inputs and outputs show where that state goes. `saveAllFlags`, `testFlags`, `testSavedFlags`, `lowerFlags`, `raiseFlags`, and `restoreFlags` support selected groups of exceptions. Restoring a saved clear flag clears it; flags outside the group stay as they were.

`Environment.withRounding` changes rounding within one computation. Rounding $1/3$ toward positive infinity produces $0.3333334$; on return, the caller's rounding direction is restored and the new inexact flag survives. The proofs characterize every flag after an operation, clearing, or restoration, and establish that grouping operations does not change the accumulated flags.

<a id="choosing-a-decimal-grid"></a>

### Quantization and integral rounding

`quantize` requests a particular exponent rather than allowing the operation to choose one. Quantizing $1.235$ to the exponent of $0.01$ gives $1.24$ under nearest-even: the adjacent coefficients are 123 and 124, and 124 is even. The result has exponent $-2$ and raises inexact. Quantizing $1.2$ to the same exponent instead gives $1.20$ without inexact, because the numerical value has not changed.

The quantize proofs fix the successful result's quantum, bound nearest rounding by half that grid step, and characterize inexactness as a numerical change. Directed bounds and an error below one grid step cover the other modes. If the rounded coefficient cannot fit at the requested exponent, quantize raises invalid; it never raises overflow, underflow, or divide-by-zero. Even an inexact subnormal quantize result therefore has no underflow flag.

Integral rounding chooses exponent $\max(q,0)$ for an input exponent $q$. Both `roundToIntegral` and `roundToIntegralExact` return the same integer-valued datum and preserve the sign of a zero result. Under nearest-even, $1.5$ becomes $2$ in either variant; only `roundToIntegralExact` raises inexact. An already integral datum with positive exponent, such as $12\cdot10^2$, keeps that exponent.

This requires the format's largest quantum exponent to be nonnegative, as it is in all three IEEE decimal formats. A custom layout whose exponents are all negative cannot encode the requested quantum; the operation raises invalid, and the proofs characterize that case too.

### Comparing values and representations

Numerical comparison treats $1.20$ and $1.2$ as equal. `totalOrder` can still distinguish them by their exponents, and also orders signed zeros and NaNs. Its proofs establish transitivity, totality, and agreement with the numerical, sign, and cohort rules. NaN payloads follow the documented implementation choice.

The API provides all 22 quiet and signaling comparisons. Their Boolean answers agree; their invalid flags differ when a quiet NaN is present. Classification distinguishes the ten IEEE classes and proves that changing cohort does not turn a normal value into a subnormal one. Sign operations on raw BID and DPD words preserve every other bit, even for redundant encodings and signaling NaNs.

<a id="moving-through-the-decimal-values"></a>

### Adjacent values, scaling, and remainder

The value immediately below decimal32's $1.000000$ is $0.9999999$. The value immediately above it is $1.000001$. Notice the unequal distances: crossing a power of ten changes the grid. `nextDown` and `nextUp` handle that boundary, and their adjacency proofs rule out every valid value between the input and its neighbor. They choose the finest quantum that represents the delivered value.

`scaleB` shifts a datum's quantum by an integer and rounds once if the result no longer fits. `remainder` uses the nearest-even integer quotient: the remainder of $7/2$ is $7-4\cdot2=-1$. Its proofs establish exact representability, the half-divisor magnitude bound, and the even-quotient rule at a tie. `logB` reports the exponent of the leading decimal digit.

<a id="writing-a-value-without-losing-its-representation"></a>

### Decimal text round trips

Printing $1.20$ as `1.2` is numerically harmless, but loses its quantum. `Formatting.formatExact` preserves the entire datum, including zero signs and NaN metadata. The parsing theorem recovers that datum in every rounding mode; the BID and DPD word theorem recovers its canonical encoding.

Requested precision is a separate choice. Formatting to two significant digits rounds $1.25$ to $1.2$ under nearest-even and $1.3$ under nearest-away. The digit count is any positive integer, and the text exponent is unbounded. The proofs establish the requested precision, rounding direction, midpoint behavior, and numerical inexactness. Asking for at least the source precision preserves its value through output and input in any pair of rounding modes.

<a id="crossing-into-another-format"></a>

### Conversions between numerical formats

Converting decimal $0.1$ to binary cannot preserve its value exactly: no finite binary fraction equals $1/10$. The converter starts from that exact rational and rounds once into the destination. Converting a binary value back to decimal starts from the binary value actually stored, so it need not recover the original decimal spelling.

The same route connects decimal formats to each other and to posits: exact source decoding, then destination rounding. Decimal-to-decimal conversion also chooses the available cohort exponent closest to the source's preferred exponent when the value is exact. Posit destinations follow their own appended-bit rounding rule, including saturation at the range limits. BID and DPD encoding adds no further numerical rounding.

Integer conversion rounds before checking the destination range. That ordering matters: a small negative fraction can round to unsigned zero. The five directions each have a quiet and an `Exact` variant; they return the same integer, while the latter reports inexactness. Exceptional sources and rounded values outside the destination range raise invalid and deliver zero in this binding. Integer-to-decimal conversion uses the same decimal projection as the other sources.

The proofs state the rounding bounds and exception behavior for each destination. The [validation discussion](#/chapter/external-validation/decimal-values-cohorts-and-flags) explains what an independent comparison must check about complete datums, conversions, and flags.

## Transcendental functions

The optional [binary transcendental module](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/Transcendentals.lean) provides software implementations of `exp`, `log`, `sin`, `cos`, `sinCos`, `sinh`, `cosh`, and `tanh` for every `ExecFloat.Binary` type. It also provides `Model.pow` and `MathFunctions` instances, so generic code can call these functions alongside the certified `sqrt` and `abs` and the constant `pi`. Each function decodes its input, calls the descriptor-generic model kernel, and packs the result back into the configured word.

These binary transcendental kernels have no proved general accuracy bound. They use nearest-even rounding internally, accept no rounding direction, and return no status flags. The separate test workspace has an Arb adapter for point evaluation with an explicit rounding direction; it uses python-flint as an external reference, as described in [chapter 16](#/chapter/external-validation). The software kernels require the named import below; `import FloatLib` alone provides the `MathFunctions` class and its host `Float` instance, but does not install these binary functions:

```lean standalone
import FloatLib
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

abbrev Binary32 := ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)

#eval ExecFloat.Binary.exp (1 : Binary32)
-- 2850325 * 2^-20
#eval ExecFloat.Binary.toBits32 (ExecFloat.Binary.exp (1 : Binary32))
-- 1076754516
#eval ExecFloat.Binary.log (ExecFloat.Binary.exp (1 : Binary32))
-- 16777215 * 2^-24
#eval ExecFloat.Binary.exp (100 : Binary32)
-- inf

example (x : Binary32) :
    ExecFloat.Binary.toModel (ExecFloat.Binary.exp x) = Model.exp (ExecFloat.Binary.toModel x) :=
  ExecFloat.Binary.toModel_exp x
```

The result $2850325 \cdot 2^{-20} = 2.71828174591\ldots$, word `0x402df854`, is the binary32 value nearest to $e$. Taking the logarithm of that word returns $1 - 2^{-24}$ rather than $1$.

The theorem `toModel_exp` connects the configured binary function to the model kernel: decoding the configured call gives `Model.exp` of the decoded input. The same lemma exists for each of the other functions, so a proof about a model kernel also applies to its configured function. This equality concerns the two implementations; it does not relate their output to the real exponential. The [posit functions](#/chapter/posits-and-the-quire/exponentials-and-logarithms) use different algorithms with proved real-rounding equations.

Sine and cosine also need enough argument-reduction data for the input's exponent. The default generated configuration has an exponent budget of 4,096. `Model.sinCosResult` and the configured `ExecFloat.Binary.sinCosResult` report an input beyond that budget as `Except.error`, carrying `TrigReductionError.inputExponent` and `maxExponent`. `Model.sinCosWithResult` accepts a chosen configuration; `Config.generatedFullRange` supplies data for the format's full exponent range, at potentially substantial cost.

This error reports a reduction-budget limit, not an IEEE status flag. `Except.ok` means the approximation policy executed; it is not an accuracy certificate. The value-only sine and cosine APIs map a budget error to `Model.invalidResult fmt`, a canonical NaN for IEEE formats. A format without an exceptional encoding falls back to positive zero, so callers who need to distinguish failure must use the checked result.

The [transcendental contracts](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Transcendentals/Contract.lean) define three kinds of accuracy claim, introduced in [chapter 03](#/chapter/a-short-history-of-floating-point). A `RealEnclosure` is a proved pair of real bounds around $f(x)$. An `ApproximationCertificate` is a proposition about a whole kernel: on every finite input it returns a finite result within a stated absolute error budget of the real function.

`ApproximationCertificateOn` and `CorrectlyRoundedCertificateOn` allow a stated domain, such as positive logarithm inputs or exponential inputs whose outputs remain finite; the guarantee must hold throughout that domain.

A `StableEnclosure` has endpoints that round to the same grid value under `roundAt`. Once we have such bounds, `CertifiedRoundedResult.toReal_value_eq_roundAt` proves that a stored result equal to their common rounding is the correctly rounded $f(x)$. Multiple-precision libraries use this criterion to decide when their bounds are tight enough; the theorem does not depend on how the bounds were obtained. The contract module contains enclosure constructors for `exp`, `log`, `sinh`, `cosh`, `tanh`, `sin`, `cos`, and `sqrt` and theorems for combining them.

`#float_info` lists this framework as conditional even with the default import. Applying it requires a whole-algorithm certificate for the selected kernel. The built-in binary transcendental kernels do not supply such certificates; the enclosure definitions and generic implications do not establish their accuracy.

## Custom widths

The IEEE theorems apply to an arbitrary descriptor with `isIEEE`, so a custom format needs no new arithmetic proofs. Consider a 24-bit layout with seven exponent bits and sixteen fraction bits, and a 71-bit layout with eleven exponent bits and fifty-nine fraction bits.

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
-- 768614336404564651 * 2^-61
```

The 24-bit format has bias 63, normal exponents from $-62$ to $63$, and $p = 17$ significant bits; an eight-exponent-bit, fifteen-fraction-bit layout would occupy the same 24 bits with more range and one bit less precision, which is why "a 24-bit float" is not a specification until the split is given. The addition theorem applies with `by simp` discharging `binary24.isIEEE = true` through the lemma `isIEEE_ieee`, and nothing else in the proof mentions the width. The 71-bit format has 60 significant bits, and its quotient $1/3$ shows them: the significand $768614336404564651$ lies between $2^{59}$ and $2^{60}$. A format with 71 significant bits would instead take `fracWidth := 70` and occupy 82 stored bits with the same exponent field. [Chapter 09](#/chapter/low-precision-formats-for-machine-learning) goes the other way, down to eight and four bits, and changes what the reserved patterns mean.

## Formats: encodings and their meaning

When using a format in a proof, keep its layout separate from the meaning of its values. [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat]] specifies widths, bias, and the [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.Encoding]] of special values. The catalog provides names such as [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.binary16]] and `binary256`; a named layout need not be a standard format. [[FloatLib.Floats.Formats.BinaryInterchange.Model]] stores the bits, [[FloatLib.Floats.Formats.BinaryInterchange.Model.toDyadic?]] decodes a finite word exactly, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal]] supplies its real value.

For a directed operation, choose an [[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEERoundingMode]]. The general policy rounder and the directed rounder are proved to agree for every descriptor and exact dyadic input in each of the four IEEE directions. To inspect exceptions, use the five-flag [[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEEStatus]] interface: [[FloatLib.Floats.Formats.BinaryInterchange.Model.addWithStatus_value]] relates the returned value to ordinary addition, while [[FloatLib.Floats.Formats.BinaryInterchange.Model.dyadicRoundingStatus_overflow]] characterizes its overflow test.

For numerical analysis, [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt]] and [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_sqrt_eq_roundAt]] connect executable operations to real rounding. The half-ulp bound [[FloatLib.Floats.Formats.BinaryInterchange.Model.abs_roundAt_sub_le]] then bounds error, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_sub_eq_of_sterbenz]] gives conditions for exact subtraction. Exact accumulation has a different contract: [[FloatLib.Floats.Formats.BinaryInterchange.Model.Reduction.dotWithStatus_eq_round_of_finite_nonzero]] identifies one final rounding of the exact dot product for finite operands with a nonzero exact sum. Directed rounding also supports interval containment, as in [[FloatLib.Floats.Formats.BinaryInterchange.Model.Interval.add_sound]]. The hypotheses determine when each theorem applies. For addition they are an IEEE descriptor, finite operands, and a finite result:

```lean
open FloatLib.Floats.Formats.BinaryInterchange in
#check @Model.toReal_add_eq_roundAt
-- @Model.toReal_add_eq_roundAt : ∀ {fmt : FloatFormat} (x y : Model fmt),
--   fmt.isIEEE = true →
--     x.isFinite = true →
--       y.isFinite = true → (x.add y).isFinite = true → (x.add y).toReal = Model.roundAt fmt (x.toReal + y.toReal)
```

Every hypothesis is visible in the signature: a conventional IEEE descriptor, finite operands, and a finite executable result, which excludes overflow because overflow has no value in $\mathbb{R}$. `Model.toReal` is total, using zero for a non-finite word, so dropping those premises would change the meaning of the assertion. Once they are supplied, the theorem replaces a decoded executable addition with `roundAt` of the exact real sum. That is the point where a word-level calculation can use the [general rounding theory](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/Flocq/Theory); [chapter 01](#/chapter/using-the-library) works through the additional bridge from a configured `Binary32` value to this model.

Programs normally use [[FloatLib.Floats.ExecFloat.Binary]] or [[FloatLib.Floats.ExecFloat.BinaryLimbs]], whose [[FloatLib.Floats.Formats.BinaryInterchange.Configured.StoragePlan]] chooses a carrier. Above 64 bits, `Binary` stores `Model format` directly; above 128 bits, `BinaryLimbs` uses an array of 32-bit limbs. Both have the same descriptor and reference semantics.

The configured interface exposes the same choices, including the `rounding` argument of [[FloatLib.Floats.ExecFloat.Binary.add]] and casts through exact signed rationals. The [configured word kernels](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/Core/Runtime.lean) adapt software arithmetic to the chosen format and carrier, with certificates such as [[FloatLib.Floats.Formats.BinaryInterchange.Configured.Backend.wordAdd_eq_spec]]. Calling the processor's floating-point instructions requires the explicit [unchecked native-FPU import](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/NativeFPU/Unchecked.lean) discussed in [chapter 15](#/chapter/performance/comparing-with-leans-native-floats); certified modules do not import it.

For decimal formats, choosing the represented value is only part of the result. The [decimal interchange examples](#/chapter/ieee-binary-formats/decimal-interchange) also track the quantum and exceptional metadata. `decode_transcode` proves that conversion between BID and DPD preserves that complete datum; numerical rounding and cohort selection are separate operations.
