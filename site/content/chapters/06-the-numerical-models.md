---
number: "06"
slug: "the-numerical-models"
title: "The numerical models"
summary: "Bits, exact dyadics, and real numbers let us state different properties of the same stored value."
phases: [numerical-models, binary-format, binary-arithmetic, status-and-directed]
---

An addition theorem can identify the bits an operation returns, including the sign of zero and the choice of NaN. For a conventional IEEE format, another theorem identifies the result's real value as the exact sum rounded once, provided the inputs and output are finite. A real-valued error bound cannot distinguish the two zeros or describe a NaN payload. Exact dyadics connect finite bit patterns to real values while preserving the sign of zero.

## One word, three readings

We'll keep the stored word fixed and change only how we read it. Our binary proof model is [[FloatLib.Floats.Formats.BinaryInterchange.Model]], and a value of `Model fmt` contains one field, `bits`, of type `fmt.ExecWord`, which abbreviates `BitVec fmt.bitWidth`. No decoded value is stored alongside the word, and the decoders are what give it meaning:

```lean
open FloatLib.Floats.Formats.BinaryInterchange

#print Model
-- structure FloatLib.Floats.Formats.BinaryInterchange.Model (fmt : FloatFormat) : Type
-- number of parameters: 1
-- fields:
--   FloatLib.Floats.Formats.BinaryInterchange.Model.bits : fmt.ExecWord
-- constructor:
--   FloatLib.Floats.Formats.BinaryInterchange.Model.mk {fmt : FloatFormat} (bits : fmt.ExecWord) : Model fmt
```

Programs normally use `ExecFloat`, whose storage is chosen per format. For binary32 it holds a `UInt32` and converts to `Model` through [[FloatLib.Floats.ExecFloat.Binary.toModel]]. With one common model, theorems can quantify over descriptors while executable values keep whatever storage suits them. [Chapter 05](#/chapter/why-execution-and-proofs-are-separate) explains the proofs connecting the representations.

At the word level, we inspect the bits. `signBit`, `expField`, and `fracField` extract the three fields by masking, and classifiers such as [[FloatLib.Floats.Formats.BinaryInterchange.Model.isNaN]] and [[FloatLib.Floats.Formats.BinaryInterchange.Model.isFinite]] interpret them according to the descriptor's exceptional-value policy.

That descriptor, `fmt : FloatFormat`, supplies the exponent and fraction widths, bias, and encoding. Non-IEEE encodings reuse some exceptional-value words for finite values, and [Chapter 11](#/chapter/low-precision-formats-for-machine-learning) develops them. What matters here is [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.isIEEE]]. It's true exactly when the encoding is `ieee` and the bias is the conventional $2^{w-1} - 1$ for exponent width $w$, and the real-valued arithmetic theorems below require it.

The second reading is the exact value. A finite word denotes a dyadic rational, $(-1)^s \cdot m \cdot 2^e$ with $m \in \mathbb{N}$ and $e \in \mathbb{Z}$, and [[FloatLib.Numerics.Dyadic]] stores those three fields as `negative`, `significand`, and `exponent`. The sign has a field of its own, so a zero keeps its sign here. A dyadic with `significand = 0` still remembers whether it was negative.

Decoding is done by [[FloatLib.Floats.Formats.BinaryInterchange.Model.toDyadic?]], which returns `none` for a NaN or an infinity and `some` for everything else, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.toDyadic?_isSome_eq_isFinite]] says that succeeding and being finite are the same thing.

For an IEEE descriptor the rule is the usual one. A zero exponent field with a zero fraction is a signed zero. With a nonzero fraction $f$, a zero exponent field gives the subnormal $f \cdot 2^{e_{\min}}$, where $e_{\min}$ is [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.minSubnormalExponent]]. A nonzero exponent field $E$ that isn't all ones, with fraction $f$, is $(2^{p} + f) \cdot 2^{E - \mathrm{bias} - p}$. Here $p$ is the fraction width and the $2^{p}$ is the hidden leading one. For binary32 that puts one at $8388608 \cdot 2^{-23}$, where $8388608 = 2^{23}$, and the least subnormal at $1 \cdot 2^{-149}$. Let's decode our two operands, and the least subnormal while we're at it:

```lean
/-- The binary32 word for 1.0. -/
def one32 : Model FloatFormat.binary32 := Model.ofNatBits 0x3f800000

/-- The binary32 word nearest to 1e-8. -/
def tiny32 : Model FloatFormat.binary32 := Model.ofNatBits 0x322bcc77

#eval Model.toDyadic? one32
-- some { negative := false, significand := 8388608, exponent := -23 }

#eval Model.toDyadic? tiny32
-- some { negative := false, significand := 11258999, exponent := -50 }

#eval Model.toDyadic? (Model.posMinSubnormal FloatFormat.binary32)
-- some { negative := false, significand := 1, exponent := -149 }
```

The small value has significand 11258999 and exponent $-50$. Keep those two integers in mind, because they will determine the rounding of its sum with one.

The exact reading doesn't stop at finite values, though. [[FloatLib.Floats.Formats.BinaryInterchange.Model.ExactValue]] is an inductive type with three constructors, `finite`, `infinity`, and `nan`, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.exactValue]] decodes any word into it without losing anything. A finite value keeps its dyadic and an infinity keeps its sign, while a NaN keeps its sign, whether it is signaling, and its whole fraction field. To compare bit for bit against an external oracle you need these exceptional-value fields as well as the finite value, and mapping to a real number would throw them away.

In the common `NumericalValue` view, a NaN's diagnostic payload is kept apart from its encoding markers. Binary decoders remove the quiet bit before they supply that payload. They keep the sign and signaling class in fields of their own, so generic conversion can preserve the payload without knowing the source format's bit layout. For the complete stored fraction field, you still look at `ExactValue.nan`.

```lean
#eval Model.exactValue (Model.negZero FloatFormat.binary32)
-- FloatLib.Floats.Formats.BinaryInterchange.Model.ExactValue.finite { negative := true, significand := 0, exponent := 0 }

#eval Model.exactValue (Model.posInf FloatFormat.binary32)
-- FloatLib.Floats.Formats.BinaryInterchange.Model.ExactValue.infinity false

#eval Model.exactValue (Model.canonicalNaN FloatFormat.binary32)
-- FloatLib.Floats.Formats.BinaryInterchange.Model.ExactValue.nan false false 4194304
```

That canonical NaN is positive and quiet, and its fraction field is $4194304 = 2^{22}$, the single quiet bit. In the output, the two booleans are the sign and the signaling flag.

For real-valued proofs we interpret the dyadic as a real number, where [[FloatLib.Numerics.Dyadic.toReal]] sends a dyadic to $m \cdot 2^{e}$ with the sign applied and [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal]] composes it with the decoder. This dyadic interpretation doesn't depend on any packed format.

We make `Model.toReal` total by sending a NaN or an infinity to $0$. A partial version, `toReal?`, returns an `Option ℝ` and exposes the nonfinite case, but inside algebraic statements, where `toReal (add x y)` should be a real number, a total function is more convenient. So an arithmetic theorem has to establish finiteness before it treats `toReal` as the numerical value of a result. `Represents` packages the two facts, and `represents_iff` states that `Represents x r` holds exactly when `isFinite x = true` and `toReal x = r`. A rounded-real contract then says that the real value of the result equals the exact real result rounded to the format's grid.

Say all we know is `toReal x = 0`. On its own that can't tell us whether `x` is a finite zero, an infinity, or a NaN, because this total decoder sends all of them to the same real number. Adding `isFinite x = true` rules out the exceptional cases and still leaves both signs of zero. So a proof of `Represents x 0` is enough for real algebra but not enough for a bit-for-bit conformance claim.

You can follow `tiny32` through all three readings in [Figure 6.1](#/chapter/the-numerical-models/figure-ch06-three-readings). Its fraction field is nonzero, decoding gives its integer significand and exponent, and `Dyadic.toReal` then reads that pair as a real value.

![Three cards read tiny32 as stored fields (sign 0, exponent 100, fraction 2870391), an exact dyadic (significand 11258999, exponent -50), and the real value 11258999 times 2^-50; the arrows decode and interpret without rounding](assets/ch06-three-readings.png "One finite word, read as stored fields, an exact dyadic, and a real value.")

## What rounding discards

We now have the operands for the addition: $x = 1$ and $y$ the binary32 value nearest to $10^{-8}$, which is $11258999 \cdot 2^{-50}$. Their exact sum $1 + y$ is a dyadic with a fifty-bit fraction. But binary32 has twenty-three fraction bits, and just above $1$ the representable numbers are $2^{-23} \approx 1.19 \times 10^{-7}$ apart. Since the increment $y$ is about $0.084$ of that spacing, the representable value nearest the exact sum is $1$ itself.

```lean
#eval Model.add one32 tiny32
-- 1

#eval Model.add one32 tiny32 (status := true)
-- { value := 1,
--   status := { invalid := false, divideByZero := false, overflow := false, underflow := false, inexact := true },
--   ternary := Ordering.lt }
```

We can make the comparison exact by measuring everything in units of $2^{-50}$, the scale `tiny32` already uses. Then one is $2^{50}$ units, the next binary32 value above one is another $2^{27}$ units away, and their midpoint is $2^{26}$ units above one. The increment is only $11258999$ units, with

$$
0 < 11258999 < 2^{26} = 67108864.
$$

So the exact sum is strictly above one and strictly below the midpoint. That proves both facts the example reports: nearest rounding returns one, and the rounding is inexact. The integer inequality also rules out a midpoint tie.

Now look at what the result leaves behind. Nothing in the returned word, `0x3f800000`, records the small increment. Its decoded value is exactly one, just as it would be after adding zero. The `inexact` flag comes from comparing the rounded result with the exact intermediate $1 + y$, so it keeps information that the result word alone can't supply. In the real-valued model, $\mathrm{round}(1 + y) = 1$ and the absolute rounding error is $y$, less than half the spacing. So the bit result, the discarded dyadic part, and the error bound each describe a different stage of this computation.

## The reference operations: decode, compute exactly, round once

Every arithmetic operation on `Model fmt` has a reference definition in the `Model.Spec` namespace, and each of these definitions exposes the exact intermediate that determines the rounded result. The reference for the addition we just ran is [[FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.add]]. It decodes both operands with `toDyadic?` and, if both succeed, adds the dyadics exactly with `addDyadic` and rounds once with [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundDyadic]]. Otherwise it follows the descriptor's NaN and infinity rules.

[[FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.mul]] multiplies significands and adds exponents, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.fma]] forms the exact product, adds the third operand exactly, and rounds once, which is what makes it fused.

Division can't stay inside the dyadics, because a quotient of dyadics is a general rational, so [[FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.div]] rounds a scaled rational with `roundRatScaled`. [[FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.sqrt]] handles the sign and zero cases and delegates a positive finite input to the exact square-root routine.

<details>
<summary>The square-root connection to Lean's logical model</summary>

Lean's core library ships a logical model of IEEE floats, `Float.Model.UnpackedFloat`. It's an inductive with a zero, an infinity, a NaN, and a finite case carrying a sign, a mantissa, and an exponent, and it comes with its own rounding function. For an IEEE descriptor and a positive finite input, [[FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.sqrt_eq_model]] identifies our square root with the repacked result of that model. Its hypotheses require finiteness, a nonzero input, and a clear sign bit, so zero and exceptional inputs aren't covered. And agreeing with Lean's logical float model is a different thing from agreeing with host instructions.

</details>

We prove the dispatched operations equal to these references for every descriptor, with no IEEE assumption. [[FloatLib.Floats.Formats.BinaryInterchange.Model.Proof.add_eq_spec]], for example, states `add x y = Spec.add x y`, and [Chapter 05](#/chapter/why-execution-and-proofs-are-separate) follows this equation through the configured carrier and its selected backend.

## The rounding contract as a statement about reals

To relate an operation to rounding on $\mathbb{R}$, we use Boldo and Melquiond's Flocq description of a grid [@boldoMelquiond2011]. Picture the real numbers a format can hold exactly. They're isolated points on the real line, evenly spaced between one power of two and the next, and in the normal range the spacing doubles at each power of two. We call this set the format's grid. Flocq describes the spacing through an exponent function. For a real $x$ with $2^{e-1} \le |x| < 2^{e}$, $\mathrm{fexp}(e)$ is the exponent of the spacing around $x$. For a descriptor `fmt`, [[FloatLib.Floats.Formats.BinaryInterchange.Model.fexpOf]] is [[FloatLib.Floats.Formats.Flocq.fltExp]] applied to the least subnormal exponent and the precision $p + 1$. That precision counts the $p$ stored fraction bits plus the hidden leading one, and the exponent function is

$$\mathrm{fexp}(e) = \max\bigl(e - (p + 1),\; e_{\min}\bigr),$$

so in the normal range the spacing is $2^{e - (p + 1)}$ and $p + 1$ significant bits are kept. Below the normal range the spacing stops shrinking and stays at $2^{e_{\min}}$, which is gradual underflow. [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt]] is Flocq's [[FloatLib.Floats.Formats.Flocq.round]] on that grid with the [[FloatLib.Floats.Formats.Flocq.nearestEven]] integer rounding rule. It's defined on all of $\mathbb{R}$ and its grid has no largest element, so `roundAt` never overflows. The packed executable operation can overflow, so the equality between these two computations requires the executable result to be finite.

Two theorems tie the grid to the words. [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_genericFormat_of_isFinite]] says that every finite word decodes to a point of the descriptor's grid, in the sense of Flocq's [[FloatLib.Floats.Formats.Flocq.genericFormat]]. That holds for every descriptor, including custom biases and finite-only encodings. [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt_toReal_eq]] then says that rounding a finite word's value returns it unchanged. [Chapter 07](#/chapter/the-mathematics-of-rounding) develops the grid theory behind the half-ulp bound [[FloatLib.Floats.Formats.BinaryInterchange.Model.abs_roundAt_sub_le]], which reads $|\mathrm{roundAt}_f(x) - x| \le \varepsilon_f(x)$. Here $\varepsilon_f(x)$, the format's [[FloatLib.Floats.Formats.BinaryInterchange.Model.epsilonAt]], is half the grid spacing at $x$. Monotonicity, `roundAt_mono`, comes from the same theory.

Our central refinement theorem is [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt]]. For `x y : Model fmt` it states

$$\operatorname{toReal}(\operatorname{add}(x, y)) = \operatorname{roundAt}_{f}\bigl(\operatorname{toReal}(x) + \operatorname{toReal}(y)\bigr)$$

under four hypotheses: `fmt.isIEEE = true`, `isFinite x = true`, `isFinite y = true`, and `isFinite (add x y) = true`. It's an equation for the real value of the rounded result, and an error bound follows from properties of `roundAt`.

Its proof first replaces the dispatched `add` with `Spec.add` using `add_eq_spec`. Finiteness makes both decoders succeed, say with `dx` and `dy`, so the reference operation becomes `roundDyadic fmt (addDyadic dx dy)`. Then [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_roundDyadic_eq_roundAt]] identifies the executable rounder with `roundAt` on the exact dyadic sum, and because dyadic addition is exact, that supplies the real sum on the right.

Back to `one32` and `tiny32`. Their exact sum lies between adjacent binary32 values near $1$, and in [Figure 6.2](#/chapter/the-numerical-models/figure-ch06-one-rounding) the shorter distance is back to $1$, so both the reference rounder and the executable addition return that grid point.

![Binary32 number line near 1, with neighbours 1 - 2^-24 and 1 + 2^-23; the exact sum 1 + 11258999 · 2^-50 lies about 0.084 of the gap above 1, before the midpoint, and rounds to 1 with inexact set](assets/ch06-one-rounding.png "The exact sum rounds back to one, setting the inexact flag.")

For these concrete words every hypothesis is decidable. `apply` leaves four side goals (`isIEEE`, finiteness of each input, and finiteness of the sum), and `decide` closes each one by evaluating the boolean:

```lean
example :
    Model.toReal (Model.add one32 tiny32) =
      Model.roundAt FloatFormat.binary32
        (Model.toReal one32 + Model.toReal tiny32) := by
  apply Model.toReal_add_eq_roundAt <;> decide
```

For symbolic words the hypotheses become assumptions instead. The `numerics` tactic, which knows the registered refinement theorems and discharges the `isIEEE` side condition for named formats, closes the generic statement:

```lean
example (x y : Model FloatFormat.binary32)
    (hx : Model.isFinite x = true) (hy : Model.isFinite y = true)
    (hout : Model.isFinite (Model.add x y) = true) :
    Model.toReal (Model.add x y) =
      Model.roundAt FloatFormat.binary32
        (Model.toReal x + Model.toReal y) := by
  numerics
```

Now we can rewrite the executable result using this equality and apply the rounding error bound. [[FloatLib.Floats.Formats.BinaryInterchange.Model.abs_toReal_add_sub_le]] does this for one addition, and its proof applies `toReal_add_eq_roundAt` followed by `abs_roundAt_sub_le`.

```lean
example (x y : Model FloatFormat.binary32)
    (hx : Model.isFinite x = true) (hy : Model.isFinite y = true)
    (hout : Model.isFinite (Model.add x y) = true) :
    |Model.toReal (Model.add x y) - (Model.toReal x + Model.toReal y)| ≤
      Model.epsilonAt FloatFormat.binary32 (Model.toReal x + Model.toReal y) :=
  Model.abs_toReal_add_sub_le x y FloatFormat.isIEEE_binary32 hx hy hout
```

In the bound, `epsilonAt` takes the exact sum of the decoded operands as its argument. For `one32` and `tiny32` that sum lies in the binade from one to two, whose spacing is $2^{-23}$, so the bound is $2^{-24}$. The actual error is $11258999 \cdot 2^{-50}$, and the integer comparison above proves it's smaller. In a symbolic proof, keep the bound at the exact expression until you've justified its magnitude. If you substitute the rounded output as its argument, the spacing can change when rounding crosses a power of two.

<details>
<summary>Rounding theorems for the other operations</summary>

Subtraction, multiplication, and fused multiply-add have corresponding nearest-even real-rounding equations, [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_sub_eq_roundAt]], [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_mul_eq_roundAt]], and [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_fma_eq_roundAt]]. They require `fmt.isIEEE = true` and finite inputs and results. Division also needs a nonzero divisor, in [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_div_eq_roundAt]], and casts between IEEE formats use [[FloatLib.Floats.Formats.BinaryInterchange.Model.cast_eq_roundAt]], again with finite source and result. Square root is different, because it can't overflow on a finite input that is nonnegative or a signed zero. So [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_sqrt_eq_roundAt]] needs no output-finiteness premise, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.isFinite_sqrt_of_isFinite]] proves finiteness under the same domain condition.

</details>

## Proving inputs and results are finite

Each finiteness hypothesis rules out a case where the equality would fail. We need the input hypotheses because `toReal` returns a placeholder for nonfinite values. Without them, `toReal x` could be the $0$ that stands in for a NaN, and the theorem would happily claim that adding a NaN behaves like adding zero :) The output hypothesis rules out overflow. If $x$ and $y$ are both the largest finite binary32 value, the executable sum is $+\infty$ and `toReal` of it is $0$. The right-hand side is the ordinary real $\mathrm{roundAt}_f(2 \cdot \mathrm{maxFinite})$, near $6.8 \times 10^{38}$. An infinity can't be identified with that finite real value.

For known words, computing the result settles whether it's finite. For symbolic inputs, magnitude bounds can establish finiteness before the result is computed. [[FloatLib.Floats.Formats.BinaryInterchange.Model.isFinite_add_of_abs_add_le_posMaxFinite]] says that if $|x| + |y|$ is at most the value of [[FloatLib.Floats.Formats.BinaryInterchange.Model.posMaxFinite]], the executable sum is finite. [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt_of_abs_add_le_posMaxFinite]] combines it with the refinement so that the output hypothesis never appears. Subtraction, multiplication, division, and fused multiply-add have the same pair of lemmas with the corresponding triangle, product, quotient, or product-plus-addend bound. Division also keeps its nonzero-divisor hypothesis. For binary32, `posMaxFinite` decodes to $16777215 \cdot 2^{104}$, about $3.4 \times 10^{38}$.

```lean
example (x y : Model FloatFormat.binary32)
    (hx : Model.isFinite x = true) (hy : Model.isFinite y = true)
    (hbound : |Model.toReal x| + |Model.toReal y| ≤
      Model.toReal (Model.posMaxFinite FloatFormat.binary32)) :
    Model.toReal (Model.add x y) =
      Model.roundAt FloatFormat.binary32
        (Model.toReal x + Model.toReal y) :=
  Model.toReal_add_eq_roundAt_of_abs_add_le_posMaxFinite x y
    FloatFormat.isIEEE_binary32 hx hy hbound
```

A triangle bound is convenient when you have a bound on each operand, but it's only sufficient. Take one operand to be the largest finite value and the other its negation. Their sum is exactly zero, but the sum of their absolute values is twice the largest finite value. When cancellation matters, use `isFinite_add_of_abs_toReal_add_le_posMaxFinite`, which takes a bound on the absolute value of the exact sum itself. We derive the triangle-bound theorem from this tighter criterion with the triangle inequality, and which one you pick depends on what the application already knows about its operands.

The remaining hypothesis is about the format. Our real-valued refinement theorem needs `fmt.isIEEE = true`, which restricts it to conventional IEEE descriptors. Exact decoding, the reference operations, and the `Spec` equalities hold for every descriptor, FNUZ and finite-only encodings included. The bridge to `roundAt` also goes through Lean's float model, because `roundDyadic` delegates its normalization to that model for IEEE descriptors. That model is IEEE-shaped. `toDyadic?_ieee_eq_model` and [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_eq_unpackedToReal_toModel]] identify the binary decoder with it exactly when the descriptor is conventionally IEEE. So a non-IEEE format has exact dyadic semantics and executable arithmetic, but its operations don't have a `roundAt` theorem yet.

<a id="numerics-exact-values-and-contracts"></a>

## A common interface for numerical formats

Posits, fixed point, logarithmic codes, and block-scaled values also have codes and numerical meanings. They all share [[FloatLib.Numerics.NumericalSystem]], a structure with a `Code` type, a `Scalar` type, and a `denote` function from codes to [[FloatLib.Numerics.NumericalValue]]. A code can denote `finite x`, `infinity negative`, or `exceptional e`. Here [[FloatLib.Numerics.ExceptionalValue]] covers NaNs with their metadata, posit NaR, reserved words, and undefined results. [[FloatLib.Numerics.NumericalSystem.Represents]] states that a code denotes a particular finite scalar. `Model fmt` gets two systems, and both reuse its existing code type. `numericalSystem` takes $\mathbb{R}$ as its scalar and suits error analysis, while `exactNumericalSystem` takes `Numerics.Dyadic` and keeps the sign of finite zero for exact comparisons. Both preserve infinity signs and NaN metadata in their exceptional cases.

Through this interface, the addition theorem becomes a refinement contract. Under `fmt.isIEEE = true`, `add_refines` says that `Model.add` satisfies [[FloatLib.Numerics.Operation.Finite2If]], with specification `fun x y => roundAt fmt (x + y)` and condition `isFinite result = true`. Whenever the inputs represent finite reals and the result is finite, the result represents the rounded exact sum. [[FloatLib.Numerics.Operation.Refines]] expresses the contract as a relation in `Prop`, so it adds no runtime data.

<details>
<summary>Interfaces for a new representation or rounder</summary>

`EncodedFormat` and `FormatSemantics` keep the computable code type apart from its possibly noncomputable meaning, so a program can manipulate codes even when their semantics lives in $\mathbb{R}$. Exact intermediates keep the information the destination needs. [[FloatLib.Numerics.Dyadic.toRat]] reads a dyadic as a rational, and [[FloatLib.Numerics.Dyadic.add_toRat]] proves that dyadic addition preserves the exact sum. [[FloatLib.Numerics.SignedRat]] keeps an IEEE sign bit next to a rational, which lets a cast preserve $-0$. [[FloatLib.Numerics.QuantizationPolicy]] spells out the rounding, saturation, and flush-to-zero choices. [[FloatLib.Numerics.Quantization.Spec]] describes an allowed rounded result, and [[FloatLib.Numerics.Quantization.Spec.Implements]] is the obligation an executable rounder must prove. At the integer level, [[FloatLib.Numerics.roundShiftRightEven]] makes the nearest-even choice when bits are discarded. In the [endpoint-adapter example](#/chapter/further-examples/choosing-a-different-endpoint-format), one shared contract is used with different representations.

</details>

## Extended reals for directed rounding

Our binary IEEE operation interface implements six rounding modes, which [chapter 02](#/chapter/from-reals-to-machine-numbers) discusses. [[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEERoundingMode]] lists the five IEEE directions `nearest` (ties to even), `nearestAway`, `towardZero`, `up`, and `down`, plus MPFR's `away`. The `mode` option of [[FloatLib.Floats.Formats.BinaryInterchange.Model.add]] and its siblings executes all of them for every descriptor.

A bound for directed rounding has to include infinite results if it's going to stay valid through overflow. [[FloatLib.Floats.Formats.BinaryInterchange.Model.toEReal]] maps words into Mathlib's `EReal`. Finite words coerce from `toReal`, and the two infinities become $-\infty$ and $+\infty$, which Mathlib writes $\bot$ and $\top$. A partial version, `toEReal?`, returns `none` on NaNs and only on NaNs. Its total counterpart `toEReal` sends a NaN to $0$, the same placeholder `toReal` uses, so the theorems still need to exclude NaNs.

Our directed theorems are inequalities in `EReal` with no finiteness hypothesis on the output. [[FloatLib.Floats.Formats.BinaryInterchange.Model.toEReal_add_down_le]] bounds the downward-rounded sum by the exact real sum. [[FloatLib.Floats.Formats.BinaryInterchange.Model.le_toEReal_add_up]] bounds the exact sum by the upward-rounded one. Multiplication and division have the same pairs. We built the library's interval arithmetic on these two directions, in the tradition of Moore [@moore1966]. [[FloatLib.Floats.Formats.BinaryInterchange.Model.Interval.add_sound]] encloses the exact sum of two reals between the downward-rounded sum of the lower bounds and the upward-rounded sum of the upper bounds. Its proof is the two inequalities above applied to the endpoints.

For interval addition, we can write out the whole chain. If the finite endpoint values satisfy $a \le x \le b$ and $c \le y \le d$, monotonicity of real addition gives $a+c \le x+y \le b+d$. Downward rounding places the stored lower endpoint at or below $a+c$, upward rounding places the stored upper endpoint at or above $b+d$, and transitivity then encloses the exact sum. If an endpoint operation overflows outward, its infinite endpoint still makes sense in this order. A NaN doesn't, because it supplies no ordered bound to put into the chain, and that's why the NaN exclusions are necessary.

## Status flags as data

A status-bearing operation returns its exception flags along with its value. You can inspect that operation in isolation or combine its flags with earlier ones, and the meaning of the call never depends on a mutable status register. [[FloatLib.Numerics.IEEEStatus]] is a structure of five booleans, `invalid`, `divideByZero`, `overflow`, `underflow`, and `inexact`. [[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEEOutcome]] holds a result word, a status, and a ternary value. That last one says whether the delivered value lies below, at, or above the exact result, and [chapter 07](#/chapter/the-mathematics-of-rounding/rounding-directions-and-the-ternary-value) defines it.

For finite operands, [[FloatLib.Floats.Formats.BinaryInterchange.Model.add]] with `(status := true)` computes the exact dyadic sum and the rounded value under the requested mode. It then classifies the pair with [[FloatLib.Floats.Formats.BinaryInterchange.Model.dyadicRoundingStatus]] and compares it with [[FloatLib.Floats.Formats.BinaryInterchange.Model.dyadicTernary]], and division uses the rational counterpart of this classifier. So the flags describe the same intermediate and rounded result that determine the value, and that's where the inexact flag on our very first addition came from. [[FloatLib.Floats.Formats.BinaryInterchange.Model.value_add]] proves that the value field equals the value-only operation.

Overflow follows IEEE 754-2019 Section 7.4 [@ieee754_2019] and the MPFR exception definition [@fousseMpfr2007]. The exact value is rounded to the destination precision with an unbounded exponent range, and the result overflows when that lands beyond the largest finite value. `dyadicRoundingOverflows` implements this per mode. So a magnitude just above the largest finite value overflows under a mode that increases magnitude, but not under rounding toward zero. Inexact compares the exact dyadic with the decoded result.

Underflow follows Section 7.5 with tininess detected after rounding. The exact value is first rounded to the destination precision as if the exponent range were unbounded. The result counts as tiny when that rounded magnitude is below the least normal number, which [[FloatLib.Floats.Formats.BinaryInterchange.Model.dyadicIsTinyAfterRounding]] decides. Underflow is raised only when the result is tiny and inexact, so an exact subnormal raises nothing. Overflow and underflow, the range flags, are mutually exclusive, and either implies `inexact`.

Classifiers for exceptional inputs have conditions of their own. [[FloatLib.Floats.Formats.BinaryInterchange.Model.div_divideByZero]] requires a nonzero finite numerator and a zero denominator, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.sqrt_invalid]] identifies signaling NaNs and negative nonzero inputs. [Chapter 08](#/chapter/ieee-binary-formats) gives the full flag characterizations.

Two operations can return the same infinity for different reasons, and their flags keep the reasons apart. Dividing one by positive zero returns positive infinity, `0x7f800000`, and raises only `divideByZero`. Doubling the largest finite value overflows to the same infinity and raises `overflow` together with `inexact`, as `dyadicRoundingStatus_inexact_of_overflow` requires. Subtracting infinity from itself is invalid, so the result is the canonical quiet NaN, `0x7fc00000`, with only `invalid` raised. The ternary value is `Ordering.eq` for the exact infinity of the division and for the NaN, and `Ordering.gt` for the overflow, whose delivered infinity lies above the exact product.

```lean
/-- The binary32 word for 2.0. -/
def two32 : Model FloatFormat.binary32 := Model.ofNatBits 0x40000000

#eval Model.div one32 (Model.posZero FloatFormat.binary32) (status := true)
-- { value := inf,
--   status := { invalid := false, divideByZero := true, overflow := false, underflow := false, inexact := false },
--   ternary := Ordering.eq }

#eval Model.mul (Model.posMaxFinite FloatFormat.binary32) two32 (status := true)
-- { value := inf,
--   status := { invalid := false, divideByZero := false, overflow := true, underflow := false, inexact := true },
--   ternary := Ordering.gt }

#eval Model.sub (Model.posInf FloatFormat.binary32) (Model.posInf FloatFormat.binary32) (status := true)
-- { value := nan,
--   status := { invalid := true, divideByZero := false, overflow := false, underflow := false, inexact := false },
--   ternary := Ordering.eq }
```

The least subnormal makes the underflow rule concrete. Adding the least subnormal to itself is exact, so nothing is raised even though the result is subnormal. Halving it falls below the grid, rounds to zero, and raises both `underflow` and `inexact`.

```lean
/-- The binary32 word for 0.5. -/
def half32 : Model FloatFormat.binary32 := Model.ofNatBits 0x3f000000

#eval Model.add (Model.posMinSubnormal FloatFormat.binary32)
  (Model.posMinSubnormal FloatFormat.binary32) (status := true)
-- { value := 3e-45,
--   status := { invalid := false, divideByZero := false, overflow := false, underflow := false, inexact := false },
--   ternary := Ordering.eq }

#eval Model.mul (Model.posMinSubnormal FloatFormat.binary32) half32 (status := true)
-- { value := 0,
--   status := { invalid := false, divideByZero := false, overflow := false, underflow := true, inexact := true },
--   ternary := Ordering.lt }
```

Flags accumulate with [[FloatLib.Numerics.IEEEStatus.union]] when a caller wants them to persist across a sequence of operations, the way a hardware status register does.

## From one operation to a calculation

Each arithmetic theorem describes one operation, so in a longer calculation we have to carry its rounded result into the next step. Take a two-stage sum in an IEEE format and suppose the inputs and both results are finite. Write the decoded results as $s_1 = \mathrm{roundAt}_f(x+y)$ and $s_2 = \mathrm{roundAt}_f(s_1+z)$, with $x,y,z$ now denoting the finite input reals. Applying the theorem a second time needs a finiteness argument for the addition that involves the stored first result. That step's local error is measured against $s_1+z$, but the total error is measured against $x+y+z$. Subtracting the latter gives the exact decomposition

$$
s_2-(x+y+z) = \bigl(s_2-(s_1+z)\bigr) + \bigl(s_1-(x+y)\bigr).
$$

Now the triangle inequality combines the two local error bounds. Both local errors remain in the final answer; applying the theorem twice does not give a single rounding of the three-input sum. In a longer computation you have to establish the hypotheses at every step and account for each rounding. The relevant grid results are in [chapter 07](#/chapter/the-mathematics-of-rounding), and [further examples](#/chapter/further-examples) apply the interfaces to configured arithmetic and exact reductions.
