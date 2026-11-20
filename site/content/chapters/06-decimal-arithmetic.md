---
number: "06"
slug: decimal-arithmetic
title: "Decimal numbers"
summary: "Why decimal numbers store 1.20 and 1.2 differently, and how FloatLib computes, rounds, flags, stores and prints them."
phases: [ieee-formats, status-and-directed]
---

In decimal32, adding $1.20$ and $0.30$ returns $1.50$. A proof that the sum equals $3/2$ explains its value, but leaves the last zero unexplained. IEEE 754 also specifies how to select the exponent of an exact sum. FloatLib models both decisions for decimal32, decimal64 and decimal128 [@ieee754_2019].

## Why use decimal numbers?

A finite binary fraction has a power of two in its denominator, so entering $0.10$ as a binary float already requires rounding. In a decimal format the coefficient $10$ and exponent $-2$ represent it exactly and preserve the two decimal places.

## What is a decimal number?

The representations $120\cdot10^{-2}$ and $12\cdot10^{-1}$ have the same rational value. Their coefficients are $120$ and $12$, and their exponents are $-2$ and $-1$. The exponent, called the *quantum exponent*, determines the *quantum*, the value of one unit in the last stored decimal place: $0.01$ in the first representation and $0.1$ in the second. IEEE decimal formats retain this distinction, so equality of numerical values does not imply equality of representations.

FloatLib calls a stored representation a *datum* (plural *data*). A finite datum contains a sign, coefficient and quantum exponent; other data represent infinities and NaNs. Data with the same numerical value form a *cohort*, so the representations of $1.20$ and $1.2$ belong to the same cohort. Removing the trailing zero changes the datum while preserving its rational value.

## What are decimal32, decimal64 and decimal128?

These are the three IEEE decimal formats, named for their width in bits. FloatLib makes them presets of one layout with three settings: the number of *declets* (groups of three decimal digits), the width of the exponent continuation (the field holding most of the exponent), and the *bias*, subtracted from the stored exponent to give the quantum exponent. Precision, the number of digits a format keeps, is three digits per declet plus one, so decimal32's two declets give seven. Our algorithms and our proofs about encoding to bits also work for custom layouts with any bias, and a theorem that needs quantum zero to be available says so.

## How to add and multiply decimal numbers

Add $1.20+0.30$ and you have to decide two things: the sum, and which member of its cohort to return. Both operands have quantum exponent $-2$, so the exact result is

$$
(120+30)\cdot10^{-2}=150\cdot10^{-2}.
$$

A rule called the *preferred exponent* makes the choice. For addition it's the smaller input exponent, here $-2$, so you get $1.50$ back with no flags. Multiplication adds the input exponents, so $1.2\cdot3.0$ comes back as $3.60$, as you'd write it by hand. `preferredCohort` moves a result toward the preferred exponent within the destination's limits, and only by removing trailing zeros, so the value never changes.

Let's try both in Lean. A `Datum` literal keeps the digits you wrote, so `1.20` is $120\cdot10^{-2}$, `1.2e4` is $12\cdot10^{3}$ and `-0.0` is a negative zero. An operation takes a format, a rounding mode (`.nearest` is nearest, ties to even) and its operands. It reads a literal exactly, even one longer than the format, and rounds only its result. That result comes back in an `Outcome` with five exception flags, and `.value` picks it out. The comments show what you get:

```lean standalone
import FloatLib

open FloatLib.Floats.Formats.DecimalInterchange

#eval ((1.20 : Datum), (1.2e4 : Datum), (-0.0 : Datum))
-- (1.20, 1.2e4, -0.0)
example : (1.20 : Datum) ≠ 1.2 := by decide

#eval (Arithmetic.add Format.decimal32 .nearest 1.20 0.30).value
-- 1.50
#eval (Arithmetic.mul Format.decimal32 .nearest 1.2 3.0).value
-- 3.60
```

Here `decide` proves that `1.20` and `1.2` are different data. Our [decimal arithmetic API](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/DecimalInterchange/Arithmetic/Basic.lean) has addition, subtraction, multiplication, division, fused multiply-add ($xy+z$ as one operation) and square root for decimal32, decimal64 and decimal128. They come in five rounding modes: nearest with ties to even or away, toward zero, and toward positive or negative infinity. Each takes decoded `Datum` values, not the stored bits we'll meet at the end of the chapter.

## What happens when the digits don't fit?

Decimal32 holds seven digits, so the exact sum $1.000000+0.0000005=1.0000005$ sits halfway between $1.000000$ and $1.000001$. The rounding mode settles it. Nearest-even picks the first, since the coefficient 1000000 is even, and nearest-away the second. Both report inexact.

On finite operands the five rational operations, all but square root, round the exact rational result, so FMA never rounds or overflows on its intermediate product. Square root's preferred exponent is the floor of half the input exponent, negative zero stays negative, and a negative nonzero input returns a quiet NaN and raises invalid.

## What does FloatLib prove about the results?

The [arithmetic proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/DecimalInterchange/Arithmetic/Proof.lean) and [square-root proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/DecimalInterchange/Sqrt/Proof.lean) show every result is a valid datum in the destination. With finite operands and no overflow, nearest-mode error is at most half the selected decimal grid step (the spacing of values near the exact result), provided division has a nonzero denominator and square root a nonnegative input. Directed modes land on the required side of the exact value. The midpoint theorems settle ties like the one we just met, and a representable rational rounds to itself. The inexact flag records a change in numerical value. Choosing a different member of the same cohort leaves it clear.

The exponent you get back is proved too. An exact result like our $1.50$ gets the representation closest to the preferred exponent. An inexact finite one gets the smallest quantum exponent in its cohort, even for an irrational square root, as the [preferred-cohort proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/DecimalInterchange/Projection/Cohort.lean), the [minimal-quantum proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/DecimalInterchange/Projection/Minimal.lean) and their square-root counterparts show.

We also compared decimal addition, subtraction and multiplication with Python's `decimal` module (libmpdec) across all three interchange widths and five rounding directions. Both the reference implementation in Lean and its kernel rewrites agreed with libmpdec on the values and flags in all 20,000 generated cases. [Recorded comparisons](https://github.com/lean-dojo/FloatLib/blob/main/tests/results/differential/ieee2019.csv)

### What happens with zeros, NaNs and tiny results?

Exact cancellation in $1.20-1.20$ returns a zero with exponent $-2$, negative when rounding toward negative infinity and positive in the other modes. A signaling NaN raises invalid and comes back quiet. The first NaN operand supplies sign and payload (the small number a NaN carries), and a payload too large for the destination becomes zero.

**Note:** Decimal tests tininess **before rounding**, where the [binary kernels](#/chapter/ieee-binary-formats/how-to-read-the-status-flags) test it after. Tiny means below the least normal magnitude, and decimal underflow needs both a tiny exact result and inexactness.

## How to take powers and roots

What happens to the quantum if you cube $2.0$ and then take the cube root? Let's try it. The exponents add as in any product, giving $8.000$, whose cube root comes back as $2.0$:

```lean standalone
import FloatLib
open FloatLib.Floats.Formats.DecimalInterchange

#eval (Arithmetic.pown Format.decimal32 .nearest 2.0 3).value
-- 8.000
#eval (Arithmetic.rootn Format.decimal32 .nearest 8.000 3).value
-- 2.0
```

The decimal [algebraic API](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/DecimalInterchange/Algebraic/Runtime.lean) adds `square`, `rSqrt` (reciprocal square root), `hypot` ($\sqrt{x^2+y^2}$, named for the hypotenuse), `pown` and `rootn` (integer powers and $n$th roots), with the same modes and exact intermediates, and an exact result keeps its preferred quantum where the format allows.

How far off can a result be? Given finite operands and no reported overflow, the [numerical bounds](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/DecimalInterchange/Algebraic/Proof.lean) give a half-grid error bound in the nearest modes and a directed bound in the others, on custom layouts too. Reciprocal square root also needs a positive input, and an integer power with a negative exponent needs a nonzero base. The [general-root bounds](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/DecimalInterchange/Algebraic/Root/Semantics.lean) need a nonzero base and degree (the $n$ of the $n$th root), odd for a negative base, and are measured against a real root that carries a proof of its defining power equation. Other theorems cover validity and exceptional inputs.

The recommended functions of clause 9.2 are here too, from `exp2` and `log10` to `atan2` and `pow`. With one more import, each takes a format, one of the five rounding directions and its operands, and gives back the datum with its flags. Let's take $2^{0.5}$, the square root of two, in decimal32:

```lean standalone
import FloatLib
import FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.CorrectlyRounded.Proof
open FloatLib.Floats.Formats.DecimalInterchange

#eval (Transcendentals.CorrectlyRounded.exp2 Format.decimal32 .nearest 0.5).value
-- 1.414214
#eval (Transcendentals.CorrectlyRounded.exp2 Format.decimal32 .down 0.5).value
-- 1.414213
#eval (Transcendentals.CorrectlyRounded.exp2 Format.decimal32 .nearest 0.5).status.inexact
-- true
```

Seven digits of $1.41421356\ldots$ come back. To nearest the last digit goes up, toward negative infinity the tail is cut off, and `inexact` is raised either way. For finite operands in the domain, [[FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.CorrectlyRounded.apply_roundsTo]] proves that the result is the real function rounded once in the direction you asked for, with its five flags, and the functions of two operands have theorems of their own, such as [[FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.CorrectlyRounded.atan2_roundsTo]]. The results at infinities, at NaNs and outside the domain follow the tables of the standard, and those are definitions. `Transcendentals.Certified.exp2` and its siblings are a second form: they return the nearest-even result when an enclosure settles the rounding, and `none` when it doesn't.

## How to keep track of exception flags

An `Outcome` records the result and flags for one operation. An environment records the current rounding direction and the flags accumulated across a calculation. For example, decimal32 division rounds $1/3$ to $0.3333333$ and raises `inexact`. A subsequent division of one by zero must retain that flag as well as raising `divideByZero`. `Environment.run` supplies the rounding direction and combines the returned flags with the existing flags.

For groups of exceptions there's `saveAllFlags`, `testFlags`, `testSavedFlags`, `restoreFlags`, and `lowerFlags` and `raiseFlags` to clear and set them. Restoring a flag that was clear when saved clears it, and flags outside the group stay as they were. `Environment.withRounding` changes the rounding for one computation. Round $1/3$ toward positive infinity there to get $0.3333334$. The caller gets its rounding back, and the new inexact flag stays on the tab. Our proofs describe every flag after an operation, a clear or a restore, and show that regrouping operations doesn't change the accumulated flags.

## How to choose the exponent yourself

With `quantize`, named for the quantum it sets, you choose the exponent yourself, by passing a second datum that has it. Quantizing $1.235$ to the exponent of $0.01$ under nearest-even gives $1.24$ and raises inexact, because the value ties between coefficients 123 and 124, and 124 is even. Quantizing $1.2$ the same way gives $1.20$ with no flag, since the value is unchanged.

The proofs fix the quantum of a successful result, bound nearest rounding by half that grid step, and give directed bounds within one grid step in the other modes. A rounded coefficient that can't fit at the requested exponent raises invalid, and quantize never raises overflow, underflow or divide-by-zero, not even on an inexact subnormal result.

## How to round to a whole number

Rounding to a whole number, called integral rounding, picks the exponent for you: $\max(q,0)$ for an input exponent $q$. `roundToIntegral` and `roundToIntegralExact` return the same integer-valued datum, keeping the sign of a zero, and differ only in the flag. Under nearest-even $1.5$ becomes $2$ in both, and only `roundToIntegralExact` raises inexact. An integral datum with a positive exponent, such as $12\cdot10^2$, keeps it.

**Note:** Integral rounding needs a nonnegative largest quantum exponent, as in all three IEEE decimal formats. A custom layout with only negative exponents can't encode the requested quantum, so there the operation raises invalid.

## How to compare decimal numbers

Numerical comparison says $1.20$ and $1.2$ are equal. `totalOrder` tells them apart by their exponents and orders signed zeros and NaNs too. We prove it's transitive, total and in agreement with the numerical, sign and cohort rules. For NaN payloads it follows the documented implementation choice.

Ten of the 22 IEEE comparisons come in two forms, quiet and signaling. We prove the two return the same Boolean and differ only in the invalid flag, which the signaling form also raises for a quiet NaN. Classification tells the ten IEEE classes apart, such as positive zero or quiet NaN, and changing cohort never turns a normal value subnormal.

## What are the neighbours of a value?

Neighbours in decimal can be lopsided. In decimal32 the value just below $1.000000$ is $0.9999999$ and the value just above it is $1.000001$, a step of $10^{-7}$ down and $10^{-6}$ up, because the grid gets ten times coarser at a power of ten. `nextDown` and `nextUp` handle that boundary with the finest quantum for the delivered value, and their adjacency proofs rule out any valid value in between.

## How to scale and take a remainder

`scale` multiplies by $10^n$ by shifting the quantum, rounding once if the result no longer fits. `logB` reports the exponent of the leading digit. `remainder` uses the nearest-even integer quotient. Seven halves is a tie between three and four, nearest-even picks four, and so the remainder of $7/2$ is $7-4\cdot2=-1$. The remainder is negative because the selected integer quotient is four. FloatLib proves it's exactly representable and at most half the divisor in magnitude, and that ties take the even quotient.

A long product can leave the exponent range halfway and come back. `Arithmetic.scaledProd` avoids that by returning the product in two parts, a datum `product` between one and ten in magnitude and an integer `scaleFactor`, so that the product of the operands is `product` times ten to the `scaleFactor`, up to one rounding:

```lean standalone
import FloatLib
open FloatLib.Floats.Formats.DecimalInterchange

#eval Arithmetic.scaledProd Format.decimal64 .nearest #[2.50, 4]
-- { product := 1.000, scaleFactor := 1, status := {} }
#eval Arithmetic.scaledProd Format.decimal64 .nearest #[1e384, 1e384, 1e-398]
-- { product := 1, scaleFactor := 370, status := {} }
```

The second product passes $10^{768}$ on its way, far above the largest decimal64 number, and no flag is raised. [[FloatLib.Floats.Formats.DecimalInterchange.Arithmetic.scaledProd_eq_project]] says that `product` is one rounding of the exact product divided by its power of ten. `scaledProdSum` and `scaledProdDiff` do the same for a product of sums and of differences. For a sum that rounds at every addition, `Arithmetic.reduceInOrder` and `reduceAlong` take the format of the accumulator and the order of the additions as arguments and collect the flags of every step, and [[FloatLib.Floats.Formats.DecimalInterchange.Arithmetic.abs_reduceAlong_sub_le]] bounds the error of the sum in any order.

## How decimal numbers are stored in bits

To store a datum you encode it as a *word*, a fixed-width pattern of bits. Decimal formats come in two encodings. Binary integer decimal, or BID, stores the coefficient as one binary integer. Densely packed decimal, or DPD, packs it in declets. Our [decimal codec proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/DecimalInterchange/Basic.lean) show that decimal32, decimal64 and decimal128 data make exact round trips through both. `decode_transcode` says a word transcoded, that is, converted to the other encoding, decodes to the same datum, down to the exponent, the signs of zero and infinity, and a NaN's sign, signaling bit and payload, so BID $120 \cdot 10^{-2}$ becomes DPD $120 \cdot 10^{-2}$, exponent $-2$ and all.

The bits themselves may not come back, because some patterns are redundant, other spellings of the same datum. Every word decodes to a valid datum, though, and `Encoding.encode?_decode` proves that encoding it again gives its canonical word, the standard spelling. None of this rounds. `encode?` rejects a datum that doesn't fit instead of nudging it. Sign operations such as negation, on raw BID and DPD words, leave every other bit alone, even in redundant encodings and signaling NaNs.

## How to print a decimal number

The bits keep the quantum, and text can too, if you ask. Print $1.20$ as `1.2` and the number survives, but the quantum is gone. `Formatting.formatExact` keeps the entire datum, zero signs and NaN metadata included, and reading that text back in any rounding mode provably gives the same datum and its canonical BID and DPD words.

Ask for two significant digits and $1.25$ rounds to $1.2$ under nearest-even and to $1.3$ under nearest-away. The formatter takes any positive digit count, and the text exponent is unbounded. We prove the requested precision, the rounding direction, the midpoint behaviour and numerical inexactness. We also prove that if you print at least the source precision, the value survives the round trip in any pair of rounding modes, one to print and one to read.

## How to convert to other formats

Decimal $0.1$ can't keep its value in binary, so the converter rounds that exact rational once. Coming back, it starts from the binary value actually stored, so you may not get the original spelling. Conversions between decimal formats and to posits, another kind of number format, also decode exactly and round once. An exact decimal-to-decimal conversion picks the available cohort exponent closest to the source's preferred one. Posit destinations follow their own appended-bit rounding rule, which saturates at the range limits, and encoding to BID or DPD adds no rounding.

Conversion to an integer rounds first and checks the range after, so a small negative fraction can round to unsigned zero instead of being rejected. Each of the five rounding directions has a quiet and an `Exact` variant returning the same integer, and only the second reports inexactness. Exceptional sources (NaNs and infinities) and out-of-range results raise invalid and return integer zero, our choice for an invalid integer result. Integer-to-decimal conversion uses the same decimal projection as arithmetic, with rounding bounds and exception behaviour proved for each destination. Certified decimal `expm1` and `logp1` are in [Elementary functions](#/chapter/elementary-functions/how-to-use-these-functions-with-decimal-numbers), and return a value only when its rounding has been certified.

## Can Lean's kernel check a decimal computation?

Yes. A statement about concrete decimal data is decided by evaluation, and `float_decide` makes that evaluation cheap. The reference definitions round exact rational numbers, which the kernel reduces in milliseconds. Before the kernel runs, `float_decide` rewrites `add`, `sub`, `mul`, `div`, `remainder`, `sqrt`, `rSqrt`, `hypot`, `pown`, `rootn`, `fma`, the reductions `sum`, `sumAbs`, `sumSquare` and `dot`, `scale`, `logB`, `nextUp`, `nextDown`, `quantize`, the integral roundings, the conversions between formats, to and from integers and to and from character sequences, the four encoding operations, the 22 comparisons, the total order, the classification and the minimum and maximum operations to forms that compute on the sign, the coefficient and the exponent as natural numbers. Each rewrite is a theorem that the form equals the operation for every format, rounding direction and datum, so the statement you prove is about the operation itself.

```lean standalone
import FloatLib

open FloatLib.Floats.Formats.DecimalInterchange

example :
    (Arithmetic.add Format.decimal64 .nearest 1.20 0.30).value = 1.50 ∧
      (Arithmetic.div Format.decimal64 .nearest 1e0 3e0).value = 0.3333333333333333 ∧
      (Arithmetic.quantize Format.decimal64 .nearest 123.45 1e0).value = .finite false 123 0 ∧
      (Datum.compareQuietLess 1.20 1.3).value = true ∧
      (Arithmetic.nextUp Format.decimal32 1e0).value = 1.000001 := by
  float_decide
```

With the rewrite a decimal64 operation costs a few tenths of a millisecond in the kernel, and the table in `benchmarks/results/ieee2019` has the time of every operation. The functions of clause 9.2, certified and total, the scaled products and the reductions in a chosen order are reduced as they are defined.
