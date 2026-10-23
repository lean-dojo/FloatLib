---
number: "09"
slug: decimal-arithmetic
title: "Decimal arithmetic"
summary: "Decimal arithmetic chooses both a rounded value and a cohort member, preserving quantum exponents and reporting exceptions explicitly."
phases: [ieee-formats, status-and-directed]
---

The trailing zero in $1.20$ records a hundredths place that $1.2$ doesn't have. As rationals they're equal, but their stored forms are $120\cdot10^{-2}$ and $12\cdot10^{-1}$. IEEE decimal arithmetic calls representations with the same numerical value members of a *cohort*. The exponent is the *quantum exponent*: $-2$ makes the coefficient count hundredths, and $-1$ makes it count tenths. Dropping the trailing zero changes the represented datum even though a rational equality test would still pass.

## Encoding the complete datum

Decimal formats come in two encodings. Binary integer decimal, or BID, stores the coefficient as a binary integer, and densely packed decimal, or DPD, packs it in groups of decimal digits. In the [decimal codec proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/DecimalInterchange/Basic.lean) we show that decimal32, decimal64 and decimal128 make exact datum round trips in both. Switching from one encoding to the other keeps the coefficient and its decimal exponent. It also keeps the sign of zero, the sign of an infinity, and a NaN's sign, signaling bit and payload. That is what `decode_transcode` says: convert a word and decode it in the destination encoding, and you get the same datum as decoding the original word in its source encoding. So BID $120 \cdot 10^{-2}$ becomes DPD $120 \cdot 10^{-2}$, with the exponent still $-2$, and nothing normalizes it to $12 \cdot 10^{-1}$.

Some bit patterns are redundant. Every word decodes to a valid datum, but encoding that datum again gives its canonical word, as `Encoding.encode?_decode` proves. So a trip to the other encoding and back can change the bits while every component of the datum survives. None of this is rounding, though. When a datum doesn't fit the destination, `encode?` rejects it instead of rounding it to a nearby one.

All three standard formats are presets of one descriptor. A layout picks the number of declets, the width of the exponent continuation and the exponent bias, and its precision is three digits per declet plus one leading digit. The algorithms and the codec proofs work for custom layouts with any bias, so you can try other choices of precision and range :) The IEEE names keep meaning the parameters the standard specifies. If a theorem needs quantum zero to be available, it says so.

## Arithmetic and preferred exponents

Adding $1.20+0.30$ gives us a choice of cohort as well as a sum. Both operands have quantum exponent $-2$, so the exact result is

$$
(120+30)\cdot10^{-2}=150\cdot10^{-2}.
$$

For addition the preferred exponent is the smaller input exponent, here $-2$, so the runtime returns $1.50$ and raises no exception flags. Multiplication adds the input exponents, so $1.2\cdot3.0$ has preferred exponent $-2$ and comes back as $3.60$. Dropping a trailing zero from either result would keep the number and change the cohort member. `preferredCohort` moves toward the preferred exponent within the destination's limits. It gets there only by removing trailing zeros of the coefficient, so the value never changes on the way.

The [decimal arithmetic API](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/DecimalInterchange/Arithmetic/Basic.lean) has addition, subtraction, multiplication, division, fused multiply-add and square root for decimal32, decimal64 and decimal128. Every one of them takes decoded `Datum` values and returns an `Outcome` that pairs the result with five exception flags, and you only choose BID or DPD when you read or write the bits. All six operations accept the five decimal rounding modes: nearest with ties to even or away, toward zero, toward positive infinity, and toward negative infinity.

```lean standalone
import FloatLib

open FloatLib.Floats.Formats.DecimalInterchange

#eval (Arithmetic.add Format.decimal32 .nearestEven
    (.finite false 120 (-2)) (.finite false 30 (-2))).value
-- 1.50
#eval (Arithmetic.mul Format.decimal32 .nearestEven
    (.finite false 12 (-1)) (.finite false 30 (-1))).value
-- 3.60
```

When the digits don't fit, the rounding mode settles the numerical result first. Decimal32 has seven significant digits, and the exact sum $1.000000+0.0000005=1.0000005$ sits halfway between $1.000000$ and $1.000001$. Nearest-even picks the first because coefficient 1000000 is even, nearest-away picks the second, and both report inexact. Finite addition, subtraction, multiplication, division and FMA all form the exact rational expression before this projection. So FMA never rounds its intermediate product, and it never signals overflow on that product alone. Square root finds the two adjacent candidates with an integer square root and then compares the radicand with the square of their midpoint. That decides which candidate to return without computing a decimal approximation to the irrational root. Its preferred exponent is the floor of half the input exponent. Negative zero comes back as negative zero, while a negative nonzero input returns a quiet NaN and raises invalid.

In the [arithmetic proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/DecimalInterchange/Arithmetic/Proof.lean) we prove that the rational operations deliver a valid datum in the destination, and the [square-root proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/DecimalInterchange/Sqrt/Proof.lean) do the same for square root. With finite operands and no overflow, the error in a nearest mode is at most half the selected decimal grid step. For that bound, division needs a nonzero denominator and square root a nonnegative input. In the directed modes the theorems put the result on the required side of the exact value, and the midpoint theorems settle ties. Any representable rational projects to its own value. The inexactness theorems tie the flag to a numerical change, so moving to another cohort member doesn't raise inexact by itself.

Signs and flags tell apart cases that rational equality can't. Exact cancellation in $1.20-1.20$ returns a zero with exponent $-2$, and that zero is negative when rounding toward negative infinity and positive in the other four modes. A signaling NaN raises invalid and comes back quiet. When the first NaN operand's payload fits the destination, that operand supplies both the sign and the payload. Five flags come back: invalid, divide-by-zero, overflow, underflow and inexact. Decimal tests tininess **before rounding**, unlike the [binary kernels](#/chapter/ieee-binary-formats/status-flags), which test it after rounding, and underflow needs both a tiny exact result and inexactness. The cohort theorems also determine the returned exponent. For an exact result, the projection and square-root theorems compare its exponent with every valid representation of that value and prove that it is the one closest to the preferred exponent. An inexact finite result takes the smallest quantum exponent in its cohort, even when the exact square root is irrational. All of this is proved in the [preferred-cohort proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/DecimalInterchange/Projection/Cohort.lean), the [minimal-quantum proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/DecimalInterchange/Projection/Minimal.lean) and their square-root counterparts.

### Powers and roots retain a quantum

The decimal [algebraic
API](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/DecimalInterchange/Algebraic/Runtime.lean)
also has `square`, `rsqrt`, `hypot`, `powInt`, and `rootN`, all with the same five rounding modes.
Their intermediate rational expressions are exact, and general roots compare integer powers at
candidate midpoints. An exact result keeps its preferred quantum wherever the format allows it. Say
we cube $2.0$. That gives $8.000$, and the cube root of that gives $2.0$ again.

```lean standalone
import FloatLib
open FloatLib.Floats.Formats.DecimalInterchange

#eval (Arithmetic.powInt Format.decimal32 .nearestEven (.finite false 20 (-1)) 3).value
-- 8.000
#eval (Arithmetic.rootN Format.decimal32 .nearestEven (.finite false 8000 (-3)) 3).value
-- 2.0
```

These operations work on custom decimal layouts too. Given finite operands and no reported overflow,
the [numerical
bounds](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/DecimalInterchange/Algebraic/Proof.lean)
give a half-grid error bound in the nearest modes and a directed bound in the others. Reciprocal
square root needs a positive input, and an integer power with a negative exponent needs a nonzero
base. The [general-root
bounds](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/DecimalInterchange/Algebraic/Root/Semantics.lean)
need a nonzero base and degree, with an odd degree for a negative base. They compare the delivered
value with a real root whose defining power equation has its own proof, and other theorems cover
validity and exceptional inputs.

## Accumulating exception flags

An `Outcome` tells us what happened in one operation, but a longer calculation has to remember earlier exceptions too. Say decimal32 division rounds $1/3$ to $0.3333333$ and raises inexact, and then the next operation divides $1$ by zero. That raises divide-by-zero, and it must not erase the inexact flag from the first.

`Environment.run` supplies the current rounding direction and accumulates the returned flags. The environment is an ordinary Lean value passed between operations, so its inputs and outputs show exactly where the flags are kept. The operations `saveAllFlags`, `testFlags`, `testSavedFlags`, `lowerFlags`, `raiseFlags`, and `restoreFlags` work on selected groups of exceptions. Restoring a flag that was clear when it was saved clears it, and flags outside the group stay as they were. `Environment.withRounding` changes the rounding inside one computation. Round $1/3$ toward positive infinity there and you get $0.3333334$. On return the caller gets its own rounding direction back, and the new inexact flag survives. The proofs describe every flag after an operation, a clear or a restore, and they show that grouping the operations differently doesn't change the accumulated flags.

## Quantization and integral rounding

With `quantize` you choose the exponent yourself. Quantize $1.235$ to the exponent of $0.01$ under nearest-even and you get $1.24$, because the adjacent coefficients are 123 and 124, and 124 is even. That result has exponent $-2$ and raises inexact, while quantizing $1.2$ to the same exponent gives $1.20$ with no inexact flag, since the numerical value hasn't changed. The quantize proofs fix the quantum of a successful result and bound nearest rounding by half that grid step. For the other modes they give directed bounds and an error below one grid step, and they also tie inexact to a numerical change. If the rounded coefficient can't fit at the requested exponent, quantize raises invalid. It never raises overflow, underflow or divide-by-zero, so even an inexact subnormal quantize result has no underflow flag.

Integral rounding chooses exponent $\max(q,0)$ for an input exponent $q$. The two operations `roundToIntegral` and `roundToIntegralExact` return the same integer-valued datum, and both keep the sign of a zero result. Under nearest-even, $1.5$ becomes $2$ in either variant, but only `roundToIntegralExact` raises inexact. A datum that is already integral with a positive exponent, such as $12\cdot10^2$, keeps that exponent. Integral rounding needs the format's largest quantum exponent to be nonnegative, which it is in all three IEEE decimal formats. In a custom layout whose exponents are all negative, the requested quantum can't be encoded, so the operation raises invalid.

## Comparing values and representations

Numerical comparison treats $1.20$ and $1.2$ as equal, but `totalOrder` can tell them apart by their exponents, and it orders signed zeros and NaNs as well. Its proofs give transitivity, totality, and agreement with the numerical, sign and cohort rules, and for NaN payloads it follows the documented implementation choice. For each of the 22 quiet and signaling comparisons, the Boolean answer agrees with its counterpart. The invalid flags differ when a quiet NaN is present. Classification tells the ten IEEE classes apart, and we prove that changing cohort never turns a normal value into a subnormal one. Sign operations on raw BID and DPD words leave every other bit alone, even in redundant encodings and signaling NaNs.

## Adjacent values, scaling, and remainder

Neighbours in decimal can be lopsided. In decimal32, the value just below $1.000000$ is $0.9999999$ and the value just above it is $1.000001$. That's a distance of $10^{-7}$ below and $10^{-6}$ above, because the grid changes when you cross a power of ten. `nextDown` and `nextUp` handle that boundary and choose the finest quantum that represents the delivered value. Their adjacency proofs rule out every valid value between the input and its neighbor.

For decimal formats, `scale` multiplies by $10^n$ by shifting a datum's quantum, and it rounds once if the result no longer fits. `remainder` uses the nearest-even integer quotient, so the remainder of $7/2$ is $7-4\cdot2=-1$. Yes, negative :) Its proofs give exact representability, the half-divisor bound on the magnitude, and the even-quotient rule at a tie. `decimalExponent` reports the exponent of the leading decimal digit.

## Decimal text round trips

Print $1.20$ as `1.2` and the number is fine, but its quantum is gone. `Formatting.formatExact` keeps the entire datum, zero signs and NaN metadata included. Parse that text in any rounding mode and the parsing theorem says you get the same datum back, and the BID and DPD word theorem says you get its canonical encoding. Formatting to two significant digits rounds $1.25$ to $1.2$ under nearest-even and to $1.3$ under nearest-away. The digit count can be any positive integer, with no bound on the text exponent. We prove the requested precision, the rounding direction, the midpoint behavior and numerical inexactness. Ask for at least the source precision and the value survives output and input in any pair of rounding modes.

## Conversions between numerical formats

No finite binary fraction equals $1/10$, so decimal $0.1$ can't keep its value when it is converted to binary. The converter starts from that exact rational and rounds once into the destination. Going back, it starts from the binary value actually stored, so it need not recover the original decimal spelling. Decimal formats convert to each other and to posits by the same route: the source is decoded exactly and then rounded in the destination. When the value is exact, decimal-to-decimal conversion also picks the available cohort exponent closest to the source's preferred exponent. Posit destinations follow their own appended-bit rounding rule, which saturates at the range limits, and encoding to BID or DPD adds no rounding of its own.

Integer conversion rounds before checking the destination range. That ordering matters, because a small negative fraction can round to unsigned zero. Each of the five directions has a quiet and an `Exact` variant that return the same integer, and only the second reports inexactness. Exceptional sources, and rounded values outside the destination range, raise invalid and deliver zero in this binding. Integer-to-decimal conversion uses the same decimal projection as every other source. The proofs state the rounding bounds and exception behavior for each destination. Certified decimal `expMinus1` and `logPlus1` are in [Elementary functions](#/chapter/elementary-functions/certified-decimal-functions), and those APIs return a value only when its rounding has been certified.