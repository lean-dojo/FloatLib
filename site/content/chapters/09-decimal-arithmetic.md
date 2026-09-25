---
number: "09"
slug: decimal-arithmetic
title: "Decimal arithmetic"
summary: "Decimal arithmetic chooses both a rounded value and a cohort member, preserving quantum exponents and reporting exceptions explicitly."
phases: [ieee-formats, status-and-directed]
---

With decimal, we need to keep track of more than the numerical value of a datum. The amounts $1.20 = 120 \cdot 10^{-2}$ and $1.2 = 12 \cdot 10^{-1}$ are equal as rationals, but their coefficients and exponents differ. They belong to the same *cohort*: different representations of one value. A codec that silently removes the trailing zero has changed the datum even though a rational equality test would pass.

## Encoding the complete datum

The [decimal codec proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/DecimalInterchange/Basic.lean) establish exact datum round trips for decimal32, decimal64, and decimal128 in both binary integer decimal (BID) and densely packed decimal (DPD). BID stores the coefficient as a binary integer; DPD packs groups of decimal digits. Changing between them preserves the coefficient and its decimal exponent. It also preserves the sign of zero, infinity sign, and NaN sign, signaling bit, and payload.

The theorem `decode_transcode` states this directly: decoding a converted word in the destination encoding gives the same datum as decoding the original word in its source encoding. Thus BID $120 \cdot 10^{-2}$ becomes DPD $120 \cdot 10^{-2}$, with the exponent still $-2$. The conversion does not normalize it to $12 \cdot 10^{-1}$.

Some bit patterns are redundant. Every word decodes to a valid datum, but encoding that datum again returns its canonical word, as `Encoding.encode?_decode` proves. Converting to the other encoding and back can therefore change the bits while preserving every component of the datum. This is different from rounding: `encode?` rejects a datum that does not fit the destination rather than rounding it to a nearby one.

The three standard formats are presets of one descriptor. A layout chooses the number of declets, the exponent continuation width, and the exponent bias; its precision is three digits per declet plus one leading digit. The algorithms and codec proofs also work for custom layouts with arbitrary bias. A theorem that needs quantum zero to be available says so explicitly. Custom layouts let us study other choices of precision and range; the IEEE names still refer to their specified parameters.

<a id="arithmetic-keeps-track-of-the-cohort"></a>

## Arithmetic and preferred exponents

The [decimal arithmetic API](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/DecimalInterchange/Arithmetic/Basic.lean) provides addition, subtraction, multiplication, division, fused multiply-add, and square root for decimal32, decimal64, and decimal128. The operations consume decoded `Datum` values and return an `Outcome`, pairing the result with five exception flags. BID or DPD is chosen when reading or writing the bits. All six operations accept the five decimal rounding modes: nearest with ties to even or away, toward zero, toward positive infinity, and toward negative infinity.

We can see the preferred exponent at work in $1.20+0.30$. Both operands have quantum exponent $-2$, so their exact sum is

$$
(120+30)\cdot10^{-2}=150\cdot10^{-2}.
$$

The preferred exponent for addition is the smaller input exponent, here $-2$. The runtime therefore returns $1.50$, preserving that exponent, with no exception flags. Multiplication adds the input exponents: $1.2\cdot3.0$ has preferred exponent $-2$ and returns $3.60$. Removing a trailing zero would preserve each numerical result but change its cohort member. `preferredCohort` moves toward the preferred exponent by removing only exact trailing coefficient zeros, within the destination's limits.

```lean standalone
import FloatLib

open FloatLib.Floats.Formats.DecimalInterchange

#eval (Arithmetic.add Format.decimal32 .nearestEven
    (.finite false 120 (-2)) (.finite false 30 (-2))).value
-- FloatLib.Floats.Formats.DecimalInterchange.Datum.finite false 150 (-2)
#eval (Arithmetic.mul Format.decimal32 .nearestEven
    (.finite false 12 (-1)) (.finite false 30 (-1))).value
-- FloatLib.Floats.Formats.DecimalInterchange.Datum.finite false 360 (-2)
```

When precision is insufficient, the rounding mode decides the numerical result first. Decimal32 has seven significant digits. The exact sum $1.000000+0.0000005=1.0000005$ lies halfway between $1.000000$ and $1.000001$. Nearest-even chooses the former because coefficient 1000000 is even; nearest-away chooses the latter. Both results report inexact. Finite addition, subtraction, multiplication, division, and FMA form the exact rational expression before this projection. FMA therefore never rounds or signals overflow on its intermediate product alone.

Square root uses an integer square root to locate adjacent candidates, then compares the radicand with their squared midpoint. This decides the rounding without approximating the real root. Its preferred exponent is the floor of half the input exponent. Square root preserves negative zero, while a negative nonzero input returns a quiet NaN and raises invalid.

The [arithmetic proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/DecimalInterchange/Arithmetic/Proof.lean) establish destination validity for the rational operations; the [square-root proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/DecimalInterchange/Sqrt/Proof.lean) do so for square root. With finite operands and no overflow, the nearest-mode error is at most half the selected decimal grid step; division requires a nonzero denominator and square root a nonnegative input. Directed-rounding theorems place the result on the required side of the exact value, and midpoint theorems resolve ties. Every representable rational projects to its exact numerical value. The inexactness theorems detect a numerical change, so choosing another cohort member does not itself raise inexact.

Signs and flags distinguish cases that rational equality cannot. Exact cancellation in $1.20-1.20$ returns a zero with exponent $-2$: negative under rounding toward negative infinity, positive under the other four modes. A signaling NaN raises invalid and is quieted; the first NaN operand supplies the sign and payload when that payload fits the destination. The five returned flags are invalid, divide-by-zero, overflow, underflow, and inexact. Decimal tininess is tested **before rounding**, and underflow requires both a tiny exact result and inexactness. The [binary kernels](#/chapter/ieee-binary-formats/status-flags) test tininess after rounding.

Cohort selection has a stronger guarantee than preserving the numerical value. For an exact result, the projection and square-root theorems compare its exponent with every valid representation of that value and prove that it is closest to the preferred exponent. An inexact finite result uses the smallest quantum exponent in its cohort, including when the exact square root is irrational. The [preferred-cohort proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/DecimalInterchange/Projection/Cohort.lean), [minimal-quantum proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/DecimalInterchange/Projection/Minimal.lean), and their square-root counterparts establish these results.

### Powers and roots retain a quantum

The decimal [algebraic API](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/DecimalInterchange/Algebraic/Runtime.lean)
also provides `square`, `rsqrt`, `hypot`, `powInt`, and `rootN`, all with the same five rounding
modes. Their intermediate rational expressions are exact, and general roots compare integer
powers at candidate midpoints. Exact results keep their preferred quantum where the format
allows it: cubing $2.0$ gives $8.000$, and taking its cube root gives $2.0$.

```lean standalone
import FloatLib
open FloatLib.Floats.Formats.DecimalInterchange

#eval (Arithmetic.powInt Format.decimal32 .nearestEven (.finite false 20 (-1)) 3).value
-- FloatLib.Floats.Formats.DecimalInterchange.Datum.finite false 8000 (-3)
#eval (Arithmetic.rootN Format.decimal32 .nearestEven (.finite false 8000 (-3)) 3).value
-- FloatLib.Floats.Formats.DecimalInterchange.Datum.finite false 20 (-1)
```

These operations work on custom decimal layouts too. The [numerical bounds](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/DecimalInterchange/Algebraic/Proof.lean)
require finite operands and no reported overflow. They give half-grid error bounds for the
nearest modes and directed bounds for the other modes. Reciprocal square root requires
a positive input; integer powers require a nonzero base when the exponent is negative.
The [general-root bounds](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/DecimalInterchange/Algebraic/Root/Semantics.lean)
require a nonzero base and degree, with an odd degree for a negative base. They compare the
delivered value with a real root whose defining power equation is proved separately.
Validity and exceptional-input results are separate from these numerical bounds.

<a id="remembering-exceptions-across-a-calculation"></a>

## Accumulating exception flags

An `Outcome` tells us what happened in one operation. A longer calculation needs to remember earlier exceptions too. Suppose decimal32 division rounds $1/3$ to $0.3333333$, raising inexact, and the next operation divides $1$ by zero. The second operation raises divide-by-zero; it must not erase the earlier inexact flag.

`Environment.run` supplies the current rounding direction and accumulates the returned flags. The environment is an ordinary Lean value, so a function's inputs and outputs show where that state goes. `saveAllFlags`, `testFlags`, `testSavedFlags`, `lowerFlags`, `raiseFlags`, and `restoreFlags` support selected groups of exceptions. Restoring a saved clear flag clears it; flags outside the group stay as they were.

`Environment.withRounding` changes rounding within one computation. Rounding $1/3$ toward positive infinity produces $0.3333334$; on return, the caller's rounding direction is restored and the new inexact flag survives. The proofs characterize every flag after an operation, clearing, or restoration, and establish that grouping operations does not change the accumulated flags.

<a id="choosing-a-decimal-grid"></a>

## Quantization and integral rounding

`quantize` requests a particular exponent rather than allowing the operation to choose one. Quantizing $1.235$ to the exponent of $0.01$ gives $1.24$ under nearest-even: the adjacent coefficients are 123 and 124, and 124 is even. The result has exponent $-2$ and raises inexact. Quantizing $1.2$ to the same exponent instead gives $1.20$ without inexact, because the numerical value has not changed.

The quantize proofs fix the successful result's quantum, bound nearest rounding by half that grid step, and characterize inexactness as a numerical change. Directed bounds and an error below one grid step cover the other modes. If the rounded coefficient cannot fit at the requested exponent, quantize raises invalid; it never raises overflow, underflow, or divide-by-zero. Even an inexact subnormal quantize result therefore has no underflow flag.

Integral rounding chooses exponent $\max(q,0)$ for an input exponent $q$. Both `roundToIntegral` and `roundToIntegralExact` return the same integer-valued datum and preserve the sign of a zero result. Under nearest-even, $1.5$ becomes $2$ in either variant; only `roundToIntegralExact` raises inexact. An already integral datum with positive exponent, such as $12\cdot10^2$, keeps that exponent.

This requires the format's largest quantum exponent to be nonnegative, as it is in all three IEEE decimal formats. A custom layout whose exponents are all negative cannot encode the requested quantum; the operation raises invalid, and the proofs characterize that case too.

## Comparing values and representations

Numerical comparison treats $1.20$ and $1.2$ as equal. `totalOrder` can still distinguish them by their exponents, and also orders signed zeros and NaNs. Its proofs establish transitivity, totality, and agreement with the numerical, sign, and cohort rules. NaN payloads follow the documented implementation choice.

The API provides all 22 quiet and signaling comparisons. Their Boolean answers agree; their invalid flags differ when a quiet NaN is present. Classification distinguishes the ten IEEE classes and proves that changing cohort does not turn a normal value into a subnormal one. Sign operations on raw BID and DPD words preserve every other bit, even for redundant encodings and signaling NaNs.

<a id="moving-through-the-decimal-values"></a>

## Adjacent values, scaling, and remainder

The value immediately below decimal32's $1.000000$ is $0.9999999$. The value immediately above it is $1.000001$. The distances are $10^{-7}$ below and $10^{-6}$ above: crossing a power of ten changes the grid. `nextDown` and `nextUp` handle that boundary, and their adjacency proofs rule out every valid value between the input and its neighbor. They choose the finest quantum that represents the delivered value.

For decimal formats, `scale` multiplies by $10^n$ by shifting a datum's quantum and rounds once if the result no longer fits. `remainder` uses the nearest-even integer quotient: the remainder of $7/2$ is $7-4\cdot2=-1$. Its proofs establish exact representability, the half-divisor magnitude bound, and the even-quotient rule at a tie. `decimalExponent` reports the exponent of the leading decimal digit.

<a id="writing-a-value-without-losing-its-representation"></a>

## Decimal text round trips

Printing $1.20$ as `1.2` is numerically harmless, but loses its quantum. `Formatting.formatExact` preserves the entire datum, including zero signs and NaN metadata. The parsing theorem recovers that datum in every rounding mode; the BID and DPD word theorem recovers its canonical encoding.

Requested precision is a separate choice. Formatting to two significant digits rounds $1.25$ to $1.2$ under nearest-even and $1.3$ under nearest-away. The digit count is any positive integer, and the text exponent is unbounded. The proofs establish the requested precision, rounding direction, midpoint behavior, and numerical inexactness. Asking for at least the source precision preserves its value through output and input in any pair of rounding modes.

<a id="crossing-into-another-format"></a>

## Conversions between numerical formats

Converting decimal $0.1$ to binary cannot preserve its value exactly: no finite binary fraction equals $1/10$. The converter starts from that exact rational and rounds once into the destination. Converting a binary value back to decimal starts from the binary value actually stored, so it need not recover the original decimal spelling.

The same route connects decimal formats to each other and to posits: exact source decoding, then destination rounding. Decimal-to-decimal conversion also chooses the available cohort exponent closest to the source's preferred exponent when the value is exact. Posit destinations follow their own appended-bit rounding rule, including saturation at the range limits. BID and DPD encoding adds no further numerical rounding.

Integer conversion rounds before checking the destination range. That ordering matters: a small negative fraction can round to unsigned zero. The five directions each have a quiet and an `Exact` variant; they return the same integer, while the latter reports inexactness. Exceptional sources and rounded values outside the destination range raise invalid and deliver zero in this binding. Integer-to-decimal conversion uses the same decimal projection as the other sources.

The proofs state the rounding bounds and exception behavior for each destination. The [validation discussion](#/chapter/external-validation/decimal-datums-and-exact-text) explains what an independent comparison must check about complete datums, conversions, and flags.

For certified decimal `expMinus1` and `logPlus1`, see [Elementary functions](#/chapter/elementary-functions/certified-decimal-functions). Those APIs return a value only when its rounding has been certified.
