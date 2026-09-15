---
number: "03"
slug: a-short-history-of-floating-point
title: "A short history of floating point"
summary: "Common arithmetic rules, numerical failures, and newer formats explain the choices made in today's floating-point systems."
---

To read an old floating-point word, we need more than its field widths: we need the radix, bias, and rules for reserved values. Machines have differed in all three, so moving numerical code between them has often required more than changing the word size. IEEE 754 established common formats and arithmetic rules; more recent low-precision formats allocate their limited bit patterns differently. The encodings described in [chapter 02](#/chapter/from-reals-to-machine-numbers) fit into the timeline in [Figure 3.1](#/chapter/a-short-history-of-floating-point/figure-ch04-standards-timeline): choices about range, precision, and exceptional results keep recurring.

![Timeline of floating-point formats, standards, machines, and verification results, from 1914 through P3109](assets/ch04-standards-timeline.png "Selected developments in floating-point representation, standardization, and verification. The P3109 entry refers to an interim report.")

<a id="before-there-was-a-standard"></a>

## Before IEEE 754

The sliding exponent predates electronic computing. Leonardo Torres y Quevedo described a mechanical unit with a floating decimal point in 1914, and Konrad Zuse's Z3, completed in Berlin in 1941, used binary floating point with 14 stored significand bits and a 7-bit exponent. The Z3 also had encodings for an infinite result and an undefined one.

Through the 1960s and 1970s manufacturers built floating-point units with incompatible formats and arithmetic rules. IBM's System/360, announced in 1964, used hexadecimal floating point. Normalization shifted the significand four bits at a time until its first hexadecimal digit was nonzero. If that digit was 1, its binary expansion began with three zero bits followed by a one. Those leading zeros occupied storage without contributing precision. A 32-bit System/360 float therefore stored 24 significand bits but could provide as few as 21 significant binary digits, depending on its leading hexadecimal digit.

The CDC 6600, delivered the same year, used 60-bit words with an 11-bit exponent and a 48-bit coefficient, and its arithmetic was not correctly rounded. The Cray-1 in 1976 flushed underflows to zero without a flag: a result too small to normalize was replaced by zero. This affects a useful property of subtraction, that $x - y = 0$ implies $x = y$. Two distinct representable values can have a difference below the smallest normal value. If that difference flushes to zero, testing the computed difference no longer distinguishes them. Gradual underflow preserves small differences by allowing subnormal results, at an additional implementation cost that contributed to the resistance to adopting it.

DEC's VAX had its own F_float and G_float formats, incompatible with what became IEEE in both bias and byte order, with a reserved operand that trapped instead of an infinity or a NaN. A program developed on a VAX, ported to a System/360, and validated on a CDC machine could produce three answers for reasons having nothing to do with its algorithm.

To reproduce an operation across these machines, a description needed the radix, the normalization rule, and the treatment of results outside the normal range. It also needed rules for operations such as $0/0$. A word's field widths could not supply those answers: the same allocation of bits could be interpreted with a different bias or a different exceptional-value convention.

## Kahan, the 8087, and 754-1985

William Kahan, at Berkeley since 1969, became a central advocate for a common arithmetic standard. His proposal included reproducible results across conforming machines, specified exceptional cases, and correct rounding of the basic operations. Under nearest rounding, each operation returns the representable value nearest its exact result. This determines the output of an individual operation even when the hardware algorithms used to compute it differ.

Correct rounding also gives us something precise to prove. For finite binary32 addition with a finite result, we want equality between the decoded output and a rounding of the exact real sum:

```lean
open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

example (x y : Model FloatFormat.binary32)
    (hx : Model.isFinite x = true)
    (hy : Model.isFinite y = true)
    (hout : Model.isFinite (Model.add x y) = true) :
    Model.toReal (Model.add x y) =
      Model.roundAt FloatFormat.binary32
        (Model.toReal x + Model.toReal y) :=
  Model.toReal_add_eq_roundAt x y (by simp) hx hy hout
```

[[FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt]] is the real-valued rounding function on the right. The `by simp` discharges `fmt.isIEEE = true`, which requires the IEEE encoding with the conventional bias. The other hypotheses require both operands and their sum to be finite; without them, decoding the words to real numbers would lose the exceptional-value behaviour. The numerical layers in [chapter 06](#/chapter/the-numerical-models) explain that decoding. The theorem [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt]] is parameterized by the descriptor, so it also applies to binary16 through binary128 when those hypotheses hold.

Intel's 8087 coprocessor, released in 1980, implemented correctly rounded basic operations, gradual underflow through subnormals, infinities, NaNs, an 80-bit extended internal format, and sticky exception flags. It provided a working implementation of ideas being developed for the standard. The committee ratified IEEE 754-1985 [@ieee754_1985] five years later, after disagreements that included the cost of gradual underflow and compatibility with existing hardware. Kahan received the Turing Award in 1989. His lecture notes on the standard, still marked "work in progress" in the 1997 revision cited here [@kahan1997], describe its contested choices.

IEEE 754-1985 specified binary formats, including the familiar biased exponent and implicit leading bit of the interchange formats. It required gradual underflow and defined zeros, subnormals, infinities, and NaNs. The arithmetic rules specified correct rounding for addition, subtraction, multiplication, division, square root, and remainder, with four rounding modes and nearest-even as the default. Five sticky flags recorded invalid operation, division by zero, overflow, underflow, and inexactness.

In FloatLib, [[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEERoundingMode]] has the four 1985 modes, and status-bearing operations return the five flags as a record. The reference `Model` used in the theorem and the executable `ExecFloat.Binary` carrier are connected by the proofs described in [chapter 05](#/chapter/why-execution-and-proofs-are-separate). On the executable carrier, dividing one by three illustrates how the rounding mode changes the answer while the status records that neither answer is exact:

```lean
abbrev Binary32 := ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)

#eval ExecFloat.Binary.div (1 : Binary32) 3 (rounding := .nearestEven)
-- 11184811 * 2^-25
#eval ExecFloat.Binary.div (1 : Binary32) 3 (rounding := .towardZero)
-- 5592405 * 2^-24
#eval (ExecFloat.Binary.divWithStatus (1 : Binary32) 3 (rounding := .nearestEven)).2
-- { invalid := false, divideByZero := false, overflow := false, underflow := false, inexact := true }
#eval (ExecFloat.Binary.divWithStatus (1 : Binary32) 0 (rounding := .nearestEven)).2
-- { invalid := false, divideByZero := true, overflow := false, underflow := false, inexact := false }
```

Nearest-even rounds one third up to $11184811 \cdot 2^{-25}$ and toward-zero rounds it down to the neighbour below, $5592405 \cdot 2^{-24}$, which is $11184810 \cdot 2^{-25}$ written with a smaller significand. The first division raises only `inexact`. The final evaluation, division of one by zero, raises `divideByZero` alone. Its infinity is the specified result of dividing a finite nonzero value by zero; it is not an overflow caused by rounding a large finite quotient.

The 8087's 80-bit extended format stores its integer bit explicitly. A [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat]] assumes an implicit leading bit, so a descriptor with 15 exponent bits and 63 fraction bits has the same normal values as x87 extended but different bit patterns. Representing the numerical grid does not by itself represent that storage format.

The 1985 standard did not require correct rounding of transcendental functions. The 2008 revision [@ieee754_2008] recommends it, but determining the rounded result of $\exp$ or $\log$ can require much more precision than the destination stores. If the exact result lies very close to a rounding midpoint, an approximation may need many additional digits before it establishes which side of the midpoint contains the result. This is the table maker's dilemma. De Dinechin, Lauter, and Muller's correctly rounded logarithm [@deDinechinLog2007] is an example of the analysis and algorithms needed to resolve it.

FloatLib's binary transcendental kernels are deterministic approximation algorithms. Their [accuracy contracts](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Transcendentals/Contract.lean) separate that reproducibility from accuracy. A kernel can carry a proved enclosure or an absolute error budget. An enclosure also establishes correct rounding when both endpoints round to the same destination value: every enclosed value then has that rounded result. The separate [posit exponentials and logarithms](#/chapter/posits-and-the-quire/exponentials-and-logarithms) have real-rounding proofs; the natural functions use successively tighter enclosures and a proof that the comparison eventually resolves.

The location of an enclosure matters as much as its width. On an integer rounding grid, an enclosure from 1.4999 to 1.5001 is very narrow but still crosses the midpoint between one and two. Its lower endpoint rounds to one and its upper endpoint to two, so it has not determined the rounded answer. An enclosure from 1.5001 to 1.5002 does determine two. For a transcendental result close to a midpoint, the computation must reduce the uncertainty enough to establish which rounding interval contains it. A small error estimate alone may leave this unresolved.

The arithmetic standard also leaves work to language and compiler specifications, including how a program accesses flags and which evaluation transformations are permitted. The examples in [Chapter 04](#/chapter/why-verifying-floating-point-is-hard) show how those execution rules affect the bits a program returns.

<a id="what-imprecision-has-cost"></a>

A common arithmetic standard fixes the result of an operation. The programs using it still need suitable conversions, error bounds, and models. The causes marked in [Figure 3.2](#/chapter/a-short-history-of-floating-point/figure-ch03-incident-timeline) distinguish accumulated rounding and conversion errors from an incorrect implementation or an inadequate physical model.

A timestamp can be accurate to one part in a million and still be unsuitable for measuring a short interval. What matters is how its error combines with the error in the timestamp being subtracted from it. A narrowing conversion has a different constraint: a value that fits in the source register may exceed the destination range. These failures depend on how a program uses its numbers, as well as on the accuracy of each arithmetic operation.

![Five incidents, each marked by the kind of numerical failure described in its primary sources. Sleipner concerns the physical model.](assets/ch03-incident-timeline.png "Five failures with different causes, from arithmetic and conversion errors to an inadequate physical model. Correct rounding alone would not resolve all five.")

<a id="an-index-that-truncated-itself-vancouver-1982-to-1983"></a>

## Accumulated truncation: Vancouver, 1982 to 1983

The Vancouver Stock Exchange launched a composite index in January 1982 at 1000.000. The index was recomputed after every trade, close to 3000 times on a busy day, and each result was truncated to three decimal places rather than rounded [@quinn1983]. Twenty-two months later, on Friday 25 November 1983, it closed at 524.811. After three weeks of recomputation by consultants it reopened on Monday 28 November at 1098.892, 574.081 points above Friday's close [@lilley1983]. The repeated truncations had introduced a substantial downward bias into the published index.

For a positive value, truncating to three decimal places discards an amount between 0 and 0.001. If the discarded digits are evenly spread, the average loss is 0.0005 per update, so 3000 updates a day would lose about a point and a half per trading day, on the order of thirty points a month. This is an estimate under a distributional assumption, not a reconstruction of every trade. The exchange put the loss at a point a day and twenty a month [@lilley1983]; the recorded 574 points over 22 months is about 26 a month. All describe the same accumulation of many small downward errors.

Rounding to nearest allows errors of both signs, but it does not guarantee that they cancel. We can see this in a binary32 example, separate from the exchange's decimal calculation: start at zero and add `0.1` ten thousand times. We need to distinguish two sources of error: the literal is stored as $13421773 / 2^{27}$, and each subsequent addition may round again.

```lean
open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics
open FloatLib.Numerics.Representations

abbrev Binary64 :=
  ExecFloat.Binary (exponentBits := 11) (fractionBits := 52)
```

```lean
#eval ExecFloat.Binary.toRat? (0.1 : Binary32)
-- some (13421773 / 134217728)

#eval 10000 * (13421773 / 134217728 : Rat)
-- 8388608125 / 8388608

def accumulate (steps : Nat) (step : Binary32)
    (rounding : Model.IEEERoundingMode) : Binary32 :=
  (List.range steps).foldl
    (fun total _ => (ExecFloat.Binary.addWithStatus total step rounding).1) 0

#eval accumulate 10000 0.1 .nearestEven
-- 999.90289306640625

#eval accumulate 10000 0.1 .towardZero
-- 999.80487060546875

#eval (ExecFloat.Binary.addWithStatus (1000 : Binary32) 0.1 .towardZero).2
-- { invalid := false, divideByZero := false, overflow := false, underflow := false, inexact := true }
```

The result is worth pausing over: we started with a stored step that is too large, yet both accumulated totals are too small. The stored tenth is $13421773 / 2^{27}$, slightly above $0.1$, so ten thousand exact copies sum to just over 1000: the second result, $8388608125 / 8388608$, is 1000 plus about $1.5 \times 10^{-5}$. Nearest-even accumulation instead ends about a tenth short, and truncation twice as far short. Most of that error comes from rounding the additions, not from converting the literal.

Within a binade, the interval between consecutive powers of two, the spacing of floats is constant. Away from its boundary, the accumulated total is on that grid and the fixed step has the same remainder relative to the grid spacing. When the exact sums are not ties, this produces the same rounding error on each addition. For this step, the direction repeats with period four as the binade doubles: two binades round up, then two round down. The last binade, $[512, 1024)$, contains about half the steps and rounds down, so it contributes a large part of the final error. Toward-zero rounding of these positive sums discards a nonnegative amount at every step. In [Figure 3.3](#/chapter/a-short-history-of-floating-point/figure-ch03-binary32-accumulation), look for the straight stretches of error within each binade and the changes at their boundaries.

![Ten thousand binary32 additions of 0.1 under nearest-even and toward-zero rounding, as the running total minus k/10, with the points where the total reaches a new binade marked](assets/ch03-binary32-accumulation.png "Accumulated error after repeated binary32 additions of 0.1, measured against the exact decimal total. Rounding direction changes the drift; each binade changes the step size.")

We can calculate the slope of the final stretch directly. In $[512,1024)$, a binary32 step is $h = 2^{-14}$. The stored tenth, in units of this spacing, is

$$
  \frac{13421773 / 2^{27}}{2^{-14}}
  = \frac{13421773}{8192}
  = 1638 + \frac{3277}{8192}.
$$

The fractional part is about 0.400024, below one half. As long as the addition stays in this binade, both nearest-even and toward-zero therefore advance the accumulator by $1638h = 0.0999755859375$. The plotted reference advances by exactly one tenth, so the error falls by

$$
  \frac{1638}{16384} - \frac1{10}
  = -\frac1{40960}
$$

on each step. This explains why the two final stretches are parallel: they use the same increment but arrive in the binade with different accumulated errors. Doubling the grid spacing changes the fractional part of the step measured in grid units, which explains the earlier changes of slope.

The last evaluation inspects one addition. Its five flags are the fields of [[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEEStatus]], and `inexact` is true because this sum required rounding. The rounding direction is an argument of [[FloatLib.Floats.Formats.BinaryInterchange.Model.addWithStatus]] and of the executable operation used above; `towardZero` is a constructor of [[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEERoundingMode]]. The mode is therefore visible at the call site.

A loop can retain the flags from earlier steps using [[FloatLib.Numerics.IEEEStatus.union]], which combines each field with logical OR. This records whether an event occurred anywhere in the loop. It cannot distinguish one inexact addition from ten thousand, or tell whether their errors cancel. A bound on the final error needs the rounding analysis as well as the status record.

<a id="a-clock-that-drifted-patriot-dhahran-1991"></a>

## Inconsistent time conversions: Patriot, Dhahran, 1991

On 25 February 1991 the Patriot battery protecting Dhahran Air Base failed to track an incoming Scud, which struck an Army barracks and killed 28 American soldiers. The General Accounting Office reported a year later [@gaoPatriot1992] that the battery had run continuously for over 100 hours. The weapons control computer kept time as an integer count of tenths of a second. Its range gate algorithm, which predicts where the target will next appear, needed that count converted to seconds, and the registers were 24 bits long. The conversion lost precision; an inconsistency in how converted times were used made the range gate shift grow with running time.

Robert Skeel worked out the arithmetic in SIAM News in July 1992 [@skeel1992]. One tenth has no finite binary expansion: $\tfrac{1}{10} = 0.0\overline{0011}_2$. Keeping 23 fraction bits and discarding the rest stores

$$
\frac{\lfloor 2^{23}/10 \rfloor}{2^{23}} = \frac{838860}{8388608} = \frac{1}{10}\left(1 - 2^{-20}\right),
$$

so every converted time is short by a relative error of $2^{-20}$, about one part in a million, and the absolute error per tick is $\tfrac{1}{10 \cdot 2^{20}} = \tfrac{1}{10{,}485{,}760} \approx 9.5 \times 10^{-8}$ seconds. After 100 hours the clock has counted $3{,}600{,}000$ ticks, so the accumulated error is $3{,}600{,}000 / 10{,}485{,}760 \approx 0.3433$ seconds, the GAO's own figure. Its table puts the range gate shift at 55 meters after 8 hours, 137 meters after 20 hours, by which point the target is outside the gate, and 687 meters after 100 hours. A Scud travels at roughly Mach 5, so in a third of a second it covers, as Skeel put it, more than half a kilometer.

Skeel also examined how the converted times were used. Tracking depends on the difference between the times of two radar pulses. If both timestamps have the same relative error of $2^{-20}$, subtracting them scales the short interval by that same relative error: most of the error in the two large timestamps cancels. The software instead mixed conversions of different accuracy. A more accurate conversion subroutine had been added during deployment, but only some of the half dozen places that needed it called the new routine. Subtracting a truncated timestamp from a more accurate one leaves an error that grows with the absolute clock time, even when the two pulses are close together.

To see the dependence on uptime, write the earlier time as $T$, the later time as $T+\Delta$, and the truncation's relative error as $\varepsilon = 2^{-20}$. Using the truncated conversion for both timestamps gives

$$
  (1-\varepsilon)(T+\Delta) - (1-\varepsilon)T
  = (1-\varepsilon)\Delta.
$$

The error is proportional to the short interval. To isolate the effect of mixing conversions, temporarily treat the more accurate conversion as exact and use it for the later timestamp only:

$$
  (T+\Delta) - (1-\varepsilon)T
  = \Delta + \varepsilon T.
$$

Now the error contains the total uptime. This simplified calculation does not assume that the replacement routine was perfectly exact; it shows why a difference between the conversion rules can survive subtraction even when the pulse interval is small. The 0.3433-second error after 100 hours measures this uptime term, rather than a millionth of the time between pulses.

Israeli users had reported the drift on 11 February 1991. A corrected version was released on 16 February and reached Dhahran on 26 February, the day after the barracks was hit.

We can reproduce the truncated constant with exact integer arithmetic. `ClockGrid` uses fixed point with 23 fraction bits. Its unbounded integer coefficient is divided by $2^{23}$ when decoded. This reproduces the rounding grid without modelling the clock register's finite storage. [[FloatLib.Floats.ExecFloat.FixedPoint.toRat]] reads the coefficient back as an exact rational:

```lean
/-- Binary fixed point with 23 fractional bits: the grid of the Patriot's clock conversion. -/
abbrev ClockGrid := ExecFloat.FixedPoint binaryRadix 23

/-- The first 23 fraction bits of one tenth, with everything after them discarded. -/
def choppedTenth : ClockGrid :=
  ExecFloat.FixedPoint.ofCoefficient (2 ^ 23 / 10)

#eval ExecFloat.FixedPoint.coefficient choppedTenth
-- 838860

#eval (1 / 10 : Rat) - ExecFloat.FixedPoint.toRat choppedTenth
-- 1 / 10485760

#eval (3600000 : Rat) * ((1 / 10 : Rat) - ExecFloat.FixedPoint.toRat choppedTenth)
-- 5625 / 16384

#eval ExecFloat.FixedPoint.coefficient (0.1 : ClockGrid)
-- 838861
```

The third result, $5625 / 16384$, is the GAO's 0.3433 seconds as an exact fraction. The last line instead rounds the literal `0.1 : ClockGrid` to nearest and stores 838861. Its error is a quarter the size of truncation's and has the opposite sign. That changes the conversion error; it does not by itself make two differently converted timestamps consistent.

Same-scale addition is exact by [[FloatLib.Floats.Formats.FixedPoint.add_refines]], and fixed-point multiplication composes the operand scales in its result type. We can therefore isolate the conversion's discarded $1/10485760$ per tick without adding rounding error to the analysis itself. The analogous binary floating-point decoder, [[FloatLib.Floats.Formats.BinaryInterchange.Model.toDyadic?]], returns a dyadic record instead of the rational returned by [[FloatLib.Floats.ExecFloat.FixedPoint.toRat]]. Both make the represented value available to an exact calculation.

An error budget for the tracking calculation would need the maximum uptime, the interval between observations, and the accuracy of each conversion used in forming that interval. Increasing precision reduces a conversion error, while using a consistent conversion allows the errors in nearby timestamps to cancel. Bounds such as those developed in [chapter 07](#/chapter/the-mathematics-of-rounding) are useful only after the analysis has identified which expression the program actually computes.

<a id="a-platform-that-sank-sleipner-a-1991-and-why-it-belongs-in-a-different-list"></a>

## Model error: Sleipner A, 1991

On 23 August 1991 the concrete gravity base of the Sleipner A platform sank in the Gandsfjord outside Stavanger during a controlled ballasting operation, at a depth of about 65 meters. A tricell wall cracked, water came in faster than the pumps could remove it, and the structure went to the bottom. The loss is put at about 700 million dollars. The finite element analysis, done with NASTRAN, had underestimated the shear stresses in the tricell walls by about 47 percent, and the reinforcement in the critical zone was inadequately anchored; a corrected analysis predicted failure at 62 meters [@jakobsenRosendahl1994] [@selbyVecchioCollins1997]. Arnold summarizes both accounts [@arnoldDisasters].

Here we have to look beyond arithmetic to the model itself: the reported problem was that the discretization did not resolve the stresses near a corner of the structure. A finite element calculation approximates a physical structure with a mesh and computes stresses within that model. Correctly rounding every operation would help bound the error in solving the chosen discrete problem, but it would not establish that the mesh captured the local stress concentration. That needs evidence about the modelling assumptions and the discretization, in addition to the arithmetic.

<a id="a-table-with-five-holes-the-pentium-fdiv-bug-1994"></a>

## Missing table entries: the Pentium FDIV bug, 1994

Thomas Nicely, a mathematician at Lynchburg College computing sums of reciprocals of twin primes, noticed inconsistent results on his new Pentium in June 1994 and reported them to Intel on 24 October. Coe, Mathisen, Moler, and Pratt describe the discovery and its consequences [@coePentium1995]. The Pentium divided with a radix-4 SRT algorithm, a form of long division that produces two quotient bits per step and picks each quotient digit from a lookup table indexed by a few leading bits of the partial remainder and the divisor. The table should have had 1066 populated cells; five cells whose value was $+2$ were missing. Divisions that hit them were wrong by a relative error of up to about $6 \times 10^{-5}$, in the fourth or fifth significant digit, and more typically by far less [@coePentium1995] [@edelman1997]. The canonical example is $4195835 / 3145727$, which is $1.333820449136241002\ldots$ and which the flawed chips returned as $1.333739068902037589$. Intel's 1994 annual report [@intelAnnualReport1994] records a 475 million dollar pretax charge for replacing the processors.

We can compute that quotient with the library and compare its digits with the exact fraction. The correctly rounded binary64 quotient agrees with the exact one to seventeen significant digits:

```lean
#eval (4195835 : Binary64) / 3145727
-- 6006993277709123 * 2^-52

#eval (6006993277709123 * 10 ^ 18) / 4503599627370496
-- 1333820449136241093

#eval (4195835 * 10 ^ 18) / 3145727
-- 1333820449136241002
```

The second and third evaluations print the first nineteen digits of the rounded and exact quotient using integer arithmetic, avoiding another floating-point conversion in the display. They agree through the seventeenth. [[FloatLib.Floats.ExecFloat.Proof.div_eq_spec]] states that the executable `/` returns the reference division result regardless of which certified kernel the planner selects. [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_div_eq_roundAt]] then relates that reference result to the nearest-even rounding of the exact real quotient, assuming finite operands, a nonzero divisor, and a finite result. The two statements use the executable type and reference model respectively, connected by the refinement chain in [chapter 06](#/chapter/the-numerical-models):

```lean
example (x y : Binary64) : x / y = ExecFloat.Spec.div x y :=
  ExecFloat.Proof.div_eq_spec x y

example (x y : Model FloatFormat.binary64)
    (hx : Model.isFinite x = true) (hy : Model.isFinite y = true)
    (hy0 : Model.isZero y = false)
    (hout : Model.isFinite (Model.div x y) = true) :
    Model.toReal (Model.div x y) =
      Model.roundAt FloatFormat.binary64 (Model.toReal x / Model.toReal y) :=
  Model.toReal_div_eq_roundAt x y FloatFormat.isIEEE_binary64 hx hy hy0 hout
```

FloatLib also has a fast divider for the common finite binary64 path. It generates quotient bits with a restoring `UInt64` loop. The theorem `divFiniteFastImpl_eq` compares it with the generic implementation on every input pair, including cases where the implementations decline to handle the operands:

```lean
#check @Model.NativeBinary64.divFiniteFastImpl_eq
-- Model.NativeBinary64.divFiniteFastImpl_eq : ∀ (x y : Model.NativeBinary64.Value),
--   Model.NativeBinary64.divFiniteFastImpl? x y = Model.NativeBinary64.divFiniteImpl? x y
```

The restoring loop keeps an integer quotient and an exact remainder. To follow the loop ourselves, we can divide 13 by 7, starting with quotient 1 and remainder 6. After $j$ binary digits have been generated, the relation is

$$
  13\cdot 2^j = 7q_j + r_j, \qquad 0 \le r_j < 7.
$$

Doubling both sides makes room for the next quotient bit. If the doubled remainder is at least 7, the loop subtracts 7 and sets that bit to one; otherwise the bit is zero:

| Digits generated | Scaled numerator | Quotient | Remainder |
| --- | ---: | ---: | ---: |
| 0 | 13 | 1 | 6 |
| 1 | 26 | 3 | 5 |
| 2 | 52 | 7 | 3 |
| 3 | 104 | 14 | 6 |

At three fractional bits, the exact quotient is $(14+6/7)\cdot2^{-3}$. The remainder is more than half the divisor, so nearest rounding increments 14 to 15 and returns $15/8$. A remainder below half would keep the quotient; an exact half would inspect its parity. The binary64 loop uses the same recurrence with enough digits for its significand. Its proof also needs bounds ensuring that doubling the quotient and remainder fits the machine words. The reference equality above covers both that finite-word calculation and the fallback for cases outside its range.

A divider that returns an incorrect quotient for even one input pair cannot satisfy this equality with a correct reference. The proof for an optimized loop or table must cover every returned result, including inputs that exercise rarely used branches.

<a id="what-a-verified-library-changes"></a>

We can use this agreement without naming the kernel that runs. [[FloatLib.Floats.ExecFloat.Proof.add_eq_spec]] and [[FloatLib.Floats.ExecFloat.Proof.div_eq_spec]] connect executable operations to their references; [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt]] and the division theorem above connect those references to real rounding. For binary32 addition, the executable equation is:

```lean
example (x y : Binary32) : x + y = ExecFloat.Spec.add x y :=
  ExecFloat.Proof.add_eq_spec x y
```

<a id="what-it-does-not-change"></a>

These equations concern Lean definitions. Running the software also relies on the compiler and runtime to implement integer and bit-vector operations correctly. The certified software divider uses integer arithmetic. Optional calls to the host floating-point divider live in the [unchecked host-arithmetic module](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/NativeFPU/Unchecked.lean); [chapter 16](#/chapter/external-validation) compares their results with the software model. Those comparisons can reveal disagreements, but the software proof does not establish correctness of the processor's divider.

<a id="an-overflow-that-was-not-floating-point-ariane-5-flight-501-1996"></a>

## A narrowing conversion: Ariane 5, flight 501, 1996

On 4 June 1996 the maiden flight of Ariane 5 lifted off from Kourou. The inquiry board chaired by Jacques-Louis Lions reported on 19 July 1996 [@lions1996] that the failure "was caused by the complete loss of guidance and attitude information 37 seconds after start of the main engine ignition sequence (30 seconds after lift-off)". The launcher swung to an angle of attack above 20 degrees, the boosters tore off, and the self-destruct fired about 39 seconds after H0, the report's zero, the moment the launch sequence was initiated.

The failure occurred in a conversion from floating point to a bounded integer. The board wrote that the inertial reference system's software exception "was caused during execution of a data conversion from 64-bit floating point to 16-bit signed integer value. The floating-point number which was converted had a value greater than what could be represented by a 16-bit signed integer. This resulted in an Operand Error." The horizontal bias variable BH could be represented in binary64, but exceeded its destination's range. The destination was a 16-bit two's complement integer whose largest value is 32767. In IEEE 754 terms this is the invalid-operation case of conversion to an integer format (clause 5.8 of [@ieee754_2019]); rounding played no part in the failure. The board found that "the data conversion instructions (in Ada code) were not protected from causing an Operand Error, although other conversions of comparable variables in the same place in the code were protected", so the handler did what it was designed to do for a hardware fault and shut the unit down. The backup unit, running the same software on the same data, had shut itself down during the previous 72 millisecond data cycle, for the same reason.

The decision to leave this conversion unprotected rested on a range assumption. With a processor workload ceiling of 80 percent, checks were omitted for variables judged "either physically limited or that there was a large margin of safety, a reasoning which in the case of the variable BH turned out to be faulty". The computation belonged to an alignment function, meaningful only before lift-off, that for Ariane 4's sake kept running for about 40 seconds of flight. Ariane 5's early trajectory "results in considerably higher horizontal velocity values", and the equipment-level tests "did not specifically include the Ariane 5 trajectory data". The bound on BH was an assumption inherited from another rocket, and the board recommended: "Identify all implicit assumptions made by the code and its justification documents on the values of quantities provided by the equipment."

In FloatLib a 16-bit signed destination is [[FloatLib.Numerics.Representations.FixedInt]] at width 16. Its representable range is expressed by the decidable proposition [[FloatLib.Numerics.Representations.FixedInt.InRange]]. The board did not publish the value BH reached, so we'll use 40000 as an illustrative input above 32767, not a reconstruction of the flight data. The first two evaluations show that it is out of range and that storing its low sixteen bits wraps it to $-25536$. The remaining evaluations convert a binary64 value to the same sixteen-bit integers, represented as a bounded fixed-point grid with no fraction digits. Only the overflow policy changes between the three casts.

```lean
#eval decide (FixedInt.InRange 16 40000)
-- false

#eval (FixedInt.ofInt 40000 : FixedInt 16).toInt
-- -25536

/-- Sixteen-bit two's complement integers, seen as a fixed-point grid with no fraction digits. -/
abbrev Int16Grid := ExecFloat.BoundedFixedPoint binaryRadix 0 16

open FloatLib.Floats.ExecFloat.BoundedFixedPoint.Conversion (OverflowPolicy)

def horizontalBias : Binary64 := 40000

#eval (ExecFloat.cast (target := Int16Grid) horizontalBias).map
  ExecFloat.BoundedFixedPoint.coefficient
-- FloatLib.Floats.ExecFloat.ConversionOutcome.failure (FloatLib.Floats.ExecFloat.ConversionFailure.outOfRange)

#eval (ExecFloat.castWith (target := Int16Grid) horizontalBias OverflowPolicy.wrap).map
  ExecFloat.BoundedFixedPoint.coefficient
-- FloatLib.Floats.ExecFloat.ConversionOutcome.success
--   (-25536)
--   { inexact := true, overflow := true, underflow := false, saturated := false, wrapped := true, mappedSpecial := false }

#eval (ExecFloat.castWith (target := Int16Grid) horizontalBias OverflowPolicy.saturate).map
  ExecFloat.BoundedFixedPoint.coefficient
-- FloatLib.Floats.ExecFloat.ConversionOutcome.success
--   32767
--   { inexact := true, overflow := true, underflow := false, saturated := true, wrapped := false, mappedSpecial := false }
```

The default cast returns `outOfRange` as an ordinary result, allowing the caller to handle the failed conversion. Explicit alternatives wrap to $-25536$ or saturate to $32767$. They are selected with constructors of [[FloatLib.Floats.ExecFloat.BoundedFixedPoint.Conversion.OverflowPolicy]] passed to [[FloatLib.Floats.ExecFloat.castWith]], and their `ConversionStatus` records both the overflow and the selected behaviour. Neither alternative preserves the original value, so whether it is useful depends on the application.

The wrapped value follows from the bit interpretation. Sixteen bits store a residue modulo $2^{16} = 65536$. The residue 40000 has its top bit set, so reading it as a signed two's-complement integer subtracts 65536 and gives $40000 - 65536 = -25536$. Saturation instead returns the upper endpoint, losing $40000 - 32767 = 7233$. Both are well-defined arithmetic operations, but each replaces a positive measurement with a different value. Reporting the selected policy in the status lets the caller distinguish that replacement from a successful value-preserving conversion.

The round-trip theorem for a 16-bit store, `toInt_ofInt_eq_self`, assumes that the value fits:

```lean
example (value : Int) (h : FixedInt.InRange 16 value) :
    (FixedInt.ofInt value : FixedInt 16).toInt = value :=
  FixedInt.toInt_ofInt_eq_self (by decide) h
```

The `InRange 16 value` hypothesis is the precise condition under which storing and reading the integer preserves it. Proving this theorem once does not establish `InRange 16 BH` for a particular trajectory. That requires evidence about the values the guidance system can produce, and a change from Ariane 4 to Ariane 5 requires revisiting that evidence. The same distinction appeared in the division theorem above: the arithmetic proof assumes finite inputs and a nonzero divisor; the application must show that its inputs satisfy those conditions.

The alignment output was unused after lift-off, but an exception in the unused calculation could still shut down the reference unit. Choosing a conversion policy therefore also requires tracing how the surrounding program handles the result. A returned failure, a wrapped value, and a saturated value each need an appropriate response from the caller.

<a id="verification-enters"></a>

## Proofs of hardware and software arithmetic

The FDIV failure showed why a division algorithm had to meet its specification on every input. Subsequent hardware verification work included Moore, Lynch, and Kaufmann's proof of AMD5K86 division microcode in ACL2 in 1998 [@mooreLynchKaufmann1998], and Russinoff's proofs for AMD-K7 multiplication, division, and square root that year [@russinoff1998]. Harrison built a machine-checked theory of floating point in HOL Light in 1999 [@harrison1999], which Intel then used for its own algorithms.

Flocq, Boldo and Melquiond's Coq library [@boldoMelquiond2011], organizes floating point around a rounded-real model. A float is a real number on a grid determined by a radix and an exponent function; rounding maps a real number onto that grid. This separates properties of the represented values from details of how a machine stores them. Theorems about ulps, error bounds, and Sterbenz subtraction can then be stated for a family of grids and applied to individual formats by proving that they meet the hypotheses.

FloatLib's rounded-real layer follows this organization in Lean; its grid definitions and proofs are developed in [chapter 07](#/chapter/the-mathematics-of-rounding). [Chapter 15](#/chapter/performance) compares its execution cost with an independent proved implementation extracted from Flocq. This measures their relative execution cost without comparing their outputs. [Chapter 16](#/chapter/external-validation) describes the separate checks of numerical results.

<a id="the-2008-and-2019-revisions-and-the-decimal-question"></a>

## The 2008 and 2019 revisions

The 1985 standard was binary only. IEEE 854 in 1987 [@ieee854_1987] restated the rules for radix 2 or 10 without fixing any bit layout, and the two were merged in IEEE 754-2008, which added decimal32, decimal64, and decimal128 with two competing significand encodings, IBM's densely packed decimal and Intel's binary integer decimal. It also added binary16 as an interchange format, made fused multiply-add a required operation, added a ties-to-away rounding mode required only for decimal arithmetic, and introduced `minNum` and `maxNum`. IEEE 754-2019 [@ieee754_2019] was a smaller revision. It replaced `minNum` and `maxNum` with four operations, `minimum`, `maximum`, `minimumNumber`, and `maximumNumber`, which distinguish NaN-propagating behaviour from a preference for numerical operands. It also recommended augmented operations that return the exact rounding error alongside the result and revised other edge cases.

FloatLib implements some of these additions to the standard. Fused multiply-add is an ordinary operation with the same theorem shape as addition. Both generations of minimum and maximum exist, [[FloatLib.Floats.Formats.BinaryInterchange.Model.minNum]] from 2008 and [[FloatLib.Floats.Formats.BinaryInterchange.Model.minimum]] and [[FloatLib.Floats.Formats.BinaryInterchange.Model.minimumNumber]] from 2019, so programs using either set of operations can be modelled. The augmented operations are not implemented.

The binary IEEE arithmetic operations take [[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEERoundingMode]], the four 1985 modes only. The policy rounding function [[FloatLib.Floats.Formats.BinaryInterchange.Model.Policy.roundDyadic]] takes a policy whose rounding field is the wider [[FloatLib.Numerics.RoundingMode]]; that vocabulary also names ties-to-away and stochastic rounding and gives each a precise meaning on any `FloatFormat`. Decimal arithmetic has its own five-mode type, adding nearest with ties away. P3109 needs modes neither vocabulary has, round-to-odd and three stochastic rules with explicit random bits, so [[FloatLib.Floats.Formats.P3109.RoundingMode]] is its own nine-constructor type.

The exact numerical layer accepts a general radix: [[FloatLib.Numerics.Radix]] is a natural base at least two, [[FloatLib.Numerics.decimalRadix]] is one such value, and the exact fixed-point and logarithmic systems accept it. The [decimal codecs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/DecimalInterchange/Basic.lean) support decimal32, decimal64, and decimal128 in both BID and DPD. Their proofs preserve the entire datum when changing encodings, including the decimal exponent and special-value metadata. The [decimal arithmetic module](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/DecimalInterchange/Arithmetic/Basic.lean) adds addition, subtraction, multiplication, division, fused multiply-add, and square root, with numerical rounding proofs and five exception flags. [Chapter 08](#/chapter/ieee-binary-formats/decimal-interchange) explains how numerical exactness differs from choosing a representation within a decimal cohort. Parsing decimal text into a binary destination still rounds to a binary value.

For a calculation with a known scale, we can use decimal fixed point. A two-digit scale represents hundredths using integer coefficients, so adding two amounts on that grid can be exact. The scale stays fixed instead of moving with an exponent. We can see this by adding the coefficients for ten and twenty cents to get thirty:

```lean
abbrev Cents := ExecFloat.FixedPoint FloatLib.Numerics.decimalRadix 2

#eval ExecFloat.FixedPoint.toRat ((0.10 : Cents) + 0.20)
-- 3 / 10
#eval ((0.1 : Binary32) + 0.2)
-- 5033165 * 2^-24
```

The decimal grid returns $3/10$ exactly. The binary32 result, $5033165 \cdot 2^{-24}$, is about $0.30000001$, the nearest binary32 value to $3/10$. A fixed decimal grid is useful when the calculation has a known scale, such as hundredths. It does not provide the variable range and spacing of decimal floating point, and operations whose results fall between grid points still need a rounding policy.

<a id="machine-learning-reopens-the-encoding-questions"></a>

## Low-precision formats for machine learning

Binary64 became common in scientific computing and binary32 in graphics. Deep learning brought renewed interest in narrower formats. A gradient estimated from a random mini-batch already contains noise, which can make reduced precision acceptable, while smaller operands reduce storage and data movement. The usable precision still depends on the model and training procedure.

Micikevicius and colleagues demonstrated mixed-precision training in 2018 [@micikevicius2018mixed], using binary16 storage with a binary32 master copy of the weights and loss scaling to protect small gradients. These techniques address different losses of information: the master weights retain updates too small for binary16, while scaling helps keep gradients within its usable exponent range. The format limits are described in [chapter 09](#/chapter/low-precision-formats-for-machine-learning). Google's TPUs used bfloat16 [@kalamkarBfloat2019], which keeps binary32's 8 exponent bits but stores only 7 fraction bits. Its 8-bit significand provides about two decimal digits. Within a 16-bit word, this allocates more bits to range and fewer to precision than binary16. The catalog entries [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.binary16]] and [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.bfloat16]] both use the IEEE encoding, but their different field allocations lead to different rounding grids and range limits.

At one, binary16 has spacing $2^{-10}$, while bfloat16 has spacing $2^{-7}$, eight times larger. The exact value $1+2^{-8}$ occupies four binary16 steps above one and is representable there; in bfloat16 it is a midpoint and nearest-even returns one. The extra exponent bits give bfloat16 a wider range: binary16's smallest positive normal is $2^{-14}$, while bfloat16's is $2^{-126}$. Equal storage width therefore does not make the two formats interchangeable. A computation can need the finer steps of one and the smaller normal magnitudes of the other.

A binary32 master weight preserves small updates by accumulating them before conversion back to the storage format. For example, a binary16 weight at one cannot retain an increment of $2^{-12}$: each separately rounded update returns one. In binary32, four such increments accumulate exactly to $2^{-10}$, a full binary16 step, which survives the next conversion. Loss scaling addresses a different point in the calculation. Multiplying a gradient of $2^{-20}$ by $2^{10}$ moves it to $2^{-10}$, within binary16's normal range, where more significant bits are available. The scale must be introduced before the low-precision operations whose small outputs it is meant to protect, then accounted for when applying the update. Making it too large can cause overflow. These small calculations illustrate the two mechanisms; they do not establish an error bound for a training run.

Micikevicius and colleagues proposed the eight-bit E5M2 and E4M3 formats in 2022 [@micikevicius2022fp8], and NVIDIA's H100 shipped tensor cores for both that year. The Open Compute Project's OFP8 specification standardized them in 2023 [@ocpOfp8], with differences in exceptional-value encoding as well as precision. E5M2 keeps IEEE conventions, including infinities and multiple NaN codes. E4M3FN has no infinity and one NaN pattern per sign. It uses most of the all-ones exponent class for finite values, extending its finite range beyond what the same field widths would provide with the IEEE reservation. With only 256 words available, changing a reserved code class changes an appreciable part of the format.

The ONNX float8 definitions [@onnxFloat8] include FNUZ variants that remove negative zero, reuse its word as the sole NaN, and shift the bias by one. The OCP Microscaling specification, also from 2023 [@ocpMx], combines narrow elements in blocks with a shared eight-bit power-of-two scale. Its E8M0 scale has no sign, fraction, or zero. The FP8 elements reuse OFP8 formats, while the FP6 and FP4 formats E2M3, E3M2, and E2M1 make every word finite, with no NaN. An element's decoded value is then multiplied by the block scale, so the element word alone does not determine its value in the block.

Describing these formats requires specifying the bias and exceptional-value encoding as well as the field widths. A [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat]] records all four. Its [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.Encoding]] field has four alternatives: `ieee`, `finiteMaxNaN` for the E4M3FN family, `finiteUnsignedZero` for FNUZ, and `finite` for the MX element formats. These are the encodings represented by this type; other layouts need their own representation. [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.custom]] pairs one of these encodings with validated widths and bias.

We can try changing the encoding ourselves. `telemetry16` below is an invented descriptor with binary16's field widths and bias but the `finiteMaxNaN` encoding. Its word size agrees with binary16's, while the meaning of the top exponent class changes:

```lean
-- an invented descriptor: binary16's field widths and bias with the E4M3FN-style policy,
-- no infinities, one NaN word per sign at the top of the code space.
abbrev telemetry16 : FloatFormat := FloatFormat.custom 5 10 15 .finiteMaxNaN

#eval FloatFormat.binary16.bitWidth
-- 16
#eval telemetry16.bitWidth
-- 16
example : telemetry16 ≠ FloatFormat.binary16 := by decide

#eval Model.isInf (Model.ofNatBits (fmt := FloatFormat.binary16) 0x7c00)
-- true
#eval Model.toDyadic? (Model.ofNatBits (fmt := telemetry16) 0x7c00)
-- some { negative := false, significand := 1024, exponent := 6 }
```

The word `0x7c00` is $+\infty$ in binary16 and $1024 \cdot 2^6 = 65536$ in the invented descriptor. Catalog formats show the same dependence on encoding: [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.e5m2]], [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.e4m3fn]], and [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.e4m3fnuz]] assign their eight bits differently. The examples and proofs in [chapter 09](#/chapter/low-precision-formats-for-machine-learning) decode `0x7c` as $+\infty$ in E5M2 and as 384 in E4M3FN. They also establish properties of the encoding families: the non-IEEE alternatives in this descriptor have no infinity, the MX element formats have no NaN, and an FNUZ format has one zero word.

Overflow behaviour is a separate part of conversion. In FloatLib, an E4M3FN result too large to round back to 448 can become a NaN word or saturate at 448, according to the selected policy. The encoding is the same in either case. The function [[FloatLib.Floats.Formats.BinaryInterchange.Model.Policy.roundDyadic]] takes a [[FloatLib.Numerics.QuantizationPolicy]] as an argument, and a theorem proved under one policy is a theorem about that policy alone; [chapter 04](#/chapter/why-verifying-floating-point-is-hard) runs the same input through both policies and [chapter 09](#/chapter/low-precision-formats-for-machine-learning) gives the mathematics.

The E8M0 scale needs a different representation because it has neither a sign nor a significand field. It is therefore defined separately from `FloatFormat`. [[FloatLib.Floats.Formats.OCP.MX.E8M0]] is its own eight-bit type: code $c$ from 0 through 254 denotes $2^{c-127}$ and code 255 is the sole NaN, and [[FloatLib.Floats.Formats.OCP.MX.E8M0.exponent?]] reads a scale back as an integer exponent or nothing:

```lean
open FloatLib.Floats.Formats.OCP.MX

#eval E8M0.exponent? (E8M0.ofNatBits 128)
-- some 1
#eval E8M0.exponent? (E8M0.ofNatBits 255)
-- none
```

The E8M0 code supplies an exponent for the entire block, while each element supplies its own signed value. The exact block decoding in [chapter 09](#/chapter/low-precision-formats-for-machine-learning) combines these two parts without rounding. The format catalog distinguishes these scaled representations from the [IEEE binary formats](#/chapter/ieee-binary-formats) and relates them to the other [fixed-point and block-scaled systems](#/chapter/fixed-point-logarithmic-codebook-and-block-scaled).

In the evaluation above, `some 1` is an exponent, so code 128 supplies a scale of two. An element that decodes to 1.5 then denotes 3 in the block; an element that decodes to −0.5 denotes −1. Changing only the scale code to 129 doubles both values again. Multiplying a dyadic by a power of two changes its exponent without discarding significand bits, which is why this joint decoding is exact. Choosing element codes and a scale to approximate an input block is a separate conversion problem.

TF32 has a sign, exponent, and fraction, so [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.tf32]] uses a 19-bit IEEE-encoded descriptor with eight exponent and ten fraction bits. Here the descriptor records the grid of rounded values. It does not describe an independent 19-bit hardware storage format; TF32 computation uses binary32 inputs with reduced significand precision.

<a id="the-dissenters-posits-and-the-quire"></a>

## Posits and the quire

Posits allocate bits differently again. Gustafson and Yonemoto proposed in 2017 [@gustafsonYonemoto2017] a variable-length, run-length-coded regime field. Values near 1 need a short regime, leaving more bits for the fraction; extreme magnitudes need a longer regime and leave fewer fraction bits. Posits have one NaR (not a real) code, one zero, and no separate subnormal encoding. A companion fixed-point accumulator, the quire, can accumulate products exactly until its coefficient range is exhausted. The 2017 family was written `posit<n, es>`; the Posit Standard of 2022 [@positStandard2022] fixed the exponent parameter at two bits, so a standard posit is identified by total width alone.

FloatLib implements the core arithmetic and quire of the 2022 posit standard. The descriptor [[FloatLib.Floats.Formats.Posit.Format]] contains the width and a proof that it is at least two. [[FloatLib.Floats.Formats.Posit.Format.exponentBits]] is the constant 2 and [[FloatLib.Floats.Formats.Posit.Format.regimeExponentStep]] the constant 4, matching the fixed exponent parameter. The executable carriers [[FloatLib.Floats.ExecFloat.Binary]] and [[FloatLib.Floats.ExecFloat.Posit]] expose the same operation and status vocabulary, while [[FloatLib.Floats.ExecFloat.Posit.Quire]] exposes the quire. This lets a calculation such as division by three be written for either family:

```lean
#eval (FloatLib.Floats.Formats.Posit.Format.mk 32 (by decide)).exponentBits
-- 2

abbrev Posit32 := ExecFloat.Posit (bits := 32)

#eval ((1 : Posit32) / 3)
-- 33333333395421504974365234375e-29
#eval ((1 : Binary32) / 3)
-- 11184811 * 2^-25
```

The posit quotient is closer to one third in this example because its short regime leaves more fraction bits than binary32 has. At extreme magnitudes the longer regime consumes those bits, so the comparison depends on the values being represented. De Dinechin, Forget, Muller, and Uguen examine this distribution of precision and its hardware costs [@deDinechinPosits2019]. The format and quire are developed in [chapter 11](#/chapter/posits-and-the-quire), and [chapter 15](#/chapter/performance) reports measured execution times.

The posit printer uses decimal notation here; its output is exactly $178956971\cdot2^{-29}$. With both quotients written as dyadics, we can compare their errors directly:

$$
  \frac{178956971}{2^{29}} - \frac13 = \frac{1}{3\cdot2^{29}},
  \qquad
  \frac{11184811}{2^{25}} - \frac13 = \frac{1}{3\cdot2^{25}}.
$$

Both quotients lie above one third. The posit error is sixteen times smaller here, corresponding to four additional fraction bits at this magnitude. This advantage comes from how the format distributes its fixed bit budget: lengthening the regime for very large or very small values reduces the space left for those fraction bits. A comparison on one third therefore tells us about precision near one third, without settling which format suits a calculation whose intermediates span a wider range.

[Chapter 16](#/chapter/external-validation) compares posit results with Stillwater's independent implementation and explains which operations and widths that implementation supports.

<a id="p3109-and-the-attempt-to-standardize-again"></a>

## P3109 formats

The IEEE P3109 working group's interim report [@p3109InterimReport] proposes a parameterized family for low-precision arithmetic; it is not an approved IEEE standard. Its four parameters are total width $K$, precision $P$ including the implicit bit, signedness, and a domain that is finite or extended with infinities. A signed P3109 format places its single NaN at the midpoint of the code space, in the word that would otherwise be negative zero. An extended format places infinities at the endpoints of its finite ranges, instead of reserving an all-ones exponent class. Unsigned formats use the sign bit for magnitude. The report also specifies nine rounding modes, including round-to-odd and three stochastic variants, and three saturation behaviours.

[[FloatLib.Floats.Formats.P3109.Format]] represents this family with proof fields that rule out invalid parameter combinations. [[FloatLib.Floats.Formats.P3109.Format.signed]] discharges them by `decide` for literal parameters. The corresponding mode types are [[FloatLib.Floats.Formats.P3109.RoundingMode]] and [[FloatLib.Floats.Formats.P3109.SaturationMode]], and [[FloatLib.Floats.ExecFloat.P3109]] is the configured carrier. An eight-bit signed extended format with precision four has the following special codes:

```lean
def p3109Signed8 : FloatLib.Floats.Formats.P3109.Format := .signed 8 4 .extended

#eval p3109Signed8.exponentBits
-- 4
#eval p3109Signed8.nanBits
-- 128
#eval p3109Signed8.positiveInfinityBits
-- 127
#eval p3109Signed8.negativeInfinityBits
-- 255
```

An eight-bit signed format with precision four has four exponent bits, its NaN at code 128, and its infinities at 127 and 255. FloatLib builds arithmetic on this representation: addition, subtraction, multiplication, division, and fused multiply-add compute an exact expression and then round and saturate once. Square root uses exact comparisons with squared rounding boundaries. [Chapter 10](#/chapter/p3109) develops these operations and their proofs against the working-group report.

<a id="what-is-still-open"></a>

The working group's value tables provide an independent way to check how a word is decoded. [Chapter 16](#/chapter/external-validation) describes those comparisons. They check the interpretation of the encoding; they do not test arithmetic, exception behaviour, or accelerator hardware.

<a id="where-this-lives-in-the-library"></a>

## Sources and definitions

The cited reports and analyses are listed in the [bibliography](#/references). The code used here includes the [fixed-point family](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/FixedPoint), [bounded integer representation](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Numerics/Representations/FixedInt/Core.lean), and [integer interpretation proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Numerics/Representations/FixedInt/Semantics/Basic.lean). The [status operations](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Status/Runtime.lean) return the flags. For the arithmetic arguments, see the [configured refinement equations](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Proof/Arithmetic.lean), [binary arithmetic semantics](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/BinaryInterchange/Arithmetic), and [binary64 divider proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/Word/Full/Division/Proof.lean); the [backend guide](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/README.md) describes how the implementations fit together.
