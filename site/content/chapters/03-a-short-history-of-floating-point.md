---
number: "03"
slug: a-short-history-of-floating-point
title: "A short history of floating point"
summary: "Common arithmetic rules, numerical failures, and newer formats explain the choices made in today's floating-point systems."
---

To read an old floating-point word, we need more than its field widths: we need the radix, bias, and rules for reserved values. Machines have differed in all three, so moving numerical code between them has often required more than changing the word size. IEEE 754 established common formats and arithmetic rules; more recent low-precision formats allocate their limited bit patterns differently. The encodings described in [chapter 02](#/chapter/from-reals-to-machine-numbers) fit into the timeline in [Figure 3.1](#/chapter/a-short-history-of-floating-point/figure-ch04-standards-timeline): choices about range, precision, and exceptional results keep recurring.

![Five milestones in floating-point formats, from an early computer design to low-precision standards](assets/ch04-standards-timeline.png "Selected milestones in floating-point representation and standardization. The P3109 entry refers to an interim report.")

<a id="before-there-was-a-standard"></a>

## Before IEEE 754

Konrad Zuse's electromechanical Z3 used binary floating point with 14 stored significand bits and a 7-bit exponent. In his [reconstruction based on Zuse's 1941 patent application](https://www.inf.fu-berlin.de/inst/ag-ki/rojas_home/documents/1996/Konrad_Zuses_Legacy.pdf), Raúl Rojas describes exponent encodings for zero and infinity. Undefined operations such as $0/0$ lit an exception lamp and stopped the machine.

Through the 1960s and 1970s manufacturers built floating-point units with incompatible formats and arithmetic rules. IBM's System/360, announced in 1964, used the hexadecimal formats specified in its [Principles of Operation](https://bitsavers.org/pdf/ibm/360/princOps/A22-6821-6_360PrincOpsJan67.pdf). Normalization shifted the significand four bits at a time until its first hexadecimal digit was nonzero. If that digit was 1, its binary expansion began with three zero bits followed by a one. Those leading zeros occupied storage without contributing precision. A 32-bit System/360 float therefore stored 24 significand bits but could provide as few as 21 significant binary digits, depending on its leading hexadecimal digit.

The CDC 6600 used 60-bit words with an 11-bit exponent and a 48-bit coefficient; its [reference manual](https://bitsavers.org/pdf/cdc/cyber/cyber_70/60045000_6600_Computer_System_RefMan_Aug63.pdf) distinguishes rounded from unrounded floating-point instructions. For the Cray-1, the [hardware reference manual](https://bitsavers.org/pdf/cray/CRAY-1/HR-0004-CRAY_1_Hardware_Reference_Manual-PRELIMINARY-1975.OCR.pdf) specifies that vector floating-point underflow clears the affected result to zero without an interrupt. This affects a useful property of subtraction, that $x - y = 0$ implies $x = y$. Two distinct representable values can have a difference below the smallest normal value. If that difference flushes to zero, testing the computed difference no longer distinguishes them. Gradual underflow preserves small differences by allowing subnormal results, at an additional implementation cost that contributed to the resistance to adopting it.

DEC's VAX F_float and G_float formats used different exponent conventions and field layouts from IEEE binary formats. The [VAX Architecture Reference Manual](https://bitsavers.org/pdf/dec/vax/archSpec/EY-3459E-DP_VAX_Architecture_Reference_Manual_1987.pdf) specifies reserved operands that raise a reserved-operand fault when used in arithmetic; the formats have no infinity or NaN encodings. A program developed on a VAX, ported to a System/360, and validated on a CDC machine could produce three answers for reasons having nothing to do with its algorithm.

To reproduce an operation across these machines, a description needed the radix, the normalization rule, and the treatment of results outside the normal range. It also needed rules for operations such as $0/0$. A word's field widths could not supply those answers: the same allocation of bits could be interpreted with a different bias or a different exceptional-value convention.

## Kahan, the 8087, and 754-1985

William Kahan, at Berkeley since 1969, became a central advocate for a common arithmetic standard. His proposal included reproducible results across conforming machines, specified exceptional cases, and correct rounding of the basic operations. Under nearest rounding, each operation returns the representable value nearest its exact result. This determines the output of an individual operation even when the hardware algorithms used to compute it differ.

Correct rounding gives a numerical proof a precise target: for finite operands and a finite result, the decoded answer equals one rounding of the exact real operation. [Chapter 06](#/chapter/the-numerical-models/the-rounding-contract-as-a-statement-about-reals) develops that statement and its hypotheses.

Intel's 8087 coprocessor, released in 1980, implemented correctly rounded basic operations, gradual underflow through subnormals, infinities, NaNs, an 80-bit extended internal format, and sticky exception flags. It provided a working implementation of ideas being developed for the standard. The committee ratified IEEE 754-1985 [@ieee754_1985] five years later, after disagreements that included the cost of gradual underflow and compatibility with existing hardware. Kahan received the Turing Award in 1989. His lecture notes on the standard, still marked "work in progress" in the 1997 revision cited here [@kahan1997], describe its contested choices.

IEEE 754-1985 specified binary formats, including the familiar biased exponent and implicit leading bit of the interchange formats. It required gradual underflow and defined zeros, subnormals, infinities, and NaNs. The arithmetic rules specified correct rounding for addition, subtraction, multiplication, division, square root, and remainder, with four rounding modes and nearest-even as the default. Five sticky flags recorded invalid operation, division by zero, overflow, underflow, and inexactness.

The 8087's 80-bit extended format stores its integer bit explicitly. A [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat]] assumes an implicit leading bit, so a descriptor with 15 exponent bits and 63 fraction bits has the same normal values as x87 extended but different bit patterns. Representing the numerical grid does not by itself represent that storage format.

The 1985 standard did not require correct rounding of transcendental functions. The 2008 revision [@ieee754_2008] recommends it, but determining the rounded result of $\exp$ or $\log$ can require much more precision than the destination stores. If the exact result lies very close to a rounding midpoint, an approximation may need many additional digits before it establishes which side of the midpoint contains the result. This is the table maker's dilemma. De Dinechin, Lauter, and Muller's correctly rounded logarithm [@deDinechinLog2007] is an example of the analysis and algorithms needed to resolve it.

An enclosure establishes correct rounding when both endpoints round to the same destination value: every enclosed value then has that rounded result. A deterministic approximation or a small absolute-error budget alone does not settle the question.

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

abbrev Binary32 := ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)
abbrev Binary64 := ExecFloat.Binary (exponentBits := 11) (fractionBits := 52)

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

We started with a stored step that is too large, yet both accumulated totals are too small. The stored tenth is $13421773 / 2^{27}$, slightly above $0.1$, so ten thousand exact copies sum to just over 1000: the second result, $8388608125 / 8388608$, is 1000 plus about $1.5 \times 10^{-5}$. Nearest-even accumulation instead ends about a tenth short, and truncation twice as far short. Most of that error comes from rounding the additions, not from converting the literal.

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

The last evaluation sets `inexact` because that addition required rounding. A loop can retain such flags with [[FloatLib.Numerics.IEEEStatus.union]], which combines each field with logical OR. This records whether an event occurred anywhere in the loop. It cannot distinguish one inexact addition from ten thousand, or tell whether their errors cancel. A bound on the final error needs the rounding analysis as well as the status record.

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

We can reproduce the truncated constant with exact integer arithmetic. `ClockGrid` uses the [fixed-point family](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/FixedPoint) with 23 fraction bits. Its unbounded integer coefficient is divided by $2^{23}$ when decoded. This reproduces the rounding grid without modelling the clock register's finite storage. [[FloatLib.Floats.ExecFloat.FixedPoint.toRat]] reads the coefficient back as an exact rational:

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

The check computes with exact integer coefficients and rationals, so it isolates the discarded $1/10485760$ per tick without adding rounding error to the analysis itself.

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

The second and third evaluations print the first nineteen digits of the rounded and exact quotient using integer arithmetic, avoiding another floating-point conversion in the display. They agree through the seventeenth. [[FloatLib.Floats.ExecFloat.Proof.div_eq_spec]] covers every pair of stored operands, including exceptional cases. The real-valued theorem [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_div_eq_roundAt]] identifies the rounded quotient under finite-input, nonzero-divisor, and finite-result hypotheses; [chapter 06](#/chapter/the-numerical-models) explains that connection.

An implementation proof must also account for the quotient bits the algorithm generates. FloatLib's [finite binary64 divider](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/Word/Full/Division/Proof.lean) uses a restoring `UInt64` loop, a simpler recurrence than the Pentium's SRT digit selection.

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

At three fractional bits, the exact quotient is $(14+6/7)\cdot2^{-3}$. The remainder is more than half the divisor, so nearest rounding increments 14 to 15 and returns $15/8$. A remainder below half would keep the quotient; an exact half would inspect its parity. The binary64 loop uses the same recurrence with enough digits for its significand. Its proof also needs bounds ensuring that doubling the quotient and remainder fits the machine words. The refinement proof covers both the finite-word calculation and calls declined by the partial kernel; the total dispatcher supplies a proved fallback.

A divider that returns an incorrect quotient for even one input pair cannot satisfy this equality with a correct reference. The proof for an optimized loop or table must cover every returned result, including inputs that exercise rarely used branches.

<a id="what-a-verified-library-changes"></a>

The public refinement equation lets a caller use that agreement without naming the selected kernel. [Chapter 05](#/chapter/why-execution-and-proofs-are-separate) follows how a local algorithm proof becomes a theorem about the public operation.

<a id="what-it-does-not-change"></a>

These equations concern Lean definitions. Running the software also relies on the compiler and runtime to implement integer and bit-vector operations correctly. The certified software divider uses integer arithmetic. Optional calls to the host floating-point divider live in the [unchecked host-arithmetic module](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/NativeFPU/Unchecked.lean); [chapter 19](#/chapter/external-validation) compares their results with the software model. Those comparisons can reveal disagreements, but the software proof does not establish correctness of the processor's divider.

<a id="an-overflow-that-was-not-floating-point-ariane-5-flight-501-1996"></a>

## A narrowing conversion: Ariane 5, flight 501, 1996

On 4 June 1996 the maiden flight of Ariane 5 lifted off from Kourou. The inquiry board chaired by Jacques-Louis Lions reported on 19 July 1996 [@lions1996] that the failure "was caused by the complete loss of guidance and attitude information 37 seconds after start of the main engine ignition sequence (30 seconds after lift-off)". The launcher swung to an angle of attack above 20 degrees, the boosters tore off, and the self-destruct fired about 39 seconds after H0, the report's zero, the moment the launch sequence was initiated.

The failure occurred in a conversion from floating point to a bounded integer. The board wrote that the inertial reference system's software exception "was caused during execution of a data conversion from 64-bit floating point to 16-bit signed integer value. The floating-point number which was converted had a value greater than what could be represented by a 16-bit signed integer. This resulted in an Operand Error." The horizontal bias variable BH could be represented in binary64, but exceeded its destination's range. The destination was a 16-bit two's complement integer whose largest value is 32767. In IEEE 754 terms this is the invalid-operation case of conversion to an integer format (clause 5.8 of [@ieee754_2019]); rounding played no part in the failure. The board found that "the data conversion instructions (in Ada code) were not protected from causing an Operand Error, although other conversions of comparable variables in the same place in the code were protected", so the handler did what it was designed to do for a hardware fault and shut the unit down. The backup unit, running the same software on the same data, had shut itself down during the previous 72 millisecond data cycle, for the same reason.

The decision to leave this conversion unprotected rested on a range assumption. With a processor workload ceiling of 80 percent, checks were omitted for variables judged "either physically limited or that there was a large margin of safety, a reasoning which in the case of the variable BH turned out to be faulty". The computation belonged to an alignment function, meaningful only before lift-off, that for Ariane 4's sake kept running for about 40 seconds of flight. Ariane 5's early trajectory "results in considerably higher horizontal velocity values", and the equipment-level tests "did not specifically include the Ariane 5 trajectory data". The bound on BH was an assumption inherited from another rocket, and the board recommended: "Identify all implicit assumptions made by the code and its justification documents on the values of quantities provided by the equipment."

In FloatLib a [16-bit signed destination](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Numerics/Representations/FixedInt/Core.lean) is [[FloatLib.Numerics.Representations.FixedInt]] at width 16. Its representable range is expressed by the decidable proposition [[FloatLib.Numerics.Representations.FixedInt.InRange]]. The board did not publish the value BH reached, so we'll use 40000 as an illustrative input above 32767, not a reconstruction of the flight data. The first two evaluations show that it is out of range and that storing its low sixteen bits wraps it to $-25536$. The remaining evaluations convert a binary64 value to the same sixteen-bit integers, represented as a bounded fixed-point grid with no fraction digits. Only the overflow policy changes between the three casts.

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

#eval (ExecFloat.castWith (target := Int16Grid) horizontalBias OverflowPolicy.wrap).value?.map
  ExecFloat.BoundedFixedPoint.coefficient
-- some (-25536)

#eval (ExecFloat.castWith (target := Int16Grid) horizontalBias OverflowPolicy.saturate).value?.map
  ExecFloat.BoundedFixedPoint.coefficient
-- some 32767
```

The default cast returns `outOfRange` as an ordinary result, allowing the caller to handle the failed conversion. Explicit alternatives wrap to $-25536$ or saturate to $32767$. The full outcomes also mark `overflow` and `inexact`, with `wrapped` or `saturated` identifying the selected policy; the last two evaluations show only their returned values. Neither alternative preserves the original value, so whether it is useful depends on the application.

The wrapped value follows from the bit interpretation. Sixteen bits store a residue modulo $2^{16} = 65536$. The residue 40000 has its top bit set, so reading it as a signed two's-complement integer subtracts 65536 and gives $40000 - 65536 = -25536$. Saturation instead returns the upper endpoint, losing $40000 - 32767 = 7233$. Both are well-defined arithmetic operations, but each replaces a positive measurement with a different value. Reporting the selected policy in the status lets the caller distinguish that replacement from a successful value-preserving conversion.

The round-trip theorem for a 16-bit store, `toInt_ofInt_eq_self`, assumes that the value fits:

```lean
example (value : Int) (h : FixedInt.InRange 16 value) :
    (FixedInt.ofInt value : FixedInt 16).toInt = value :=
  FixedInt.toInt_ofInt_eq_self (by decide) h
```

The `InRange 16 value` hypothesis in the [integer interpretation proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Numerics/Representations/FixedInt/Semantics/Basic.lean) is the precise condition under which storing and reading the integer preserves it. Proving this theorem once does not establish `InRange 16 BH` for a particular trajectory. That requires evidence about the values the guidance system can produce, and a change from Ariane 4 to Ariane 5 requires revisiting that evidence. The same distinction appeared in the division theorem above: the arithmetic proof assumes finite inputs and a nonzero divisor; the application must show that its inputs satisfy those conditions.

The alignment output was unused after lift-off, but an exception in the unused calculation could still shut down the reference unit. Choosing a conversion policy therefore also requires tracing how the surrounding program handles the result. A returned failure, a wrapped value, and a saturated value each need an appropriate response from the caller.

<a id="verification-enters"></a>
<a id="where-this-lives-in-the-library"></a>
<a id="sources-and-definitions"></a>

## Proofs of hardware and software arithmetic

The FDIV failure showed why a division algorithm had to meet its specification on every input. Subsequent hardware verification work included Moore, Lynch, and Kaufmann's proof of AMD5K86 division microcode in ACL2 in 1998 [@mooreLynchKaufmann1998], and Russinoff's proofs for AMD-K7 multiplication, division, and square root that year [@russinoff1998]. Harrison built a machine-checked theory of floating point in HOL Light in 1999 [@harrison1999], which Intel then used for its own algorithms.

Flocq, Boldo and Melquiond's Coq library [@boldoMelquiond2011], organizes floating point around a rounded-real model. A float is a real number on a grid determined by a radix and an exponent function; rounding maps a real number onto that grid. This separates properties of the represented values from details of how a machine stores them. Theorems about ulps, error bounds, and Sterbenz subtraction can then be stated for a family of grids and applied to individual formats by proving that they meet the hypotheses.

FloatLib's rounded-real layer follows this organization in Lean; its grid definitions and proofs are developed in [chapter 07](#/chapter/the-mathematics-of-rounding). [Chapter 17](#/chapter/performance) compares its execution cost with an independent proved implementation extracted from Flocq. The comparison matches binary precision and exponent bounds and checks the complete input and output values; [chapter 19](#/chapter/external-validation/binary-arithmetic-with-flocq-and-mpfr) describes those numerical checks.

<a id="the-2008-and-2019-revisions-and-the-decimal-question"></a>

## The 2008 and 2019 revisions

The 1985 standard was binary only. IEEE 854 in 1987 [@ieee854_1987] restated the rules for radix 2 or 10 without fixing any bit layout, and the two were merged in IEEE 754-2008, which added decimal32, decimal64, and decimal128 with two competing significand encodings, IBM's densely packed decimal and Intel's binary integer decimal. It also added binary16 as an interchange format, made fused multiply-add a required operation, added a ties-to-away rounding mode required only for decimal arithmetic, and introduced `minNum` and `maxNum`. IEEE 754-2019 [@ieee754_2019] was a smaller revision. It replaced `minNum` and `maxNum` with four operations, `minimum`, `maximum`, `minimumNumber`, and `maximumNumber`, which distinguish NaN-propagating behaviour from a preference for numerical operands. It also recommended augmented operations that return the exact rounding error alongside the result and revised other edge cases.

Decimal arithmetic makes a familiar distinction visible. On a grid of hundredths, ten cents plus twenty cents is exactly thirty cents: the integer coefficients add as $10+20=30$, denoting $3/10$. Binary32 cannot represent that rational and rounds it to $5033165 \cdot 2^{-24}$. A fixed decimal scale is useful when the application knows its unit; decimal floating point allows the scale to change with an exponent. Either still needs a rounding rule for results between grid points. [The decimal discussion](#/chapter/decimal-arithmetic/encoding-the-complete-datum) develops the two encodings and explains why one numerical value can have several decimal representations.

<a id="machine-learning-reopens-the-encoding-questions"></a>

## Low-precision formats for machine learning

Binary64 became common in scientific computing and binary32 in graphics. Deep learning brought renewed interest in narrower formats. A gradient estimated from a random mini-batch already contains noise, which can make reduced precision acceptable, while smaller operands reduce storage and data movement. The usable precision still depends on the model and training procedure.

Micikevicius and colleagues demonstrated mixed-precision training in 2018 [@micikevicius2018mixed], using binary16 storage with a binary32 master copy of the weights and loss scaling to protect small gradients. These techniques address different losses of information: the master weights retain updates too small for binary16, while scaling helps keep gradients within its usable exponent range. The format limits are described in [chapter 11](#/chapter/low-precision-formats-for-machine-learning). [Google's TPU v2 and v3 used bfloat16](https://cloud.google.com/blog/products/ai-machine-learning/bfloat16-the-secret-to-high-performance-on-cloud-tpus), which keeps binary32's 8 exponent bits but stores only 7 fraction bits. Its 8-bit significand provides about two decimal digits. Within a 16-bit word, this allocates more bits to range and fewer to precision than binary16.

At one, binary16 has spacing $2^{-10}$, while bfloat16 has spacing $2^{-7}$, eight times larger. The exact value $1+2^{-8}$ occupies four binary16 steps above one and is representable there; in bfloat16 it is a midpoint and nearest-even returns one. The extra exponent bits give bfloat16 a wider range: binary16's smallest positive normal is $2^{-14}$, while bfloat16's is $2^{-126}$. Equal storage width therefore does not make the two formats interchangeable. A computation can need the finer steps of one and the smaller normal magnitudes of the other.

A binary32 master weight preserves small updates by accumulating them before conversion back to the storage format. For example, a binary16 weight at one cannot retain an increment of $2^{-12}$: each separately rounded update returns one. In binary32, four such increments accumulate exactly to $2^{-10}$, a full binary16 step, which survives the next conversion. Loss scaling addresses a different point in the calculation. Multiplying a gradient of $2^{-20}$ by $2^{10}$ moves it to $2^{-10}$, within binary16's normal range, where more significant bits are available. The scale must be introduced before the low-precision operations whose small outputs it is meant to protect, then accounted for when applying the update. Making it too large can cause overflow. These small calculations illustrate the two mechanisms; they do not establish an error bound for a training run.

Micikevicius and colleagues proposed the eight-bit E5M2 and E4M3 formats in 2022 [@micikevicius2022fp8], and NVIDIA's H100 shipped tensor cores for both that year. The Open Compute Project's OFP8 specification standardized them in 2023 [@ocpOfp8], with differences in exceptional-value encoding as well as precision. E5M2 keeps IEEE conventions, including infinities and multiple NaN codes. E4M3FN has no infinity and one NaN pattern per sign. It uses most of the all-ones exponent class for finite values, extending its finite range beyond what the same field widths would provide with the IEEE reservation. With only 256 words available, changing a reserved code class changes an appreciable part of the format.

The ONNX float8 definitions [@onnxFloat8] include FNUZ variants that remove negative zero, reuse its word as the sole NaN, and shift the bias by one. The OCP Microscaling specification, also from 2023 [@ocpMx], combines narrow elements in blocks with a shared eight-bit power-of-two scale. Its E8M0 scale has no sign, fraction, or zero. The FP8 elements reuse OFP8 formats, while the FP6 and FP4 formats E2M3, E3M2, and E2M1 make every word finite, with no NaN. An element's decoded value is then multiplied by the block scale, so the element word alone does not determine its value in the block.

The same word can consequently mean very different things: `0x7c` is $+\infty$ in E5M2 and 384 in E4M3FN. [Chapter 11](#/chapter/low-precision-formats-for-machine-learning) decodes both and develops the format-specific arithmetic. The field widths alone cannot determine the value.

Overflow policy is a separate choice. In FloatLib, an E4M3FN result too large to round back to 448 can become NaN or saturate at 448, according to the selected policy. The encoding stays the same. A theorem about one policy does not establish the behaviour of another; [chapter 04](#/chapter/why-verifying-floating-point-is-hard/overflow-policy-and-the-sign-of-zero) compares them on the same input.

A shared scale changes the interpretation of every element in a block. E8M0 code $c$, from 0 through 254, denotes $2^{c-127}$; code 255 is NaN. Code 128 therefore supplies a scale of two: elements that decode to 1.5 and $-0.5$ denote 3 and $-1$ in the block. Changing the scale code to 129 doubles both again. Multiplication by a power of two changes a dyadic's exponent without discarding significand bits, so this joint decoding is exact. Choosing the codes and scale to approximate an input block is a separate conversion problem, developed in [chapter 11](#/chapter/low-precision-formats-for-machine-learning).

A numerical grid also need not be a hardware storage format. TF32 computations use binary32 inputs with reduced significand precision. Its eight exponent and ten fraction bits describe the rounded values; they do not imply an independent 19-bit hardware word.

<a id="the-dissenters-posits-and-the-quire"></a>

## Posits and the quire

Posits allocate bits differently again. Gustafson and Yonemoto proposed in 2017 [@gustafsonYonemoto2017] a variable-length, run-length-coded regime field. Values near 1 need a short regime, leaving more bits for the fraction; extreme magnitudes need a longer regime and leave fewer fraction bits. Posits have one NaR (not a real) code, one zero, and no separate subnormal encoding. A companion fixed-point accumulator, the quire, can accumulate products exactly until its coefficient range is exhausted. The 2017 family was written `posit<n, es>`; the Posit Standard of 2022 [@positStandard2022] fixed the exponent parameter at two bits, so a standard posit is identified by total width alone.

This allocation changes precision even at familiar values. Rounding one third to a standard 32-bit posit gives $178956971\cdot2^{-29}$, while binary32 gives $11184811\cdot2^{-25}$. Their errors are

$$
  \frac{178956971}{2^{29}} - \frac13 = \frac{1}{3\cdot2^{29}},
  \qquad
  \frac{11184811}{2^{25}} - \frac13 = \frac{1}{3\cdot2^{25}}.
$$

Both quotients lie above one third. The posit error is sixteen times smaller here, corresponding to four additional fraction bits at this magnitude. This advantage comes from how the format distributes its fixed bit budget: lengthening the regime for very large or very small values reduces the space left for those fraction bits. A comparison on one third therefore tells us about precision near one third, without settling which format suits a calculation whose intermediates span a wider range.

De Dinechin, Forget, Muller, and Uguen examine this distribution of precision and its hardware costs [@deDinechinPosits2019]. [Chapter 13](#/chapter/posits-and-the-quire) develops the encoding and the quire's capacity conditions; [chapter 19](#/chapter/external-validation) compares the arithmetic with an independent implementation.

<a id="p3109-and-the-attempt-to-standardize-again"></a>

## P3109 formats

The IEEE P3109 working group's interim report [@p3109InterimReport] proposes a parameterized family for low-precision arithmetic; it is not an approved IEEE standard. Its four parameters are total width $K$, precision $P$ including the implicit bit, signedness, and a domain that is finite or extended with infinities. A signed P3109 format places its single NaN at the midpoint of the code space, in the word that would otherwise be negative zero. An extended format places infinities at the endpoints of its finite ranges, instead of reserving an all-ones exponent class. Unsigned formats use the sign bit for magnitude. The report also specifies nine rounding modes, including round-to-odd and three stochastic variants, and three saturation behaviours.

For example, a signed eight-bit extended format with precision four has its NaN at code 128 and its infinities at 127 and 255. Those placements differ from an IEEE exponent-class reservation despite the familiar division into sign, exponent, and fraction. [Chapter 12](#/chapter/p3109) develops the encoding, rounding and saturation rules, and FloatLib's proofs against the interim report.

<a id="what-is-still-open"></a>

The working group's value tables provide an independent way to check how a word is decoded. [Chapter 19](#/chapter/external-validation) describes those comparisons. They check the interpretation of the encoding; they do not test arithmetic, exception behaviour, or accelerator hardware.
