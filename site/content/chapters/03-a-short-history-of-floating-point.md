---
number: "03"
slug: a-short-history-of-floating-point
title: "A short history of floating point"
summary: "Common arithmetic rules, numerical failures, and newer formats explain the choices made in today's floating-point systems."
---

An IBM System/360 float could store 24 significand bits and provide only 21 significant binary digits. A VAX float had no encodings for infinity or NaN. Porting a numerical program between machines meant accounting for differences like these in both representation and arithmetic. IEEE 754 established common rules for the basic operations, and later standards added decimal arithmetic and formats with fewer bits. [Figure 3.1](#/chapter/a-short-history-of-floating-point/figure-ch04-standards-timeline) places the formats we'll use in that history.

![Five milestones in floating-point formats, from an early computer design to low-precision standards](assets/ch04-standards-timeline.png "Selected milestones in floating-point representation and standardization. The P3109 entry refers to an interim report.")

## Before IEEE 754

Konrad Zuse's electromechanical Z3 used binary floating point with 14 stored significand bits and a 7-bit exponent. In his [reconstruction based on Zuse's 1941 patent application](https://www.inf.fu-berlin.de/inst/ag-ki/rojas_home/documents/1996/Konrad_Zuses_Legacy.pdf), Raúl Rojas describes exponent encodings for zero and infinity, and undefined operations such as $0/0$ lit an exception lamp and stopped the machine.

Through the 1960s and 1970s manufacturers built floating-point units whose formats and arithmetic rules didn't agree with each other. IBM's System/360, announced in 1964, used the hexadecimal formats specified in its [Principles of Operation](https://bitsavers.org/pdf/ibm/360/princOps/A22-6821-6_360PrincOpsJan67.pdf). Normalization shifted the significand four bits at a time until its first hexadecimal digit was nonzero. If that digit was 1, its binary expansion began with three zero bits and then a one, and those zeros took up storage and added no precision. So a 32-bit System/360 float stored 24 significand bits, but depending on its leading hexadecimal digit it could provide as few as 21 significant binary digits.

The CDC 6600 used 60-bit words with an 11-bit exponent and a 48-bit coefficient, and its [reference manual](https://bitsavers.org/pdf/cdc/cyber/cyber_70/60045000_6600_Computer_System_RefMan_Aug63.pdf) distinguishes rounded from unrounded floating-point instructions. On the Cray-1, the [hardware reference manual](https://bitsavers.org/pdf/cray/CRAY-1/HR-0004-CRAY_1_Hardware_Reference_Manual-PRELIMINARY-1975.OCR.pdf) specifies that a vector floating-point underflow clears the affected result to zero without an interrupt. That breaks a useful property of subtraction, that $x - y = 0$ implies $x = y$. Two distinct representable values can have a difference below the smallest normal value, and if that difference flushes to zero, testing it no longer tells them apart. Gradual underflow keeps small differences by allowing subnormal results. It costs more to implement, and that cost was part of the resistance to adopting it.

DEC's VAX F_float and G_float formats used different exponent conventions and field layouts from the IEEE binary formats, and they had no infinity or NaN encodings at all. The [VAX Architecture Reference Manual](https://bitsavers.org/pdf/dec/vax/archSpec/EY-3459E-DP_VAX_Architecture_Reference_Manual_1987.pdf) specifies reserved operands instead, and arithmetic that uses one raises a reserved-operand fault. So a program developed on a VAX, ported to a System/360, and validated on a CDC machine could produce three different answers, for reasons that had nothing to do with its algorithm.

To reproduce an operation across these machines, a description needed the radix, the normalization rule, and the treatment of results outside the normal range, and it also needed rules for operations such as $0/0$. Field widths couldn't supply any of that, because the same allocation of bits could be read with a different bias or a different exceptional-value convention.

## Kahan, the 8087, and 754-1985

William Kahan, at Berkeley since 1969, became a central advocate for a common arithmetic standard. His proposal asked for reproducible results across conforming machines, specified exceptional cases, and correct rounding of the basic operations. Under nearest rounding, each operation returns the representable value nearest its exact result. That fixes the output of every individual operation, even when two machines compute it with different hardware algorithms.

Correct rounding also gives a numerical proof something definite to aim at. For finite operands and a finite result, the decoded answer equals one rounding of the exact real operation, and [Chapter 06](#/chapter/the-numerical-models/the-rounding-contract-as-a-statement-about-reals) develops that statement and its hypotheses.

Intel's 8087 coprocessor came out in 1980. It had correctly rounded basic operations, gradual underflow through subnormals, infinities, NaNs, an 80-bit extended internal format, and sticky exception flags, so the ideas being developed for the standard already had a working implementation. The committee ratified IEEE 754-1985 [@ieee754_1985] five years later, after disagreements that included the cost of gradual underflow and compatibility with existing hardware. Kahan received the Turing Award in 1989. His lecture notes on the standard describe its contested choices, and the 1997 revision cited here [@kahan1997] is still marked "work in progress".

IEEE 754-1985 specified binary formats with the familiar biased exponent and implicit leading bit of the interchange formats. It required gradual underflow and defined zeros, subnormals, infinities, and NaNs. Addition, subtraction, multiplication, division, square root, and remainder had to be correctly rounded, with four rounding modes and nearest-even as the default, and five sticky flags recorded invalid operation, division by zero, overflow, underflow, and inexactness.

The 8087's 80-bit extended format is the odd one out, because it stores its integer bit in the word. A [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat]] assumes an implicit leading bit, so a descriptor with 15 exponent bits and 63 fraction bits has the same normal values as x87 extended, but different bit patterns. Getting the numerical grid right doesn't give you that storage format.

The 1985 standard didn't require correct rounding of transcendental functions. The 2008 revision [@ieee754_2008] recommends it, but finding the rounded result of $\exp$ or $\log$ can take much more precision than the destination stores. When the exact result lies very close to a rounding midpoint, an approximation may need many more digits before it can tell which side of the midpoint the result is on. That's the table maker's dilemma. De Dinechin, Lauter, and Muller's correctly rounded logarithm [@deDinechinLog2007] shows the kind of analysis and algorithms it takes to resolve it.

An enclosure settles correct rounding when both endpoints round to the same destination value, because then every value inside it has that rounded result. A deterministic approximation doesn't settle the question, and neither does a small absolute-error budget on its own.

Where an enclosure sits matters as much as how wide it is. On an integer rounding grid, an enclosure from 1.4999 to 1.5001 is very narrow, but it still crosses the midpoint between one and two. Its lower endpoint rounds to one and its upper endpoint rounds to two, so the rounded answer is still undetermined. An enclosure from 1.5001 to 1.5002 does determine two. For a transcendental result close to a midpoint, the computation has to shrink the uncertainty until it knows which rounding interval contains the result.

Language and compiler specifications decide some things the arithmetic standard leaves open, such as how a program accesses flags and which evaluation transformations are permitted. [Chapter 04](#/chapter/why-verifying-floating-point-is-hard) has examples where those execution rules change the bits a program returns.

<a id="what-imprecision-has-cost"></a>

A common arithmetic standard fixes the result of an operation, but the programs using it still need suitable conversions, error bounds, and models. In [Figure 3.2](#/chapter/a-short-history-of-floating-point/figure-ch03-incident-timeline), the marked causes tell accumulated rounding and conversion errors apart from an incorrect implementation or an inadequate physical model.

A timestamp can be accurate to one part in a million and still be no good for measuring a short interval, because what matters is how its error combines with the error in the timestamp subtracted from it. Narrowing conversions have a different problem, since a value that fits in the source register may not fit the destination range. Both kinds of failure depend on how a program uses its numbers, and not only on the accuracy of each arithmetic operation.

![Five incidents, each marked by the kind of numerical failure described in its primary sources. Sleipner concerns the physical model.](assets/ch03-incident-timeline.png "Five failures with different causes, from arithmetic and conversion errors to an inadequate physical model. Correct rounding alone would not resolve all five.")

## Accumulated truncation: Vancouver, 1982 to 1983

In January 1982 the Vancouver Stock Exchange launched a composite index at 1000.000. It was recomputed after every trade, close to 3000 times on a busy day, and each result was truncated to three decimal places instead of rounded [@quinn1983]. Twenty-two months later, on Friday 25 November 1983, it closed at 524.811. It reopened on Monday 28 November at 1098.892, 574.081 points above Friday's close, after consultants had spent three weeks recomputing it [@lilley1983]. Repeated truncation had dragged the published index a long way down.

For a positive value, truncating to three decimal places throws away something between 0 and 0.001. If the discarded digits are evenly spread, the average loss is 0.0005 per update. So 3000 updates a day would lose about a point and a half per trading day, on the order of thirty points a month. That's an estimate under a distributional assumption. It doesn't reconstruct every trade. The exchange put the loss at a point a day and twenty a month [@lilley1983]. The recorded 574 points over 22 months comes to about 26 a month. All three figures describe the accumulation of small downward errors.

Rounding to nearest allows errors of both signs, but nothing guarantees that they cancel. Let's see that in binary32, with an example that has nothing to do with the exchange's decimal calculation. Start at zero and add `0.1` ten thousand times. Two sources of error need to be kept apart here, because the literal is stored as $13421773 / 2^{27}$, and each addition after that may round again.

```lean
open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics
open FloatLib.Numerics.Representations

#eval ExecFloat.Binary.toRat? (0.1 : Binary32)
-- some (13421773 / 134217728)

#eval 10000 * (13421773 / 134217728 : Rat)
-- 8388608125 / 8388608

def accumulate (steps : Nat) (step : Binary32)
    (rounding : Model.IEEERoundingMode) : Binary32 :=
  (List.range steps).foldl
    (fun total _ => (ExecFloat.Binary.add total step (mode := rounding) (status := true)).1) 0

#eval accumulate 10000 0.1 .nearest
-- 999.9029

#eval accumulate 10000 0.1 .towardZero
-- 999.8049

#eval (ExecFloat.Binary.add (1000 : Binary32) 0.1 (mode := .towardZero) (status := true)).2
-- { invalid := false, divideByZero := false, overflow := false, underflow := false, inexact := true }
```

We started with a stored step that's too large, and yet both accumulated totals come out too small. With the stored tenth at $13421773 / 2^{27}$, slightly above $0.1$, ten thousand exact copies sum to just over 1000. The second result, $8388608125 / 8388608$, is 1000 plus about $1.5 \times 10^{-5}$. Nearest-even accumulation ends about a tenth short, and truncation twice as far short. Most of that error comes from rounding the additions, and very little from converting the literal.

A binade is the interval between consecutive powers of two, and within one the spacing of floats is constant. Away from the binade's boundary, the accumulated total sits on that grid, and the fixed step leaves the same remainder relative to the grid spacing. So as long as the exact sums aren't ties, every addition makes the same rounding error. For this step the direction repeats with period four as the binade doubles, with two binades rounding up and then two rounding down. About half the steps fall in the last binade, $[512, 1024)$, which rounds down, so it contributes a large part of the final error. Toward-zero rounding of these positive sums discards a nonnegative amount at every step. In [Figure 3.3](#/chapter/a-short-history-of-floating-point/figure-ch03-binary32-accumulation), look for the straight stretches of error within each binade and the changes at their boundaries.

![Ten thousand binary32 additions of 0.1 under nearest-even and toward-zero rounding, as the running total minus k/10, with the points where the total reaches a new binade marked](assets/ch03-binary32-accumulation.png "Accumulated error after repeated binary32 additions of 0.1, measured against the exact decimal total. Rounding direction changes the drift; each binade changes the step size.")

Let's work out the slope of the final stretch by hand. In $[512,1024)$ a binary32 step is $h = 2^{-14}$, and in units of this spacing, the stored tenth is

$$
  \frac{13421773 / 2^{27}}{2^{-14}}
  = \frac{13421773}{8192}
  = 1638 + \frac{3277}{8192}.
$$

The fractional part is about 0.400024, below one half. So as long as the addition stays in this binade, nearest-even and toward-zero both advance the accumulator by $1638h = 0.0999755859375$. The plotted reference advances by exactly one tenth, so the error falls by

$$
  \frac{1638}{16384} - \frac1{10}
  = -\frac1{40960}
$$

on each step. Both modes use this same increment and differ only in the accumulated error they bring into the binade, so the two final stretches are parallel. Each doubling of the grid spacing changes the fractional part of the step measured in grid units, and that explains the earlier changes of slope.

The last evaluation sets `inexact` because that addition had to round. A loop can keep such flags with [[FloatLib.Numerics.IEEEStatus.union]], which combines each field with logical OR, and the result records whether an event occurred anywhere in the loop. It can't tell one inexact addition from ten thousand, or whether their errors cancel. For a bound on the final error you need the rounding analysis as well as the status record.

## Inconsistent time conversions: Patriot, Dhahran, 1991

On 25 February 1991 the Patriot battery protecting Dhahran Air Base failed to track an incoming Scud, which struck an Army barracks and killed 28 American soldiers. A year later the General Accounting Office reported [@gaoPatriot1992] that the battery had run continuously for over 100 hours. The report also says that its weapons control computer kept time as an integer count of tenths of a second. The range gate algorithm, which predicts where the target will appear next, needed that count converted to seconds, and the registers were 24 bits long. Converting lost precision, and because the converted times were used inconsistently, the range gate shift grew with running time.

Robert Skeel worked out the arithmetic in SIAM News in July 1992 [@skeel1992]. One tenth has no finite binary expansion: $\tfrac{1}{10} = 0.0\overline{0011}_2$. Keeping 23 fraction bits and discarding the rest stores

$$
\frac{\lfloor 2^{23}/10 \rfloor}{2^{23}} = \frac{838860}{8388608} = \frac{1}{10}\left(1 - 2^{-20}\right),
$$

so every converted time is short by a relative error of $2^{-20}$, about one part in a million. The absolute error per tick is $\tfrac{1}{10 \cdot 2^{20}} = \tfrac{1}{10{,}485{,}760} \approx 9.5 \times 10^{-8}$ seconds. After 100 hours the clock has counted $3{,}600{,}000$ ticks, so the accumulated error is $3{,}600{,}000 / 10{,}485{,}760 \approx 0.3433$ seconds, the GAO's own figure. Its table puts the range gate shift at 55 meters after 8 hours and 137 meters after 20 hours, by which point the target is outside the gate. After 100 hours it's 687 meters. A Scud travels at roughly Mach 5, so in a third of a second it covers, as Skeel put it, more than half a kilometer.

Skeel also examined how the converted times were used. Tracking depends on the difference between the times of two radar pulses. If both timestamps have the same relative error of $2^{-20}$, subtracting them scales the short interval by that same relative error, and most of the error in the two large timestamps cancels. But the software mixed conversions of different accuracy. A more accurate conversion subroutine had been added during deployment, and only some of the half dozen places that needed it called the new routine. Subtract a truncated timestamp from a more accurate one and you're left with an error that grows with the absolute clock time, even when the two pulses are close together.

To see the dependence on uptime, write the earlier time as $T$, the later time as $T+\Delta$, and the truncation's relative error as $\varepsilon = 2^{-20}$. Using the truncated conversion for both timestamps gives

$$
  (1-\varepsilon)(T+\Delta) - (1-\varepsilon)T
  = (1-\varepsilon)\Delta.
$$

That error is proportional to the short interval. To isolate the effect of mixing conversions, treat the more accurate conversion as exact for the moment and use it for the later timestamp only:

$$
  (T+\Delta) - (1-\varepsilon)T
  = \Delta + \varepsilon T.
$$

Now the error contains the total uptime. This simplified calculation doesn't assume the replacement routine was perfectly exact, but it shows why a difference between the conversion rules can survive subtraction, even when the pulse interval is small. The 0.3433-second error after 100 hours measures this uptime term rather than a millionth of the time between pulses. Israeli users had reported the drift on 11 February 1991. A corrected version was released on 16 February and reached Dhahran on 26 February, the day after the barracks was hit.

We can reproduce the truncated constant with exact integer arithmetic. `ClockGrid` uses the [fixed-point family](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/FixedPoint) with 23 fraction bits, and decoding divides its unbounded integer coefficient by $2^{23}$. That reproduces the rounding grid without modelling the clock register's finite storage. [[FloatLib.Floats.ExecFloat.FixedPoint.toRat]] reads the coefficient back as an exact rational:

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

The third result, $5625 / 16384$, is the GAO's 0.3433 seconds as an exact fraction. On the last line, the literal `0.1 : ClockGrid` is rounded to nearest instead and stores 838861. Its error is a quarter the size of truncation's and has the opposite sign. That changes the conversion error, but it doesn't, on its own, make two differently converted timestamps consistent. Since the check computes with exact integer coefficients and rationals, it isolates the discarded $1/10485760$ per tick without adding any rounding error to the analysis itself.

An error budget for the tracking calculation would need the maximum uptime, the interval between observations, and the accuracy of each conversion used in forming that interval. More precision shrinks a conversion error, and a consistent conversion lets the errors in nearby timestamps cancel. Bounds like those in [chapter 07](#/chapter/the-mathematics-of-rounding) only help once the analysis has identified which expression the program actually computes.

## Model error: Sleipner A, 1991

On 23 August 1991 the concrete gravity base of the Sleipner A platform sank in the Gandsfjord outside Stavanger during a controlled ballasting operation, at a depth of about 65 meters. A tricell wall cracked, water came in faster than the pumps could remove it, and the structure went to the bottom. Estimates put the loss at about 700 million dollars. The finite element analysis, done with NASTRAN, had underestimated the shear stresses in the tricell walls by about 47 percent, and the reinforcement in the critical zone was also inadequately anchored. A corrected analysis predicted failure at 62 meters [@jakobsenRosendahl1994] [@selbyVecchioCollins1997]. Arnold summarizes both accounts [@arnoldDisasters].

Here we have to look past the arithmetic to the model itself. The reported problem was that the discretization didn't resolve the stresses near a corner of the structure. A finite element calculation approximates a physical structure with a mesh and computes stresses within that model. Correctly rounding every operation would help bound the error in solving the chosen discrete problem, but it wouldn't tell you whether the mesh captured the local stress concentration. That takes evidence about the modelling assumptions and the discretization, on top of the arithmetic.

## Missing table entries: the Pentium FDIV bug, 1994

Thomas Nicely, a mathematician at Lynchburg College, was computing sums of reciprocals of twin primes. He noticed inconsistent results on his new Pentium in June 1994 and reported them to Intel on 24 October. Coe, Mathisen, Moler, and Pratt describe the discovery and its consequences [@coePentium1995]. The Pentium divided with a radix-4 SRT algorithm, a form of long division that produces two quotient bits per step. It picks each quotient digit from a lookup table indexed by a few leading bits of the partial remainder and the divisor. That table should have had 1066 populated cells, and five cells whose value was $+2$ were missing. Divisions that hit them were off by a relative error of up to about $6 \times 10^{-5}$, in the fourth or fifth significant digit, and usually by far less [@coePentium1995] [@edelman1997]. In the canonical example, $4195835 / 3145727$ is $1.333820449136241002\ldots$, and the flawed chips returned $1.333739068902037589$.

Intel's 1994 annual report [@intelAnnualReport1994] records a 475 million dollar pretax charge for replacing the processors. We can compute that quotient with the library and compare its digits with the exact fraction. Correctly rounded to binary64, it agrees with the exact quotient to seventeen significant digits:

```lean
#eval (4195835 : Binary64) / 3145727
-- 1.333820449136241

#eval (6006993277709123 * 10 ^ 18) / 4503599627370496
-- 1333820449136241093

#eval (4195835 * 10 ^ 18) / 3145727
-- 1333820449136241002
```

The second and third evaluations print the first nineteen digits of the rounded and exact quotient using integer arithmetic, so the display doesn't add another floating-point conversion. They agree through the seventeenth. [[FloatLib.Floats.ExecFloat.Proof.div_eq_spec]] covers every pair of stored operands, including exceptional cases. Under finite-input, nonzero-divisor, and finite-result hypotheses, the real-valued theorem [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_div_eq_roundAt]] identifies the rounded quotient. [Chapter 06](#/chapter/the-numerical-models) explains that connection.

A proof about an implementation also has to account for the quotient bits the algorithm generates. FloatLib's [finite binary64 divider](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/Word/Full/Division/Proof.lean) uses a restoring `UInt64` loop, a simpler recurrence than the Pentium's SRT digit selection. A restoring loop keeps an integer quotient and an exact remainder. For a small instance of the recurrence, divide 13 by 7, starting with quotient 1 and remainder 6. After $j$ binary digits have been generated, the relation is

$$
  13\cdot 2^j = 7q_j + r_j, \qquad 0 \le r_j < 7.
$$

Doubling both sides makes room for the next quotient bit. If the doubled remainder is at least 7, the loop subtracts 7 and sets that bit to one, and otherwise the bit is zero:

| Digits generated | Scaled numerator | Quotient | Remainder |
| --- | ---: | ---: | ---: |
| 0 | 13 | 1 | 6 |
| 1 | 26 | 3 | 5 |
| 2 | 52 | 7 | 3 |
| 3 | 104 | 14 | 6 |

At three fractional bits, the exact quotient is $(14+6/7)\cdot2^{-3}$. The remainder is more than half the divisor, so nearest rounding increments 14 to 15 and returns $15/8$. A remainder below half would keep the quotient, and an exact half would look at its parity. The binary64 loop runs the same recurrence with enough digits for its significand, and its proof also needs bounds showing that the doubled quotient and remainder fit in the machine words. The refinement proof covers both the finite-word calculation and the calls the partial kernel declines. For those calls the total dispatcher supplies a proved fallback.

If a divider returns a wrong quotient for even one input pair, it can't satisfy this equality with a correct reference. So a proof for an optimized loop or table has to cover every returned result, including inputs that exercise rarely used branches. Through the public refinement equation, a caller can use that agreement without naming the selected kernel, and [Chapter 05](#/chapter/why-execution-and-proofs-are-separate) follows how a local algorithm proof becomes a theorem about the public operation.

All of these equations are about Lean definitions. Running the software also relies on the compiler and runtime implementing integer and bit-vector operations correctly. The certified software divider uses integer arithmetic, while optional calls to the host floating-point divider live in the [unchecked host-arithmetic module](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/NativeFPU/Unchecked.lean). [Chapter 19](#/chapter/external-validation) compares their results with the software model. Those comparisons can reveal disagreements, but the software proof says nothing about whether the processor's divider is correct.

## A narrowing conversion: Ariane 5, flight 501, 1996

Ariane 5's maiden flight lifted off from Kourou on 4 June 1996. On 19 July 1996 the inquiry board chaired by Jacques-Louis Lions reported [@lions1996] that the failure "was caused by the complete loss of guidance and attitude information 37 seconds after start of the main engine ignition sequence (30 seconds after lift-off)". The launcher swung to an angle of attack above 20 degrees, the boosters tore off, and the self-destruct fired about 39 seconds after H0. H0 is the report's zero, the moment the launch sequence was initiated.

What failed was a conversion from floating point to a bounded integer. The board wrote that the inertial reference system's software exception "was caused during execution of a data conversion from 64-bit floating point to 16-bit signed integer value. The floating-point number which was converted had a value greater than what could be represented by a 16-bit signed integer. This resulted in an Operand Error."

The horizontal bias variable BH fit in binary64 but exceeded its destination's range. That destination was a 16-bit two's complement integer, whose largest value is 32767. In IEEE 754 terms this is the invalid-operation case of conversion to an integer format, clause 5.8 of [@ieee754_2019]. Rounding played no part in it. The board found that "the data conversion instructions (in Ada code) were not protected from causing an Operand Error, although other conversions of comparable variables in the same place in the code were protected".

So the handler did what it was designed to do for a hardware fault and shut the unit down. The backup unit, running the same software on the same data, had shut itself down during the previous 72 millisecond data cycle, for the same reason.

Leaving this conversion unprotected rested on a range assumption. With a processor workload ceiling of 80 percent, checks were omitted for variables judged "either physically limited or that there was a large margin of safety, a reasoning which in the case of the variable BH turned out to be faulty". The computation belonged to an alignment function, meaningful only before lift-off, that kept running for about 40 seconds of flight for Ariane 4's sake. But Ariane 5's early trajectory "results in considerably higher horizontal velocity values", and the equipment-level tests "did not specifically include the Ariane 5 trajectory data". So the bound on BH was an assumption inherited from another rocket. The board recommended: "Identify all implicit assumptions made by the code and its justification documents on the values of quantities provided by the equipment."

In FloatLib a [16-bit signed destination](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Numerics/Representations/FixedInt/Core.lean) is [[FloatLib.Numerics.Representations.FixedInt]] at width 16, and the decidable proposition [[FloatLib.Numerics.Representations.FixedInt.InRange]] expresses its representable range. The board didn't publish the value BH reached, so we'll use 40000. It's an illustrative input above 32767 and doesn't reconstruct the flight data. The first two evaluations show that it's out of range and that storing its low sixteen bits wraps it to $-25536$. The rest convert a binary64 value to the same sixteen-bit integers, represented as a bounded fixed-point grid with no fraction digits. Only the overflow policy changes between the three casts.

```lean
#eval decide (FixedInt.InRange 16 40000)
-- false

#eval (FixedInt.ofInt 40000 : FixedInt 16).toInt
-- -25536

/-- Sixteen-bit two's complement integers, seen as a fixed-point grid with no fraction digits. -/
abbrev Int16Grid := ExecFloat.BoundedFixedPoint binaryRadix 0 16

open FloatLib.Floats.ExecFloat.BoundedFixedPoint (OverflowPolicy)

def horizontalBias : Binary64 := 40000

#eval (ExecFloat.cast (target := Int16Grid) horizontalBias).map
  ExecFloat.BoundedFixedPoint.coefficient
-- FloatLib.Floats.ExecFloat.ConversionOutcome.failure (FloatLib.Floats.ExecFloat.ConversionFailure.outOfRange)

#eval (horizontalBias.cast (target := Int16Grid) (context := OverflowPolicy.wrap)).value?.map
  ExecFloat.BoundedFixedPoint.coefficient
-- some (-25536)

#eval (horizontalBias.cast (target := Int16Grid) (context := OverflowPolicy.saturate)).value?.map
  ExecFloat.BoundedFixedPoint.coefficient
-- some 32767
```

By default the cast returns `outOfRange` as an ordinary result, so the caller gets to handle the failed conversion. If you ask for them, the alternatives wrap to $-25536$ or saturate to $32767$. The full outcomes also mark `overflow` and `inexact`, with `wrapped` or `saturated` identifying the selected policy, and the last two evaluations show only their returned values. Neither alternative preserves the original value, so whether one is useful depends on the application.

Wrapping follows from the bit interpretation. Sixteen bits store a residue modulo $2^{16} = 65536$. The residue 40000 has its top bit set, so reading it as a signed two's-complement integer subtracts 65536 and gives $40000 - 65536 = -25536$. Saturation returns the upper endpoint instead and loses $40000 - 32767 = 7233$. Both are well-defined arithmetic operations, but each replaces a positive measurement with a different value. Because the status reports the selected policy, the caller can tell that replacement apart from a successful value-preserving conversion.

For a 16-bit store, the round-trip theorem `toInt_ofInt_eq_self` assumes that the value fits:

```lean
example (value : Int) (h : FixedInt.InRange 16 value) :
    (FixedInt.ofInt value : FixedInt 16).toInt = value :=
  FixedInt.toInt_ofInt_eq_self (by decide) h
```

In the [integer interpretation proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Numerics/Representations/FixedInt/Semantics/Basic.lean), the `InRange 16 value` hypothesis is the condition under which storing and reading the integer gives it back unchanged.

Proving this theorem once doesn't establish `InRange 16 BH` for a particular trajectory. That takes evidence about the values the guidance system can produce, and a move from Ariane 4 to Ariane 5 means revisiting that evidence. The division theorem above had the same split. Its arithmetic proof assumes finite inputs and a nonzero divisor, and the application has to show that its inputs meet those conditions.

The alignment output was unused after lift-off, but an exception in that unused calculation could still shut down the reference unit. So choosing a conversion policy also means tracing how the surrounding program handles the result. A returned failure, a wrapped value, and a saturated value each need the right response from the caller.

<a id="sources-and-definitions"></a>

## Proofs of hardware and software arithmetic

The FDIV failure showed why a division algorithm had to meet its specification on every input. The hardware verification work that followed included Moore, Lynch, and Kaufmann's proof of AMD5K86 division microcode in ACL2 in 1998 [@mooreLynchKaufmann1998], and Russinoff's proofs for AMD-K7 multiplication, division, and square root came the same year [@russinoff1998]. In 1999 Harrison built a machine-checked theory of floating point in HOL Light [@harrison1999], and Intel then used it for its own algorithms.

Boldo and Melquiond's Coq library Flocq [@boldoMelquiond2011] organizes floating point around a rounded-real model. A float is a real number on a grid determined by a radix and an exponent function, and rounding maps a real number onto that grid. That keeps the properties of the represented values apart from the details of how a machine stores them. Theorems about ulps, error bounds, and Sterbenz subtraction can be stated once for a family of grids, then applied to a particular format by proving that it meets the hypotheses.

FloatLib's rounded-real layer follows this organization in Lean, with its grid definitions and proofs in [chapter 07](#/chapter/the-mathematics-of-rounding). [Chapter 17](#/chapter/performance) compares its execution cost with an independent proved implementation extracted from Flocq. That comparison matches binary precision and exponent bounds and checks the complete input and output values, and [Chapter 19](#/chapter/external-validation/binary-arithmetic-with-flocq-and-mpfr) describes those numerical checks.

## The 2008 and 2019 revisions

The 1985 standard was binary only. IEEE 854 in 1987 [@ieee854_1987] restated the rules for radix 2 or 10 without fixing any bit layout, and the two standards were merged in IEEE 754-2008. That revision added decimal32, decimal64, and decimal128, with two competing significand encodings, IBM's densely packed decimal and Intel's binary integer decimal. It added binary16 as an interchange format and made fused multiply-add a required operation. It also introduced `minNum` and `maxNum`, and a ties-to-away rounding mode required only for decimal arithmetic. IEEE 754-2019 [@ieee754_2019] was a smaller revision. It replaced `minNum` and `maxNum` with four operations, `minimum`, `maximum`, `minimumNumber`, and `maximumNumber`, which distinguish NaN-propagating behaviour from a preference for numerical operands. The revision also recommended augmented operations that return the exact rounding error alongside the result, and it revised other edge cases.

Decimal arithmetic makes a familiar distinction visible. On a grid of hundredths, ten cents plus twenty cents is exactly thirty cents, because the integer coefficients add as $10+20=30$. That sum denotes $3/10$, a rational that binary32 can't represent and rounds to $5033165 \cdot 2^{-24}$. A fixed decimal scale works when the application knows its unit, and decimal floating point lets the scale change with an exponent. Either one still needs a rounding rule for results between grid points. [The decimal discussion](#/chapter/decimal-arithmetic/encoding-the-complete-datum) develops the two encodings and explains why one numerical value can have several decimal representations.

## Low-precision formats for machine learning

Binary64 became common in scientific computing and binary32 in graphics, and then deep learning revived interest in narrower formats. A gradient estimated from a random mini-batch is already noisy, and that can make reduced precision acceptable. Smaller operands also cut storage and data movement. How much precision is usable still depends on the model and the training procedure. Micikevicius and colleagues demonstrated mixed-precision training in 2018 [@micikevicius2018mixed]. They used binary16 storage with a binary32 master copy of the weights, and loss scaling to protect small gradients. The two techniques address different losses of information. Master weights retain updates too small for binary16, while scaling helps keep gradients within its usable exponent range. [Chapter 11](#/chapter/low-precision-formats-for-machine-learning) describes the format limits.

[Google's TPU v2 and v3 used bfloat16](https://cloud.google.com/blog/products/ai-machine-learning/bfloat16-the-secret-to-high-performance-on-cloud-tpus), which keeps binary32's 8 exponent bits but stores only 7 fraction bits, so its 8-bit significand provides about two decimal digits. Within a 16-bit word, that puts more bits into range and fewer into precision than binary16 does.

At one, binary16 has spacing $2^{-10}$ while bfloat16 has spacing $2^{-7}$, eight times larger. So the exact value $1+2^{-8}$, four binary16 steps above one, is representable in binary16, but in bfloat16 it lands on a midpoint, where nearest-even returns one. The extra exponent bits buy bfloat16 a wider range. Binary16's smallest positive normal is $2^{-14}$, while bfloat16's is $2^{-126}$. So equal storage width doesn't make the two formats interchangeable, and a computation can need the finer steps of one and the smaller normal magnitudes of the other.

A binary32 master weight keeps small updates by accumulating them before converting back to the storage format. A binary16 weight at one can't retain an increment of $2^{-12}$, for example, because each update rounded on its own returns one. In binary32, four such increments accumulate exactly to $2^{-10}$, a full binary16 step, and that survives the next conversion.

Loss scaling works at a different point in the calculation. Multiplying a gradient of $2^{-20}$ by $2^{10}$ moves it to $2^{-10}$, within binary16's normal range, where more significant bits are available. The scale has to go in before the low-precision operations whose small outputs it's meant to protect, and it also has to be accounted for when the update is applied. Make it too large and you can get overflow. These small calculations illustrate the two mechanisms, but they don't establish an error bound for a training run.

Micikevicius and colleagues proposed the eight-bit E5M2 and E4M3 formats in 2022 [@micikevicius2022fp8]. NVIDIA's H100 shipped tensor cores for both that year, and the Open Compute Project's OFP8 specification standardized them in 2023 [@ocpOfp8]. They differ in exceptional-value encoding as well as precision. E5M2 keeps IEEE conventions, including infinities and multiple NaN codes, while E4M3FN has no infinity and one NaN pattern per sign. It uses most of the all-ones exponent class for finite values, which extends its finite range past what the same field widths would give with the IEEE reservation. With only 256 words available, changing one reserved code class changes an appreciable part of the format.

ONNX's float8 definitions [@onnxFloat8] include FNUZ variants that remove negative zero, reuse its word as the sole NaN, and shift the bias by one. The OCP Microscaling specification, also from 2023 [@ocpMx], groups narrow elements into blocks with a shared eight-bit power-of-two scale. Its E8M0 scale has no sign, fraction, or zero. The FP8 elements reuse OFP8 formats, and the FP6 and FP4 formats E2M3, E3M2, and E2M1 make every word finite, with no NaN. Each element's decoded value is then multiplied by the block scale, so the element word alone doesn't determine its value in the block.

These conventions change what the same word denotes. The byte `0x7c` is $+\infty$ in E5M2 and 384 in E4M3FN, which is quite a difference for one byte :) [Chapter 11](#/chapter/low-precision-formats-for-machine-learning) decodes both and develops the format-specific arithmetic.

Overflow policy is its own choice. In FloatLib, an E4M3FN result too large to round back to 448 can become NaN or saturate at 448, depending on the selected policy, and the encoding stays the same. A theorem about one policy doesn't establish the behaviour of another, and [chapter 04](#/chapter/why-verifying-floating-point-is-hard/overflow-policy-and-the-sign-of-zero) compares them on the same input.

A shared scale changes the interpretation of every element in a block. E8M0 code $c$, from 0 through 254, denotes $2^{c-127}$, and code 255 is NaN. So code 128 supplies a scale of two, and elements that decode to 1.5 and $-0.5$ denote 3 and $-1$ in the block. Change the scale code to 129 and both double again. Multiplying by a power of two changes a dyadic's exponent without discarding significand bits, so this joint decoding is exact.

Choosing the codes and scale to approximate an input block is a different conversion problem, which [Chapter 11](#/chapter/low-precision-formats-for-machine-learning) develops.

A numerical grid doesn't have to be a hardware storage format, either. TF32 computations use binary32 inputs with reduced significand precision. Its eight exponent and ten fraction bits describe the rounded values, but they don't imply a 19-bit hardware word of its own.

## Posits and the quire

Posits allocate bits differently again. In 2017 Gustafson and Yonemoto proposed [@gustafsonYonemoto2017] a variable-length, run-length-coded regime field. Values near 1 need a short regime that leaves more bits for the fraction, and extreme magnitudes need a longer regime and leave fewer fraction bits. Posits have one zero and one code for NaR, which stands for not a real, and they have no subnormal encoding of their own. A companion fixed-point accumulator, the quire, can accumulate products exactly until its coefficient range is exhausted. The 2017 family was written `posit<n, es>`. The Posit Standard of 2022 [@positStandard2022] fixed the exponent parameter at two bits, so a standard posit is identified by total width alone.

We can measure the precision difference near one third. Rounding it to a standard 32-bit posit gives $178956971\cdot2^{-29}$, while binary32 gives $11184811\cdot2^{-25}$. Their errors are

$$
  \frac{178956971}{2^{29}} - \frac13 = \frac{1}{3\cdot2^{29}},
  \qquad
  \frac{11184811}{2^{25}} - \frac13 = \frac{1}{3\cdot2^{25}}.
$$

Both quotients lie above one third. Here the posit error is sixteen times smaller, which corresponds to four extra fraction bits at this magnitude. That advantage comes from how the format distributes its fixed bit budget, since lengthening the regime for very large or very small values reduces the space left for those fraction bits. A comparison on one third tells you about precision near one third, and it doesn't settle which format suits a calculation whose intermediates span a wider range. De Dinechin, Forget, Muller, and Uguen examine this distribution of precision and its hardware costs [@deDinechinPosits2019]. [Chapter 13](#/chapter/posits-and-the-quire) develops the encoding and the quire's capacity conditions, and [Chapter 19](#/chapter/external-validation) compares the arithmetic with an independent implementation.

## P3109 formats

The IEEE P3109 working group's interim report [@p3109InterimReport] proposes a parameterized family for low-precision arithmetic, but it isn't an approved IEEE standard. Its four parameters are total width $K$, precision $P$ including the implicit bit, signedness, and a domain that is finite or extended with infinities. A signed P3109 format places its single NaN at the midpoint of the code space, in the word that would otherwise be negative zero. An extended format places infinities at the endpoints of its finite ranges and doesn't reserve an all-ones exponent class. Unsigned formats use the sign bit for magnitude. The report also specifies nine rounding modes, including round-to-odd and three stochastic variants, and three saturation behaviours.

A signed eight-bit extended format with precision four, for example, has its NaN at code 128 and its infinities at 127 and 255. It keeps the familiar division into sign, exponent, and fraction, but those placements differ from an IEEE exponent-class reservation. [Chapter 12](#/chapter/p3109) develops the encoding, rounding and saturation rules, and FloatLib's proofs against the interim report.

The working group's value tables give an independent check of how a word is decoded, and [Chapter 19](#/chapter/external-validation) describes those comparisons. They check the interpretation of the encoding. Arithmetic, exception behaviour, and accelerator hardware aren't part of what they test.