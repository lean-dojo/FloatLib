---
number: "10"
slug: elementary-functions
title: "Elementary functions"
summary: "Exact root comparisons and rational enclosures can determine a rounded elementary function, and the approximation calls and partial certified calls come with different guarantees."
phases: [binary-arithmetic, status-and-directed, elementary-functions]
---

A floating-point function must choose a stored value for an exact expression that may be irrational. For $\sqrt{2}$, we can decide between two neighbouring candidates by squaring their midpoint and comparing it with 2. That comparison is exact, even though the root is irrational. For $\exp x$ or $\log x$, we instead enclose the exact answer and refine the bounds until both endpoints round to the same value. This search can run out of budget before it settles.

FloatLib's algebraic operations have real-rounding theorems, and its certified enclosure searches prove their answers when they succeed. The separate value-only transcendental approximations have no general accuracy proof.

## Powers and roots with one rounding

Rounding an intermediate value can change a calculation even when the final result fits. Binary32
can store a number near $10^{20}$, and it can store the hypotenuse of that number with itself, but
it can't store the square. So `sqrt (x * x + y * y)` overflows before it ever reaches the square
root, while `hypot` forms the exact sum of squares and rounds only the root. These [algebraic
operations](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/BinaryInterchange/Algebraic)
use the same [binary descriptors and storage choices](#/chapter/ieee-binary-formats/custom-widths)
as ordinary arithmetic:

| Operation | Exact expression before nearest-even rounding |
| --- | --- |
| `square x` | $x^2$ |
| `rsqrt x` | $1/\sqrt{x}$ |
| `hypot x y` | $\sqrt{x^2+y^2}$ |
| `powInt x n` | $x^n$, with an integer exponent |
| `rootN x n` | The signed $n$th root; a negative degree takes its reciprocal |

```lean standalone
import FloatLib

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

#eval ExecFloat.Binary.toRat? (ExecFloat.Binary.square (3 : Binary32))
-- some 9
#eval ExecFloat.Binary.toRat? (ExecFloat.Binary.hypot (3 : Binary32) 4)
-- some 5
#eval ExecFloat.Binary.toRat? (ExecFloat.Binary.rsqrt (4 : Binary32))
-- some (1 / 2)
#eval ExecFloat.Binary.toRat? (ExecFloat.Binary.powInt (2 : Binary32) (-3))
-- some (1 / 8)
#eval ExecFloat.Binary.toRat? (ExecFloat.Binary.rootN (-8 : Binary32) 3)
-- some (-2)

def largeForHypot : Binary32 := 100000000000000000000
#eval Model.isInf (ExecFloat.Binary.toModel (largeForHypot * largeForHypot))
-- true
#eval ExecFloat.Binary.isFinite (ExecFloat.Binary.hypot largeForHypot largeForHypot)
-- true
```

Squaring reuses the multiplication kernels, and the word paths decode the operand only once. In
`hypot` both squared significands are nonnegative integers, so shifts and one integer addition give
their exact sum, and that's why the large example above stays finite. Integer powers use exact
rational arithmetic. For an $n$th root, the radicand's binary magnitude fixes the output exponent.
After scaling the radicand to a rational $a/b$, an integer-root kernel computes the significand $c$
with a proof of $c^n b \le a < (c+1)^n b$. That pins down the two neighbouring results, and an exact
midpoint comparison picks the nearest-even one. Degree two uses integer square root, and higher
degrees use Newton iteration from a power-of-two upper bound. In the [integer-root
theorem](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/IntegerRoot/Proof.lean) we
prove the kernel equal to Mathlib's `Nat.nthRoot` for every input and degree. Binary and decimal
roots share the kernel, each with its own format-specific scaling and final rounding. Precision and
exponent range come from the descriptor, so the same proofs apply at standard and custom widths.

The [real-value
theorems](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/Algebraic/Proof.lean)
say that a finite result is the rounding of the corresponding real expression. They include
[[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_hypot_eq_roundAt]] and
[[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_rootN_eq_roundAt]], and they assume a
conventional IEEE descriptor and finite operands in its real domain. For `powInt` and `rootN` the
theorems need a nonzero base, and `rootN` also needs a nonzero degree, odd when the base is
negative. For `rsqrt` the theorem needs a positive input. Their configured versions cover the calls
above as written, and `square_eq_mul` also proves that squaring gives the complete encoded
multiplication result. Exceptional inputs have their own rules. A root of degree zero, or an
even-degree root of a negative nonzero value, returns NaN. Negative degrees give reciprocal roots,
including the signed infinities at zero. In `hypot` an infinity beats a quiet NaN, while a signaling
NaN is quieted and propagated.

## Calling the approximation kernels

Import the optional [binary transcendental module](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/Transcendentals.lean) and every `ExecFloat.Binary` type gets a value-only approximation API for `exp`, `log`, `sin`, `cos`, `sinCos`, `sinh`, `cosh`, and `tanh`. The module also adds the power `pow`, which lifts `Model.pow`, and `MathFunctions` instances, so generic code can call these functions next to the certified `sqrt` and `abs` and the constant `pi`. Each function decodes its input, calls the descriptor-generic model kernel and packs the result back into the configured word. We haven't proved a general accuracy bound for these value-only kernels. `Model.pow` for an IEEE descriptor is the one exception. With a finite nonzero base, a finite integral exponent and a finite result, [[FloatLib.Floats.Formats.BinaryInterchange.Model.Power.toReal_pow_of_eq_intCast]] proves that the decoded result is the nearest-even rounding of the exact power.

For a finite positive base and any other finite exponent, `pow` first runs the certified enclosure search [[FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals.Certified.pow]]. It encloses $y \log x$ on a first grid, uses that enclosure to settle underflow and reject overflow, and reduces the argument by $\log 2$. Then it refines the scaled exponential enclosure, where the first attempt reuses the first enclosure of $y \log x$ and each finer grid computes a new one. The search accepts a result only when both endpoints round to the same value. Whenever the search settles, [[FloatLib.Floats.Formats.BinaryInterchange.Model.Power.pow_spec_of_certified]] proves the result finite and correctly rounded. Only overflow, most exact results on a rounding boundary, and a search that runs out of attempts fall back to `exp (y * log x)`. If you'd rather get the failure, `pow x y (certify := true)` runs the search alone and returns it. The search adds work: on mixed binary64 operands `pow` went from 36.6 to 42.8 µs. When every input settles through the search it gets up to 1.9 times slower, and an exact rounding boundary takes about 3.5 ms before its fallback.

Internally the kernels round to nearest-even, take no rounding direction and return no status flags. For point evaluation in a rounding direction you pass in, the separate test workspace has an Arb adapter that uses python-flint as an external reference, as [chapter 19](#/chapter/external-validation) describes. The call below needs the named import to get the software kernels, because `import FloatLib` on its own gives you the `MathFunctions` class and its host `Float` instance, but it doesn't install these binary functions:

```lean standalone
import FloatLib
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

#eval ExecFloat.Binary.exp (1 : Binary32)
-- 2.7182817
#eval ExecFloat.Binary.toBits32 (ExecFloat.Binary.exp (1 : Binary32))
-- 1076754516
#eval ExecFloat.Binary.log (ExecFloat.Binary.exp (1 : Binary32))
-- 0.99999994
#eval ExecFloat.Binary.exp (100 : Binary32)
-- inf

example (x : Binary32) :
    ExecFloat.Binary.toModel (ExecFloat.Binary.exp x) = Model.exp (ExecFloat.Binary.toModel x) :=
  ExecFloat.Binary.toModel_exp x
```

That result, $2850325 \cdot 2^{-20} = 2.71828174591\ldots$ or word `0x402df854`, is the binary32 value nearest to $e$. Take the logarithm of that word and you get $1 - 2^{-24}$ instead of $1$ :) `toModel_exp` connects the configured binary function to the model kernel. Decode the configured call and you get `Model.exp` of the decoded input. Each of the other functions has the same lemma, so a proof about a model kernel carries over to its configured function. That equality is between two implementations. It says nothing about how either output relates to the real exponential. Our [posit functions](#/chapter/posits-and-the-quire/exponentials-and-logarithms) use different algorithms, and those come with proved real-rounding equations.

The sine and cosine kernels reduce the argument modulo $\pi/2$ by the method of Payne and Hanek. Say we write $x = m \cdot 2^e$. Bits of $2/\pi$ of weight $2^{2-e}$ and above only contribute whole multiples of four quarter turns to $2x/\pi$, so the kernel multiplies $m$ by just a window of a few hundred bits of $2/\pi$ below that weight. That window comes from a cache of proved bounds of $2/\pi$, held at 64, 128, 256 and more fractional bits and computed once on first use. [[FloatLib.Numerics.Enclosure.ArgumentReduction.reduceWindow_spec]] bounds the error of the computed remainder by $2m$ units of its last place, and the reduction keeps doubling its window until that error is below $2^{-(p+32)}$ of the remainder for a destination precision $p$. Then [[FloatLib.Numerics.Enclosure.ArgumentReduction.QuarterTurns.Reduces.exists_sin_cos_eq_rotate]] gives the sine and cosine of $x$ from those of the reduced argument and the quadrant. Both the quadrant and the sign of $x$ are applied to the exact Taylor sums before the single rounding.

For nonzero dyadic $x$, a wide enough window exists because $2x/\pi$ is irrational, and [[FloatLib.Numerics.Enclosure.ArgumentReduction.exists_accepting_window]] proves it. Each call tries the first window and at most four doublings, checking each one for acceptance as it goes. If none of them is accepted, it gives the format's invalid result. It reads at most $2^{21}$ bits of $2/\pi$ and only doubles its window within them. In a format with at most 524,258 fraction bits, the first window lies within those bits for every finite argument below $2^{2^{20}}$, which covers every exponent field of at most 21 bits with the conventional bias. In wider exponent fields the largest arguments give the format's invalid result.

We haven't proved that one of the permitted windows is accepted for these arguments. It's checked when the kernel runs, and it has succeeded on every input we tested. Every finite sine and cosine argument in the MPFR gate described below was accepted, since each of the gate's cases matches MPFR. For each format, the regression fixtures include the two inputs of the hard-case corpus closest to a multiple of $\pi/2$. For binary64 that's $6381956970095103 \cdot 2^{797}$, at a distance of $2^{-60.9}$, and these inputs are accepted at their first window. Even the largest finite binary128 and binary256 values reduce to a finite sine and cosine.

The same cache supplies $\log 2$ to the exponential and the logarithm. Its constants come from binary splitting of Machin's formula and of a series for $\log 2$, and the theorems [[FloatLib.Numerics.Enclosure.Constants.piLevel_twoOverPi_spec]], `piLevel_halfPi_spec`, and [[FloatLib.Numerics.Enclosure.Constants.ln2Fixed_spec]] prove each one within two units of its last place at every precision. [[FloatLib.Floats.Formats.BinaryInterchange.Model.pi]] rounds an enclosure from the cache, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_pi]] proves it correctly rounded in every IEEE format. For the approximation kernels we measure accuracy against MPFR instead. In the [MPFR gate](#/chapter/external-validation/elementary-functions-against-mpfr) we compare `exp`, `log`, `sin`, `cos`, `sinh`, `cosh`, `tanh`, `pow`, and `pi` with MPFR's correctly rounded results in six formats. Every case in its three tiers matches, and its list of known failures is empty. The constants used to be computed on every call, and caching them per format took binary64 `exp` from 366 to 27 µs and binary128 `exp` from 1.8 ms to 95 µs. The [performance chapter](#/chapter/performance/speed-work-in-october-2026) has the sine timings.

## Certified exponential and logarithm

Certification is an option on the functions themselves. With `certify := true`, `exp`, `log`, and
`pow` turn rational enclosures into rounding decisions you can run: they refine the bounds until
both endpoints round to the same finite encoding, then return `.ok result`. The success theorems
prove that this result is finite and equals nearest-even rounding of the corresponding real
function. A call that can't certify returns `.error` with the reason. It never falls back to the
approximation. `expMinus1` and `logPlus1` exist only in this certified form. The enclosure engine
stores each endpoint as an integer multiple of $2^{-w}$. When it evaluates a polynomial, it rounds
every intermediate product and division outward on this binary grid. Adding a proved remainder bound
then turns the result into an enclosure of the real function. That way the polynomial avoids the
growing denominators of exact rational evaluation. Argument reduction and scalar factors still use
rationals, and the final grid endpoints are converted to rationals for the destination rounder.

For the logarithm, setting $t=(x-1)/(x+1)$ gives the odd series $\log x=2(t+t^3/3+t^5/5+\cdots)$.
Each term gains a factor of $t^2$ over the one before, so short polynomials use a Horner loop in
$t^2$. Longer ones share a table of powers and group the terms into blocks. With $n$ terms, blocks
of about $\sqrt n$ cut the number of full-width multiplications from order $n$ to order $\sqrt n$.
Each coefficient still needs a scalar division. This is *rectangular splitting*, as described in
[Johansson's account of elementary-function implementation](https://arxiv.org/abs/1410.7176), and we
like it a lot. A [containment
proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Numerics/Enclosure/Elementary/BinaryGridProof.lean)
combines Mathlib's series bound with the outward-rounded polynomial and remainder. For the
exponential, the engine reduces the argument, sums a Taylor series, and then squares repeatedly to
restore the original scale. More reduction can make a shorter polynomial enough, but you pay for it
in squarings. The engine picks this extra reduction from the degree, the working width and the input
magnitude, and it adds fractional bits before squaring. An argument that is already small needs less
reduction.

Refinement starts from a working width that depends on the input's scale. A small `expMinus1` result
needs extra fractional bits to survive subtracting one, and `logPlus1` needs them to hold on to a
small increment. After that it adjusts the degree and the width independently. A failed check makes
it try twice the degree and one extra working bit. If the interval shrinks by at most a factor of
four, the following attempt keeps the degree and doubles the working width. Here's a case where more
terms don't help. In binary64, $\exp(2^{-53})$ lies only about $2^{-107}$ above the rounding
midpoint $1+2^{-53}$. Once the series remainder is small, more terms can't resolve that decision on
a coarse grid, but increasing the working width reduces the rounding error that the enclosure
calculation itself introduces. Containment is proved at every width, and acceptance still requires
both endpoints to round to the same finite encoding. Binary and decimal certified operations share
this refinement engine. In the code below, the budget allows the first call twelve
enclosure attempts and the third none.

```lean standalone
import FloatLib
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

#eval (ExecFloat.Binary.exp (1 : Binary32) (certify := true)
  (budget := { initialDegree := 8, maxSteps := 12 })).map ExecFloat.Binary.toBits32
-- Except.ok 1076754516

#eval (ExecFloat.Binary.log (2 : Binary32) (certify := true)).map ExecFloat.Binary.toBits32
-- Except.ok 1060205080

#eval (ExecFloat.Binary.exp (1 : Binary32) (certify := true)
  (budget := { maxSteps := 0 })).map ExecFloat.Binary.toBits32
-- Except.error (FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals.Certified.Failure.inconclusive)

#eval (ExecFloat.Binary.log (-1 : Binary32) (certify := true)).map ExecFloat.Binary.toBits32
-- Except.error (FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals.Certified.Failure.domain)

example (x y : Binary32) (budget : Model.Transcendentals.Certified.Options)
    (h : ExecFloat.Binary.exp x (certify := true) (budget := budget) = Except.ok y) :
    ExecFloat.Binary.toReal y =
      Model.roundAt FloatFormat.binary32 (Real.exp (ExecFloat.Binary.toReal x)) :=
  ExecFloat.Binary.toReal_of_exp_eq_ok h
```

For the logarithm and power, `toReal_of_log_eq_ok` and `toReal_of_pow_eq_ok` take the same success
hypothesis. In the third evaluation even the valid input 1 comes back `inconclusive`, because no
refinement attempts are allowed :) By default the Taylor degree is 8, and there are at most 16
direct enclosure attempts, counting retries at higher working precision. `maxSteps` bounds those
attempts, **not total running time**, because the exponential's preliminary underflow and overflow
comparisons aren't counted against it. Simple rational bounds derived from the format's exponent
limits skip those comparisons when the argument is safely between the underflow and overflow
thresholds. Custom widths work if they use conventional IEEE encoding and bias. When a call returns
no result, the failure says why. Another encoding gives `unsupportedFormat`, and a NaN or an
infinity gives `nonfiniteInput`. A nonpositive logarithm argument or power base gives `domain`, and
a result beyond the largest finite value gives `range`. A search that didn't settle within its
budget gives `inconclusive`. An `inconclusive` result makes no claim about whether more refinement
would succeed, and the API does not promise success on every valid input. A successful call
certifies a finite rounded value and returns no IEEE status flags.

<details>
<summary>What the transcendental certificates state</summary>

A `RealEnclosure` proves bounds $l\le f(x)\le u$. If $l$ and $u$ round to the same destination value, monotonicity puts the rounded value of $f(x)$ there too. A `StableEnclosure` records this agreement, and `CertifiedRoundedResult.toReal_value_eq_roundAt` proves that the accepted stored result is correctly rounded. The [contract module](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Transcendentals/Contract.lean) supplies enclosure constructors for `exp`, `log`, `sinh`, `cosh`, `tanh`, `sin`, `cos`, and `sqrt`, and theorems for combining them. An `ApproximationCertificate` makes a claim about an entire kernel. On every finite input, the kernel returns a finite value within a given absolute error. `ApproximationCertificateOn` restricts this claim to a stated domain. `CorrectlyRoundedCertificateOn` requires correct rounding throughout its domain, for example positive logarithm inputs whose outputs remain finite. These certificate types state proof obligations. They do not supply a certificate for the value-only approximation kernels. `#float_info` therefore reports that framework as conditional. Applying a generic accuracy theorem still requires the corresponding kernel certificate.

</details>

## Keeping small differences

Near zero, evaluating `exp x - 1` or `log (1 + x)` as two floating-point operations can
lose the result before the final subtraction or logarithm. `expMinus1` subtracts one from
the rational enclosure before rounding, and `logPlus1` forms `1 + x` exactly before enclosing
its logarithm. At $x = 2^{-26}$ in binary32, the rounded sum $1 + x$ is already $1$,
but both stable functions round to $x$:

```lean standalone
import FloatLib
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals

open FloatLib.Floats
def tiny : Binary32 := 1 / 67108864

#eval (1 : Binary32) + tiny == 1
-- true
#eval (ExecFloat.Binary.expMinus1 tiny).map (· == tiny)
-- Except.ok true
#eval (ExecFloat.Binary.logPlus1 tiny).map (· == tiny)
-- Except.ok true
```

`toReal_of_expMinus1_eq_ok` and `toReal_of_logPlus1_eq_ok` connect these
results to `Real.exp x - 1` and `Real.log (1 + x)`. Both operations preserve either signed
zero. `logPlus1` requires $x > -1$ and otherwise fails with `domain`.

## Certified decimal functions

On the decimal side, the `Transcendentals.Certified` API uses the same binary-grid enclosures. It
rounds their rational endpoints into the decimal format, with a working width that follows the
decimal precision. Its optional import exposes `expMinus1` and `logPlus1` on the [decoded decimal
data](#/chapter/decimal-arithmetic/encoding-the-complete-datum). Give both functions the decimal32
input $10^{-9}$ and they keep the increment that would disappear if $1+x$ were rounded on its own:

```lean standalone
import FloatLib
import FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Certified.Proof
open FloatLib.Floats.Formats.DecimalInterchange

def tiny : Datum := .finite false 1 (-9)
#eval (Transcendentals.Certified.expMinus1 Format.decimal32 tiny).bind Datum.toRat?
-- some (1 / 1000000000)
#eval (Transcendentals.Certified.logPlus1 Format.decimal32 tiny).bind Datum.toRat?
-- some (1 / 1000000000)
#eval (Transcendentals.Certified.logPlus1 Format.decimal32
  (.finite true 1 0)).bind Datum.toRat?
-- none

example (x y : Datum) (options : Transcendentals.Certified.Options)
    (h : Transcendentals.Certified.logPlus1 Format.decimal32 x options = some y) :
    Transcendentals.toReal y = Transcendentals.roundAt Format.decimal32
      (Real.log (1 + Transcendentals.toReal x)) :=
  Transcendentals.Certified.toReal_of_logPlus1_eq_some h
```

A successful result is valid, finite and nearest-even rounded, as
[[FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Certified.toReal_of_logPlus1_eq_some]]
states for `logPlus1`. Both functions keep a valid zero's sign and quantum. The success theorems
work for arbitrary decimal layouts, including quantum ranges that exclude zero. Invalid or nonfinite
datums return `none`, and so do `logPlus1` inputs at or below $-1$, overflow and inconclusive
refinement. The options limit enclosure attempts, but the exact exponential comparisons that settle
the tail and overflow cases run outside that budget. Success certifies a finite result and supplies
no IEEE status flags.