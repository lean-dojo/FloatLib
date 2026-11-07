---
number: "10"
slug: elementary-functions
title: "Elementary functions"
summary: "How to compute square roots, exponentials, logarithms and sines with FloatLib, and how to choose between the approximate, certified and correctly rounded versions."
phases: [binary-arithmetic, status-and-directed, elementary-functions]
---

FloatLib provides square roots, powers, exponentials, logarithms and trigonometric functions. Their interfaces differ in the guarantees they provide: some kernels return approximations, certified searches return correctly rounded results when they succeed, and total correctly rounded operations prove that a result always exists. This chapter explains how to choose and use these interfaces.

Square root can be rounded by comparing the square of a candidate midpoint with the input. That comparison is exact even when the root is irrational. Exponential and logarithm use enclosures instead: a computation finds lower and upper bounds, then checks whether both round to the same format value. If they disagree, the search needs tighter bounds. A bounded search can stop before this condition is established.

## What are the three kinds of function?

First, some terms the table uses. *Correctly rounded* means the exact real answer rounded once. Nearest-even rounding takes the nearest representable number, or at a tie the one whose last bit is even, and MPFR is a library whose results are correctly rounded. A *descriptor* records a format's layout (exponent width, fraction width and bias), and an IEEE descriptor follows IEEE 754's encoding and usual bias. The namespace tells you which kind you're calling, and the kind decides what you can prove about the answer:

| Kind | Namespace | Functions | What you get |
| --- | --- | --- | --- |
| Approximate | `ExecFloat.Binary` | `exp`, `log`, `sin`, `cos`, `sinCos`, `sinh`, `cosh`, `tanh`, `pow` | A value, with no general accuracy proof (parts of `pow` are proved). We test all but `sinCos` against MPFR. |
| Certified | `ExecFloat.Binary.Certified` | `exp`, `log`, `pow`, `expMinus1`, `logPlus1` | `.ok` with a value proved finite and nearest-even rounded, or `.error` with the reason. A call can fail on a valid input. |
| Correctly rounded | `ExecFloat.Binary.CorrectlyRounded` | `exp`, `log`, `expMinus1`, `logPlus1`, `expMul` | A value every time. On an IEEE descriptor, for a finite input in the domain, it's proved to be the nearest-even rounding of the exact result, or the signed infinity once that result reaches the overflow threshold. |

So how do you choose? If tested numbers are enough, use the approximate functions, the only kind with sine and cosine. If you need a proof and can handle a failure, use the certified ones. If you need an answer every time, and a proof on IEEE formats, use the correctly rounded ones. Square roots and their relatives come first, because they need none of this.

## How to square, take roots and compute hypot

Say a right triangle has both short sides near $10^{20}$. Binary32, IEEE's 32-bit format, can store the sides and the long side, but not the square of either one, so the textbook formula `sqrt (x * x + y * y)` overflows before it ever reaches the square root. One rounding in the middle wrecks a calculation whose answer fits comfortably. FloatLib's `hypot`, short for hypotenuse, forms the exact sum of squares and rounds only the root, so for these sides its answer stays finite. Round once, at the end.

`hypot` and its relatives, the [algebraic operations](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/BinaryInterchange/Algebraic), built from arithmetic and roots alone, use the same [binary descriptors and storage choices](#/chapter/ieee-binary-formats/how-to-make-your-own-width) as ordinary arithmetic. We've proved that on an IEEE descriptor, a finite result from finite inputs is the exact answer, rounded once to nearest-even. Here's the exact expression for each operation:

| Operation | Exact expression before nearest-even rounding |
| --- | --- |
| `square x` | $x^2$ |
| `rsqrt x` | $1/\sqrt{x}$ |
| `hypot x y` | $\sqrt{x^2+y^2}$ |
| `powInt x n` | $x^n$, with an integer exponent |
| `rootN x n` | The signed $n$th root, or its reciprocal for a negative degree |

If you start with small whole numbers, `toRat?` shows each result as an exact fraction:

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

In the last example, direct multiplication overflows while `hypot` returns a finite result. Its computation uses the integer significands and exponents to form the exact sum of squares before rounding the root. More generally, a root computation scales the radicand to a rational $a/b$. The integer-root kernel computes a significand $c$ satisfying $c^n b\le a<(c+1)^n b$, and an exact midpoint comparison determines the nearest-even result. The [integer-root theorem](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/IntegerRoot/Proof.lean) proves agreement with Mathlib's `Nat.nthRoot` for every input and degree. Precision and exponent range are descriptor parameters, so the proofs also apply to custom widths.

### What is proved about these operations?

When you prove things about these operations, you'll want our [real-value theorems](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/Algebraic/Proof.lean), such as [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_hypot_eq_roundAt]] and [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_rootN_eq_roundAt]]. They say that a finite result is the rounding of the real expression. They assume a conventional IEEE descriptor and a finite result, which rules out the invalid cases and the poles (where the exact answer is infinite), so `hypot` needs nothing more. `powInt` and `rootN` need a finite base (zero included), and `rsqrt` needs a finite input with a clear sign bit. The configured versions, on the types you compute with, cover the calls above as written, and `square_eq_mul` proves that squaring gives the complete encoded multiplication result.

### What happens with NaN and infinity?

A root of degree zero, or an even-degree root of a negative nonzero value, is NaN (not a number). Negative degrees give reciprocal roots, including the signed infinities at zero. And in `hypot` an infinity beats a quiet NaN, the ordinary kind, while a signaling NaN, one meant to raise an alarm when used, is quieted and propagated.

## How to compute exp, log and sine

Now for the *transcendental* functions, such as $e^x$ and $\log x$, named because they transcend algebra: no finite formula of arithmetic and roots produces them. We'll start with the kind that promises the least. Import the optional [binary transcendental module](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/Transcendentals.lean) and every `ExecFloat.Binary` type gets value-only approximations (a number, with no claim about its accuracy) of `exp`, `log`, `sin`, `cos`, `sinCos`, `sinh`, `cosh` and `tanh`. It also gets a `pow` that lifts `Model.pow` (`Model` is FloatLib's bit-level reference for a format), and `MathFunctions` instances, which let generic code call them.

These kernels always round to nearest-even, take no rounding direction and return no status flags, IEEE's record of events such as overflow. They need the named import, because `import FloatLib` on its own gives you the `MathFunctions` class and its host `Float` instance but not these binary functions. Let's ask binary32 for $e$:

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

You get `2.7182817`, which is $2850325 \cdot 2^{-20} = 2.71828174591\ldots$, the binary32 value nearest to $e$, and `toBits32` shows its *word* (the raw bits read as a whole number), 1076754516 or `0x402df854`. Take the logarithm of that value and you get $1 - 2^{-24}$ instead of $1$. That happens to be correctly rounded, because the stored value is less than $e$. And $e^{100}$ is too big for binary32, so it prints `inf`.

The `example` at the end uses `toModel_exp`, which says the configured call decodes to `Model.exp` of the decoded input. Every function has this lemma, so model proofs carry over, but it relates two implementations, the configured call and the model, and says nothing about the real exponential. For that you need the [correctly rounded functions](#/chapter/elementary-functions/how-to-get-a-correctly-rounded-answer-every-time) below or our [posit functions](#/chapter/posits-and-the-quire/how-to-compute-exponentials-and-logarithms), which come with proved real-rounding equations.

**Note:** Inside `open scoped FloatLib.Floats.Formats.BinaryInterchange.CorrectlyRoundedMath`, the `exp` and `log` of the `MathFunctions` instances on an IEEE descriptor are the [correctly rounded functions](#/chapter/elementary-functions/how-to-get-a-correctly-rounded-answer-every-time), not the approximations.

### How to raise a number to a power

`pow x y` computes $x^y$. We haven't proved a general accuracy bound for the approximation kernels, with one exception. With a finite base, a finite integral exponent and a finite result, [[FloatLib.Floats.Formats.BinaryInterchange.Model.Power.toReal_pow_of_eq_intCast]] proves that `Model.pow` on an IEEE descriptor is the nearest-even rounding of the exact power.

For a finite positive base and any other finite exponent, `pow` first runs the certified search [[FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals.Certified.pow]], which we come back to below. Whenever it settles, [[FloatLib.Floats.Formats.BinaryInterchange.Model.Power.pow_spec_of_certified]] proves the result finite and correctly rounded, and a certified range failure gives positive infinity. Most exact results on a rounding boundary (a midpoint between two neighbours), and any search that runs out of attempts, fall back to `exp (y * log x)`, which has no accuracy proof. If you'd rather see the failure, `ExecFloat.Binary.Certified.pow x y` runs the search alone and returns it instead. On mixed binary64 operands `pow` takes 42.8 µs, but an exact rounding boundary takes about 3.5 ms before it falls back.

### How do sine and cosine handle huge arguments?

Sine and cosine only care where you end up on the circle, the way a clock shows the time of day and not how many days have passed. So our kernels first take away whole quarter turns, multiples of $\pi/2$, a step called argument reduction. They use the method of Payne and Hanek, multiplying the significand $m$ of $x = m \cdot 2^e$ by a window of a few hundred bits of $2/\pi$ from a cache of proved bounds. [[FloatLib.Numerics.Enclosure.ArgumentReduction.reduceWindow_spec]] bounds the error of the remainder by $2m$ units of its last place, and [[FloatLib.Numerics.Enclosure.ArgumentReduction.QuarterTurns.Reduces.exists_sin_cos_eq_rotate]] recovers the sine and cosine of $x$ from the reduced argument and the quadrant.

Does a wide enough window always exist? For nonzero dyadic $x$, a number $m \cdot 2^e$ like every finite float, it does, because $2x/\pi$ is irrational ([[FloatLib.Numerics.Enclosure.ArgumentReduction.exists_accepting_window]]), but we haven't proved that one of the permitted windows is accepted. Each call tries the first window and at most four doublings within $2^{21}$ bits of $2/\pi$, and gives the format's invalid result if none passes. In a format with at most 524,258 fraction bits, the first window fits for every finite argument below $2^{2^{20}}$. That covers every exponent field of at most 21 bits with the conventional bias, and in wider fields the largest arguments give the invalid result. The runtime check has succeeded on every input we tried, including every finite sine and cosine argument in the MPFR gate below and each format's two hard-case inputs closest to a multiple of $\pi/2$. For binary64 that's $6381956970095103 \cdot 2^{797}$, only $2^{-60.9}$ away, and it's accepted at its first window.

The cache isn't only for sine and cosine. It also holds $\log 2$ for the exponential and the logarithm, and every constant in it is proved within two units of its last place at every precision ([[FloatLib.Numerics.Enclosure.Constants.piLevel_twoOverPi_spec]], `piLevel_halfPi_spec` and [[FloatLib.Numerics.Enclosure.Constants.ln2Fixed_spec]]). [[FloatLib.Floats.Formats.BinaryInterchange.Model.pi]] rounds an *enclosure* from the cache, a pair of bounds that trap the true value, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_pi_eq_roundAt]] proves it correctly rounded in every IEEE format. The cache saves a lot of time, too. Without it, a binary64 `exp` takes 366 µs instead of 27 µs, and a binary128 `exp` 1.8 ms instead of 95 µs. The sine timings are in the [performance chapter](#/chapter/performance/what-made-floatlib-faster-in-october-2026).

### How do we test the approximations?

The approximation kernels themselves have no general accuracy proof, so we measure them. Our [MPFR gate](#/chapter/external-validation/how-do-we-test-the-elementary-functions), a test suite, compares `exp`, `log`, `sin`, `cos`, `sinh`, `cosh`, `tanh`, `pow` and `pi` with MPFR's correctly rounded results in six formats, and every case in its three tiers matches, with an empty list of known failures.

## How to get an exp or log with a proof

The functions `ExecFloat.Binary.Certified.exp`, `log`, `pow`, `expMinus1` and `logPlus1` refine rational enclosures until both endpoints round to the same finite encoding. A successful call returns `.ok result`. The success theorems prove that this result is finite and equals nearest-even rounding of the real function. If the search does not establish the condition, the call returns `.error` with a reason. A valid input can therefore produce an error when the search budget is insufficient. These functions do not return an uncertified approximation on failure.

Inside, a [containment proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Numerics/Enclosure/Elementary/BinaryGridProof.lean) combines Mathlib's series bounds with polynomial evaluation on a binary grid, rounded outward so the true value stays inside, at every working width, and a failed check retries with a higher degree or a wider grid. The logarithm's series uses *rectangular splitting*, a method that reduces the number of expensive multiplications in a long series, from [Johansson's account of elementary-function implementation](https://arxiv.org/abs/1410.7176). Watch the budget in these calls: it allows the first call twelve enclosure attempts and the third none.

```lean standalone
import FloatLib
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

#eval (ExecFloat.Binary.Certified.exp (1 : Binary32)
  (budget := { initialDegree := 8, maxAttempts := 12 })).map ExecFloat.Binary.toBits32
-- Except.ok 1076754516

#eval (ExecFloat.Binary.Certified.log (2 : Binary32)).map ExecFloat.Binary.toBits32
-- Except.ok 1060205080

#eval (ExecFloat.Binary.Certified.exp (1 : Binary32)
  (budget := { maxAttempts := 0 })).map ExecFloat.Binary.toBits32
-- Except.error .inconclusive

#eval (ExecFloat.Binary.Certified.log (-1 : Binary32)).map ExecFloat.Binary.toBits32
-- Except.error .domain

example (x y : Binary32) (budget : Certified.Budget)
    (h : ExecFloat.Binary.Certified.exp x (budget := budget) = Except.ok y) :
    ExecFloat.Binary.toReal y =
      Model.roundAt FloatFormat.binary32 (Real.exp (ExecFloat.Binary.toReal x)) :=
  ExecFloat.Binary.Certified.toReal_of_exp_eq_ok h
```

The first call returns 1076754516, the same word the approximation gave for $e$, and this time it comes with a proof. In the third, even the valid input 1 comes back `inconclusive`, because its budget permits no enclosure attempts. The fourth fails with `domain`, and the `example` is the success theorem for `exp`.

### What does the budget count?

By default the Taylor polynomial (a truncated power series) has degree 8, with at most 16 direct enclosure attempts, counting retries at higher working precision. `Certified.Budget` bounds those attempts, **not total work or running time**, because the exponential's preliminary underflow and overflow comparisons aren't counted and each retry works at a higher degree or precision than the one before. Custom widths work if they use conventional IEEE encoding and bias.

### Why did a certified call fail?

A failed call says why. You get `unsupportedFormat` for another encoding, `nonfiniteInput` for a NaN or an infinity, `domain` for a nonpositive logarithm argument or power base, and `range` for an exponential or power whose exact result reaches the overflow threshold, the largest finite value plus half an ulp (a unit in the last place, the gap between neighbouring floats there). `inconclusive` means the search didn't settle within its budget, with no claim about whether more refinement would succeed, and we don't promise success on every valid input. A successful call certifies a finite rounded value and returns no IEEE status flags.

<details>
<summary>What the transcendental certificates state</summary>

A `StableEnclosure` records that the bounds $l\le f(x)\le u$ of a `RealEnclosure` round to the same destination value, and `CertifiedRoundedResult.toReal_value_eq_roundAt` proves the accepted stored result correctly rounded. Our [contract module](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Transcendentals/Contract.lean) supplies enclosure constructors and theorems for combining them. An `ApproximationCertificate` claims that a kernel returns, on every finite input, a finite value within a given absolute error, and `ApproximationCertificateOn` restricts the claim to a stated domain. `CorrectlyRoundedCertificateOn` asks for correct rounding throughout its domain. These types state proof obligations. We don't supply a certificate for the value-only approximation kernels, so `#float_info` reports that framework as conditional, and a generic accuracy theorem needs that kernel certificate first.

</details>

## How to keep tiny differences near zero

Why have `expMinus1` and `logPlus1` at all, when `exp` and `log` are right there? As their names say, they compute $e^x - 1$ and $\log(1 + x)$, and near zero, writing either one as two floating-point operations can lose the whole answer. Take $x = 2^{-26}$ in binary32, the `tiny` below. The rounded sum $1 + x$ is already $1$, whose logarithm is $0$, so every bit of the answer is gone. `expMinus1` subtracts one from the rational enclosure before rounding, and `logPlus1` forms `1 + x` exactly before enclosing its logarithm, and both round to $x$:

```lean standalone
import FloatLib
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals

open FloatLib.Floats
def tiny : Binary32 := 1 / 67108864

#eval (1 : Binary32) + tiny == 1
-- true
#eval (ExecFloat.Binary.Certified.expMinus1 tiny).map (· == tiny)
-- Except.ok true
#eval (ExecFloat.Binary.Certified.logPlus1 tiny).map (· == tiny)
-- Except.ok true
```

Both certified calls come back `.ok` with `tiny` itself. The success theorems `Certified.toReal_of_expMinus1_eq_ok` and `Certified.toReal_of_logPlus1_eq_ok` connect these results to `Real.exp x - 1` and `Real.log (1 + x)`. The two operations keep the sign of a zero input, and `logPlus1` requires $x > -1$ and fails with `domain` otherwise. `Certified.expMinus1` and `Certified.logPlus1` have no approximate counterpart, and their total versions, which always return a value, are among the [correctly rounded functions](#/chapter/elementary-functions/how-to-get-a-correctly-rounded-answer-every-time).

## How to get a correctly rounded answer every time

A bounded certified search can return an error even for a valid input. `ExecFloat.Binary.CorrectlyRounded.exp`, `log`, `expMinus1`, `logPlus1` and `expMul`, where `expMul x w`, exp then multiply, rounds $e^x w$ once, are total operations. They live in the [correctly rounded module](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/CorrectlyRounded.lean), which the transcendental module also imports. Each first runs an enclosure search within its `budget` (for `exp` and `expMinus1`, the certified search). If that doesn't settle, exact comparisons of the real result with rational rounding candidates decide, as they do for `Model.pi` and the [posit functions](#/chapter/posits-and-the-quire/how-to-compute-exponentials-and-logarithms). This fallback uses exact comparisons to determine the rounded result when the bounded enclosure search is inconclusive.

If you start with no enclosure attempts at all, you can watch the exact comparisons take over:

```lean standalone
import FloatLib
import FloatLib.Floats.Formats.BinaryInterchange.Configured.CorrectlyRounded

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

#eval ExecFloat.Binary.toBits32
  (ExecFloat.Binary.CorrectlyRounded.exp (1 : Binary32) (budget := { maxAttempts := 0 }))
-- 1076754516

#eval ExecFloat.Binary.CorrectlyRounded.exp (100 : Binary32) * 1e-10
-- inf
#eval ExecFloat.Binary.CorrectlyRounded.expMul (100 : Binary32) 1e-10
-- 2.6881172e33

example (x : Binary32) (hx : ExecFloat.Binary.isFinite x = true)
    (hrange : Real.exp (ExecFloat.Binary.toReal x) <
      Model.Transcendentals.Certified.overflowThreshold FloatFormat.binary32) :
    ExecFloat.Binary.toReal (ExecFloat.Binary.CorrectlyRounded.exp x) =
      Model.roundAt FloatFormat.binary32 (Real.exp (ExecFloat.Binary.toReal x)) :=
  ExecFloat.Binary.CorrectlyRounded.toReal_exp_eq_roundAt hx hrange
```

With the setting that made the certified call come back `inconclusive`, you now get 1076754516, the binary32 word nearest to $e$, because the exact comparisons decide. The next two calls are the `hypot` problem with an exponential in it. Since $e^{100} \approx 2.69 \cdot 10^{43}$ is beyond binary32's largest finite value, rounding the exponential first leaves an infinity that multiplying by the binary32 value nearest $10^{-10}$ can't bring back. `expMul` rounds the product once and gets a finite $2.69 \cdot 10^{33}$.

### What does the theorem promise?

The `example` at the bottom is the promise itself, fine print included. Its theorem, `toReal_exp_eq_roundAt`, says the result is the nearest-even rounding of $e^x$ below `Certified.overflowThreshold`, the largest finite value plus half its ulp. At or beyond it, `toModel_exp_eq_nativeOverflow` gives $+\infty$. `expMinus1`, `log`, `logPlus1` and `expMul` have the same two cases. For `log`, `logPlus1` and `expMul` the threshold applies to the magnitude of the exact result, beyond which you get the infinity of its sign. All of these theorems need an IEEE descriptor and a finite input in the domain. NaNs, infinities, zeros and arguments outside the domain get their IEEE 754 results, and a finite logarithm can only come from a positive input (`toReal_pos_of_isFinite_log`).

### Why does the search always stop?

To compare an exponential with a positive boundary $b$, we compare the argument with $\log b$ and refine logarithm enclosures until one excludes the candidate. That terminates because the logarithm of a positive rational other than one is irrational ($\log 1 = 0$ is decided on its own). So the budget only decides how long the search runs, and no correctness theorem has a premise on it. We proved termination, but the proof bounds neither the number of refinements nor the size of the rationals.

## How to use these functions with decimal numbers

The decimal formats, which count in base ten, get the same binary-grid enclosures through the `Transcendentals.Certified` API, whose optional import gives you `expMinus1` and `logPlus1` on the [decoded decimal data](#/chapter/decimal-arithmetic/how-decimal-numbers-are-stored-in-bits). On the decimal32 input $10^{-9}$ both keep the increment that would vanish if $1+x$ were rounded on its own:

```lean standalone
import FloatLib
import FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Certified.Proof
open FloatLib.Floats.Formats.DecimalInterchange

def tiny : Datum := 1e-9
#eval (Transcendentals.Certified.expMinus1 Format.decimal32 tiny).bind Datum.toRat?
-- some (1 / 1000000000)
#eval (Transcendentals.Certified.logPlus1 Format.decimal32 tiny).bind Datum.toRat?
-- some (1 / 1000000000)
#eval (Transcendentals.Certified.logPlus1 Format.decimal32 (-1)).bind Datum.toRat?
-- none

example (x y : Datum) (budget : FloatLib.Floats.Certified.Budget)
    (h : Transcendentals.Certified.logPlus1 Format.decimal32 x (budget := budget) = some y) :
    Transcendentals.toReal y = Transcendentals.roundAt Format.decimal32
      (Real.log (1 + Transcendentals.toReal x)) :=
  Transcendentals.Certified.toReal_of_logPlus1_eq_some h
```

When a call succeeds, the result is valid, finite and nearest-even rounded, as [[FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Certified.toReal_of_logPlus1_eq_some]] states for `logPlus1`. Both functions keep a valid zero's sign and quantum, the stored exponent that tells $1.20$ from $1.2$. Their success theorems work for arbitrary decimal layouts, including quantum ranges that exclude zero. Invalid or nonfinite datums return `none`, and so do `logPlus1` inputs at or below $-1$ (the third call above), overflow, and refinement that doesn't settle. As on the binary side, `Certified.Budget` limits enclosure attempts, not the exact exponential comparisons that settle the tail and overflow cases, and success gives you no IEEE status flags.
