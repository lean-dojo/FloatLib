---
number: "10"
slug: elementary-functions
title: "Elementary functions"
summary: "Exact root comparisons and rational enclosures can determine a rounded elementary function; approximation calls and partial certified calls offer different guarantees."
phases: [binary-arithmetic, status-and-directed]
---

A floating-point function must choose a stored value for an exact expression that may be irrational. For powers and roots, integer comparisons can identify the rounding boundary. For an exponential or logarithm, rational bounds can narrow the answer until both endpoints round to the same value. FloatLib provides these algorithms alongside value-only transcendental approximations, whose general accuracy has not been proved.

## Powers and roots with one rounding

Rounding an intermediate value can change a calculation even when its final result fits.
For example, binary32 can store a number near $10^{20}$ and its hypotenuse with itself,
but it cannot store the square. Computing `sqrt (x * x + y * y)` overflows before reaching
the square root. `hypot` forms the exact sum of squares and rounds only its root.

The [algebraic operations](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/BinaryInterchange/Algebraic)
use the [binary descriptors and storage choices](#/chapter/ieee-binary-formats/custom-widths) of ordinary arithmetic:

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

abbrev Binary32 := ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)

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

Squaring reuses the multiplication kernels; the word paths decode the operand once.
For `hypot`, both squared significands are nonnegative integers, so shifts and one
integer addition form their exact sum. Integer powers use exact rational arithmetic.

For an $n$th root, the radicand's binary magnitude determines the output exponent.
After scaling the radicand to a rational $a/b$, an integer-root kernel computes the
significand $c$. Its proof establishes $c^n b \le a < (c+1)^n b$, identifying the two
neighbouring results. An exact midpoint comparison then chooses nearest-even rounding.
Degree two uses integer square root; higher degrees use Newton iteration starting from a
power-of-two upper bound. The [integer-root theorem](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/IntegerRoot/Proof.lean)
proves equality with Mathlib's `Nat.nthRoot` for every input and degree. Binary and decimal
roots share this kernel, with their format-specific scaling and final rounding. Precision
and exponent range come from the descriptor, so the same proofs apply at standard and
custom widths.

The [real-value theorems](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/Algebraic/Proof.lean),
including [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_hypot_eq_roundAt]] and
[[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_rootN_eq_roundAt]], identify a finite result
with rounding the corresponding real expression for a conventional IEEE descriptor and
finite operands in its real domain. The `powInt` and `rootN` theorems require a nonzero base;
`rootN` also requires a nonzero degree, odd when the base is negative. The `rsqrt` theorem
requires a positive input. The configured versions apply directly to the calls above.
`square_eq_mul` also proves equality of the complete encoded multiplication result.

Exceptional inputs have explicit rules. A root of degree zero or an even-degree root of
a negative nonzero value returns NaN. Negative degrees allow reciprocal roots, including
the signed infinities at zero. For `hypot`, infinity dominates a quiet NaN, while a signaling
NaN is quieted and propagated.

## Calling the approximation kernels

The optional [binary transcendental module](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/Transcendentals.lean) provides a value-only approximation API for `exp`, `log`, `sin`, `cos`, `sinCos`, `sinh`, `cosh`, and `tanh` for every `ExecFloat.Binary` type. It also provides `Model.pow` and `MathFunctions` instances, so generic code can call these functions alongside the certified `sqrt` and `abs` and the constant `pi`. Each function decodes its input, calls the descriptor-generic model kernel, and packs the result back into the configured word.

These value-only transcendental kernels have no proved general accuracy bound. The one exception is `Model.pow` for an IEEE descriptor with a finite nonzero base, a finite integral exponent, and a finite result: `Model.Power.toReal_pow_of_eq_intCast` proves that the decoded result is nearest-even rounding of the exact power. The kernels use nearest-even rounding internally, accept no rounding direction, and return no status flags. The separate test workspace has an Arb adapter for point evaluation with an explicit rounding direction; it uses python-flint as an external reference, as described in [chapter 19](#/chapter/external-validation). The software kernels require the named import below; `import FloatLib` alone provides the `MathFunctions` class and its host `Float` instance, but does not install these binary functions:

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

`#float_info` lists this framework as conditional even with the default import. Applying it requires a certificate for the selected kernel on the stated domain. The value-only approximation kernels above do not supply such certificates; the enclosure definitions and generic implications do not establish their accuracy.

## Certified exponential and logarithm

The optional `Binary.Certified.exp`, `log`, `expMinus1`, and `logPlus1` turn rational
enclosures into executable rounding decisions. They refine the bounds until both endpoints
round to the same finite encoding, then return `some result`. The success theorems prove
that this result is finite and equals nearest-even rounding of the corresponding real
function.

The enclosure engine stores each endpoint as an integer multiple of $2^{-w}$. Polynomial
evaluation rounds each intermediate product and division outward on this binary grid.
Adding a proved remainder bound gives an enclosure of the real function. The polynomial
calculation avoids the growing denominators of exact rational evaluation. Argument
reduction and scalar factors still use rationals, and the final grid endpoints are
converted to rationals for the destination rounder.

For the logarithm, setting $t=(x-1)/(x+1)$ gives the odd series
$\log x=2(t+t^3/3+t^5/5+\cdots)$. Each successive term gains a factor of $t^2$,
so short polynomials use a Horner loop in $t^2$. Longer polynomials share a table
of powers and group the terms into blocks. With $n$ terms, blocks of about $\sqrt n$
reduce the number of full-width multiplications from order $n$ to order $\sqrt n$;
each coefficient still needs a scalar division. This is *rectangular splitting*,
described in [Johansson's account of elementary-function implementation](https://arxiv.org/abs/1410.7176).
The [containment proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Numerics/Enclosure/Elementary/BinaryGridProof.lean)
combines Mathlib's series bound with the outward-rounded polynomial and remainder.

The exponential uses a Taylor series after reducing the argument, then repeated
squaring restores the original scale. Further reduction can make a shorter polynomial
sufficient, at the cost of more squarings. The engine chooses this extra reduction from
the degree, working width, and input magnitude, and adds fractional bits before squaring.
An already small argument needs less reduction.

The initial working width accounts for the input's scale: a small `expMinus1` result
needs extra fractional bits to survive subtracting one, and `logPlus1` needs them to
retain a small increment. Refinement then adjusts the degree and width separately.
After a failed check, it tries twice the degree and one extra working bit. If the
interval shrinks by at most a factor of four, the following attempt keeps the degree
and doubles the working width.

For binary64, $\exp(2^{-53})$ lies only about $2^{-107}$ above the rounding midpoint
$1+2^{-53}$. Once the series remainder is small, more terms cannot resolve that
decision on a coarse grid. Increasing the working width reduces the rounding error
introduced by the enclosure calculation itself. Containment is proved at every width,
and acceptance still requires both endpoints to round to the same finite encoding.
Binary and decimal certified operations share this refinement engine.

The [focused import](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/Transcendentals/Certified.lean)
below exposes these operations without installing the approximation API or its
`MathFunctions` instances. The broader transcendental import above exposes both APIs and
keeps the value-only functions as its defaults.

```lean standalone
import FloatLib
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals.Certified

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

abbrev Binary32 := ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)

#eval (ExecFloat.Binary.Certified.exp (1 : Binary32)
  { initialDegree := 8, maxSteps := 12 }).map ExecFloat.Binary.toBits32
-- some 1076754516

#eval (ExecFloat.Binary.Certified.log (2 : Binary32)).map ExecFloat.Binary.toBits32
-- some 1060205080

#eval (ExecFloat.Binary.Certified.exp (1 : Binary32)
  { maxSteps := 0 }).map ExecFloat.Binary.toBits32
-- none

example (x y : Binary32) (options : ExecFloat.Binary.Certified.Options)
    (h : ExecFloat.Binary.Certified.exp x options = some y) :
    Model.toReal (ExecFloat.Binary.toModel y) =
      Model.roundAt FloatFormat.binary32
        (Real.exp (Model.toReal (ExecFloat.Binary.toModel x))) :=
  ExecFloat.Binary.Certified.toReal_of_exp_eq_some h
```

The logarithm theorem, `toReal_of_log_eq_some`, has the same success hypothesis.
The last evaluation shows that even the valid input 1 can return `none` when no refinement
attempts are allowed.
Defaults are Taylor degree 8 and at most 16 direct enclosure attempts, including retries
at higher working precision. `maxSteps` bounds those attempts, **not total running time**:
the exponential's preliminary underflow and overflow comparisons run independently of it.
Simple rational bounds derived from the format's exponent range skip those comparisons
when the argument is safely inside the range.

Custom widths are supported with conventional IEEE encoding and bias. Nonfinite inputs,
nonpositive logarithm arguments, unsupported descriptors, overflow, or exhausted refinement
return `none`; the API does not promise success on every valid input. A successful call
certifies a finite rounded value and returns no IEEE status flags.

## Keeping small differences

Near zero, evaluating `exp x - 1` or `log (1 + x)` as separate floating-point operations can
lose the result before the final subtraction or logarithm. `expMinus1` subtracts one from
the rational enclosure before rounding; `logPlus1` forms `1 + x` exactly before enclosing
its logarithm. For binary32, take $x = 2^{-26}$. The rounded sum $1 + x$ is already $1$,
but both stable functions round to $x$:

```lean standalone
import FloatLib
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals.Certified

open FloatLib.Floats
abbrev Binary32 := ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)
def tiny : Binary32 := 1 / 67108864

#eval (1 : Binary32) + tiny == 1
-- true
#eval (ExecFloat.Binary.Certified.expMinus1 tiny).map (· == tiny)
-- some true
#eval (ExecFloat.Binary.Certified.logPlus1 tiny).map (· == tiny)
-- some true
```

The theorems `toReal_of_expMinus1_eq_some` and `toReal_of_logPlus1_eq_some` connect these
results to `Real.exp x - 1` and `Real.log (1 + x)`. Both operations preserve either signed
zero. `logPlus1` requires $x > -1$; otherwise it returns `none`.

## Certified decimal functions

The decimal `Transcendentals.Certified` API uses the same binary-grid enclosures and rounds
their rational endpoints into the decimal format. Its working width follows the decimal
precision. The optional import exposes `expMinus1` and `logPlus1` on the
[decoded decimal data](#/chapter/decimal-arithmetic/encoding-the-complete-datum).
For a decimal32 input $10^{-9}$, both functions retain the increment that would disappear
in a separately rounded $1+x$:

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

A successful result is valid, finite, and nearest-even rounded, as
[[FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Certified.toReal_of_logPlus1_eq_some]]
states for `logPlus1`. Both functions preserve a
valid zero's sign and quantum. The success theorems work for arbitrary decimal layouts,
including quantum ranges that exclude zero. Invalid or nonfinite datums return `none`,
as do `logPlus1` inputs at or below $-1$, overflow, and inconclusive refinement.
The options limit enclosure attempts; the exact exponential comparisons used to settle
the tail and overflow cases run outside that budget. Success certifies a finite result
and supplies no IEEE status flags.
