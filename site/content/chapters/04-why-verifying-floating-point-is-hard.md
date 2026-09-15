---
number: "04"
slug: why-verifying-floating-point-is-hard
title: Proving floating-point arithmetic correct
summary: Correctness proofs must account for rounding, exceptional values, and the way an implementation evaluates an expression.
---

We now know what correct rounding promises for one operation: compute its exact result, then select a representable value. In a program, the selected value becomes the input to the next operation. Moving a pair of parentheses can change where rounding happens; changing an intermediate format can change which side of a midpoint the next operation sees. The bit patterns and rounding rule developed in [chapter 02](#/chapter/from-reals-to-machine-numbers) let us follow these effects precisely. To verify an implementation, we also need to show that its shifts, table lookups, and exceptional branches implement that rule for every input.

<a id="the-state-space"></a>

## Limits of exhaustive testing

A binary64 addition has $2^{64} \cdot 2^{64} = 2^{128}$ possible input pairs. At a billion tests per second that is about $10^{22}$ years. Binary32 has $2^{64}$ pairs, which is a few hundred years at the same rate. Exhaustive testing becomes feasible at smaller widths: binary16 has $2^{32}$ ordered pairs, roughly four billion, and an eight-bit format has $2^{16} = 65{,}536$, which fits in a table. Actual running time also depends on the cost of computing the expected result. [Figure 4.1](#/chapter/why-verifying-floating-point-is-hard/figure-ch02-state-space) compares the counts using the same hypothetical rate for every format.

![Ordered input pairs of one binary operation at 8, 16, 32 and 64 bits, read also as the time to run them all at a billion tests per second; binary32 and binary64 are impractical to enumerate at this rate](assets/ch02-state-space.png "Ordered pairs for one binary operation, on a logarithmic scale. The time scale assumes one billion checks per second and is illustrative, not a measured test run.")

For formats of eight bits or fewer, the table backends evaluate the reference operation once at every pair of inputs and store the results. A `CertifiedBinary` kernel carries that table together with two certificates: `table_eq`, that every entry equals the operation the table was generated from, and `model_eq_spec`, that the generating operation equals the reference. The theorem [[FloatLib.Floats.Formats.BinaryInterchange.Configured.ByteTable.runBinary_eq_lift]] states that calling the table gives the same result as the configured model operation. Corresponding theorems cover operations with one and three arguments.

For binary16, the library's addition and multiplication can be compared with MPFR [@fousseMpfr2007] in batches of the $2^{32}$ ordered input pairs. Dividing the work makes an exhaustive comparison manageable, but it is complete only after every batch has run. The binary16 comparisons described in [chapter 16](#/chapter/external-validation) cover a sample of the full $2^{32}$ pairs.

For binary32 and binary64, tests can exercise known difficult cases and search for disagreements, but they cannot practically enumerate the whole input space. A proof handles this differently: its variables range over arbitrary input words. For example, an argument about how many low bits a shift discards can apply to every significand and exponent at once, without evaluating $2^{128}$ individual cases.

<a id="the-algebra-that-fails"></a>

## Rounding changes algebraic identities

Real addition is associative, and real multiplication distributes over addition. Correct rounding does not preserve these laws: grouping an expression differently changes the intermediate results that are rounded. We can see this with $2^{-24}$, exactly representable in binary32 and exactly half the grid spacing at one. We'll construct it from its bit pattern below, so no decimal conversion is involved:

```lean
open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

abbrev Binary32 :=
  ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)
abbrev Binary64 :=
  ExecFloat.Binary (exponentBits := 11) (fractionBits := 52)

def halfUlp : Binary32 :=
  ExecFloat.Binary.ofBits32 0x33800000

#eval ExecFloat.Binary.toRat? halfUlp
-- some (1 / 16777216)

#eval ((1 : Binary32) + halfUlp) + halfUlp
-- 1

#eval (1 : Binary32) + (halfUlp + halfUlp)
-- 8388609 * 2^-23
```

Try tracing the intermediate sums yourself, keeping the rounding after each addition.

In the first grouping, adding `halfUlp` to one lands exactly halfway between two binary32 values. The even significand belongs to one, so nearest-even returns one. The second addition starts from one again and encounters the same tie. In the other grouping, the two small terms add exactly to $2^{-23}$, a full step on the grid at one. Adding that step is exact too: the printed `8388609 * 2^-23` is $1 + 2^{-23}$. Each individual addition obeys the rounding rule, but the intermediate roundings differ. Distributivity fails for the same reason:

```lean
#eval (10 : Binary64) * (0.1 + 0.7)
-- 9007199254740991 * 2^-50

#eval (10 : Binary64) * 0.1 + 10 * 0.7
-- 8
```

The first is $8 - 2^{-50}$. To follow the difference, call the stored binary64 values of `0.1` and `0.7` $A$ and $B$. Their exact sum, measured in grid steps of $2^{-53}$, is

$$
  A+B = \left(7205759403792793 + \frac14\right)2^{-53}.
$$

The addition discards the quarter-step. Multiplying its rounded result by ten gives the exact intermediate $8 - 3\cdot2^{-52}$. Just below eight, binary64 values are spaced $2^{-50}$ apart, so this intermediate is three quarters of a step below eight. It rounds to the neighbour below eight, the first printed result.

In the distributed expression, the exact products before rounding are

$$
  10A = 1 + 2^{-54}, \qquad 10B = 7 - 2^{-51}.
$$

The first rounds to one. The second is exactly halfway between seven and the word below it; seven has the even significand, so the tie rounds to seven. Adding the two rounded products gives eight exactly. Distributing the multiplication changed which errors reached the final addition, even though both expressions began with the same stored constants.

Decimal literals introduce a rounding before the arithmetic even starts. For $0.1 + 0.2 \ne 0.3$, [chapter 02](#/chapter/from-reals-to-machine-numbers) follows the conversion of each literal and then the addition. In binary64 the sum lands one ulp above the rounded `0.3`:

```lean
#eval ExecFloat.Binary.toBits64 ((0.1 : Binary64) + 0.2)
-- 4599075939470750516

#eval ExecFloat.Binary.toBits64 (0.3 : Binary64)
-- 4599075939470750515

#eval ((0.1 : Binary64) + 0.2) == (0.3 : Binary64)
-- false
```

The two words are `0x3fd3333333333334` and `0x3fd3333333333333`. The first is obtained by adding two already rounded inputs and rounding their sum. The second comes from rounding the exact decimal three-tenths directly.

Nor does $x + y = x$ imply $y = 0$. In binary32 the integers above $2^{24}$ are spaced two apart, so adding one to $2^{24}$ is a tie. Ties go to even, returning the original value. A status-bearing operation can report that information was discarded: [[FloatLib.Floats.ExecFloat.Binary.addWithStatus]] returns the value paired with the five IEEE flags, and `.2` selects the flags:

```lean
#eval (16777216 : Binary32) + 1
-- 1 * 2^24

#eval (ExecFloat.Binary.addWithStatus (16777216 : Binary32) 1
  (rounding := .nearestEven)).2
-- { invalid := false, divideByZero := false, overflow := false, underflow := false, inexact := true }
```

The `inexact` flag records that this addition did not return its exact real sum. It does not record the size of the discarded increment. A loop that counts by adding one to a binary32 accumulator stops counting at $2^{24}$: each subsequent addition returns the same word and sets the same flag.

When a subtraction gives a poor answer, it is tempting to blame the subtraction. We need to check where the error entered. Sterbenz's lemma [@sterbenz1974] says that subtracting nearby floating-point values is exact under the conditions stated below. Yet the difference can be a poor approximation to the quantity we intended to calculate:

```lean
#eval ((1 : Binary32) + 1e-6) - 1
-- 1 * 2^-20
```

The intended real calculation gives $10^{-6}$; the computed value is $2^{-20} \approx 9.54 \times 10^{-7}$, off by almost five percent. The subtraction itself is exact. The theorem [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_sub_eq_of_sterbenz]] states that for positive finite values within a factor of two of each other the decoded difference is the exact real difference. Here it is applied at binary32, with `by decide` discharging the hypothesis that the format is a conventional IEEE one:

```lean
example (x y : Model FloatFormat.binary32)
    (hx : Model.isFinite x = true) (hy : Model.isFinite y = true)
    (hxpos : 0 < Model.toReal x) (hypos : 0 < Model.toReal y)
    (hxy : Model.toReal x ≤ 2 * Model.toReal y)
    (hyx : Model.toReal y ≤ 2 * Model.toReal x) :
    Model.toReal (Model.sub x y) = Model.toReal x - Model.toReal y :=
  Model.toReal_sub_eq_of_sterbenz (by decide) hx hy hxpos hypos hxy hyx
```

The addition rounded $1 + 10^{-6}$ to the nearest multiple of $2^{-23}$, introducing an absolute error of about $4.6 \times 10^{-8}$. Subtracting one leaves that absolute error unchanged while reducing the magnitude of the result by about a million. Its relative error therefore grows sharply. Exact subtraction cannot recover information discarded by the addition. [Chapter 07](#/chapter/the-mathematics-of-rounding) develops the grid form of Sterbenz's lemma, [[FloatLib.Floats.Formats.Flocq.generic_format_FLX_sterbenz]].

## Rounding twice

Rounding an exact value to an intermediate precision can move it onto a midpoint of the final format. The second rounding then resolves a tie that was absent from the original value. Consider

$$x = 1 + 2^{-24} + 2^{-53}.$$

Rounded directly to binary32 it goes up, because it is just above the midpoint between $1$ and $1 + 2^{-23}$. Rounded first to binary64 it is a tie, since $2^{-53}$ is half the binary64 spacing at one. Nearest-even gives exactly $1 + 2^{-24}$, a binary32 midpoint, so the final rounding returns $1$.

Those two grids are too far apart in spacing to draw on one line. We'll use three binary digits to stand in for binary32's 24 and five for binary64's 53 in [Figure 4.2](#/chapter/why-verifying-floating-point-is-hard/figure-ch02-double-rounding), so we can see both rounding steps; the arithmetic is otherwise identical.

![The chapter's double rounding on grids small enough to draw: with three binary digits as the target and five as the intermediate, x = 1 + 2^-3 + 2^-5 rounds once to 1.25 and twice, through the five-digit grid, to 1](assets/ch02-double-rounding.png "The intermediate rounding lands exactly on a target-grid midpoint. Rounding again therefore returns a different value from rounding the original input once.")

On the smaller grids, the marked input is $37/32$. The five-digit grid has spacing $1/16$, and its neighbours are $36/32$ and $38/32$. They are equally far away. In units of that spacing their significands are 18 and 19, so the first rounding chooses the even one, $36/32 = 9/8$. On the three-digit grid, $9/8$ is a new tie, between $1 = 4/4$ and $5/4$. The even significand is now 4, giving one. Direct rounding keeps the original $37/32$, which is closer to $40/32 = 5/4$ than to one. The vertical dotted line in the figure follows the intermediate value that lost this distinction.

We can run this on the model operations. The value is the dyadic $(2^{53} + 2^{29} + 1) \cdot 2^{-53}$, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.Policy.roundDyadic]] rounds an exact dyadic into a format under a [[FloatLib.Numerics.QuantizationPolicy]]; its third argument is entropy for stochastic rounding and is unused by nearest-even:

```lean
open FloatLib.Numerics (QuantizationPolicy)

def justAboveMidpoint : FloatLib.Numerics.Dyadic :=
  { negative := false, significand := 2^53 + 2^29 + 1, exponent := -53 }

def direct32 : Model FloatFormat.binary32 :=
  Model.Policy.roundDyadic FloatFormat.binary32
    QuantizationPolicy.nearestEven 0 justAboveMidpoint

def via64 : Model FloatFormat.binary64 :=
  Model.Policy.roundDyadic FloatFormat.binary64
    QuantizationPolicy.nearestEven 0 justAboveMidpoint

#eval Model.toDyadic? direct32
-- some { negative := false, significand := 8388609, exponent := -23 }

#eval Model.toDyadic? via64
-- some { negative := false, significand := 4503599895805952, exponent := -52 }

#eval Model.toDyadic?
  (Model.cast FloatFormat.binary64 FloatFormat.binary32 via64)
-- some { negative := false, significand := 8388608, exponent := -23 }
```

Direct rounding gives significand $8388609$ at exponent $-23$, which is $1 + 2^{-23}$. Rounding through binary64 gives $1 + 2^{-24}$ exactly, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.cast]] to binary32 then gives significand $8388608$, which is $1$. The final answers differ by one ulp.

The same mechanism can occur when an x87 computation first rounds in an 80-bit register and then rounds again on storage to a 64-bit memory slot. Keeping an intermediate in a register or spilling it to memory can consequently affect later results. [Chapter 07](#/chapter/the-mathematics-of-rounding) proves double-rounding identities under specific hypotheses, including results for directed modes and for round to odd followed by nearest even on a fixed grid. The nearest-even example above shows why a general identity cannot hold for that mode.

We can change the number of roundings deliberately with fused multiply-add. An FMA rounds $xy + z$ once; a multiplication followed by an addition rounds the product before using it in the sum. The product's discarded bits can affect the final answer:

```lean
def a : Binary32 :=
  ExecFloat.Binary.ofBits32 0x3f800800

#eval ExecFloat.Binary.toRat? a
-- some (4097 / 4096)

#eval ExecFloat.Binary.toRat? (ExecFloat.fma a a (-1))
-- some (8193 / 16777216)

#eval ExecFloat.Binary.toRat? (a * a - 1)
-- some (1 / 2048)
```

Here $a = 1 + 2^{-12}$, so $a^2 - 1 = 2^{-11} + 2^{-24}$ exactly, which the fused operation [[FloatLib.Floats.ExecFloat.fma]] returns. The separate product needs 25 significant bits and rounds to $1 + 2^{-11}$; the subtraction then returns $2^{-11}$. A compiler may contract `a * a - 1` into an FMA when the language and compilation options permit it. Verifying that expression therefore requires fixing whether contraction is allowed. The model-level theorem [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_fma_eq_roundAt]] specifies the fused operation as one rounding of the exact expression.

<a id="values-that-are-not-numbers"></a>

## Exceptional values and signed zeros

An arithmetic operation on stored words must also handle infinities, NaNs, and signed zeros. These cases need their own rules because their behaviour cannot be recovered from arithmetic on the reals. An infinity absorbs every finite addend, so $x + \infty = \infty$ does not determine $x$. NaN is not equal to itself under IEEE comparison, so IEEE equality is not reflexive. Lean's structural equality on the stored word is reflexive:

```lean
#eval ((0 : Binary32) / 0) == ((0 : Binary32) / 0)
-- false

#eval ((0 : Binary32) / 0) = ((0 : Binary32) / 0)
-- true
```

The first expression uses the IEEE comparison installed as `==` for `ExecFloat` types; the second decides equality of bit patterns. Thus `x == x` is false for a NaN, while `x = x` holds for every stored word. A theorem about structural equality can establish that two computations return the same NaN word without asserting that IEEE comparison returns true.

IEEE ordered comparisons with a NaN operand return false. For a NaN `x`, both `x < 1` and `1 < x` fail. A clamp written as `if x < bound then x else bound` consequently returns `bound`, replacing the NaN with a finite value when the bound is finite. Arithmetic operations can instead propagate a quiet NaN without raising `invalid` again. The evaluations below show `invalid` set by an operation that creates a NaN and clear in an addition that propagates one:

```lean
def nan32 : Binary32 := (0 : Binary32) / 0
def inf32 : Binary32 := (1 : Binary32) / 0

#eval nan32 < 1
-- false

#eval (1 : Binary32) < nan32
-- false

#eval if nan32 < 1 then nan32 else (1 : Binary32)
-- 1

#eval inf32 + (-1000000) == inf32
-- true

#eval (ExecFloat.Binary.subWithStatus inf32 inf32
  (rounding := .nearestEven)).2
-- { invalid := true, divideByZero := false, overflow := false, underflow := false, inexact := false }

#eval (2 : Binary32) * (nan32 + 1)
-- nan

#eval (ExecFloat.Binary.addWithStatus nan32 1
  (rounding := .nearestEven)).2
-- { invalid := false, divideByZero := false, overflow := false, underflow := false, inexact := false }
```

Inspecting a propagated quiet NaN still reveals that the value is a NaN, but its status flags need not reveal which earlier operation created it. If the program replaces it with a finite value, as the clamp does, that information is lost unless the program retained the earlier status or checked the input.

The two zeros are equal under `==` and different under `=`, and default nearest-even arithmetic distinguishes them: $(-0) + (-0) = -0$ but $(-0) + 0 = +0$, and $(-0) \cdot 3 = -0$.

Status flags are a further piece of state that real arithmetic does not have. Every status-bearing operation returns five of them, the fields of [[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEEStatus]], recording conditions such as overflow and inexactness. Dividing by zero and dividing zero by zero return different nonfinite values and set different flags:

```lean
#eval (ExecFloat.Binary.divWithStatus (1 : Binary32) 0
  (rounding := .nearestEven)).2
-- { invalid := false, divideByZero := true, overflow := false, underflow := false, inexact := false }

#eval (ExecFloat.Binary.divWithStatus (0 : Binary32) 0
  (rounding := .nearestEven)).2
-- { invalid := true, divideByZero := false, overflow := false, underflow := false, inexact := false }
```

Hardware commonly accumulates these flags in a status register. The library returns them with each result, making them available to ordinary program logic. [[FloatLib.Floats.Formats.BinaryInterchange.Model.divWithStatus_divideByZero]] says the divide-by-zero flag is set exactly when a finite nonzero operand is divided by a zero, and `divWithStatus_invalid` gives the exact invalid predicate, including a signaling NaN operand and infinity divided by infinity. These predicates specify information that decoding the result to a real number cannot retain.

<a id="error-bounds-are-not-bit-specifications"></a>

## Error bounds and exact output words

The classic analysis, used throughout Higham's textbook [@higham2002] and Goldberg's survey [@goldberg1991], writes $\mathrm{fl}(x \circ y) = (x \circ y)(1 + \delta)$ with $|\delta| \le u$, where $u$ is the unit roundoff. Under its range assumptions, this bounds the error introduced by an operation. It is useful precisely because the analysis can proceed without knowing the exact rounded result: the bound admits any result within the allowed error. Subnormal results require an absolute-error treatment, and overflow requires separate handling. Even where the relative bound applies, satisfying it alone does not establish correct rounding.

The halfway value $t = 1 + 2^{-24}$ makes the difference concrete in binary32. Both one and $1 + 2^{-23}$ are exactly $2^{-24}$ away from it. Either candidate satisfies the relative bound, because dividing that error by $t>1$ makes it smaller than the unit roundoff $2^{-24}$. Nearest-even nevertheless requires one: its significand is even and the upper neighbour's is odd. An implementation returning the upper neighbour would pass this error-bound check and fail the rounding specification.

A bit specification determines a particular output word for each input and rounding mode. Proving it requires enough information about the exact intermediate to choose that word, including the tie-breaking bits and exceptional cases. Once that equality is established, an error bound can be derived from the rounding rule. The layers described in [chapter 06](#/chapter/the-numerical-models) retain both kinds of result: equalities for implementations and bounds for numerical analysis.

## Compilers and hardware

A proof about source code depends on the execution rules assigned to it. Monniaux's paper on the pitfalls of verifying floating-point computations [@monniaux2008] documents several ways those rules can depend on the environment. Where permitted, a compiler may contract multiplication and addition into an FMA, keep an intermediate in an 80-bit register, or reassociate a sum under a fast-math option. A processor may run with flush-to-zero enabled, replacing subnormal results with zero. A call may also observe a rounding mode set by earlier code. Each possibility changes the arithmetic that the proof needs to describe.

When we prove a result about Lean definitions, we still need an argument connecting them to an `addss` instruction before the theorem can tell us anything about that instruction. Certified `ExecFloat` arithmetic is software: the definitions used in proofs are the definitions compiled into the program, and we assume that the Lean compiler correctly implements integer and bit-vector operations.

The optional host operations are exposed through the [unchecked host-arithmetic module](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/NativeFPU/Unchecked.lean), with calls such as `Unchecked.add32`. That module is outside the default `import FloatLib` path. Its hardware calls have separate assumptions from the certified software operations; [chapter 15](#/chapter/performance/comparing-with-leans-native-floats) describes the guards and execution conditions relevant to comparing their results.

<a id="two-decisions-a-specification-has-to-make"></a>

## Overflow policy and the sign of zero

An encoding determines which values the bits can represent. A conversion policy must also determine what to do when the exact input lies outside that set. This distinction matters particularly for small formats with different conventions for infinities and zeros.

The 8-bit format E4M3FN has no infinity. When a positive result is too large to round back to its largest finite value $448$, a conversion policy must choose an outcome. FloatLib supports returning a NaN word or saturating at $448$. Both policies use the same E4M3FN encoding. The field widths do not determine this choice, and a proof under one policy does not establish the other. A [[FloatLib.Numerics.QuantizationPolicy]] argument selects the policy, so the same input can produce different words:

```lean
def exact500 : FloatLib.Numerics.Dyadic :=
  { negative := false, significand := 500, exponent := 0 }

#eval Model.toNatBits <| Model.Policy.roundDyadic FloatFormat.e4m3fn
  QuantizationPolicy.nearestEven 0 exact500
-- 127

#eval Model.toNatBits <| Model.Policy.roundDyadic FloatFormat.e4m3fn
  QuantizationPolicy.saturating 0 exact500
-- 126
```

The word $127$ is `0x7f`, the NaN code; $126$ is `0x7e`, which encodes $448$. [Chapter 09](#/chapter/low-precision-formats-for-machine-learning) has the mathematics of both policies.

Casting between formats also has to preserve any information needed by later operations, including the sign of zero. Converting a value between formats through the rational numbers forgets whether a zero was negative, because $\mathbb{Q}$ has one zero. The exact conversion domain `SignedRat` retains that information: it is a rational together with an IEEE sign bit, whose arithmetic implements the IEEE sign rules. [[FloatLib.Floats.ExecFloat.Binary.decode]] returns such a value and keeps the sign; [[FloatLib.Floats.ExecFloat.Binary.toRat?]] returns a plain rational and does not:

```lean
#eval ExecFloat.Binary.decode ((-(0 : Binary32)) + (-(0 : Binary32)))
-- FloatLib.Numerics.NumericalValue.finite -0

#eval ExecFloat.Binary.decode ((-(0 : Binary32)) + 0)
-- FloatLib.Numerics.NumericalValue.finite 0

#eval ExecFloat.Binary.toRat? (-(0 : Binary32))
-- some 0
```

The theorem `negative_add_of_eq_zero` states the rule for the default nearest-even addition: an exact zero sum is negative exactly when both operands are. [[FloatLib.Floats.ExecFloat.Binary.Conversion.run_default_negZero_value?]] then says that converting an exact $-0$ into any binary destination yields that destination's negative zero, or its single zero when the encoding has only one, as the FNUZ formats do. A cast that lost the sign would still pass tests that compared the two zeros with `==`.

<a id="how-a-proof-assistant-closes-the-gap"></a>

## Connecting an implementation to its specification

The implementation and its specification are Lean functions on the same input words, so we can compare their outputs directly. We want equality for every input, including exceptional values and ties. A separate theorem connects that output to real-number rounding when the inputs and result are finite. This [connection between executable definitions and their proofs](#/chapter/why-execution-and-proofs-are-separate) lets us use a mathematical result while still writing ordinary arithmetic syntax.

Decoding is exact: every finite word denotes a dyadic rational, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.toDyadic?]] computes it without approximation. The reference arithmetic uses exact integer, dyadic, and rational calculations to determine the rounded result. This makes the reference executable without relying on host floating-point arithmetic. Its real-valued counterpart is [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt]], nearest-even rounding on the format's grid with gradual underflow, defined through the Flocq-style theory [@boldoMelquiond2011] developed in [chapter 07](#/chapter/the-mathematics-of-rounding).

Behind `+` there is a reference definition and a set of faster arithmetic kernels. Each certified kernel carries a proof that it agrees with the reference for every input on which it is used. The planner can choose a kernel based on the format and operation while the certificate supplies the same output equation. The certificate record in [chapter 05](#/chapter/why-execution-and-proofs-are-separate) and the planner in [chapter 14](#/chapter/backends-and-the-planner) make that connection explicit. The public equation [[FloatLib.Floats.ExecFloat.Proof.add_eq_spec]] states it for `+` without naming a kernel, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt]] connects the reference to real rounding:

```lean
example (x y : Binary32) : x + y = ExecFloat.Spec.add x y :=
  ExecFloat.Proof.add_eq_spec x y

example (x y : Model FloatFormat.binary32)
    (hx : Model.isFinite x = true)
    (hy : Model.isFinite y = true)
    (hout : Model.isFinite (Model.add x y) = true) :
    Model.toReal (Model.add x y) =
      Model.roundAt FloatFormat.binary32
        (Model.toReal x + Model.toReal y) :=
  Model.toReal_add_eq_roundAt x y (by decide) hx hy hout
```

The hypotheses of the second theorem are mathematically necessary: NaNs and infinities are not reals, and finite inputs can overflow. A caller does not have to compute the output to establish the last one; [[FloatLib.Floats.Formats.BinaryInterchange.Model.isFinite_add_of_abs_add_le_posMaxFinite]] derives it from $|x| + |y| \le \mathrm{maxFinite}$.

Before using that magnitude bound, we should check what it asks of our inputs. It is sufficient, rather than a characterization of every finite sum. If $M$ is the largest finite value, adding $M$ and $-M$ gives zero exactly, but the sum of their absolute values is $2M$ and fails the bound. For a calculation that relies on cancellation, a caller may need a sharper argument about the signed sum. The output-finiteness hypothesis states what must be true; the magnitude bound is one way to prove it.

The dispatcher `AddBackend.word` calls a specialized arithmetic kernel eligible for the format. Any input that kernel declines, including every exceptional case, is handled by the exact generic baseline. The theorem [[FloatLib.Floats.Formats.BinaryInterchange.Model.AddBackend.word_eq_spec]] proves that `word` equals `Model.Spec.add` on every input, including those that use the fallback. [Chapter 13](#/chapter/kernels-fixed-word-algorithms) shows the kernel proofs, and [chapter 14](#/chapter/backends-and-the-planner) explains how kernels are selected and why that choice cannot change a result. [[FloatLib.Floats.ExecFloat.Proof.fullArithmeticCertificate]] packages the six operation equations for a type at once.

Lean checks these proofs by type-checking proof terms and reducing definitions. The arithmetic reasoning is expressed in those terms; it does not require a trusted floating-point decision procedure. The `#print axioms` command reports the axioms used by a theorem, including dependencies inherited from other theorems:

```lean
#print axioms
  FloatLib.Floats.Formats.BinaryInterchange.Model.AddBackend.word_eq_spec
-- 'FloatLib.Floats.Formats.BinaryInterchange.Model.AddBackend.word_eq_spec' depends on axioms: [propext,
--  Classical.choice,
--  Quot.sound]

#print axioms
  FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt
-- 'FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt' depends on axioms: [propext,
--  Classical.choice,
--  Quot.sound]
```

For these two results, the list consists of propositional extensionality, classical choice, and quotient soundness, the usual axioms of classical mathematics in Lean.

## What a proof does not cover

Running the compiled program also requires the Lean compiler to implement the definitions correctly, including substitutions made for faster execution. Calls to host floating-point arithmetic introduce assumptions about the host as well. [Chapter 05](#/chapter/why-execution-and-proofs-are-separate) explains how these execution assumptions differ from the axioms listed by `#print axioms`.

The refinement theorems establish agreement with the formal reference, but that leaves a further question: whether the reference faithfully represents the intended standard. Comparing it with independent implementations can expose a mistake shared by the implementation and its own specification. [Chapter 16](#/chapter/external-validation) describes comparisons with TestFloat, MPFR, published value tables, and host arithmetic that look for such disagreements.

The historical failures discussed in [chapter 03](#/chapter/a-short-history-of-floating-point/what-imprecision-has-cost) also involve assumptions outside an individual arithmetic operation: ranges of physical inputs, accumulation over time, and the model being computed. A proof that addition rounds correctly can support such an analysis, but the application must still establish its own input bounds and error budget.
