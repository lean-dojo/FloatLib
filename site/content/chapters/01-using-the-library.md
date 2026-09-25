---
number: "01"
slug: using-the-library
title: "Getting started with FloatLib"
summary: "Set up a project, compute with binary32, apply an arithmetic theorem, and construct an interval enclosure."
phases: [planner-and-configured, ieee-formats, binary-arithmetic]
---

## Setting up a project

Use the Lean and Mathlib versions specified by FloatLib's [toolchain](https://github.com/lean-dojo/FloatLib/blob/main/lean-toolchain) and [Lake configuration](https://github.com/lean-dojo/FloatLib/blob/main/lakefile.lean). In another Lake project, add the dependency with `require`:

```text
require floatlib from git
  "https://github.com/lean-dojo/FloatLib.git" @ "main"
```

Run `lake update`, `lake exe cache get` to fetch the Mathlib cache, and `lake build`. Put `import FloatLib` at the top of `Main.lean`, and run it with `lake env lean Main.lean`. That import gives us every format family, the inspection commands, and the proof automation used below.

The [basic-operation examples](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Examples/BasicOperations.lean) are complete working programs. In the FloatLib checkout, `lake build FloatLib.Examples` compiles them. In your own file, `#eval` prints a computed value and `#check` prints a type [@leanReference].

<a id="choosing-the-format-once"></a>

## Choosing a format

A format in FloatLib is a Lean type. We'll start with binary32 and give it a name using `abbrev`, which leaves its definition visible to instance resolution and proofs. [[FloatLib.Floats.ExecFloat.Binary]] takes the exponent width and the stored fraction width; the total width, $1 + 8 + 23 = 32$ bits, is derived from them. Instances, backend selection, and theorems then apply to `Binary32` without registration.

The code assumes a file beginning with `import FloatLib`. `open FloatLib.Floats` makes names such as `ExecFloat` available without their namespace prefix. The annotation `: Binary32` chooses the format for `x` and `y`, including how their literals are rounded. The scoped `open` enables `+∞` and `-∞` as rounding directions for the interval example below.

```lean
open FloatLib.Floats
open scoped FloatLib.IEEERounding

abbrev Binary32 := ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)

def x : Binary32 := 1.5
def y : Binary32 := 2.25

#eval x + y
-- 3.75
#eval ExecFloat.sqrt y
-- 1.5
#eval x / 3
-- 0.5
```

The 23 stored fraction bits give 24 bits of precision for normal values because the leading one is implicit. Thus `x + y` selects binary32 addition, and the `3` in `x / 3` is another binary32 value. Changing the abbreviation changes the format throughout the program.

The library reads a literal as an exact rational and rounds it once to the chosen format, using nearest rounding with ties to even. Both `1.5` and `2.25` are dyadic, so nothing is lost. These three computations also have exactly representable answers.

## Arithmetic and exact stored values

Now try inputs that need rounding. Ordinary arithmetic operators also use nearest-even rounding:

```lean
#eval (0.1 : Binary32) + 0.2
-- 5033165 * 2^-24
#eval ((0.1 : Binary32) + 0.2) == 0.3
-- true
#eval ExecFloat.Binary.toRat? ((0.1 : Binary32) + 0.2)
-- some (5033165 / 16777216)
```

Neither $0.1$ nor $0.2$ is a finite binary fraction. Each literal is rounded when it is read, and their sum is rounded once more. The stored result is $5033165 \cdot 2^{-24}$, which equals the rounded binary32 literal `0.3`. [[FloatLib.Floats.ExecFloat.Binary.toRat?]] returns this exact rational and returns `none` for NaN and infinity. [The next chapter](#/chapter/from-reals-to-machine-numbers) works out the stored values and explains why the equality changes at binary64 precision.

`#eval` prints the exact stored number: as a decimal when it has a short exact decimal expansion, and otherwise as an integer times a power of two. Formatting does not convert through a host float and round again. String interpolation uses the same formatter, so `s!"sum = {x + y}"` gives `sum = 3.75`.

The `true` result compares two stored numbers; neither side is the exact rational three tenths. Here `==` is IEEE numerical equality: it treats the signed zeros as equal and every comparison of a NaN with itself as false. The `=` in the proof below means equality of stored words. It distinguishes the zeros and makes every word, including a NaN, equal to itself.

<a id="what-the-theorems-give-you"></a>

## Proving arithmetic agrees with its specification

Our first proof covers every pair of inputs. [[FloatLib.Floats.ExecFloat.Proof.add_eq_spec]] states that executable addition, whichever backend the planner selected, equals the format's reference addition [[FloatLib.Floats.ExecFloat.Spec.add]]. Since `+` calls `ExecFloat.add`, we can apply it to a goal written with ordinary notation:

```lean
example (a b : Binary32) : a + b = ExecFloat.Spec.add a b :=
  ExecFloat.Proof.add_eq_spec a b
```

This equation identifies the complete result word, including exceptional results. Interpreting a finite result as a rounded real sum requires additional finiteness hypotheses; [the numerical-model chapter](#/chapter/the-numerical-models/the-rounding-contract-as-a-statement-about-reals) explains them, and [a further example](#/chapter/further-examples/the-result-as-a-real-number) carries out that proof on the configured type.

<a id="a-tour-of-the-codebase"></a>
<a id="library-structure"></a>

The proof connects three parts of the source. [Numerics](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Numerics) defines exact values and contracts. [Kernels](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Kernels) supplies integer algorithms with refinement proofs. [Floats](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats) gives words their format and connects the executable operations to those algorithms.

![Exact values in Numerics, integer algorithms in Kernels, and configured formats in Floats.](assets/ch19-layers.png "An executable operation is connected to its exact-value specification by a refinement proof.")

[Chapter 05](#/chapter/why-execution-and-proofs-are-separate) follows the implementation and its certificate. The [theorem guide](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/THEOREMS.md) lists the public arithmetic theorems with their imports and hypotheses.

<a id="rounding-directions-and-status-flags"></a>

## An interval from two directed roundings

One third is between two binary32 values. To enclose it, compute the quotient once toward $-\infty$ and once toward $+\infty$. The `divWithRounding` operation takes that direction explicitly; ordinary `/` would select nearest-even rounding.

[[FloatLib.Floats.ExecFloat.Binary.Interval]] keeps both endpoints in the configured scalar type. `Interval.ofBounds` builds an interval from two values, falling back to the whole range when the pair is unordered or a NaN. Its arithmetic calls the descriptor model's directed operations, with endpoint conversion handled inside the library. Below, the two endpoints of each interval are the same quotient rounded toward $-\infty$ and toward $+\infty$, and `Interval.add` adds lower endpoints downward and upper endpoints upward.

```lean
open ExecFloat.Binary (Interval)

def enclose (lo hi : Binary32) := Interval.ofBounds lo hi

def oneThird := enclose (ExecFloat.Binary.divWithRounding 1 3 (rounding := -∞))
  (ExecFloat.Binary.divWithRounding 1 3 (rounding := +∞))
def twoThirds := enclose (ExecFloat.Binary.divWithRounding 2 3 (rounding := -∞))
  (ExecFloat.Binary.divWithRounding 2 3 (rounding := +∞))

def total := Interval.add oneThird twoThirds

#eval (oneThird.lo, oneThird.hi)
-- (5592405 * 2^-24, 11184811 * 2^-25)
#eval (twoThirds.lo, twoThirds.hi)
-- (5592405 * 2^-23, 11184811 * 2^-24)
#eval (total.lo, total.hi)
-- (16777215 * 2^-24, 8388609 * 2^-23)

example {x y : ℝ}
    (hA : Interval.Valid oneThird) (hB : Interval.Valid twoThirds)
    (hx : Interval.RealMem oneThird x) (hy : Interval.RealMem twoThirds y) :
    Interval.ERealMem (Interval.add oneThird twoThirds) ((x + y : ℝ) : EReal) :=
  Interval.add_sound oneThird twoThirds (by decide) hA hB hx hy
```

The two lower endpoints add exactly, $5592405 \cdot 2^{-24} + 5592405 \cdot 2^{-23} = 16777215 \cdot 2^{-24} = 1 - 2^{-24}$, while the two upper endpoints sum to $1 + 2^{-25}$, which binary32 cannot hold, so upward rounding gives $1 + 2^{-23}$. The enclosure $[1 - 2^{-24}, 1 + 2^{-23}]$ contains $1 = \tfrac13 + \tfrac23$, as it must.

The theorem at the end is [[FloatLib.Floats.ExecFloat.Binary.Interval.add_sound]] applied to these two intervals: whenever both are valid (finite, ordered endpoints) and enclose reals $x$ and $y$, the sum interval encloses $x + y$. It follows from [[FloatLib.Floats.Formats.BinaryInterchange.Model.Interval.add_sound]] by decoding the endpoints. The statement uses the extended reals to allow an upper endpoint to overflow to $+\infty$. Here the validity and membership facts are left as hypotheses; the directed-rounding bounds of [chapter 08](#/chapter/ieee-binary-formats), `toEReal_divDown_le` and its upward counterpart, establish them for these particular words. The `by decide` settles only the descriptor hypothesis.

Using the output in another addition, subtraction, multiplication, or division soundness theorem requires finite `Valid` bounds again. An infinite endpoint is allowed in the enclosure conclusion, but does not satisfy that next operation's finite-input premise.

`RealMem oneThird x` states that the decoded endpoints bracket `x`; it does not force `x` to be representable. That is how an interval with binary endpoints can make a claim about the exact real one third. The [endpoint-adapter recipe](#/chapter/further-examples/choosing-a-different-endpoint-format) uses the same enclosure idea with decimal and posit bounds.

To check whether a directed quotient was exact, use its `WithStatus` form. The pair's `.1` field holds the result and `.2` holds the five IEEE status flags:

```lean
def thirdDown := ExecFloat.Binary.divWithStatus (1 : Binary32) 3 (rounding := -∞)

#eval thirdDown.2.inexact
-- true
```

This flag describes division of the stored operands; it does not include any earlier rounding of input literals. Statuses are ordinary returned data, and `IEEEStatus.union` combines them across operations. [Further examples](#/chapter/further-examples/rounding-directions-and-status-flags) compare the four directions and the different causes of exceptional results.

<a id="asking-a-type-what-it-is"></a>

## Inspecting a format

Use `#float_info` to find a type's numerical properties, selected implementation, and available theorems:

```lean
#float_info Binary32
#float_info [errors] Binary32
```

For `Binary32`, the useful entries are:

| Report entry | What it tells us |
| --- | --- |
| Storage and precision | A packed `UInt32`, with 23 stored fraction bits and 24 significant bits for normal values. |
| Execution | The planner selects a fixed-format word kernel for the six arithmetic operations. |
| Error bounds | Nearest-even rounding has a half-ulp absolute-error bound; when the exact value is in the nonzero normal range, the relative bound is $2^{-24}$. |

`#float_info! Binary32` expands the report, including the planner's cost estimates. `#float_info! [errors] Binary32` gives the full theorem hypotheses. These are type-level contracts: applying them to a particular expression still requires the relevant finiteness, domain, and range proofs. `#float_help` lists the command options.

## Further examples

The next chapter explains the binary representation used here. For a particular programming task, the [further examples](#/chapter/further-examples) are independent recipes:

- [Decimal or posit interval endpoints](#/chapter/further-examples/choosing-a-different-endpoint-format), with explicit failure when finite bounds cannot enclose the result.
- [Sums and dot products](#/chapter/further-examples/sums-and-dot-products-with-one-rounding) that retain exact intermediates until one final rounding.
- [Real-valued proofs](#/chapter/further-examples/the-result-as-a-real-number) for configured arithmetic.
- [Mixed formats and round-once expressions](#/chapter/further-examples/mixing-formats), with explicit destinations and conversion status.
- [Complex arithmetic](#/chapter/further-examples/complex-arithmetic), keeping the scalar rounding steps in the specification.

That chapter also covers [smaller and optional imports](#/chapter/further-examples/choosing-imports) and [adding a backend or format](#/chapter/further-examples/extending-the-library).
