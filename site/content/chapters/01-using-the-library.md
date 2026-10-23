---
number: "01"
slug: using-the-library
title: "Getting started with FloatLib"
summary: "Set up a project, compute with binary32, apply an arithmetic theorem, and construct an interval enclosure."
phases: [planner-and-configured, ieee-formats, binary-arithmetic]
---

## Setting up a project

Use the Lean and Mathlib versions specified by FloatLib's [toolchain](https://github.com/lean-dojo/FloatLib/blob/main/lean-toolchain) and [Lake configuration](https://github.com/lean-dojo/FloatLib/blob/main/lakefile.lean). In your own Lake project, add FloatLib with `require`:

```text
require floatlib from git
  "https://github.com/lean-dojo/FloatLib.git" @ "main"
```

Run `lake update`, then `lake exe cache get` to fetch the Mathlib cache, then `lake build`. Now put `import FloatLib` at the top of `Main.lean` and run the file with `lake env lean Main.lean`. That one import gives you every format family, the inspection commands, and the proof automation we use below.

If you'd rather start from working code, the [basic-operation examples](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Examples/BasicOperations.lean) are complete programs, and `lake build FloatLib.Examples` compiles them in the FloatLib checkout. In your own file, `#eval` prints a computed value and `#check` prints a type [@leanReference].

## Choosing a format

A format in FloatLib is a Lean type. The annotation `: Binary32` chooses the format for `x` and `y`, including how their literals are rounded. The code assumes a file beginning with `import FloatLib`. `open FloatLib.Floats` makes names such as `ExecFloat` available without their namespace prefix, and `open FloatLib.Rounding` does the same for rounding directions such as `up` and `down`.

```lean
open FloatLib.Floats
open FloatLib.Rounding

def x : Binary32 := 1.5
def y : Binary32 := 2.25

#eval x + y
-- 3.75
#eval ExecFloat.sqrt y
-- 1.5
#eval x / 3
-- 0.5
#eval ExecFloat.Binary.div x 3 (mode := up) (status := true)
-- { value := 0.5,
--   status := { invalid := false, divideByZero := false, overflow := false, underflow := false, inexact := false },
--   ternary := Ordering.eq }
```

The named binary formats are `Binary16`, `BFloat16`, `Binary32`, `Binary64`, `Binary128`, and `Binary256`, and for posits they run from `Posit8` to `Posit64`.

`Binary32` abbreviates [[FloatLib.Floats.ExecFloat.Binary]] `(exponentBits := 8) (fractionBits := 23)`. That constructor takes the exponent width and the stored fraction width, and it derives the total width from them, $1 + 8 + 23 = 32$ bits. Any other layout is the same constructor with other widths, and you don't have to register it, because instances, backend selection, and theorems apply to every such type. Those 23 stored fraction bits give 24 bits of precision for normal values, because the leading one is implicit.

With those annotations, `x + y` is binary32 addition and the `3` in `x / 3` is another binary32 value. The nice thing is how little you have to touch to switch formats. Change `Binary32` to `Binary64` in the two annotations and the same program runs in binary64.

Each operation has one name, and options pick the variant. The last line passes two options to `ExecFloat.Binary.div`. `(mode := up)` rounds toward $+\infty$, and `(status := true)` returns the exception flags and the ternary value [described below](#/chapter/using-the-library/an-interval-from-two-directed-roundings) along with the result. Without options, a call rounds to nearest with ties to even and returns just the value, which is what `x / 3` does. A literal is read as an exact rational and rounded once to the chosen format, also to nearest with ties to even. Both `1.5` and `2.25` are dyadic, so nothing is lost, and every answer here is exactly representable too. That's why the last line comes back with all its flags clear.

## Arithmetic and exact stored values

The decimals `0.1` and `0.2` do need rounding, and the printed answer can hide that. Try the sum, compare it with the literal `0.3`, and then ask for its exact stored value:

```lean
#eval (0.1 : Binary32) + 0.2
-- 0.3
#eval ((0.1 : Binary32) + 0.2) == 0.3
-- true
#eval ExecFloat.Binary.toRat? ((0.1 : Binary32) + 0.2)
-- some (5033165 / 16777216)
```

Neither $0.1$ nor $0.2$ is a finite binary fraction, so each literal is rounded when it's read, and the sum is rounded once more. What ends up stored is $5033165 \cdot 2^{-24}$, which is also the value of the rounded binary32 literal `0.3`. [[FloatLib.Floats.ExecFloat.Binary.toRat?]] returns that exact rational, or `none` for NaN and infinity. [The next chapter](#/chapter/from-reals-to-machine-numbers) works out the stored values and explains why the equality no longer holds at binary64 precision.

`#eval` prints a decimal that reads back as the stored number, normally the shortest one. So the sum prints as `0.3`, even though its stored value is $0.300000011920928955078125$, while a value with a short exact expansion, such as $3.75$, prints in full. Formatting never goes through a host float and rounds a second time. String interpolation uses the same formatter, so `s!"sum = {x + y}"` gives `sum = 3.75`.

The `true` compares two stored numbers; neither is the exact rational three tenths. Here `==` is IEEE numerical equality, which treats the two signed zeros as equal and says a NaN isn't equal to itself :) In the proof below, `=` means equality of stored words instead. It tells the zeros apart, and every word, NaN included, is equal to itself.

<a id="what-the-theorems-give-you"></a>

## Proving arithmetic agrees with its specification

The evaluations above give answers for particular inputs. To justify the operation for arbitrary inputs, we use its refinement theorem. [[FloatLib.Floats.ExecFloat.Proof.add_eq_spec]] says that executable addition equals the format's reference addition [[FloatLib.Floats.ExecFloat.Spec.add]], whichever backend the planner picked. Since `+` calls `ExecFloat.add`, you can apply it to a goal written in ordinary notation:

```lean
example (a b : Binary32) : a + b = ExecFloat.Spec.add a b :=
  ExecFloat.Proof.add_eq_spec a b
```

This equation pins down the whole result word, exceptional results included, and it needs no hypotheses at all. Hypotheses come in when you want to read a finite result as a rounded real sum, which takes the extra finiteness assumptions that [the numerical-model chapter](#/chapter/the-numerical-models/the-rounding-contract-as-a-statement-about-reals) explains. [A further example](#/chapter/further-examples/the-result-as-a-real-number) carries out that proof on the configured type.

<a id="library-structure"></a>

That proof ties together three parts of the source. [Numerics](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Numerics) defines exact values and contracts, [Kernels](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Kernels) supplies integer algorithms with refinement proofs, and [Floats](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats) gives words their format and connects the executable operations to those algorithms. In [Figure 1.1](#/chapter/using-the-library/figure-ch19-layers), follow one binary32 addition down the two arrows. Floats calls the kernel's align, add and round steps, and those steps are proved using the dyadics and rounding laws in Numerics.

![Exact values in Numerics, integer algorithms in Kernels, and configured formats in Floats.](assets/ch19-layers.png "An executable operation is connected to its exact-value specification by a refinement proof.")

If you want to see how that addition is put together, [Chapter 05](#/chapter/why-execution-and-proofs-are-separate) follows the implementation and its certificate, and the [theorem guide](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/THEOREMS.md) lists the public arithmetic theorems with their imports and hypotheses.

<a id="rounding-directions-and-status-flags"></a>

## An interval from two directed roundings

One third falls between two binary32 values. Rounding downward gives us a lower bound, and rounding upward gives an upper bound, so two divisions enclose the exact real quotient even though neither endpoint equals it. You pass the direction through the `mode` option of `ExecFloat.Binary.div`, because ordinary `/` would round to nearest-even.

[[FloatLib.Floats.ExecFloat.Binary.Interval]] keeps both endpoints in the configured scalar type. `Interval.ofBounds` builds an interval from two values, and when the pair is unordered or a NaN, it falls back to the whole range. Interval arithmetic calls the descriptor model's directed operations, and the library handles the endpoint conversion itself. In the code below, each interval's two endpoints are the same quotient rounded toward $-\infty$ and toward $+\infty$, and `Interval.add` adds the lower endpoints downward and the upper endpoints upward.

```lean
open ExecFloat.Binary (Interval)

def enclose (lo hi : Binary32) := Interval.ofBounds lo hi

def oneThird := enclose (ExecFloat.Binary.div 1 3 (mode := down))
  (ExecFloat.Binary.div 1 3 (mode := up))
def twoThirds := enclose (ExecFloat.Binary.div 2 3 (mode := down))
  (ExecFloat.Binary.div 2 3 (mode := up))

def total := Interval.add oneThird twoThirds

#eval (oneThird.lo, oneThird.hi)
-- (0.3333333, 0.33333334)
#eval (twoThirds.lo, twoThirds.hi)
-- (0.6666666, 0.6666667)
#eval (total.lo, total.hi)
-- (0.99999994, 1.0000001)

theorem oneThird_valid : Interval.Valid oneThird := by decide +kernel
theorem twoThirds_valid : Interval.Valid twoThirds := by decide +kernel
theorem total_valid : Interval.Valid total := by decide +kernel

theorem oneThird_mem : Interval.RealMem oneThird (1 / 3) := by
  rw [Interval.realMem_iff,
    ExecFloat.Binary.toReal_of_toRat?_eq_some (q := 5592405 / 2 ^ 24) (by decide +kernel),
    ExecFloat.Binary.toReal_of_toRat?_eq_some (q := 11184811 / 2 ^ 25) (by decide +kernel)]
  norm_num

theorem twoThirds_mem : Interval.RealMem twoThirds (2 / 3) := by
  rw [Interval.realMem_iff,
    ExecFloat.Binary.toReal_of_toRat?_eq_some (q := 5592405 / 2 ^ 23) (by decide +kernel),
    ExecFloat.Binary.toReal_of_toRat?_eq_some (q := 11184811 / 2 ^ 24) (by decide +kernel)]
  norm_num

theorem total_mem : Interval.RealMem total 1 := by
  have h := Interval.add_sound oneThird twoThirds (by decide) oneThird_valid twoThirds_valid
    oneThird_mem twoThirds_mem
  rw [show (1 / 3 + 2 / 3 : ℝ) = 1 by norm_num] at h
  exact (Interval.eRealMem_coe_iff_of_valid total_valid 1).mp h
```

We can check the enclosure of one by hand. Adding the two lower endpoints is exact, $5592405 \cdot 2^{-24} + 5592405 \cdot 2^{-23} = 16777215 \cdot 2^{-24} = 1 - 2^{-24}$. The upper endpoints sum to $1 + 2^{-25}$, which binary32 can't hold, so rounding upward gives $1 + 2^{-23}$. The enclosure $[1 - 2^{-24}, 1 + 2^{-23}]$ contains $1 = \tfrac13 + \tfrac23$, as it must.

The evaluations print the endpoints, and the theorems prove validity and membership. An interval is valid when its endpoints are finite and ordered. That's decidable, so `decide +kernel` checks it by evaluating the endpoints in Lean's kernel. Membership takes three steps. `Interval.realMem_iff` turns `RealMem oneThird (1 / 3)` into $\operatorname{lo} \le 1/3 \le \operatorname{hi}$ for the endpoints' real values. Then `toReal_of_toRat?_eq_some` replaces each real value with the exact rational that the kernel computes for the stored word, and finally `norm_num` compares those rationals with $1/3$.

`total_mem` doesn't compute the sum's endpoints at all. Instead it applies [[FloatLib.Floats.ExecFloat.Binary.Interval.add_sound]] to the two intervals. That theorem says that whenever both are valid and enclose reals $x$ and $y$, the sum interval encloses $x + y$, and it follows from [[FloatLib.Floats.Formats.BinaryInterchange.Model.Interval.add_sound]] by decoding the endpoints. Its conclusion lives in the extended reals, so that an upper endpoint is allowed to overflow to $+\infty$. `eRealMem_coe_iff_of_valid` brings a valid result back to the reals, and `by decide` settles the descriptor hypothesis.

To feed the result into another addition, subtraction, multiplication, or division soundness theorem, we need finite `Valid` bounds again. An infinite endpoint is fine in the enclosure's conclusion, but it doesn't meet the next operation's finite-input premise.

`RealMem oneThird x` says that the decoded endpoints bracket `x`, and `x` doesn't have to be representable. Our endpoints are binary values, but the membership theorem is about the exact real one third. For decimal and posit bounds, the [endpoint-adapter recipe](#/chapter/further-examples/choosing-a-different-endpoint-format) uses the same enclosure idea.

Sometimes you also want to know whether a directed quotient was exact. For that, add `(status := true)`. In the returned outcome, the `value` field holds the result and `status` holds the five IEEE status flags. `ternary` says whether the result lies below, at, or above the exact quotient, the way MPFR's ternary value does:

```lean
def thirdDown := ExecFloat.Binary.div (1 : Binary32) 3 (mode := down) (status := true)

#eval thirdDown.status.inexact
-- true
#eval thirdDown.ternary
-- Ordering.lt
```

That flag is about dividing the stored operands, and it knows nothing about any earlier rounding of the input literals. Statuses are ordinary returned data, so you can combine them across operations with `IEEEStatus.union`. [Further examples](#/chapter/further-examples/rounding-directions-and-status-flags) compare four rounding directions and the different causes of exceptional results.

## Inspecting a format

You can also ask the library about a format itself. `#float_info` shows you a type's numerical properties, its selected implementation, and the theorems available for it:

```lean
#float_info Binary32
#float_info [errors] Binary32
```

For `Binary32`, the report includes these entries:

| Report entry | What it tells us |
| --- | --- |
| Storage and precision | A packed `UInt32`, with 23 stored fraction bits and 24 significant bits for normal values. |
| Execution | The planner selects a fixed-format word kernel for the six arithmetic operations. |
| Error bounds | Nearest-even rounding has a half-ulp absolute-error bound; when the exact value is in the nonzero normal range, the relative bound is $2^{-24}$. |

The report opens with the format's constants. The largest finite binary32 value is $(2 - 2^{-23}) \cdot 2^{127} \approx 3.40282 \cdot 10^{38}$, machine epsilon is $2^{-23}$, and the least normal and subnormal values are there too. If you want the same constants as values of the type, they're `ExecFloat.Binary.maxFinite`, `minNormal`, `minSubnormal`, and `epsilon`, and `ExecFloat.Binary.ulp x` gives the spacing of the values around `x`.

`#float_info! Binary32` expands the report and adds the planner's cost estimates, and `#float_info! [errors] Binary32` gives the full theorem hypotheses. Those are type-level contracts, so to apply one to a particular expression, you still need the relevant finiteness, domain, and range proofs. `#float_help` lists the command options, for when you forget them :)

## Further examples

The [further examples](#/chapter/further-examples) build on these operations and proofs:

- [Decimal or posit interval endpoints](#/chapter/further-examples/choosing-a-different-endpoint-format), which report a failure when finite bounds can't enclose the result.
- [Sums and dot products](#/chapter/further-examples/sums-and-dot-products-with-one-rounding) that keep exact intermediates until a single final rounding.
- [Real-valued proofs](#/chapter/further-examples/the-result-as-a-real-number) for configured arithmetic.
- [Mixed formats and round-once expressions](#/chapter/further-examples/mixing-formats), with declared destinations and conversion status.
- [Complex arithmetic](#/chapter/further-examples/complex-arithmetic), keeping the scalar rounding steps in the specification.

That chapter also covers [smaller and optional imports](#/chapter/further-examples/choosing-imports) and [adding a backend or format](#/chapter/further-examples/extending-the-library).
