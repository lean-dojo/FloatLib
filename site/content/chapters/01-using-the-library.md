---
number: "01"
slug: using-the-library
title: "FloatLib for absolute beginners"
summary: "Set up FloatLib, do arithmetic in a floating-point format, see the exact value of each result, choose a rounding direction, read the status flags and prove a first theorem."
phases: [planner-and-configured, ieee-formats, binary-arithmetic]
---

Welcome to the absolute beginner's guide to FloatLib. FloatLib is a library of floating-point arithmetic, the arithmetic computers use for numbers like $0.1$ and $3.75$, written in Lean 4, a programming language that also checks proofs. You can compute with it as with any number library, see which number was really stored, choose which way each result rounds, and prove theorems about the code that ran. By the end of this chapter you will have done all four.

## What is a floating-point number?

A computer keeps each number in a fixed number of bits, so it can't keep every real number. A finite binary floating-point number is an integer with a limited number of binary digits times a power of two, like scientific notation in base two. The power of two moves, or floats, the binary point, hence the name. A format fixes how many bits each part gets. Two common formats are binary32 and binary64, the 32-bit and 64-bit binary formats of the IEEE 754 standard. Most real numbers, $0.1$ among them, don't fit a format exactly, so the format stores a nearby number that does. That step is called rounding.

Rounding can surprise you. Add 0.1 and 0.2 in binary32, and `0.1 + 0.2 == 0.3` comes back `true`. Ask binary64 the same thing and it comes back `false`. You don't have to take either answer on faith. Switching between the two formats only means changing a type annotation, and FloatLib shows you exactly which two numbers each comparison saw. It even proves things about the additions that made them.

## How to set up a project

To follow along, you need a project built with Lake, Lean's build tool, that depends on FloatLib. You also need Mathlib, Lean's mathematics library. Use the Lean and Mathlib versions that FloatLib's [toolchain](https://github.com/lean-dojo/FloatLib/blob/main/lean-toolchain) and [Lake configuration](https://github.com/lean-dojo/FloatLib/blob/main/lakefile.lean) specify, then add FloatLib with `require`:

```text
require floatlib from git
  "https://github.com/lean-dojo/FloatLib.git" @ "main"
```

Run `lake update`, then `lake exe cache get` to download Mathlib already compiled, then `lake build`. Put `import FloatLib` at the top of `Main.lean` and run the file with `lake env lean Main.lean`. That one import brings in every format family, the inspection commands and the proof automation we'll use on this page. If you'd rather start from working code, the [basic-operation examples](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Examples/BasicOperations.lean) are complete programs, and `lake build FloatLib.Examples` compiles them in the FloatLib checkout. For smaller imports, see [Which import do you need?](#/chapter/using-the-library/which-import-do-you-need)

## How to read the example code

Here is the Lean syntax the examples use. `def` names a value, `theorem` states a fact with its proof, `example` is a theorem without a name, and `by` starts a proof built by tactics, commands that each do one proof step. `#eval` prints a computed value and `#check` prints a type [@leanReference], and the `-- ` line under each `#eval` shows what Lean prints. The examples assume that import, and `open FloatLib.Floats` lets you write names such as `ExecFloat` without the prefix of their namespace, a folder-like group of names. A few examples are complete files and carry their own `import` line.

## How to pick a format

In FloatLib a format is a Lean type, so you pick it the way you'd pick any type, with a type annotation. Below, `: Binary32` picks the format for `x` and `y`, and with it how their literals, the numbers written in the code, are rounded. If you start with these two numbers, you can add them, take a square root and divide with:

```lean
open FloatLib.Floats

def x : Binary32 := 1.5
def y : Binary32 := 2.25

#eval x + y
-- 3.75
#eval ExecFloat.sqrt y
-- 1.5
#eval x / 3
-- 0.5
#eval ExecFloat.Binary.div x 3 (mode := .up) (status := true)
-- { value := 0.5, status := {}, ternary := Ordering.eq }
```

With those annotations, `x + y` is binary32 addition, and the `3` in `x / 3` is a binary32 value too. So switching formats is a two-word edit: change `Binary32` to `Binary64` in the two annotations, and the same program runs in binary64.

A call without options, like `x / 3`, rounds to nearest, ties to even, and returns just the value. That means it takes the representable number (one the format holds exactly) closest to the exact answer, and on an exact tie the one whose last binary digit is zero. An answer too big for the format becomes infinity instead, as we'll see in the flags below. Literals are read as exact rationals and rounded once to the format, also to nearest-even.

The last line adds options. Each operation has one name, and options pick the variant: `(mode := .up)` rounds toward $+\infty$, and `(status := true)` returns the exception flags and the ternary value [described below](#/chapter/using-the-library/how-to-read-the-status-flags) with the result. `1.5` and `2.25` are dyadic, fractions whose denominator is a power of two, and every answer here is representable, so binary32 holds it exactly and the status is empty, `{}`. A status prints only the flags that were raised, so `{ inexact := true }` would mean rounding changed the value.

## Which formats can you use?

For binary formats the named types are `Binary16`, `BFloat16`, `Binary32`, `Binary64`, `Binary128` and `Binary256`, and for posits, a different family of formats, they run from `Posit8` to `Posit64`.

You can also make your own. `Binary32` is just a name for [[FloatLib.Floats.ExecFloat.Binary]] `(exponentBits := 8) (fractionBits := 23)`: 8 exponent bits, 23 stored fraction bits and a sign bit, $1 + 8 + 23 = 32$ bits in all. It has 24 bits of precision (significant binary digits) for normal values, the ordinary kind, because their leading one is implicit, known without being stored. Any other layout is the same constructor with other widths, and there's nothing to register: the operations, the backend selection and the theorems all work for every such type.

## How to see the exact value

Now back to the question we started with. Unlike `1.5` and `2.25`, decimals such as `0.1` and `0.2` do need rounding, and the printed answer hides it well. If you add them, compare the sum with `0.3` and ask what was actually stored, you get:

```lean
#eval (0.1 : Binary32) + 0.2
-- 0.3
#eval ((0.1 : Binary32) + 0.2) == 0.3
-- true
#eval ExecFloat.Binary.toRat? ((0.1 : Binary32) + 0.2)
-- some (5033165 / 16777216)
```

Neither $0.1$ nor $0.2$ is a finite binary fraction, so each literal is rounded when it's read, and the sum is rounded once more. Three roundings later, what's stored is $5033165 \cdot 2^{-24}$, and the binary32 literal `0.3` lands on that same number. That's why the comparison says `true`. [[FloatLib.Floats.ExecFloat.Binary.toRat?]] returns that exact rational, or, as the `?` in its name warns, `none` for NaN ("not a number") and infinity. [The next chapter](#/chapter/from-reals-to-machine-numbers) works out the stored values and explains why the equality breaks at binary64 precision.

**Note:** That `true` compares two stored numbers, neither of them the exact rational three tenths. `==` is IEEE numerical equality, which treats the positive and the negative zero as equal and says a NaN isn't equal to itself :) In proofs, `=` between two values of a format means equality of their stored bits, which we call the value's word. It tells the zeros apart, and every word, NaN included, equals itself.

## Why does the sum print as 0.3?

So why does the first line say `0.3`? Because `#eval` prints a decimal that converts back to the stored number, normally the shortest one. Think of `0.3` as a short name for the sum's stored value $0.300000011920928955078125$, while $3.75$ has a short exact expansion and prints in full. Formatting never goes through a host float, the machine's own hardware number, so it never rounds a second time. String interpolation with `s!` uses the same formatter: `s!"sum = {x + y}"` gives `sum = 3.75`.

## How to choose a rounding direction

When the exact answer falls between two numbers of the format, the rounding direction decides which neighbour you get. Ordinary arithmetic, `x.sqrt` and `x.fma y z` (fused multiply-add, $x \cdot y + z$ rounded once) round to nearest even. Each of the six arithmetic operations, such as [[FloatLib.Floats.ExecFloat.Binary.add]] or [[FloatLib.Floats.ExecFloat.Binary.div]], also takes a direction from [[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEERoundingMode]] as `(mode := ...)`. Let's look at one divided by three in four directions, nearest, up toward $+\infty$, down toward $-\infty$ and toward zero:

```lean standalone
import FloatLib

open FloatLib.Floats

#eval ExecFloat.Binary.div (1 : Binary32) 3 (mode := .nearest)
-- 0.33333334
#eval ExecFloat.Binary.div (1 : Binary32) 3 (mode := .up)
-- 0.33333334
#eval ExecFloat.Binary.div (1 : Binary32) 3 (mode := .down)
-- 0.3333333
#eval ExecFloat.Binary.div (1 : Binary32) 3 (mode := .towardZero)
-- 0.3333333
```

Those are the two binary32 neighbours of one third, $11184810 \cdot 2^{-25}$, about $0.33333331$, and $11184811 \cdot 2^{-25}$. Nearest agrees with up because one third is closer to the upper neighbour, and down agrees with toward zero because the value is positive.

**Note:** Conversions between formats, such as `cast` in [mixing formats](#/chapter/ieee-binary-formats/how-to-mix-formats), take their direction from a different type, `Numerics.RoundingMode`. Writing `(mode := .down)` works for both, because the leading dot looks the name up in whatever type the call expects.

## How to read the status flags

A direction decides which neighbour you get, and the flags tell you what happened in that one operation. IEEE 754 asks each operation to report five conditions: invalid, divide by zero, overflow, underflow and inexact. The standard calls them exceptions, though nothing is thrown.

With `(status := true)` the result comes with a receipt. `value` is the result, `status` holds the five Booleans as an [[FloatLib.Numerics.IEEEStatus]], and `ternary`, named for its three possible answers, says whether the value lies below, at or above the exact result, the way the MPFR library's ternary value does. [[FloatLib.Floats.Formats.BinaryInterchange.Model.value_add]] states that asking for status doesn't change the value addition returns. Here are some examples, the downward third and three operations that go wrong:

```lean standalone
import FloatLib

open FloatLib.Floats

#eval ExecFloat.Binary.div (1 : Binary32) 3 (mode := .down) (status := true)
-- { value := 0.3333333, status := { inexact := true }, ternary := Ordering.lt }
#eval ExecFloat.Binary.div (1 : Binary32) 0 (status := true)
-- { value := inf, status := { divideByZero := true }, ternary := Ordering.eq }
#eval ExecFloat.Binary.mul (1e30 : Binary32) 1e30 (status := true)
-- { value := inf, status := { overflow := true, inexact := true }, ternary := Ordering.gt }
#eval ExecFloat.Binary.mul (1e-30 : Binary32) 1e-30 (status := true)
-- { value := 0, status := { underflow := true, inexact := true }, ternary := Ordering.lt }

def thirdDown := ExecFloat.Binary.div (1 : Binary32) 3 (mode := .down) (status := true)
def oneOverZero := ExecFloat.Binary.div (1 : Binary32) 0 (status := true)

#eval FloatLib.Numerics.IEEEStatus.union thirdDown.status oneOverZero.status
-- { divideByZero := true, inexact := true }
```

Rounding changed the first value, so only `inexact` is set. $1/0$ with a positive zero denominator returns $\infty$ and sets divide-by-zero, as IEEE specifies. $10^{30} \cdot 10^{30}$ overflows, too large for binary32, and overflow always comes with inexact. $10^{-30} \cdot 10^{-30}$ lies far below the least binary32 subnormal, the smallest positive binary32 number, so it becomes zero with underflow and inexact.

Statuses are ordinary returned data, with no global sticky register (one where a raised flag stays raised) collecting flags behind your back. `thirdDown.status.inexact` reads one flag without throwing the value away. For a whole computation, carry the statuses alongside its values and combine them with [[FloatLib.Numerics.IEEEStatus.union]], as the last line does. [Chapter 05](#/chapter/ieee-binary-formats) has the theorems that say when each flag is set.

**Note:** Each status describes one operation on its stored operands. It knows nothing about earlier rounding, such as the rounding that created a decimal literal or an input.

## How to prove your first theorem

So far every answer has come from an `#eval`, and an `#eval` answers for one input. A theorem answers for every input, and Lean checks its proof. Let's prove one about addition. Addition has a reference definition, a short specification of what it should compute, and a refinement theorem saying the code that runs agrees with it (the code refines the specification, filling in how to compute it). FloatLib can run an addition with different implementations, called backends, and a part of the library called the planner picks one. [[FloatLib.Floats.ExecFloat.Proof.add_eq_spec]] says the executable addition equals the reference addition [[FloatLib.Floats.ExecFloat.Spec.add]], whichever backend the planner picked. Since `+` calls `ExecFloat.add`, you can state it for two binary32 values in ordinary notation:

```lean
example (a b : Binary32) : a + b = ExecFloat.Spec.add a b :=
  ExecFloat.Proof.add_eq_spec a b
```

Say you want to rewrite `a + b` inside a larger goal. For that there's `ExecFloat.Proof.add_notation_eq_spec`, the same equation stated for the notation. It pins down the whole result word, exceptional results included, and needs no hypotheses at all, so there's nothing to prove first. Hypotheses show up when you read a finite result as a rounded real sum, and [the numerical-model chapter](#/chapter/the-numerical-models/what-does-the-addition-theorem-say-about-real-numbers) explains the finiteness assumptions that reading needs. [A worked example](#/chapter/the-numerical-models/how-to-use-these-theorems-on-binary32-values) carries out that proof on the configured type, the one you compute with.

## Where do the theorems come from?

FloatLib's source has three parts, and that one proof uses all of them, as [Figure 1.1](#/chapter/using-the-library/figure-ch19-layers) shows for a binary32 addition. [Floats](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats) gives words their format and calls the integer algorithms in [Kernels](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Kernels). Those come with refinement proofs built on [Numerics](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Numerics), where exact values and contracts, the promises an operation makes about its result, are defined. [Chapter 03](#/chapter/the-numerical-models) takes that addition apart, and the [theorem guide](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/THEOREMS.md) lists the public arithmetic theorems with their imports and hypotheses.

![Exact values in Numerics, integer algorithms in Kernels, and configured formats in Floats.](assets/ch19-layers.png "An executable operation is connected to its exact-value specification by a refinement proof.")

## How to trap a number between two roundings

Let's put the [rounding directions](#/chapter/using-the-library/how-to-choose-a-rounding-direction) to work. One third falls between two binary32 values, so why not keep both? Round the division down for a lower bound and up for an upper bound, and the pair traps the exact quotient even though neither endpoint equals it. A pair like that, with the promise that the exact answer lies between its ends, is called an interval.

`oneThird` and `twoThirds` below pass the direction through `mode`, and our `enclose` builds an interval from the pair with `Interval.ofBounds`, which falls back to the whole range if the pair is out of order or a NaN. [[FloatLib.Floats.ExecFloat.Binary.Interval]] keeps both endpoints in the configured scalar type, here `Binary32`, and `Interval.add` adds the lower endpoints downward and the upper endpoints upward.

```lean
open ExecFloat.Binary (Interval)

def enclose (lo hi : Binary32) := Interval.ofBounds lo hi

def oneThird := enclose (ExecFloat.Binary.div 1 3 (mode := .down))
  (ExecFloat.Binary.div 1 3 (mode := .up))
def twoThirds := enclose (ExecFloat.Binary.div 2 3 (mode := .down))
  (ExecFloat.Binary.div 2 3 (mode := .up))

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
  have h := Interval.add_sound oneThird twoThirds oneThird_valid twoThirds_valid oneThird_mem
    twoThirds_mem
  rw [show (1 / 3 + 2 / 3 : ℝ) = 1 by norm_num] at h
  exact (Interval.eRealMem_coe_iff_of_valid total_valid 1).mp h
```

Let's check the enclosure of one by hand. The lower endpoints add exactly, $5592405 \cdot 2^{-24} + 5592405 \cdot 2^{-23} = 16777215 \cdot 2^{-24} = 1 - 2^{-24}$. The upper endpoints sum to $1 + 2^{-25}$, which binary32 can't hold, so rounding upward lands on $1 + 2^{-23}$. The enclosure $[1 - 2^{-24}, 1 + 2^{-23}]$ contains $1 = \tfrac13 + \tfrac23$, and its upper side is twice as wide as its lower side because the binary32 grid doubles its spacing at one.

### What the theorems prove

The theorems prove two things, validity and membership. An interval is valid when its endpoints are finite and in order, which is decidable, meaning a program can check it, so `decide +kernel` settles it by evaluating the endpoints in Lean's kernel, the small core of Lean that checks every proof. For membership, `Interval.realMem_iff` turns `RealMem oneThird (1 / 3)` into $\operatorname{lo} \le 1/3 \le \operatorname{hi}$, `toReal_of_toRat?_eq_some` swaps each endpoint's real value for the exact rational the kernel computes from the stored word, and `norm_num`, Mathlib's tactic for numerical facts, compares those rationals with $1/3$.

### How to add two intervals

`total_mem` never computes the sum's endpoints. It applies [[FloatLib.Floats.ExecFloat.Binary.Interval.add_sound]] instead, a soundness theorem: whenever both intervals are valid and enclose reals $x$ and $y$, the sum interval encloses $x + y$. Its conclusion lives in the extended reals, the reals with $\pm\infty$ added, so an upper endpoint may overflow to $+\infty$, and `eRealMem_coe_iff_of_valid` brings a valid result back to the reals. The theorem also needs the format to be IEEE encoded, a default argument that `decide` supplies for binary32.

Chaining operations is where finiteness comes back. Feed the result into another addition, subtraction, multiplication or division, and its soundness theorem needs finite `Valid` bounds again, so an infinite endpoint that is fine in one conclusion fails the next operation's finite-input premise. The number inside is a different story. `RealMem oneThird x` says the decoded endpoints bracket `x`, which doesn't have to be representable. The [endpoint-adapter recipe](#/chapter/proving-numerical-bounds/how-to-choose-a-different-endpoint-format) uses the same enclosure idea for decimal and posit bounds.

## How to look up a format's properties

You can also ask the library about a format itself. `#float_info` shows a type's numerical properties, its selected implementation and the theorems about it:

```lean
#float_info Binary32
#float_info [errors] Binary32
```

For `Binary32`, the report includes these entries:

| Report entry | What it tells us |
| --- | --- |
| Storage and precision | A `UInt32`, with 23 stored fraction bits and 24 significant bits for normal values. |
| Execution | Under the balanced planning policy, the planner selects a fixed-format word kernel for the six arithmetic operations. |
| Theorems | First the theorems about `Binary32` values, such as `ExecFloat.Proof.add_notation_eq_spec` for `x + y` and `ExecFloat.Binary.toReal_add_eq_roundAt` for its single rounding, then those about the proof model, which `ExecFloat.Binary.toModel` reaches. |
| Error bounds | Nearest-even rounding has a half-ulp absolute-error bound. When the exact value is in the nonzero normal range, the relative bound is $2^{-24}$. |

The report also lists the format's constants. For binary32 the largest finite value is $(2 - 2^{-23}) \cdot 2^{127} \approx 3.40282 \cdot 10^{38}$, machine epsilon, the gap between one and the next binary32 number, is $2^{-23}$, and the least normal and subnormal values are there too. All four are also values of the type, `ExecFloat.Binary.maxFinite`, `minNormal`, `minSubnormal` and `epsilon`, and `ExecFloat.Binary.ulp x` gives the spacing around `x`, the ulp (unit in the last place, the value of a one in the last stored digit) that the error-bound entry is measured in.

`#float_info! Binary32` adds the planner's cost estimates, and `#float_info! [errors] Binary32` lists every theorem behind each bound with a summary of its scope. Hover over a theorem name in your editor to see its exact statement. These are contracts for the whole type, so applying one to a particular expression needs the relevant finiteness, domain and range proofs for it. `#float_help` lists the command options, for when you forget them :)

## Which import do you need?

`import FloatLib` gives you the format families and their arithmetic, and a few things need one more import. Take the transcendental functions, binary `exp`, `log` and `sin`. For those you add `FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals`. It makes `MathFunctions`, the class (Lean's word for an interface) that generic code calls for `exp`, `log` and the rest, work on FloatLib's values, both the ones you compute with and the model values the proofs reason about, and it adds powers with a floating-point exponent on model values. Without it, the class has only its instance for Lean's own `Float`, and FloatLib's values have integer powers through `powInt` but no power with a floating-point exponent.

That import also brings two ways to ask for a correctly rounded answer, the exact result rounded once. The certified searches `ExecFloat.Binary.Certified.exp`, `log`, `pow`, `expMinus1` and `logPlus1` return one or tell you why they couldn't certify one. In `FloatLib.Floats.Formats.BinaryInterchange.Configured.CorrectlyRounded`, which comes with it, `ExecFloat.Binary.CorrectlyRounded.exp`, `log`, `expMinus1`, `logPlus1` and weighted `exp x * w` always return one on IEEE formats. With the transcendental import in place, opening the scope `FloatLib.Floats.Formats.BinaryInterchange.CorrectlyRoundedMath` makes generic `MathFunctions` code use them for `exp` and `log`.

And watch out for the `roundoff` tactic of [chapter 11](#/chapter/proving-numerical-bounds/how-to-get-an-error-bound-for-floating-point-code), which proves error bounds. It needs `FloatLib.Floats.Formats.BinaryInterchange.Automation.Roundoff`, which `import FloatLib` doesn't reach.

For fewer dependencies, import only the layer you need:

| Import | What it gives you |
| --- | --- |
| `FloatLib.Floats.ExecFloat` | The carrier type `ExecFloat`, arithmetic, conversion and the `run = spec` equations. |
| `FloatLib.Floats.Formats.BinaryInterchange.Configured` | Adds `ExecFloat.Binary`, literals and the configured operations. |
| `FloatLib.Floats.Formats.BinaryInterchange.Semantics` | Adds the real-valued theorems. |
| `FloatLib.Floats.Formats.Posit` | The posit family. |
| `FloatLib.Numerics` | The representation-independent layer. |
| `FloatLib.Floats.ExecFloat.Runtime` | For a program that only computes: the same certified arithmetic and conversion without the proof automation and inspection commands. |

None of these imports, `import FloatLib` and the transcendental one included, brings in the [Arb adapter](https://github.com/lean-dojo/FloatLib/blob/main/tests/FloatLibTests/Arb/ModelTranscendentals.lean), which lives in the separate test workspace and calls the Arb library through python-flint, so its results depend on that external library.

## Where to go next

These examples build on the operations and proofs on this page:

- [Decimal or posit interval endpoints](#/chapter/proving-numerical-bounds/how-to-choose-a-different-endpoint-format), which report a failure when finite bounds can't enclose the result.
- [Sums and dot products](#/chapter/the-mathematics-of-rounding/how-to-add-a-list-with-one-rounding) that keep exact intermediates until a single final rounding.
- [Real-valued proofs](#/chapter/the-numerical-models/how-to-use-these-theorems-on-binary32-values) for configured arithmetic.
- [Mixed formats and round-once expressions](#/chapter/ieee-binary-formats/how-to-mix-formats), with declared destinations and conversion status.
- [Complex arithmetic](#/chapter/ieee-binary-formats/how-to-work-with-complex-numbers), keeping the scalar rounding steps in the specification.
- [Adding a backend or format](#/chapter/the-numerical-models/how-to-add-your-own-format-or-backend), for when the one you want isn't in FloatLib.
