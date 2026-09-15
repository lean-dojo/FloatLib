---
number: "01"
slug: using-the-library
title: "Getting started with FloatLib"
summary: "Compute with different formats, inspect exact stored values, and use theorems about arithmetic and rounding."
phases: [planner-and-configured, ieee-formats, binary-arithmetic]
---

## Setting up a project

We'll use the same small program for calculations and proofs, so you can run the examples as we go. Use the Lean and Mathlib versions specified by FloatLib's [toolchain](https://github.com/lean-dojo/FloatLib/blob/main/lean-toolchain) and [Lake configuration](https://github.com/lean-dojo/FloatLib/blob/main/lakefile.lean). In another Lake project, add the dependency with `require`:

```text
require floatlib from git
  "https://github.com/lean-dojo/FloatLib.git" @ "main"
```

Run `lake update`, `lake exe cache get` to fetch the Mathlib cache, and `lake build`. Put `import FloatLib` at the top of `Main.lean`, and run it with `lake env lean Main.lean`. That import gives us every format family, the inspection commands, and the proof automation used below.

<a id="choosing-the-format-once"></a>

## Choosing a format

A format in FloatLib is a Lean type. We'll start with binary32 and give it a name using `abbrev`, which leaves its definition visible to instance resolution and proofs. [[FloatLib.Floats.ExecFloat.Binary]] takes the exponent width and the stored fraction width; the total width, $1 + 8 + 23 = 32$ bits, is derived from them. Instances, backend selection, and theorems for that type then apply to `Binary32` without registration. A 24-bit or a 71-bit layout uses the same API, as does a binary16 layout with a different exceptional-value policy; the [custom-format examples](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Examples/CustomFormats.lean) show how to define them.

The code assumes a file beginning with `import FloatLib`. `open FloatLib.Floats` makes names such as `ExecFloat` available without their full namespace prefix; it does not choose a numerical format. The annotation `: Binary32` makes that choice for `x` and `y`, including how their literals are rounded. The second `open` line enables `+∞` and `-∞` as rounding directions.

```lean
open FloatLib.Floats
open scoped FloatLib.IEEERounding

abbrev Binary32 := ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)
abbrev Binary64 := ExecFloat.Binary (exponentBits := 11) (fractionBits := 52)
abbrev Posit32 := ExecFloat.Posit (bits := 32)

def x : Binary32 := 1.5
def y : Binary32 := 2.25

#eval x + y
-- 3.75
#eval ExecFloat.sqrt y
-- 1.5
#eval x / 3
-- 0.5
```

The 23 stored fraction bits give 24 bits of precision for normal values because the leading one is implicit. These widths are parameters of the type, so `x + y` selects binary32 addition and the `3` in `x / 3` is read as another binary32 value. Changing the abbreviation changes the format throughout the program.

The library reads a literal as an exact rational and rounds it once to the chosen format, using nearest rounding with ties to even. Both `1.5` and `2.25` are dyadic, so nothing is lost. The first three computations also have exactly representable answers: addition gives `3.75`, square root gives `1.5`, and division gives `0.5`.

When `#eval` prints a value it prints the exact stored number: as a decimal when the stored value has a short exact decimal expansion, and otherwise as an integer times a power of two. Formatting does not convert through a host float, which could round the value again. String interpolation uses the same formatter, so `s!"sum = {x + y}"` gives `sum = 3.75`.

The [[FloatLib.Floats.ExecFloat.Posit]] type takes only the total width; `Posit32` above is another abbreviation for a configured type.

## Arithmetic and exact stored values

Our first calculations lost no bits. Now we can try inputs that need rounding. Ordinary arithmetic operators use nearest-even rounding. The same expression can therefore produce different equality results at different widths:

```lean
#eval (0.1 : Binary32) + 0.2
-- 5033165 * 2^-24
#eval ((0.1 : Binary32) + 0.2) == 0.3
-- true
#eval ((0.1 : Binary64) + 0.2) == 0.3
-- false
#eval ExecFloat.Binary.toRat? ((0.1 : Binary32) + 0.2)
-- some (5033165 / 16777216)
#eval ExecFloat.fma x y 0.5
-- 3.875
```

Neither $0.1$ nor $0.2$ is a binary fraction, so each literal is rounded when it is read and the sum is rounded once more. In binary32 the rounded sum equals the rounded literal `0.3`; in binary64 it does not, giving the familiar `0.30000000000000004`. The stored binary32 sum is $5033165 \cdot 2^{-24}$. [[FloatLib.Floats.ExecFloat.Binary.toRat?]] returns it as an exact rational and returns `none` for NaN and infinity. [[FloatLib.Floats.ExecFloat.fma]] computes $xy + z$ with one rounding; separate multiplication and addition can round twice.

The `true` result compares two stored numbers; neither side is the exact rational three tenths. Here `==` is IEEE numerical equality, which treats the two signed zeros as equal and every comparison of a NaN with itself as false. The `=` in the proofs below means equality of the stored words: it distinguishes the zeros and makes every word, including a NaN, equal to itself. An equation with `ExecFloat.Spec.add` therefore identifies the complete result word, beyond what a numerical equality test can establish.

<a id="what-the-theorems-give-you"></a>

## Proving arithmetic agrees with its specification

Our first proof will cover every pair of inputs. [[FloatLib.Floats.ExecFloat.Proof.add_eq_spec]] states that executable addition, whichever backend the planner selected, equals the format's reference addition [[FloatLib.Floats.ExecFloat.Spec.add]]. Its statement uses `ExecFloat.add`, which is the function that `+` calls on a configured type. We can therefore apply the theorem directly to a goal written with ordinary notation. There is one such equation per operation, and the six are bundled as `FullArithmeticCertificate`.

```lean
example (a b : Binary32) : a + b = ExecFloat.Spec.add a b :=
  ExecFloat.Proof.add_eq_spec a b

example (a b : Binary32) : a / b = ExecFloat.Spec.div a b :=
  ExecFloat.Proof.div_eq_spec a b

example : ExecFloat.Proof.FullArithmeticCertificate (ExecFloat.Binary.Family 8 23) :=
  ExecFloat.Proof.fullArithmeticCertificate _
```

<a id="a-tour-of-the-codebase"></a>

## Library structure

To follow that addition into the source, we need the three parts of the library in [Figure 1.1](#/chapter/using-the-library/figure-ch19-layers). [Numerics](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Numerics) defines exact values and contracts without choosing an encoding. [Kernels](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Kernels) supplies integer and fixed-word algorithms with refinement proofs. [Floats](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats) supplies the formats and the universal carrier `ExecFloat`, and connects operations to kernels. An addition on `ExecFloat.Binary 8 23` uses all three: the format decodes its words, an integer kernel computes the result, and the exact-value definitions give the meaning used in the proof.

![FloatLib's three source layers: exact values and contracts in Numerics, integer algorithms in Kernels, and numerical formats and executable carriers in Floats. Tests, benchmarks, and the website use the library from outside these layers.](assets/ch19-layers.png "Numerics defines exact values and contracts; Kernels implements integer algorithms; Floats gives them numerical formats and executable carriers.")

For the `x + y` above, start at the [public arithmetic dispatcher](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Dispatch.lean). The call uses a certified implementation chosen for the format. The [arithmetic specification](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Spec/Arithmetic.lean) names its reference operation, and the [refinement proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Proof/Arithmetic.lean) state the equation we just used. The [architecture chapter](#/chapter/why-execution-and-proofs-are-separate) explains how execution is connected to its proof; the [kernel chapter](#/chapter/kernels-fixed-word-algorithms) develops the integer algorithms.

Public theorems are named for their conclusion and the namespace carries the family. The [theorem guide](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/THEOREMS.md) lists the public names with their imports and hypotheses, and its closing section spells out the patterns: `*_eq_spec` rewrites executable code to its reference definition, `*_refines` and `implements_*` prove a relational contract, `toReal_*` and `toRat_*` state decoded meaning, `isFinite_*` discharges the side condition a real-valued theorem needs.

## Rounding directions and status flags

The named operations [[FloatLib.Floats.ExecFloat.Binary.add]], `sub`, `mul`, [[FloatLib.Floats.ExecFloat.Binary.div]], `fma`, and `sqrt` take a rounding direction as an explicit argument with no default: one of the four values of [[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEERoundingMode]]. It can be named, `(rounding := ...)`, or positional. There is no global rounding state for a proof about `x + y` to account for. After `open scoped FloatLib.IEEERounding`, the two infinite directions may be written `+∞` and `-∞`; the scope keeps this notation separate from $\infty$ in extended-real expressions.

```lean
#eval ExecFloat.Binary.div (1 : Binary32) 3 (rounding := .nearestEven)
-- 11184811 * 2^-25
#eval ExecFloat.Binary.div (1 : Binary32) 3 (rounding := +∞)
-- 11184811 * 2^-25
#eval ExecFloat.Binary.div (1 : Binary32) 3 (rounding := -∞)
-- 5592405 * 2^-24
#eval ExecFloat.Binary.div (1 : Binary32) 3 (rounding := .towardZero)
-- 5592405 * 2^-24
```

One third lies between two binary32 neighbours. The output shows them as dyadics in lowest terms; written over the common denominator $2^{25}$ they are $11184810 \cdot 2^{-25}$ (about $0.33333331$, printed as $5592405 \cdot 2^{-24}$) and $11184811 \cdot 2^{-25}$ (about $0.33333334$), adjacent significands with one third strictly between them. Nearest-even and toward $+\infty$ pick the upper one; toward zero and toward $-\infty$ pick the lower one, and those two agree because the value is positive. (The decimal expansions are worked out in the [basic-operation examples](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Examples/BasicOperations.lean).)

IEEE 754 asks each operation to report five conditions, called exceptions in the standard though nothing is thrown: invalid, divide by zero, overflow, underflow, and inexact. The `WithStatus` variants return the result together with these five Booleans as an [[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEEStatus]]. They compute the flags from the operands, exact arithmetic, and rounded result. [[FloatLib.Floats.Formats.BinaryInterchange.Model.addWithStatus_value]] states that the returned value is the same as for addition without status.

```lean
#eval ExecFloat.Binary.divWithStatus (1 : Binary32) 3 (rounding := -∞)
-- (5592405 * 2^-24, { invalid := false, divideByZero := false, overflow := false, underflow := false, inexact := true })
#eval ExecFloat.Binary.divWithStatus (1 : Binary32) 0 (rounding := .nearestEven)
-- (inf, { invalid := false, divideByZero := true, overflow := false, underflow := false, inexact := false })
#eval ExecFloat.Binary.mulWithStatus (1e30 : Binary32) 1e30 (rounding := .nearestEven)
-- (inf, { invalid := false, divideByZero := false, overflow := true, underflow := false, inexact := true })
#eval ExecFloat.Binary.mulWithStatus (1e-30 : Binary32) 1e-30 (rounding := .nearestEven)
-- (0, { invalid := false, divideByZero := false, overflow := false, underflow := true, inexact := true })

def thirdDown := ExecFloat.Binary.divWithStatus (1 : Binary32) 3 (rounding := -∞)
def oneOverZero := ExecFloat.Binary.divWithStatus (1 : Binary32) 0 (rounding := .nearestEven)

#eval FloatLib.Numerics.IEEEStatus.union thirdDown.2 oneOverZero.2
-- { invalid := false, divideByZero := true, overflow := false, underflow := false, inexact := true }
```

The first line sets only `inexact`, because rounding changed the value. On the second, $1/0$ with a positive zero denominator returns $\infty$ and sets the divide-by-zero flag, as IEEE specifies. On the third, $10^{30} \cdot 10^{30}$ overflows, and overflow always comes with inexact. On the fourth, $10^{-30} \cdot 10^{-30}$ lies far below the least binary32 subnormal, so the result is zero, flagged underflow and inexact. There is no global sticky register. [[FloatLib.Numerics.IEEEStatus.union]] combines the flags from several operations, as the last line does. Each flag is a Boolean field of the returned status; [chapter 08](#/chapter/ieee-binary-formats) gives the theorems that characterize it.

In `thirdDown`, `.1` selects the rounded number and `.2` selects the status, so `thirdDown.2.inexact` reads one condition without discarding the value. Each status describes that operation on its stored operands. It does not also report the earlier rounding that created a decimal literal or an input to the operation. To retain conditions across a computation, carry the statuses alongside its values and combine them with `union`.

## An interval from two directed roundings

[[FloatLib.Floats.Formats.BinaryInterchange.Model.Interval]] holds two endpoints of one descriptor. `Interval.ofBounds` builds an interval from two words, falling back to the whole range when the pair is unordered or a NaN. Intervals use the descriptor model directly: `toModel` converts the configured words for interval operations, and `ofModel` converts endpoints back for printing. Below, the two endpoints of each interval are the same quotient rounded toward $-\infty$ and toward $+\infty$, and `Interval.add` adds lower endpoints downward and upper endpoints upward.

```lean
open Formats.BinaryInterchange in
def enclose (lo hi : Binary32) : Model.Interval FloatFormat.binary32 :=
  Model.Interval.ofBounds (ExecFloat.Binary.toModel lo) (ExecFloat.Binary.toModel hi)

open Formats.BinaryInterchange in
def endpoints (I : Model.Interval FloatFormat.binary32) : Binary32 × Binary32 :=
  (ExecFloat.Binary.ofModel I.lo, ExecFloat.Binary.ofModel I.hi)

def oneThird := enclose (ExecFloat.Binary.div 1 3 (rounding := -∞))
  (ExecFloat.Binary.div 1 3 (rounding := +∞))
def twoThirds := enclose (ExecFloat.Binary.div 2 3 (rounding := -∞))
  (ExecFloat.Binary.div 2 3 (rounding := +∞))

open Formats.BinaryInterchange in
def total := Model.Interval.add oneThird twoThirds

#eval endpoints oneThird
-- (5592405 * 2^-24, 11184811 * 2^-25)
#eval endpoints twoThirds
-- (5592405 * 2^-23, 11184811 * 2^-24)
#eval endpoints total
-- (16777215 * 2^-24, 8388609 * 2^-23)

open Formats.BinaryInterchange in
example {x y : ℝ}
    (hA : Model.Interval.Valid oneThird) (hB : Model.Interval.Valid twoThirds)
    (hx : Model.Interval.RealMem oneThird x) (hy : Model.Interval.RealMem twoThirds y) :
    Model.Interval.ERealMem (Model.Interval.add oneThird twoThirds) ((x + y : ℝ) : EReal) :=
  Model.Interval.add_sound oneThird twoThirds (by decide) hA hB hx hy
```

The two lower endpoints add exactly, $5592405 \cdot 2^{-24} + 5592405 \cdot 2^{-23} = 16777215 \cdot 2^{-24} = 1 - 2^{-24}$, while the two upper endpoints sum to $1 + 2^{-25}$, which binary32 cannot hold, so upward rounding gives $1 + 2^{-23}$. The enclosure $[1 - 2^{-24}, 1 + 2^{-23}]$ contains $1 = \tfrac13 + \tfrac23$, as it must.

The theorem at the end is [[FloatLib.Floats.Formats.BinaryInterchange.Model.Interval.add_sound]] applied to these two intervals: whenever both are valid (finite, ordered endpoints) and enclose reals $x$ and $y$, the sum interval encloses $x + y$. The statement uses the extended reals to allow an upper endpoint to overflow to $+\infty$. Here the validity and membership facts are left as hypotheses; the directed-rounding bounds of [chapter 08](#/chapter/ieee-binary-formats), `toEReal_divDown_le` and its upward counterpart, establish them for these particular words. The `by decide` settles only the descriptor hypothesis.

The type `Model.Interval FloatFormat.binary32` keeps both endpoints at the same format. `RealMem oneThird x` then states that the decoded endpoints bracket `x`; it does not force `x` to be representable. That is how an interval with binary endpoints can make a claim about the exact real one third. The `open ... in` lines shorten model names only for the following declaration, leaving the rest of the file's namespace choices unchanged.

<a id="reductions-that-round-once"></a>

## Sums and dot products with one rounding

When we sum a list by rounding after each addition, a small term can be lost. A binary32 significand has 24 bits, so $2^{24} + 1$ (that is, $16777216 + 1$) rounds back to $2^{24}$, and subtracting $2^{24}$ then gives zero. `sumList` and `sum` instead decode every term to an exact dyadic, accumulate the complete sum in software, and round once at the end.

```lean
def values : List Binary32 := [16777216, 1, -16777216]

#eval values.foldl (· + ·) 0
-- 0
#eval ExecFloat.Binary.sumList values .nearestEven
-- 1
#eval ExecFloat.Binary.sumListWithStatus values .nearestEven
-- (1, { invalid := false, divideByZero := false, overflow := false, underflow := false, inexact := false })
#eval ExecFloat.Binary.dot #[(1.5 : Binary32), 2, 4] #[2, 3, 4] .nearestEven
-- Except.ok 25
#eval ExecFloat.Binary.dotList [(1.5 : Binary32), 2, 4] [2, 3] .nearestEven
-- Except.error (FloatLib.Numerics.ReductionError.lengthMismatch 3 2)
```

Try reordering the list above and comparing the ordinary fold with the exact sum. Can you explain where the small term survives? :)

The status form reports that the exact sum was representable, with no rounding error. [[FloatLib.Floats.ExecFloat.Binary.dot]] keeps every product exact as well: $1.5 \cdot 2 + 2 \cdot 3 + 4 \cdot 4 = 25$ with one rounding at the end. A length mismatch returns an `Except.error` carrying both lengths before any arithmetic runs, as `dotWithStatus_lengthMismatch` proves. This check prevents the truncation that would result from using `List.zip` on unequal lists.

The configured functions call the reducer defined for the format's model. [[FloatLib.Floats.Formats.BinaryInterchange.Model.Reduction.sumWithStatus_eq_round_of_finite_nonzero]] says a nonzero finite sum is one rounding of the exact sum, with exactly that rounding's status. [[FloatLib.Floats.ExecFloat.Binary.dotWithStatus_eq_model]] says the configured dot is the model dot, errors and status included.

`dot` has no initial-addend argument. IEEE `fma` already covers one product plus an addend, and the round-once expressions in the mixed-format section cover anything larger. A posit quire, the subject of [chapter 11](#/chapter/posits-and-the-quire), also delays rounding, but it is a fixed $16n$-bit accumulator with a NaR outcome and a range condition, whereas the binary reducer uses an unbounded dyadic and follows the IEEE status rules.

## The result as a real number

We can prove which word an addition returns. To say what that word means as a real number, we need one more step. The certificate is indexed by the family: `Binary32` is `ExecFloat` applied to `Family` `8 23`. That family carries the `Capability` instances of [chapter 14](#/chapter/backends-and-the-planner), one per operation, that connect execution to the selected certified kernel. Those equations relate the fast code to the specification; the format's semantics will let us interpret the result.

For binary interchange the real-valued semantics are stated for [[FloatLib.Floats.Formats.BinaryInterchange.Model]], the descriptor-indexed model of [chapter 06](#/chapter/the-numerical-models). The function [[FloatLib.Floats.ExecFloat.Binary.toModel]] converts a configured value to that model. A configured binary32 value is stored as a packed `UInt32`; the model uses an exact-width record. `toModel` and its inverse `ofModel` connect the two representations.

We can build that connection a step at a time. The proof of `toModel_hAdd` below rewrites `a + b` using four facts: the refinement equation, the definition of the configured specification as the model specification lifted through the storage codec, the model's own `add = spec` theorem, and the codec law `decode_liftBinary`. Each tactic line applies one of these facts. Then [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt]] gives the real-number statement: for finite operands whose sum does not overflow, the decoded sum is the exact real sum rounded once by [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt]].

```lean
open Formats.BinaryInterchange

theorem toModel_hAdd (a b : Binary32) :
    ExecFloat.Binary.toModel (a + b) =
      Model.add (ExecFloat.Binary.toModel a) (ExecFloat.Binary.toModel b) := by
  rw [show a + b = ExecFloat.Spec.add a b from ExecFloat.Proof.add_eq_spec a b]
  change Configured.Family.toModel (Configured.Spec.add a b) = _
  rw [Model.Proof.add_eq_spec]
  exact ExecFloat.ModelCodec.decode_liftBinary _ _ _

theorem toReal_add_binary32 (a b : Binary32)
    (ha : Model.isFinite (ExecFloat.Binary.toModel a) = true)
    (hb : Model.isFinite (ExecFloat.Binary.toModel b) = true)
    (hout : Model.isFinite (ExecFloat.Binary.toModel (a + b)) = true) :
    Model.toReal (ExecFloat.Binary.toModel (a + b)) =
      Model.roundAt FloatFormat.binary32
        (Model.toReal (ExecFloat.Binary.toModel a) +
          Model.toReal (ExecFloat.Binary.toModel b)) := by
  rw [toModel_hAdd] at hout ⊢
  exact Model.toReal_add_eq_roundAt _ _ (by decide) ha hb hout
```

The line `rw [toModel_hAdd] at hout ⊢` rewrites both the result-finiteness hypothesis and the goal. They now mention the same `Model.add` expression, so `hout` has exactly the form the model theorem expects. The remaining arguments supply its IEEE descriptor and operand-finiteness hypotheses.

`ha` and `hb` say the operands are finite, because a NaN or an infinity has no real value to round. `Model.toReal` is a total function and returns zero on those non-finite inputs; the finiteness hypotheses are what justify interpreting it as the value of a word. `hout` says the sum did not overflow; it is decidable on the result, and when we would rather not evaluate the sum first, [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt_of_abs_add_le_posMaxFinite]] accepts the symbolic bound $|a| + |b| \le \Omega$ in its place, where $\Omega$ is the largest finite value [[FloatLib.Floats.Formats.BinaryInterchange.Model.posMaxFinite]]. The `by decide` proves `fmt.isIEEE = true`, requiring the IEEE encoding and conventional bias.

We can also bound the rounding error: [[FloatLib.Floats.Formats.BinaryInterchange.Model.abs_toReal_add_sub_le]] bounds one finite addition by half an ulp, and the `#float_info [errors]` report below states the relative bound $2^{-24}$ for nonzero normal inputs. Square root is the one operation without a result-finiteness premise, since [[FloatLib.Floats.Formats.BinaryInterchange.Model.isFinite_sqrt_of_isFinite]] shows it cannot overflow; it does ask that the operand be nonnegative (a signed zero counts), since a negative input yields NaN rather than a real.

For the named directed operations, [[FloatLib.Floats.ExecFloat.Binary.toModel_add]] and the corresponding lemmas for the other five operations are already registered with `simp`. The status variants have similar lemmas, such as `toModel_divWithStatus`. A goal about a configured directed operation therefore reduces to the corresponding model theorem in one step.

We can also put the represented value in the type. `At` `fmt r` is an encoded value of format `fmt` together with a proof, erased at runtime, that it denotes the real $r$. Operations on it, such as `Model.At.add`, take the finiteness hypotheses as arguments and produce a value indexed by the rounded result.

```lean
example (a b : Binary32) :
    ExecFloat.Binary.toModel (ExecFloat.Binary.add a b .nearestEven) =
      Model.addWithRounding .nearestEven
        (ExecFloat.Binary.toModel a) (ExecFloat.Binary.toModel b) :=
  ExecFloat.Binary.toModel_add a b .nearestEven

example {fmt : FloatFormat} {r s : Real}
    (u : Model.At fmt r) (v : Model.At fmt s)
    (hfmt : fmt.isIEEE = true)
    (hout : Model.isFinite (Model.add u.1 v.1) = true) :
    (Model.numericalSystem fmt).denote (Model.At.add u v hfmt hout).1 =
      .finite (Model.roundAt fmt (r + s)) := by
  numerics
```

The second example says that adding a value known to denote $r$ to one known to denote $s$ gives a value that the format's numerical system interprets as the finite real $\mathrm{roundAt}(r + s)$. The type of `Model.At.add` already carries the rounded sum as its index. The `numerics` tactic closes the proof using the general rule, registered under `numerics_simps`, that an `At` value denotes its index.

The values `u` and `v` contain their own proofs: their `.1` fields are executable values, and their `.2` fields establish the finite denotations. There is no separate `ha` or `hb` here because those facts follow from the indexed types. The caller still supplies `hout`; knowing two inputs are finite does not ensure their sum fits. This view is useful when several operations share the same semantic facts, since a function can return the value together with the proof its caller will need.

These theorems describe FloatLib's software arithmetic. Relating that arithmetic to Lean's native `Float32`, C operations, or GPU instructions requires a separate argument; [chapter 15](#/chapter/performance/comparing-with-leans-native-floats) examines the comparison with Lean's native floats.

## Complex arithmetic

Multiplying two complex numbers looks like one operation on paper:

$$
(a+bi)(c+di)=(ac-bd)+(ad+bc)i.
$$

For floating-point components, that formula contains six rounding steps. FloatLib's `ExecComplex fmt` stores two `Model fmt` values. Its multiplication rounds each of the four products, then rounds the subtraction and addition. Writing $R$ for the format's nearest-even rounder, the computed components are

$$
R\bigl(R(ac)-R(bd)\bigr),\qquad
R\bigl(R(ad)+R(bc)\bigr).
$$

If $ac$ and $bd$ nearly cancel, errors in the two products can dominate their difference. A proof about the implementation has to preserve those inner roundings. Replacing the first component by $R(ac-bd)$ would describe a different algorithm.

Here is the multiplication theorem for any descriptor with conventional IEEE semantics:

```lean standalone
import FloatLib.Floats.Formats.BinaryInterchange.Complex.Semantics

open FloatLib.Floats.Formats.BinaryInterchange

example {fmt : FloatFormat} (x y : ExecComplex fmt)
    (hfmt : fmt.isIEEE = true) (h : ExecComplex.MulFinite x y) :
    ExecComplex.toComplex (x * y) =
      ExecComplex.roundedMul fmt
        (ExecComplex.toComplex x) (ExecComplex.toComplex y) :=
  ExecComplex.toComplex_mul_eq_roundedMul x y hfmt h
```

`MulFinite` requires finite inputs, four finite rounded products, and finite final components. The intermediate conditions matter: a product can overflow even when the exact complex answer would fit after cancellation. Componentwise addition and subtraction have corresponding theorems; each rounds its real and imaginary components separately.

Division raises another problem. The familiar denominator $c^2+d^2$ can overflow while $c$ and $d$ are still finite. `ExecComplex.div` instead chooses the larger denominator component as a pivot. When $|c|\geq|d|$, it forms a rounded ratio $r=R(d/c)$ and evaluates the ratio formula

$$
\frac{a+br}{c+dr}+i\,\frac{b-ar}{c+dr},
$$

rounding each scalar operation. The other branch swaps the components. `toComplex_div_eq_roundedDiv` records the selected branch and its nine rounding steps. The `DivFinite` hypothesis requires a nonzero pivot and rounded denominator, along with finite inputs, intermediates, and results. Avoiding the two large squares helps, but other intermediates can still overflow.

Magnitude uses a similar scaling idea. With $s=\max(|a|,|b|)$, it computes the rounded counterpart of

$$
s\sqrt{(a/s)^2+(b/s)^2}.
$$

A zero scale returns zero directly. Otherwise, `toReal_magnitude_eq_roundedMagnitude` accounts for seven scalar roundings: two divisions, two squares, the addition, square root, and final rescaling. Its `MagnitudeFinite` conditions cover the intermediate ranges and square-root domain. The separate `normSq` operation computes a rounded sum of squares; it does not use this scaling.

Exceptional components follow a separate rule. If either component is infinite and neither is a signaling NaN, magnitude returns positive infinity, even when the other component is a quiet NaN. A signaling NaN instead follows the scalar NaN selection and quieting rules. This does not strengthen the finite theorem into a correctly rounded hypotenuse operation or establish that every intermediate stays finite.

These contracts let a larger proof reason about the operations that actually ran. They cover basic complex arithmetic, conjugation, squared norm, and magnitude. Complex exponential, logarithm, and trigonometric functions are not implemented; the scalar transcendental APIs in the binary and posit chapters do not supply them.

## Mixing formats

There is no implicit promotion between formats. When a value of one type is needed at another, we name the destination: [[FloatLib.Floats.ExecFloat.cast]] takes a `target`, and `addAs`, `subAs`, `mulAs`, `divAs`, and `fmaAs` take a `result`. Each returns a `ConversionOutcome` carrying the value and its conversion status, or an explicit failure; `value?` keeps just the value. Explicit destinations show where conversion and rounding can happen, including conversions we can prove exact.

```lean
#eval ((1.5 : Binary32).cast (target := Binary64)).value?
-- some 1.5
#eval ((-(0 : Binary32)).cast (target := Binary64)).value?
-- some -0
#eval (0.1 : Binary64).cast (target := Binary32)
-- FloatLib.Floats.ExecFloat.ConversionOutcome.success
--   13421773 * 2^-27
--   { inexact := true,
--     overflow := false,
--     underflow := false,
--     saturated := false,
--     wrapped := false,
--     mappedSpecial := false }

def tenth : Binary32 := 0.1

#eval (1.5 : Binary32) * tenth
-- 5033165 * 2^-25
#eval ExecFloat.mulAs (result := Binary64) (1.5 : Binary32) tenth
-- FloatLib.Floats.ExecFloat.ConversionOutcome.success
--   40265319 * 2^-28
--   { inexact := false,
--     overflow := false,
--     underflow := false,
--     saturated := false,
--     wrapped := false,
--     mappedSpecial := false }
#eval ((1.5 : Binary32).cast (target := Posit32)).value?
-- some 1500000000000000000000000000e-27
#eval ExecFloat.Binary.toFloat32 (x + y)
-- 3.750000
```

A mixed operation decodes its operands exactly, computes in the destination's exact domain, and rounds once. For binary destinations that domain is [[FloatLib.Numerics.SignedRat]], a rational carrying an IEEE sign bit. A plain rational has only one zero, so casting through one would turn $-0$ into $+0$; the sign bit is why the second line delivers $-0$. The narrowing cast on the third line reports `inexact := true` because binary64's $0.1$ does not fit in 24 bits.

It helps to read the two `tenth` lines together: we kept the operands fixed and changed the destination precision. The product of $1.5$ and the stored $0.1$ needs 26 significand bits, so `*` at binary32 rounds it to $5033165 \cdot 2^{-25}$, while `mulAs` into binary64 has room for all 26 and returns the exact $40265319 \cdot 2^{-28}$ with `inexact := false`, as the full outcome shows. A posit destination computes in plain `Rat`, since posits have one zero.

Here `inexact := false` refers to the product of the represented inputs. `tenth` was already rounded when it was defined, and widening the result cannot turn it back into the rational one tenth. The benefit is that the multiplication adds no further error. This distinction also matters when comparing a computed result with a formula over the original decimal data: literal conversion and arithmetic contribute at different places.

Casting to a posit follows Posit Standard (2022) §6.5 by default: either IEEE infinity or any NaN becomes NaR with `mappedSpecial := true`, and either signed zero becomes posit zero. To reject those non-finite source values, pass `{ infinity := .reject, exceptional := .reject }` to `castWith`. Mixed arithmetic such as `mulAs` still requires finite operands and reports a failure before destination conversion if an operand is non-finite.

We can use [[FloatLib.Floats.ExecFloat.spec_cast]] and `preparedSpec_addAs` with its siblings to make those steps precise: decode, embed, operate, round once. At the descriptor-model layer, [[FloatLib.Floats.Formats.BinaryInterchange.Model.cast_eq_roundAt]] characterizes nearest-even destination rounding for finite sources with finite results, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.cast_exact_of_gridExtension]] proves exact widening under its grid-inclusion and finiteness hypotheses. The configured conversion pipeline has its own bridge to rounding; chapter 08 explains the distinction, including the different NaN policies.

At the boundary with Lean's own runtime types, [[FloatLib.Floats.ExecFloat.Binary.ofFloat32]] and [[FloatLib.Floats.ExecFloat.Binary.toFloat32]] move values through the interchange word, and the last line prints in Lean's native six-decimal style. A NaN payload does not round-trip through the native type, because `Float32.ofBits` canonicalizes it; use `toBits32` when the payload matters.

We can evaluate a longer finite expression with one final rounding. [[FloatLib.Floats.ExecFloat.roundOnce]] evaluates a `do` block in the exact domain, with `operand` decoding each numbered input, and quantizes the result once. `tenth` is the stored binary32 value of $0.1$, which the cast above printed as $13421773 \cdot 2^{-27}$; `threeTenths` is the stored $0.3$, the same $5033165 \cdot 2^{-24}$ we met as the binary32 sum of $0.1$ and $0.2$. The exact value of `3 * tenth - threeTenths` is

$$3 \cdot 13421773 \cdot 2^{-27} - 5033165 \cdot 2^{-24} = (40265319 - 40265320) \cdot 2^{-27} = -2^{-27},$$

which is representable. Rounding twice gives a different answer: `3 * tenth` needs 26 bits, rounds up to exactly `threeTenths`, and the subtraction then gives $0$. `fma` and `roundOnce` round once and preserve the exact difference.

```lean
def threeTenths : Binary32 := 0.3

#eval 3 * tenth - threeTenths
-- 0
#eval ExecFloat.fma 3 tenth (-threeTenths)
-- -1 * 2^-27

def onceRounded : ExecFloat.ConversionOutcome Binary32 :=
  ExecFloat.roundOnce (Exact := FloatLib.Numerics.SignedRat) do
    let a ← ExecFloat.ExactExpression.operand 0 tenth
    let b ← ExecFloat.ExactExpression.operand 1 threeTenths
    let three ← ExecFloat.ExactExpression.operand 2 (3 : Binary32)
    pure (three * a - b)

#eval onceRounded.value?
-- some -1 * 2^-27
```

The result type `ConversionOutcome Binary32` fixes the destination. Inside the `do` block, `operand` decodes each input into `SignedRat`, so `a`, `b`, and `three` are exact values and their multiplication and subtraction do not invoke binary32 operations. The numbers `0`, `1`, and `2` label inputs for error reporting. `pure` returns the exact expression's result to `roundOnce`, which performs the destination rounding.

The result matches the `fma` line: one rounding of the exact $-2^{-27}$ is itself. [[FloatLib.Floats.ExecFloat.ConversionProof.preparedSpec_roundOnce]] states that a successful evaluation reaches the destination quantizer exactly once. A non-finite operand is returned as a failure that names its operand index, `InputPosition.operand n`, and a checked division by zero through `ExactExpression.div` as the bare `divisionByZero` failure; neither reaches the quantizer.

`roundOnceWith` supplies an explicit context for the final quantization. If cancellation in the exact expression must follow that context, use `ExactExpression.addWith (result := Destination) context x y` or `ExactExpression.subWith (result := Destination) context x y` inside the `do` block. Ordinary `SignedRat` addition still uses the nearest-even rule for the sign of an exact zero; passing a directed context to the final quantizer does not change that intermediate result. Casts preserve the sign of a supplied zero.

For example, exact cancellation under rounding toward negative infinity produces negative zero:

```lean
def downwardContext := ExecFloat.Binary.Conversion.Context.withRounding .towardNegative

def cancelledDownward : ExecFloat.ConversionOutcome Binary32 :=
  ExecFloat.roundOnceWith downwardContext do
    let a ← ExecFloat.ExactExpression.operand 0 (1 : Binary32)
    let b ← ExecFloat.ExactExpression.operand 1 (-1 : Binary32)
    ExecFloat.ExactExpression.addWith (result := Binary32) downwardContext a b

#eval cancelledDownward.value?.map ExecFloat.Binary.toBits32
-- some 2147483648
```

The word is `0x80000000`: the sign bit is set and every other bit is zero. `addAsWith`, `subAsWith`, and `fmaAsWith` apply this cancellation rule directly from their supplied context.

<a id="asking-a-type-what-it-is"></a>

## Inspecting a format

`#check Binary32` prints an elaborated Lean type. For its numerical properties, use `#float_info Binary32`: it shows the format's range and rounding rules, the implementation selected for each operation, and the available theorems.

```lean
#float_info Binary32
-- Float information: binary interchange
--   standard: IEEE 754-2019 binary32
--
-- Format:
--   storage: UInt32 specified by the configured storage plan
--   total bits: 32
--   sign bits: 1
--   exponent bits: 8
--   stored fraction bits: 23
--   normal significand precision: 24 bits
--   ... 4 more (use `#float_info!`)
--
-- Values:
--   finite numbers: yes
--   subnormals: yes; exponent field zero with a nonzero fraction
--   distinct signed zeros: yes
--   signed infinities: yes
--   ... 2 more (use `#float_info!`)
--
-- Rounding:
--   numeric literals: exact integer/rational input rounded once to nearest, ties to even
--   public ExecFloat arithmetic: nearest, ties to even
--   ... 2 more (use `#float_info!`)
--
-- Conversions:
--   source decoder: installed; finite payload domain = FloatLib.Numerics.SignedRat
--   destination quantizer: installed and proof-backed; input domain = FloatLib.Numerics.SignedRat; context = ExecFloat.Binary.Conversion.Context
--   default context: installed; `cast` and destination-driven `*As` helpers may omit the context
--   mixed arithmetic: available as source and destination: decode exactly, embed through `ExactMap`, operate in the destination exact domain, and round once
--   implicit promotion: none; ordinary same-type arithmetic stays in that type and cross-type results are named explicitly
--
-- Execution:
--   carrier: packed persistent storage; the exact binary descriptor is retained as the proof model
--   dispatch: representation-aware certified selection among direct tables, word, limb, and exact baseline kernels
--   backends: add, sub, mul, div, sqrt, fma = fixed-format word kernel (UInt32)
--
-- Arithmetic:
--   proof-backed: add, sub, mul, div, sqrt, fma
--
-- Proof coverage:
--   [verified] exact encoded interpretation
--   [verified] descriptor-indexed arithmetic refinement
--   [verified] IEEE nearest-even operation semantics
--   [verified] status-bearing operations and flag classifiers
--   ... 9 more proof topics (use `#float_info!`)
--
-- Proof boundary:
--   not claimed: equivalence between compiled Float32/Float arithmetic and this type; only the explicit conversion boundary is checked
--   ... 4 more (use `#float_info!`)
--
-- More detail: `#float_info!`
```

Under Execution, we can see that binary32 uses the fixed-format word kernel described in [chapter 14](#/chapter/backends-and-the-planner). `#float_info! Binary32` expands the abbreviated blocks and shows the cost estimates behind the planner's choice. To find a bound for a numerical argument, use the `[errors]` variant below. It lists the available range, rounding, and error theorems and identifies the conditions needed to apply them.

```lean
#float_info [errors] Binary32
-- Float range and error information: binary interchange
--   standard: IEEE 754-2019 binary32
--
-- Checked numerical guarantees:
--   [verified; rounding] IEEE nearest-even operation semantics
--     Each listed finite primitive equals one nearest-even rounding of its exact real operation.
--   [verified; range] IEEE directed rounding and interval enclosures
--     Directed endpoints and interval operations enclose the exact real result.
--   [not available; range] finite-only range-limited directed rounding and dyadic interval arithmetic
--     Range-limited directed endpoints enclose exact dyadic add, subtract, and multiply results.
--   [verified; range, rounding, absolute error, relative error] generic rounding-grid error bounds
--     The real-valued roundAt grid has absolute error at most 1/2 ULP; for nonzero normal-range inputs, relative error is at most 2^-24.
--   [verified; exactness] exact compatible widening
--     A compatible widening preserves the represented finite value with zero rounding error.
--   [conditional; absolute error] mixed-precision sequential reduction and matrix entry bounds
--     Sequential dot products and matrix entries are bounded by the sum of their checked per-site rounding residual budgets.
--   [verified; absolute error, exactness] IEEE operation error bounds and Sterbenz exactness
--     Each finite primitive has at most 1/2 ULP absolute error; Sterbenz subtraction is exact in its proved factor-of-two domain.
--   [conditional; rounding, absolute error, exactness] IEEE cross-format cast semantics
--     A finite cast is one destination rounding with at most 1/2 destination ULP error, and grid extensions are exact.
--
-- Command scope:
--   This report exposes type-level contracts; detailed mode includes full hypotheses.
--   A compound-expression range needs input ranges; no such ranges are invented here.
--
-- More detail: `#float_info! [errors] YourType`
```

The sequential-reduction bound applies when casts, products, and accumulator updates each round. Its theorem adds the error allowance for each step, including the final output conversion. Applying it requires the specified IEEE formats and finiteness of the intermediate values; a matrix-entry bound applies the corresponding dot-product result to one row and column. The exact `dot` used earlier follows a different algorithm: it holds the products and sum exactly until its final rounding. The choice of reducer therefore determines both the computed value and the theorem available about it.

An error bound for a particular expression still needs a proof about its inputs; the type-level report cannot supply those hypotheses. `#float_help` prints the command options and a short template for configuring a type.

## Choosing imports

`import FloatLib` supplies the format families and their arithmetic. For binary `exp`, `log`, and `sin`, add `FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals`; this installs the configured and model `MathFunctions` instances too. The same import provides `Model.pow` and `^` on model values. It does not provide a power operation on configured `ExecFloat.Binary` values. The class itself and its host `Float` instance are available from the main import.

For a smaller set of dependencies, import the layer you need. `FloatLib.Floats.ExecFloat` gives the carrier, arithmetic, conversion, and the `run = spec` equations. `FloatLib.Floats.Formats.BinaryInterchange.Configured` adds `ExecFloat.Binary`, literals, and the configured operations, and `FloatLib.Floats.Formats.BinaryInterchange.Semantics` adds the real-valued theorems. `FloatLib.Floats.Formats.Posit` is the posit family and `FloatLib.Numerics` the representation-independent layer. A program that only computes can use `FloatLib.Floats.ExecFloat.Runtime`, which supplies the same certified arithmetic and conversion without the proof automation and inspection commands.

The [Arb adapter](https://github.com/lean-dojo/FloatLib/blob/main/tests/FloatLibTests/Arb/ModelTranscendentals.lean) belongs to the separate test workspace. It calls Arb through python-flint, so its results depend on that external library; it is not an import supplied by the FloatLib library package.

## Examples and extension guides

The [basic-operation examples](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Examples/BasicOperations.lean) are complete working programs. Compile the examples with `lake build FloatLib.Examples`. To try a calculation of your own, put the imports and abbreviations from this chapter in `Main.lean` and run `lake env lean Main.lean`; `#eval` prints a computed value and `#check` prints a type [@leanReference]. The [theorem guide](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/THEOREMS.md) lists theorem names, imports, and hypotheses; the [binary-format source guide](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/README.md) indexes the descriptor, model, specification, arithmetic, rounding, and configured interfaces.

The [backend guide](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/README.md) gives the registration procedure and the proof obligation at each step. The [one-word kernels](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/ExecFloat/Backends/Word/Small) provide a worked implementation. For a new format family, the [numerical interfaces](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Numerics/Core) define the required vocabulary and the [fixed-point family](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/FixedPoint) provides a compact implementation of the layers, from encoding and meaning through arithmetic and its proofs.

To explain why the two `0.3` comparisons differ, we need to look at the numbers each format can store. We will work out those values in the next chapter.
