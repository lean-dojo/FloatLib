---
number: "03"
slug: "the-numerical-models"
title: "How running code and proofs fit together"
summary: "FloatLib's certified operations run fast code that is proved equal to a short reference definition, and you can read every stored value as bits, as an exact value or as a real number."
phases: [execution, trust, numerical-models, binary-format, binary-arithmetic, status-and-directed, planner-and-configured, ieee-formats]
---

FloatLib distinguishes an executable operation from its reference specification. The implementation computes with packed words, carries and specialized rounding routines. The reference operation decodes the operands, computes the exact result and rounds once. A refinement theorem states that the two return the same stored word. Later proofs can therefore use the reference operation without repeating the proof about its implementation.

**Note:** Lean's kernel is the trusted checker that accepts or rejects proofs. An arithmetic kernel is a routine implementing a numerical operation. Lean's kernel checks the proofs about arithmetic kernels, and the compiler compiles their definitions into executable code.

## What happens when you add two numbers?

`ExecFloat F`, the executable float of format `F`, stores one number in that format: a packed `UInt32` for binary32, and wider words or arrays of limbs, smaller words chained together, for other formats, as the [storage definitions](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/Storage/Core.lean) specify. If you add one tenth and two tenths as `Binary32` values,

```lean
open FloatLib.Floats

#eval ExecFloat.Binary.toBits32 ((0.1 : Binary32) + (0.2 : Binary32))
-- 1050253722

#eval toString ((0.1 : Binary32) + (0.2 : Binary32))
-- "0.3"

#eval toString (0.3 : Binary32)
-- "0.3"

example (x y : Binary32) : x + y = ExecFloat.Spec.add x y :=
  ExecFloat.Proof.add_eq_spec x y
```

you get the bits $1050253722$, `0x3e99999a` in hex, and `0.3`, the shortest decimal that reads back as that word. Each `#eval` compiles and runs the binary32 implementation. The literal `0.3` rounds to the same word, so here, unlike in binary64, the sum really does equal 0.3, though none of these words is three tenths ([Chapter 02](#/chapter/from-reals-to-machine-numbers) explains why).

The `example` is the refinement theorem. `x + y` calls [[FloatLib.Floats.ExecFloat.add]], which runs the implementation selected for the format, and [[FloatLib.Floats.ExecFloat.Proof.add_eq_spec]] says that call equals the reference operation [[FloatLib.Floats.ExecFloat.Spec.add]], a short Lean function with no floating point inside. It decodes both operands to exact dyadics, fractions whose denominator is a power of two, adds them exactly, rounds once and packs the result.

By hand, the operands are exactly $13421773 \cdot 2^{-27}$ and $13421773 \cdot 2^{-26}$, with exact sum

$$
(13421773 + 2 \cdot 13421773)\,2^{-27} = 40265319 \cdot 2^{-27}.
$$

That lies between $1/4$ and $1/2$, where neighbouring binary32 numbers are $2^{-25}$ apart, so in those units it's $40265319/4 = 10066329.75$, which rounds to $10066330$, or $5033165 \cdot 2^{-24}$, the word the first `#eval` printed. The one rounding applies to the exact sum of the already-rounded operands, never to three tenths, and a refinement theorem has to keep that order. And `x + y` itself unfolds by definition to the public operation, so `rfl` (short for reflexivity) proves this:

```lean
example (x y : Binary32) : x + y = ExecFloat.add x y := rfl
```

## How do we know the fast code is right?

An implementation, also called a backend, only becomes a candidate with its proof attached. [[FloatLib.Floats.ExecFloat.Backend.Certified]] holds a cost estimate for the planner (the next section explains it), an executable `run` and a proof `run_eq_spec : run = spec`. No equation, no record. Calling `run` never evaluates the proof, which the compiler erases.

```lean
open FloatLib.Floats.ExecFloat in
example {α : Type} (spec : α) (certified : Backend.Certified spec) :
    certified.run = spec :=
  certified.run_eq_spec
```

For a binary operation, `α` is a function type such as `Model fmt → Model fmt → Model fmt`, so `run = spec` equates whole functions, and you can rewrite an operation inside a bigger expression without repeating the backend's proof. For a `Model fmt` result, a stored word, equal means the same packed word, down to a zero's sign and a NaN's encoding.

### How is a backend chosen?

Each format registers a [[FloatLib.Floats.ExecFloat.Capability]] for each of its six operations. A capability is a record describing one operation. It holds the specification, certified candidates with a mandatory exact baseline, and the choice of the planner, [[FloatLib.Floats.ExecFloat.Backend.selectCertified]], which picks the cheapest candidate the cost policy in scope ([[FloatLib.Floats.ExecFloat.Backend.PolicyFor]]) permits. Every candidate carries its proof, so [[FloatLib.Floats.ExecFloat.Backend.selectCertified_run_eq_spec]] holds for any policy and any candidate list, so an inaccurate cost estimate can affect performance without changing the result.

```lean
open FloatLib.Floats.ExecFloat in
example {α : Type} (spec : α) (policy : Backend.Policy)
    (candidates : Backend.CandidateSet (Backend.Certified spec)) :
    (Backend.selectCertified policy candidates).run = spec :=
  Backend.selectCertified_run_eq_spec policy candidates
```

Every candidate list includes the reference itself, `Backend.Certified.reference`, proved by `rfl`, and binary formats always carry the exact generic backend as the baseline when no specialized kernel is eligible. [[FloatLib.Floats.ExecFloat.Capability.implementation_is_selected]] and [[FloatLib.Floats.ExecFloat.Capability.execute_eq_implementation]] prove that public execution returns what the selected implementation returns, and [[FloatLib.Floats.ExecFloat.Proof.fullArithmeticCertificate]] gives all six equations for `Binary.Family 8 23`, the format descriptor (the record of field widths) behind `Binary32`:

```lean
example : ExecFloat.Proof.FullArithmeticCertificate (ExecFloat.Binary.Family 8 23) :=
  ExecFloat.Proof.fullArithmeticCertificate _
```

## Where do the code and its proofs live?

On disk the split is usually two files, executable definitions in `Runtime.lean` and refinement theorems in a sibling `Proof.lean`, as in [Figure 3.1](#/chapter/the-numerical-models/figure-ch05-runtime-proof-split). Only the proof file imports the lemmas and the theories from Mathlib, Lean's mathematics library, that justify the result. The packed posit backend is the one exception: its runtime module imports range lemmas to build valid stored codes, and compilation erases those proofs.

![Runtime.lean supplies executable definitions; Proof.lean establishes their equality with the reference operation](assets/ch05-runtime-proof-split.png "An executable definition and its refinement theorem have different jobs. The proof connects the runtime result to the reference operation.")

The [runtime module](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Runtime.lean), `FloatLib.Floats.ExecFloat.Runtime`, gives you arithmetic and conversion, and building them still requires their certificates. The [full module](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat.lean) adds the specification equations, proof automation and inspection commands. Lean's module system keeps an interface apart from the dependencies behind it, so you can use an operation without importing every lemma we needed to prove it correct.

## What if a fast kernel can't handle an input?

Let's look at the one-word multiplication kernel. Its gate, the decidable predicate [[FloatLib.Floats.Formats.BinaryInterchange.Model.NativeSmallWordMul.Eligible]] (a yes-or-no test Lean can compute), asks for an IEEE encoding, at most 64 encoded bits, at most 30 exponent bits and at most 31 fraction bits, the last so that the exact product of two significands fits below $2^{64}$. The kernel, `mulNormal?`, multiplies normal operands in `UInt64` arithmetic and returns `none` outside the normal range it handles. Its [proof module](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/Word/Small/Mul/Proof.lean) proves `mulNormal_refines`: whenever the kernel accepts, its answer is the format-generic finite kernel's.

```lean
open FloatLib.Floats.Formats.BinaryInterchange in
example {fmt : FloatFormat} (h : Model.NativeSmallWordMul.Eligible fmt)
    (x y r : Model fmt) (hr : Model.NativeSmallWordMul.mulNormal? x y = some r) :
    Model.FiniteKernel.mul? x y = some r :=
  Model.NativeSmallWordMul.mulNormal_refines h x y r hr
```

A `none` isn't an error or an IEEE invalid operation. It means the kernel declined, as it does when two normal inputs have a product below the normal range, and the input goes to the exact baseline, like a specialist referring a patient back to the general practitioner. For addition, [[FloatLib.Floats.Formats.BinaryInterchange.Model.AddBackend.word]] falls back to the width-generic [[FloatLib.Floats.Formats.BinaryInterchange.Model.AddBackend.generic]] when the eligible kernel declines, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.AddBackend.word_eq_spec]] follows the same branches for every format descriptor, named or not.

```lean
open FloatLib.Floats.Formats.BinaryInterchange in
example (fmt : FloatFormat) (x y : Model fmt) :
    Model.AddBackend.word x y = Model.Spec.add x y :=
  Model.AddBackend.word_eq_spec x y
```

The dispatcher never compares its answer with the reference. The proof covers both branches before compilation, so the running program only checks its inputs and computes one branch.

## How does the compiler swap in faster code?

Reference definitions often compute on `Nat` and `Int` and allocate wide integers, so you'd want the compiler to run something faster. A `@[csimp]` equation proves two Lean definitions equal and tells the compiler to use the second in generated code, once Lean's kernel has checked it. Here are two examples. [[FloatLib.Floats.Formats.BinaryInterchange.Model.FiniteKernel.add_eq_addRuntime]] states `@add? = @addRuntime?` ([the kernel source tour](#/chapter/performance/how-slow-definitions-get-swapped-for-fast-ones) goes through such replacements), and [[FloatLib.Numerics.FixedWord.IntegerSquareRoot.natSqrt_eq_sqrtNat]] states `Nat.sqrt = sqrtNat`, so every compiled `Nat.sqrt` in a module that imports `FloatLib.Kernels`, yours included, takes FloatLib's machine-word path for inputs below $2^{64}$ and a checked Newton iteration above that, as the [module docstring](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels.lean) records.

```lean
#check @FloatLib.Floats.Formats.BinaryInterchange.Model.FiniteKernel.add_eq_addRuntime
-- Formats.BinaryInterchange.Model.FiniteKernel.add_eq_addRuntime : @Formats.BinaryInterchange.Model.FiniteKernel.add? =
--   @Formats.BinaryInterchange.Model.FiniteKernel.addRuntime?

#eval Nat.sqrt 1000000
-- 1000

#print axioms FloatLib.Numerics.FixedWord.IntegerSquareRoot.natSqrt_eq_sqrtNat
-- 'FloatLib.Numerics.FixedWord.IntegerSquareRoot.natSqrt_eq_sqrtNat' depends on axioms: [propext,
--  Classical.choice,
--  Quot.sound]
```

The `#eval` runs the replaced path, and `#print axioms` names the three standard axioms that Mathlib itself assumes (axioms are explained below). Correctness of the compiled replacement rests on the compiler honouring a proved equation.

The attributes `@[implemented_by]` and `@[extern]` select runtime implementations without requiring a theorem that they equal the logical definitions. The commands `#print axioms` and `Lean.collectAxioms` follow the logical definitions, so they do not establish this agreement. FloatLib's posit decoder [[FloatLib.Floats.Formats.Posit.Model.toDyadic?]] uses `@[implemented_by]`. A separate private theorem, `Internal.toDyadic?_eq` in the [decoder implementation](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Model/Decode.lean), proves agreement. [Chapter 08](#/chapter/posits-and-the-quire) explains the decoder.

### How is this different from code extraction?

Coq and Isabelle translate proved definitions into another language and trust the translator, and the target compiler may then optimize the output. FloatLib's fast kernel is itself a Lean definition compiled by Lean's own compiler [@moura2021lean4], with a certificate that Lean's kernel checked. Correctness at run time does rest on that compiler preserving their semantics, `@[csimp]` replacements included.

## What do the proofs assume?

Lean proofs rest on axioms, statements accepted without proof, and `#print axioms` lists those a theorem depends on. Compare these two. In a generic statement about a certified operation the certificate is an argument, so its assumptions don't show up:

```lean
#print axioms FloatLib.Floats.Formats.BinaryInterchange.Model.AddBackend.word_eq_spec
-- 'FloatLib.Floats.Formats.BinaryInterchange.Model.AddBackend.word_eq_spec' depends on axioms: [propext,
--  Classical.choice,
--  Quot.sound]

#print axioms FloatLib.Floats.ExecFloat.Proof.add_eq_spec
-- 'FloatLib.Floats.ExecFloat.Proof.add_eq_spec' does not depend on any axioms
```

`add_eq_spec` is assembled from two fields of whatever capability the format supplies, `execute_eq_implementation` and the selected certificate's `run_eq_spec`, so its own proof uses no axioms. A format's assumptions live in its certificate, and the binary addition dispatcher's are `propext`, `Classical.choice` and `Quot.sound` (propositional extensionality, the axiom of choice and the soundness of quotients), the usual axioms of classical mathematics in Lean.

Tests sit outside these proofs. Some finite checks use `native_decide`, which runs a check as compiled code. That saves build time over reduction in Lean's kernel at the price of trusting the compiler and evaluator for that check, as the [testing guide](https://github.com/lean-dojo/FloatLib/blob/main/tests/README.md#trust-surface) lists, and the general arithmetic proofs don't use native evaluation. The functions of the [unchecked host-arithmetic module](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/NativeFPU/Unchecked.lean), such as `NativeFPU.Unchecked.add32`, call the machine's own `Float32` or `Float` operation behind a guard, so they rest on host assumptions in place of a refinement theorem, and no policy can select them. Comparing their outputs with the proved kernels can find disagreements, as [Chapter 13](#/chapter/lean-native-floats/how-to-use-the-processors-own-arithmetic) shows, but can't supply the missing theorem.

## One stored value, three readings

Because every kernel is proved equal to the reference, numerical theorems can use the reference and ignore carries and rounding bits. To state them we need to know what a stored word means. Add one and the binary32 number nearest a hundred-millionth, and you get one back with the inexact flag set. Read as bits, one theorem pins down which bits came back, down to the sign of zero and the choice of NaN ("not a number"). Read as a real number, another says that for a conventional IEEE format with finite inputs and output it's the exact sum rounded once, but that reading can't tell the two zeros apart or see a NaN payload. Exact dyadics sit in between and keep the sign of zero.

### How to look at the stored bits

[[FloatLib.Floats.ExecFloat.Binary.toModel]] turns an `ExecFloat` into the [[FloatLib.Floats.Formats.BinaryInterchange.Model]] that theorems quantify over. A `Model fmt` has one field, `bits`, of type `fmt.ExecWord`, short for `BitVec fmt.bitWidth`, so everything the word means comes from the decoders:

```lean
open FloatLib.Floats.Formats.BinaryInterchange

#print Model
-- structure FloatLib.Floats.Formats.BinaryInterchange.Model (fmt : FloatFormat) : Type
-- number of parameters: 1
-- fields:
--   FloatLib.Floats.Formats.BinaryInterchange.Model.bits : fmt.ExecWord
-- constructor:
--   FloatLib.Floats.Formats.BinaryInterchange.Model.mk {fmt : FloatFormat} (bits : fmt.ExecWord) : Model fmt
```

`signBit`, `expField` and `fracField` mask out the three fields, and classifiers such as [[FloatLib.Floats.Formats.BinaryInterchange.Model.isNaN]] and [[FloatLib.Floats.Formats.BinaryInterchange.Model.isFinite]] read them by the rules of the descriptor `fmt : FloatFormat`, which supplies the exponent and fraction widths, the bias and the encoding ([Chapter 07](#/chapter/low-precision-formats-for-machine-learning) covers the non-IEEE encodings). The real-valued arithmetic theorems need [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.isIEEE]], true exactly when the encoding is `ieee` and the bias is the conventional $2^{w-1} - 1$ for exponent width $w$.

### How to see the exact value

A finite word denotes a dyadic rational $(-1)^s \cdot m \cdot 2^e$ with $m \in \mathbb{N}$ and $e \in \mathbb{Z}$, which [[FloatLib.Numerics.Dyadic]] stores as `negative`, `significand` and `exponent`, so zero keeps its sign. [[FloatLib.Floats.Formats.BinaryInterchange.Model.toDyadic?]] decodes, succeeding exactly when the word is finite ([[FloatLib.Floats.Formats.BinaryInterchange.Model.toDyadic?_isSome_eq_isFinite]]). Binary32 puts one at $8388608 \cdot 2^{-23}$ and the least subnormal, its smallest positive value, at $1 \cdot 2^{-149}$:

```lean
/-- The binary32 word for 1.0. -/
def one32 : Model FloatFormat.binary32 := Model.ofNatBits 0x3f800000

/-- The binary32 word nearest to 1e-8. -/
def tiny32 : Model FloatFormat.binary32 := Model.ofNatBits 0x322bcc77

#eval Model.toDyadic? one32
-- some { negative := false, significand := 8388608, exponent := -23 }

#eval Model.toDyadic? tiny32
-- some { negative := false, significand := 11258999, exponent := -50 }

#eval Model.toDyadic? (Model.posMinSubnormal FloatFormat.binary32)
-- some { negative := false, significand := 1, exponent := -149 }
```

Hang on to `tiny32`'s significand 11258999 and exponent $-50$, which decide how its sum with one rounds. [[FloatLib.Floats.Formats.BinaryInterchange.Model.ExactValue]] extends this reading to every word, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.exactValue]] keeps the dyadic, the infinity's sign, or the NaN's sign, signaling class and whole fraction field. A bit-for-bit comparison against an external oracle, another implementation we check against, needs all of them.

```lean
#eval Model.exactValue (Model.negZero FloatFormat.binary32)
-- FloatLib.Floats.Formats.BinaryInterchange.Model.ExactValue.finite { negative := true, significand := 0, exponent := 0 }

#eval Model.exactValue (Model.posInf FloatFormat.binary32)
-- FloatLib.Floats.Formats.BinaryInterchange.Model.ExactValue.infinity false

#eval Model.exactValue (Model.canonicalNaN FloatFormat.binary32)
-- FloatLib.Floats.Formats.BinaryInterchange.Model.ExactValue.nan false false 4194304
```

Negative zero keeps `negative := true`. The canonical NaN is positive and quiet, and its fraction field, $4194304 = 2^{22}$, is the quiet bit alone.

### How to read a word as a real number

[[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal]] decodes and applies [[FloatLib.Numerics.Dyadic.toReal]], giving $m \cdot 2^{e}$ with the sign applied. It's total, defined for every word, sending a NaN or an infinity to $0$, the way a spreadsheet fills empty cells with 0, so a 0 no longer tells you whether a value was zero or missing. A total function is easier in algebra than the partial `toReal?`, so an arithmetic theorem establishes finiteness before it treats `toReal` as a result's value. `represents_iff` says `Represents x r` holds exactly when `isFinite x = true` and `toReal x = r`. Both zeros still represent $0$, so `Represents x 0` is enough for real algebra but not for a bit-for-bit conformance claim. [Figure 3.2](#/chapter/the-numerical-models/figure-ch06-three-readings) follows `tiny32` through all three readings, with nothing rounded along the way.

![Three cards read tiny32 as stored fields (sign 0, exponent 100, fraction 2870391), an exact dyadic (significand 11258999, exponent -50), and the real value 11258999 times 2^-50; the arrows decode and interpret without rounding](assets/ch06-three-readings.png "One finite word, read as stored fields, an exact dyadic, and a real value.")

## Why does adding a tiny number to one give back one?

Back to our example. Take $x = 1$ and $y$ the binary32 value nearest to $10^{-8}$, which is $11258999 \cdot 2^{-50}$. Just above $1$, binary32 numbers are $2^{-23} \approx 1.19 \times 10^{-7}$ apart, and $y$ covers only about $0.084$ of that gap, so the representable value nearest the exact sum is $1$ itself.

```lean
#eval Model.add one32 tiny32
-- 1

#eval Model.add one32 tiny32 (status := true)
-- { value := 1, status := { inexact := true }, ternary := Ordering.lt }
```

In units of $2^{-50}$, the next binary32 value above one is $2^{27}$ units on, so the midpoint is $2^{26}$ units above one, and the increment is only $11258999$ units, with

$$
0 < 11258999 < 2^{26} = 67108864.
$$

That one integer inequality proves both facts the example printed, that nearest rounding returns one and that it's inexact, and it rules out a tie. The returned word, `0x3f800000`, doesn't remember the increment, but its `inexact` flag and its ternary value `Ordering.lt`, saying the result landed below the exact sum, come from comparing the rounded result with the exact $1 + y$.

## How are the reference operations defined?

The way we just worked: decode, compute exactly, round once. [[FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.add]] decodes both operands with `toDyadic?`, and if both succeed it adds the dyadics exactly with `addDyadic` and rounds once with [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundDyadic]]. Otherwise it follows the descriptor's NaN and infinity rules. [[FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.mul]] and [[FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.fma]] also round an exact result once, which is what makes the fused multiply-add fused. A quotient of dyadics is a general rational, so [[FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.div]] rounds a scaled rational with `roundRatScaled`, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.sqrt]] hands a positive finite input to an exact square-root routine.

<details>
<summary>The square-root connection to Lean's logical model</summary>

Lean's core library has its own logical float model, `Float.Model.UnpackedFloat`. For an IEEE descriptor and a finite input with a clear sign bit, `+0` included, [[FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.sqrt_eq_model]] says our square root is that model's result repacked, and `Spec.sqrt_eq_model_of_isZero` covers `-0`. Negative nonzero inputs, infinities and NaNs aren't covered. And agreeing with Lean's logical float model isn't the same as agreeing with host instructions.

</details>

The dispatched operations are proved equal to these references at every descriptor, with no IEEE assumption, as in [[FloatLib.Floats.Formats.BinaryInterchange.Model.Proof.add_eq_spec]], `add x y = Spec.add x y`.

## What does the addition theorem say about real numbers?

For rounding on $\mathbb{R}$ we use the grid of Boldo and Melquiond's Flocq, a floating-point library for Coq [@boldoMelquiond2011]. Picture the reals a format holds exactly as points on the line, evenly spaced between consecutive powers of two, with the spacing doubling at each one in the normal range and staying at $2^{e_{\min}}$ below it (gradual underflow). For $2^{e-1} \le |x| < 2^{e}$, [[FloatLib.Floats.Formats.BinaryInterchange.Model.fexpOf]] gives the spacing exponent as Flocq's [[FloatLib.Floats.Formats.Flocq.fltExp]] of the least subnormal exponent $e_{\min}$ and the precision $p = w_f + 1$, the fraction bits plus the hidden one:

$$\mathrm{fexp}(e) = \max\bigl(e - p,\; e_{\min}\bigr).$$

[[FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt]] is Flocq's [[FloatLib.Floats.Formats.Flocq.round]] on this grid with the [[FloatLib.Floats.Formats.Flocq.nearestEven]] rule. The grid has no largest point, so `roundAt` never overflows, while a packed executable operation can, which is why an equation between the two needs a finite executable result. Rounding a real to nearest moves it by at most half an ulp (short for unit in the last place), the gap between neighbouring grid points, $|\mathrm{roundAt}_f(x) - x| \le \tfrac12 \mathrm{ulp}_f(x)$, proved in [Chapter 04](#/chapter/the-mathematics-of-rounding) as [[FloatLib.Floats.Formats.BinaryInterchange.Model.abs_roundAt_sub_le]] with [[FloatLib.Floats.Formats.BinaryInterchange.Model.halfUlpAt]] on the right.

All of this builds toward [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt]]. For `x y : Model fmt` it states

$$\operatorname{toReal}(\operatorname{add}(x, y)) = \operatorname{roundAt}_{f}\bigl(\operatorname{toReal}(x) + \operatorname{toReal}(y)\bigr)$$

under two hypotheses, `fmt.isIEEE = true` and `isFinite (add x y) = true`. Finite operands come for free, since a NaN or infinite operand makes the sum a NaN or an infinity. It's an equation, not a bound, and for `one32` and `tiny32` both sides are $1$, because the exact sum is closer to $1$ than to its upper neighbour, as [Figure 3.3](#/chapter/the-numerical-models/figure-ch06-one-rounding) shows.

![Binary32 number line near 1, with neighbours 1 - 2^-24 and 1 + 2^-23; the exact sum 1 + 11258999 · 2^-50 lies about 0.084 of the gap above 1, before the midpoint, and rounds to 1 with inexact set](assets/ch06-one-rounding.png "The exact sum rounds back to one, setting the inexact flag.")

### How to apply the theorem in Lean

For two concrete words both hypotheses are decidable, so `decide` closes the side goals `apply` leaves:

```lean
example :
    Model.toReal (Model.add one32 tiny32) =
      Model.roundAt FloatFormat.binary32
        (Model.toReal one32 + Model.toReal tiny32) := by
  apply Model.toReal_add_eq_roundAt <;> decide
```

For symbolic words, whose bits you don't know, our `numerics` tactic knows the registered refinement theorems and discharges `isIEEE` for named formats:

```lean
example (x y : Model FloatFormat.binary32)
    (hout : Model.isFinite (Model.add x y) = true) :
    Model.toReal (Model.add x y) =
      Model.roundAt FloatFormat.binary32
        (Model.toReal x + Model.toReal y) := by
  numerics
```

### How to get an error bound for one addition

Chain `toReal_add_eq_roundAt` with `abs_roundAt_sub_le` and you get [[FloatLib.Floats.Formats.BinaryInterchange.Model.abs_toReal_add_sub_le]], which needs only a finite result. Its `halfUlpAt` is taken at the exact sum. For `one32` and `tiny32` that sum lies between one and two, where the spacing is $2^{-23}$, so the bound is $2^{-24}$, and the actual error, $11258999 \cdot 2^{-50}$, is smaller. In a symbolic proof keep the bound at the exact expression, because at the rounded output the spacing can change when rounding crosses a power of two.

```lean
example (x y : Model FloatFormat.binary32)
    (hout : Model.isFinite (Model.add x y) = true) :
    |Model.toReal (Model.add x y) - (Model.toReal x + Model.toReal y)| ≤
      Model.halfUlpAt FloatFormat.binary32 (Model.toReal x + Model.toReal y) :=
  Model.abs_toReal_add_sub_le x y FloatFormat.isIEEE_binary32 hout
```

Subtraction, multiplication, fused multiply-add, division, square root and casts into an IEEE format have matching theorems, which [Chapter 05](#/chapter/ieee-binary-formats) lists with their hypotheses.

## How to prove a result is finite

The finite-result hypothesis is necessary because `toReal` maps exceptional values to $0$. Without that hypothesis, a real-valued statement could confuse a NaN with a numerical zero. It also excludes overflow: adding two copies of the largest finite binary32 value produces $+\infty$, whose `toReal` value is $0$, while $\mathrm{roundAt}_f(2\cdot\mathrm{maxFinite})$ is near $6.8\times10^{38}$.

For symbolic inputs, [[FloatLib.Floats.Formats.BinaryInterchange.Model.isFinite_add_of_abs_add_le_posMaxFinite]] says the executable sum is finite when $|x| + |y|$ is at most the value of [[FloatLib.Floats.Formats.BinaryInterchange.Model.posMaxFinite]], $16777215 \cdot 2^{104}$ or about $3.4 \times 10^{38}$ for binary32, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt_of_abs_add_le_posMaxFinite]] folds that into the refinement, so the output hypothesis never appears. Subtraction, multiplication, division and fused multiply-add have the same pair with their own bound, and division keeps its nonzero-divisor hypothesis.

```lean
example (x y : Model FloatFormat.binary32)
    (hx : Model.isFinite x = true) (hy : Model.isFinite y = true)
    (hbound : |Model.toReal x| + |Model.toReal y| ≤
      Model.toReal (Model.posMaxFinite FloatFormat.binary32)) :
    Model.toReal (Model.add x y) =
      Model.roundAt FloatFormat.binary32
        (Model.toReal x + Model.toReal y) :=
  Model.toReal_add_eq_roundAt_of_abs_add_le_posMaxFinite x y
    FloatFormat.isIEEE_binary32 hx hy hbound
```

That triangle bound can be too cautious, since the largest finite value plus its negation is exactly zero. When cancellation matters, `isFinite_add_of_abs_toReal_add_le_posMaxFinite` bounds the exact sum itself.

Only the real-valued refinement needs `fmt.isIEEE = true`. Its bridge to `roundAt` runs through Lean's IEEE-shaped float model, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_eq_unpackedToReal_toModel]] identifies the binary decoder with it exactly when the descriptor is conventionally IEEE. So a non-IEEE format, FNUZ (unsigned-zero) and finite-only encodings included, has exact dyadic semantics and executable arithmetic, but no `roundAt` theorem for its operations.

## How to use these theorems on `Binary32` values

`ExecFloat.Binary.toReal` reads a `Binary32` value as a real through `toModel`, and where a [refinement proof](#/chapter/using-the-library/how-to-prove-your-first-theorem) tells you which word comes back, [[FloatLib.Floats.ExecFloat.Binary.toReal_add_eq_roundAt]] tells you its value: for finite operands whose sum doesn't overflow, `a + b` is the exact real sum rounded once by `roundAt`. Because `+` runs whatever implementation the format selected, it needs `HasSpec cap Configured.Spec.add`, saying that implementation's reference operation is the model's, and instance search (Lean's automatic search for such facts) proves it for every capability the library declares. Matching theorems cover `-`, `*`, `/`, fused multiply-add and square root, and [[FloatLib.Floats.ExecFloat.Binary.abs_toReal_add_sub_le]] and its siblings turn each into an error bound of half an ulp:

```lean standalone
import FloatLib

open FloatLib.Floats

open Formats.BinaryInterchange

theorem toReal_add_binary32 (a b : Binary32) (hout : (a + b).isFinite = true) :
    (a + b).toReal = Model.roundAt FloatFormat.binary32 (a.toReal + b.toReal) :=
  ExecFloat.Binary.toReal_add_eq_roundAt hout

theorem add_error_binary32 (a b : Binary32) (hout : (a + b).isFinite = true) :
    |(a + b).toReal - (a.toReal + b.toReal)| ≤
      Model.halfUlpAt FloatFormat.binary32 (a.toReal + b.toReal) :=
  ExecFloat.Binary.abs_toReal_add_sub_le hout
```

`hout` says the sum is finite, which you can decide by looking at the result. Square root has no such premise and asks instead for a nonnegative operand, either signed zero included, since a negative input gives NaN, which has no real value. `hformat : format.isIEEE = true` defaults to a `decide` proof for a concrete format such as binary32, and for a variable format a hypothesis in context or `(hformat := h)` supplies it. For a nonzero value in the normal range `#float_info [errors] Binary32` reports the relative bound $2^{-24}$.

[[FloatLib.Floats.ExecFloat.Binary.toModel_add]] and its counterparts for the other five named operations are `simp` lemmas, rewrite rules for the `simp` tactic, that move a goal about a configured operation to the model in every rounding direction. They take the same `HasSpec` instance argument, and calls with `(status := true)` have their own lemmas, such as `IEEEOutcome.toModel_div`, which keep the result, the flags and the ternary value. `Model.At fmt r` puts the represented value in the type: it's an encoded value of format `fmt` tagged with a proof, erased at runtime, that it denotes the real $r$, and operations such as `Model.At.add` take the finiteness hypotheses and return a value tagged with the rounded result.

```lean standalone
import FloatLib

open FloatLib.Floats

open Formats.BinaryInterchange

example (a b : Binary32) :
    ExecFloat.Binary.toModel (ExecFloat.Binary.add a b) =
      Model.add (ExecFloat.Binary.toModel a) (ExecFloat.Binary.toModel b) :=
  ExecFloat.Binary.toModel_add a b (mode := .nearest)

example {fmt : FloatFormat} {r s : Real}
    (u : Model.At fmt r) (v : Model.At fmt s)
    (hfmt : fmt.isIEEE = true)
    (hout : Model.isFinite (Model.add u.1 v.1) = true) :
    (Model.numericalSystem fmt).denote (Model.At.add u v hfmt hout).1 =
      .finite (Model.roundAt fmt (r + s)) := by
  numerics
```

In the second example `Model.At.add` carries $\mathrm{roundAt}(r + s)$ as its index, the real number in its type, and `numerics` closes the proof with the rule, registered under `numerics_simps`, that an `At` value denotes its index. `u` and `v` carry their finite denotations in their `.2` fields, so there's no `ha` or `hb`, but you supply `hout`, because two finite inputs can have a sum that doesn't fit. All of these theorems are about FloatLib's software arithmetic. Relating it to Lean's native `Float32`, to C operations or to GPU instructions takes another argument, which [chapter 13](#/chapter/lean-native-floats) makes for Lean's native floats.

## What about formats that aren't binary floats?

Posits, fixed point, logarithmic codes and block-scaled values all answer the same question, what does this stored code mean, through one interface, [[FloatLib.Numerics.NumericalSystem]]. Its `denote` maps a `Code` to a [[FloatLib.Numerics.NumericalValue]]: `finite x`, `infinity negative` or the catch-all `exceptional e`. [[FloatLib.Numerics.ExceptionalValue]] covers the rest: NaNs with their metadata (a binary NaN's payload there leaves out the quiet bit, and its sign and signaling class get fields of their own), posit NaR ("not a real"), reserved words and undefined results. [[FloatLib.Numerics.NumericalSystem.Represents]] says a code denotes a particular finite scalar.

`Model fmt` plugs in twice, as `numericalSystem` over $\mathbb{R}$ and as `exactNumericalSystem` over `Numerics.Dyadic`, which keeps the sign of a finite zero. On this interface an operation's contract is a theorem too. Under `fmt.isIEEE = true`, `add_refines` says `Model.add` satisfies [[FloatLib.Numerics.Operation.Finite2If]] with specification `fun x y => roundAt fmt (x + y)` and condition `isFinite result = true`, and since [[FloatLib.Numerics.Operation.Refines]] is a relation in `Prop`, the contract adds no runtime data.

## How to round down or up for a guaranteed bound

Interval arithmetic keeps a lower and an upper bound around the exact answer, rounding down at one end and up at the other. The `mode` option of [[FloatLib.Floats.Formats.BinaryInterchange.Model.add]] and the other operations runs all six directions of [[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEERoundingMode]], the five IEEE ones plus MPFR's `away` from [chapter 02](#/chapter/from-reals-to-machine-numbers), at every descriptor.

A directed bound has to survive overflow, so [[FloatLib.Floats.Formats.BinaryInterchange.Model.toEReal]] maps words into Mathlib's `EReal`, the extended reals, which add a bottom $\bot$ and a top $\top$ for the two infinities. It sends a NaN to $0$ (the partial `toEReal?` returns `none` on NaNs and only on NaNs), so the theorems exclude NaNs but need no finiteness hypothesis on the output. [[FloatLib.Floats.Formats.BinaryInterchange.Model.toEReal_add_down_le]] and [[FloatLib.Floats.Formats.BinaryInterchange.Model.le_toEReal_add_up]] put the exact real sum between the downward- and upward-rounded sums, with the same pairs for subtraction, multiplication, division and square root. On them we built the library's interval arithmetic, in the tradition of Moore [@moore1966]. For a conventional IEEE descriptor and intervals with finite, ordered endpoints, [[FloatLib.Floats.Formats.BinaryInterchange.Model.Interval.add_sound]] traps the exact sum of two reals between the downward-rounded sum of the lower bounds and the upward-rounded sum of the upper bounds. An endpoint that overflows outward becomes an infinity. The resulting enclosure is unbounded but still contains the exact value.

## How to see which flags an operation raised

A status-bearing operation returns its exception flags together with its value, without depending on a mutable status register. [[FloatLib.Numerics.IEEEStatus]] has five Booleans, `invalid`, `divideByZero`, `overflow`, `underflow` and `inexact`, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEEOutcome]] holds a result word, a status and the ternary value of [chapter 04](#/chapter/the-mathematics-of-rounding/how-to-choose-a-rounding-direction). With `(status := true)` an operation returns this outcome, with flags computed from the same exact intermediate and rounded result as the value, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.value_add]] proves that asking for status never changes the value. [[FloatLib.Numerics.IEEEStatus.union]] combines the flags from multiple outcomes using logical OR.

Overflow and underflow both round the exact value as if the exponent range never ended. Following IEEE 754-2019 Section 7.4 [@ieee754_2019] and MPFR's exception definition [@fousseMpfr2007], overflow means that rounding lands beyond the largest finite value. Underflow follows Section 7.5, with tininess (being too small for the normal range) detected after rounding ([[FloatLib.Floats.Formats.BinaryInterchange.Model.dyadicIsTinyAfterRounding]]), and needs tiny *and* inexact, so an exact subnormal raises nothing. The two never come together. [[FloatLib.Floats.Formats.BinaryInterchange.Model.div_divideByZero]], [[FloatLib.Floats.Formats.BinaryInterchange.Model.sqrt_invalid]] and their siblings in [Chapter 05](#/chapter/ieee-binary-formats) give every flag's exact condition.

Dividing one by positive zero gives infinity and raises only `divideByZero`, while doubling the largest finite value overflows to the same `0x7f800000` with `overflow` and `inexact`, and `Ordering.gt` says that infinity lies above the exact product. Infinity minus infinity is invalid and gives the canonical quiet NaN, `0x7fc00000`.

```lean
/-- The binary32 word for 2.0. -/
def two32 : Model FloatFormat.binary32 := Model.ofNatBits 0x40000000

#eval Model.div one32 (Model.posZero FloatFormat.binary32) (status := true)
-- { value := inf, status := { divideByZero := true }, ternary := Ordering.eq }

#eval Model.mul (Model.posMaxFinite FloatFormat.binary32) two32 (status := true)
-- { value := inf, status := { overflow := true, inexact := true }, ternary := Ordering.gt }

#eval Model.sub (Model.posInf FloatFormat.binary32) (Model.posInf FloatFormat.binary32) (status := true)
-- { value := nan, status := { invalid := true }, ternary := Ordering.eq }
```

The least subnormal added to itself gives an exact subnormal and no flags. Halved, it lands exactly halfway between zero and itself, and ties to even picks zero. That tiny, inexact result raises `underflow` and `inexact`.

```lean
/-- The binary32 word for 0.5. -/
def half32 : Model FloatFormat.binary32 := Model.ofNatBits 0x3f000000

#eval Model.add (Model.posMinSubnormal FloatFormat.binary32)
  (Model.posMinSubnormal FloatFormat.binary32) (status := true)
-- { value := 3e-45, status := {}, ternary := Ordering.eq }

#eval Model.mul (Model.posMinSubnormal FloatFormat.binary32) half32 (status := true)
-- { value := 0, status := { underflow := true, inexact := true }, ternary := Ordering.lt }
```

## How to bound a calculation with several roundings

A longer calculation rounds at every step. Let's add three numbers. In an IEEE format with finite inputs and finite decoded results we get $s_1 = \mathrm{roundAt}_f(x+y)$ and $s_2 = \mathrm{roundAt}_f(s_1+z)$, each step with its own finiteness argument, and the total error splits exactly as

$$
s_2-(x+y+z) = \bigl(s_2-(s_1+z)\bigr) + \bigl(s_1-(x+y)\bigr).
$$

The triangle inequality combines the two local bounds, and both errors stay, because applying the theorem twice doesn't give one rounding of the three-input sum. For configured binary programs the [`roundoff` tactic](#/chapter/proving-numerical-bounds/how-to-get-an-error-bound-for-floating-point-code), which needs `import FloatLib.Floats.Formats.BinaryInterchange.Automation.Roundoff`, composes the per-operation theorems and their range conditions into an error bound from the code. [Chapter 04](#/chapter/the-mathematics-of-rounding) goes further.

## How to add your own format or backend

You don't always need a new format family: the [custom-format examples](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Examples/CustomFormats.lean) configure a 16-bit binary telemetry type with its own bias and NaN encoding without one. A new backend for an existing format has to compute the same reference operation, and the [backend guide](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/README.md) gives the registration procedure and its proof obligations, which the [one-word kernels](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/ExecFloat/Backends/Word/Small) discharge. A new format family also needs a meaning for its stored values, and the [numerical interfaces](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Numerics/Core) define those contracts, where `EncodedFormat` and `FormatSemantics` keep the computable code type apart from its possibly noncomputable meaning. A new rounder states its rounding, saturation and flush-to-zero choices in [[FloatLib.Numerics.QuantizationPolicy]] and proves the obligation [[FloatLib.Numerics.Quantization.Spec.Implements]] against [[FloatLib.Numerics.Quantization.Spec]], and the [endpoint-adapter example](#/chapter/proving-numerical-bounds/how-to-choose-a-different-endpoint-format) uses one shared contract with different representations. The [fixed-point family](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/FixedPoint) is a compact example to read, from encoding through arithmetic and its proofs.
