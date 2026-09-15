---
number: "05"
slug: why-execution-and-proofs-are-separate
title: Executable arithmetic and its proofs
summary: An equation between an implementation and its reference operation lets numerical proofs apply to executable arithmetic.
phases: [execution, trust]
---

When we write `x + y` on a FloatLib type, we call an implementation selected for that format. We can reason about its result using a reference operation that decodes the operands, computes exactly, and rounds once: a theorem says the two return the same value. The reference makes the arithmetic meaning explicit; the implementation can use packed words, carries, and specialized rounding routines. Once we have proved them equal, we can use the reference in later proofs without repeating the word-level argument.

Lean's kernel is the trusted checker that accepts or rejects proof terms, reducing definitions as needed. An arithmetic kernel is an implementation of an operation for a class of formats. The distinction matters here: Lean's kernel checks the equations about arithmetic kernels, while the compiler translates their executable definitions into code.

<a id="one-value-type-one-operation-and-the-equation-between-them"></a>

## From addition to its reference operation

`ExecFloat F` stores the bit pattern of one value in format `F`. Binary formats use a byte when they fit in 8 bits, then `UInt16`, `UInt32`, or `UInt64` as the width increases. Above 64 bits, `ExecFloat.Binary` uses the exact-width proof model. Above 128 bits, `ExecFloat.BinaryLimbs` provides an alternative representation in arrays of 32-bit words. The [storage definitions](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/Storage/Core.lean) specify these choices.

The notation `x + y` is [[FloatLib.Floats.ExecFloat.add]], which calls the implementation selected for `F`. The theorem [[FloatLib.Floats.ExecFloat.Proof.add_eq_spec]] says that this call equals [[FloatLib.Floats.ExecFloat.Spec.add]], the reference operation of the format. For a binary format the reference is a short Lean function with no floating point inside it: decode both operands to exact dyadics, add them exactly, round once, pack the result. For binary32, the descriptor fixes 8 exponent bits and 23 fraction bits. We can inspect the same addition as packed bits, display its exact dyadic value, and then rewrite it to its specification in a proof:

```lean
open FloatLib.Floats

abbrev Binary32 := ExecFloat.Binary 8 23

#eval ExecFloat.Binary.toBits32 ((1 : Binary32) + (2 : Binary32))
-- 1077936128

#eval toString ((0.1 : Binary32) + (0.2 : Binary32))
-- "5033165 * 2^-24"

#eval toString (0.3 : Binary32)
-- "5033165 * 2^-24"

example (x y : Binary32) : x + y = ExecFloat.Spec.add x y :=
  ExecFloat.Proof.add_eq_spec x y
```

The `#eval` lines compile and run the implementation selected for binary32. The first prints the bits of $3.0$, which is `0x40400000`. The second prints the exact dyadic that binary32 addition produces for $0.1 + 0.2$, namely $5033165 \cdot 2^{-24}$, about $0.30000001$. That is not the real number $0.3$. Binary32 has no code for $0.3$, and this is the nearest one, `0x3E99999A`. The third line, the literal $0.3$ rounded to binary32, therefore prints the same dyadic. In binary64 the same sum is one ulp away from the rounded $0.3$, which is the more familiar version of this example.

Read the evaluations and the proof together: we computed particular answers, then stated an equation for arbitrary inputs. Lean's kernel checks the proof term in the `example`, which relates the selected Lean implementation to `Spec.add` for every pair of operands.

We can recover the second answer without doing any floating-point arithmetic. The binary32 operands have exact values $13421773 \cdot 2^{-27}$ and $13421773 \cdot 2^{-26}$. Put them at the same scale and their sum is

$$
(13421773 + 2 \cdot 13421773)\,2^{-27} = 40265319 \cdot 2^{-27}.
$$

Near this sum, between $1/4$ and $1/2$, the binary32 grid spacing is $2^{-25}$. In units of that spacing the exact sum is $40265319/4 = 10066329.75$. Nearest rounding therefore chooses the integer $10066330$, giving $10066330 \cdot 2^{-25} = 5033165 \cdot 2^{-24}$, the printed answer. The literals have already been rounded when they become operands; the addition's single rounding is applied to the exact sum of those operands. A refinement theorem must preserve that order of events to describe the program accurately.

The notation `x + y` unfolds to the public operation by definition, so reflexivity proves this equality:

```lean
example (x y : Binary32) : x + y = ExecFloat.add x y := rfl
```

A value can also be paired with proofs about it. Lean erases fields in `Prop` during compilation, so those proof fields add no runtime data to the `ExecFloat F` value.

<a id="a-certificate-is-a-record-with-a-proof-inside"></a>

## Certifying an implementation

To register an implementation as a candidate, we package it with its proof in [[FloatLib.Floats.ExecFloat.Backend.Certified]]. A `Certified spec` is a record with three fields: a cost estimate used by the planner, an executable `run`, and a proof `run_eq_spec : run = spec`. Constructing this record requires the equation, so a function with a cost estimate alone cannot enter the certified candidate list. The proof is a `Prop` field and is erased by the compiler. Calling `run` executes the implementation without evaluating the proof.

```lean
open FloatLib.Floats.ExecFloat in
example {α : Type} (spec : α) (certified : Backend.Certified spec) :
    certified.run = spec :=
  certified.run_eq_spec
```

For a binary operation, `α` in the certificate is a function type such as `Model fmt → Model fmt → Model fmt`. The equation `run = spec` then identifies the whole function. Applying both sides to particular `x` and `y` gives `run x y = spec x y`; conversely, a backend that proves that equation for every pair can use function extensionality, `funext`, to construct the function equality. The `Certified.binary` constructor performs exactly that step. A caller can then rewrite an operation inside a larger expression without repeating the backend's proof about carries.

The result type determines what the equation preserves. When the result is a `Model fmt`, equality compares the packed word, including a zero's sign and a NaN's encoding. An equation between the decoded real values would be weaker: decoding alone cannot distinguish those words.

A format registers a [[FloatLib.Floats.ExecFloat.Capability]] for each of the six operations (add, sub, mul, div, sqrt, fma). The capability stores the specification, a list of certified candidates with a mandatory exact baseline, and the planner's choice among them. The planner, [[FloatLib.Floats.ExecFloat.Backend.selectCertified]], checks the candidates and keeps the one with the lowest estimated cost that the policy in scope ([[FloatLib.Floats.ExecFloat.Backend.PolicyFor]]) permits. A policy is a cost model that can, for example, cap the temporary memory a candidate may use.

Every candidate already carries a proof of agreement with the specification. Choosing among them therefore cannot change the result, as [[FloatLib.Floats.ExecFloat.Backend.selectCertified_run_eq_spec]] proves for any policy and any candidate list.

```lean
open FloatLib.Floats.ExecFloat in
example {α : Type} (spec : α) (policy : Backend.Policy)
    (candidates : Backend.CandidateSet (Backend.Certified spec)) :
    (Backend.selectCertified policy candidates).run = spec :=
  Backend.selectCertified_run_eq_spec policy candidates
```

The reference is itself always a candidate. `Backend.Certified.reference` uses the specification as its own baseline with a proof by `rfl`, and for binary formats the exact generic backend is always present as the mandatory baseline. When no specialized arithmetic kernel is eligible for a format, this baseline computes the result. The dispatchers in the next section use it whenever a specialized kernel declines an input.

We can change the cost estimates or the policy and select a different candidate; every choice still comes with the same equation relating its result to the specification. Two further fields of the capability, [[FloatLib.Floats.ExecFloat.Capability.implementation_is_selected]] and [[FloatLib.Floats.ExecFloat.Capability.execute_eq_implementation]], prove that public execution and the selected implementation return the same result.

The inspection command `#float_info` identifies the registered implementation for each operation. For `Binary32`, it prints `add, sub, mul, div, sqrt, fma = fixed-format word kernel (UInt32)`. This describes the selected Lean definitions; inspecting the generated code is a separate step. The six equations are also available as one statement, [[FloatLib.Floats.ExecFloat.Proof.fullArithmeticCertificate]], that ranges over all six operations at once. It is stated for the format descriptor rather than the value type, which is why the block below names `Binary.Family 8 23` where the earlier ones named `Binary 8 23`; `Binary 8 23` is `ExecFloat` applied to that family.

```lean
example : ExecFloat.Proof.FullArithmeticCertificate (ExecFloat.Binary.Family 8 23) :=
  ExecFloat.Proof.fullArithmeticCertificate _
```

## Runtime.lean and Proof.lean

Executable definitions usually live in `Runtime.lean`, with their refinement theorems in a sibling `Proof.lean`, as in [Figure 5.1](#/chapter/why-execution-and-proofs-are-separate/figure-ch05-runtime-proof-split). The runtime file imports the definitions needed to compute: decoders, integer operations, rounding rules, and shared types. The proof file imports that runtime file together with the lemmas and Mathlib theories needed to justify its result. Shared definitions, such as the storage types above, can be used by both.

![Runtime.lean supplies executable definitions; Proof.lean establishes their equality with the reference operation](assets/ch05-runtime-proof-split.png "An executable definition and its refinement theorem have different jobs. The proof connects the runtime result to the reference operation.")

Keeping theorem developments and tactics out of the execution import path reduces what a program that only computes has to load. `FloatLib.Floats.ExecFloat.Runtime` provides arithmetic without the proof automation and inspection commands brought in by `FloatLib.Floats.ExecFloat`.

If we improve an algorithm, we change its runtime definition and may need to revise its refinement proof. Numerical theorems can continue to use the same reference operation, so the word-level proof work stays with the implementation being changed.

We can follow this split in the one-word multiplication kernel. Its runtime module defines the eligibility predicate [[FloatLib.Floats.Formats.BinaryInterchange.Model.NativeSmallWordMul.Eligible]], a decidable proposition about the format descriptor (IEEE encoding, at most 64 encoded bits, at most 30 exponent bits, at most 31 fraction bits), and the arithmetic kernel `mulNormal?`, which multiplies normal operands in `UInt64` arithmetic and returns `none` for any operand or result outside the normal range it handles. The [refinement proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/Word/Small/Mul/Proof.lean) establishes `mulNormal_refines`: whenever the arithmetic kernel accepts, its answer is the answer of the format-generic finite kernel.

```lean
open FloatLib.Floats.Formats.BinaryInterchange in
example {fmt : FloatFormat} (h : Model.NativeSmallWordMul.Eligible fmt)
    (x y r : Model fmt) (hr : Model.NativeSmallWordMul.mulNormal? x y = some r) :
    Model.FiniteKernel.mul? x y = some r :=
  Model.NativeSmallWordMul.mulNormal_refines h x y r hr
```

The 31-bit fraction limit comes from the multiplication, rather than the width of the stored result. Including the hidden leading bit, each normalized significand is below $2^{32}$, so their exact product is below $2^{64}$ and fits the working word. A format can occupy at most 64 bits while having too many fraction bits for this product bound. The encoding-width condition makes field decoding possible; the fraction-width condition makes the intermediate arithmetic exact. After multiplication the kernel must still check whether normalization and rounding produce a result in the range it handles.

The premise `mulNormal? x y = some r` records that this particular call passed those checks. `none` means the partial kernel declined the call; it is not an IEEE invalid-operation result. Even two normal inputs can have a product below the normal range. The reference operation still has an answer in that case, and the total dispatcher must compute it. This division of work lets the local proof assume its acceptance premise while the dispatch proof establishes correctness for every input, including those the local kernel never handles.

A dispatcher handles a declined input by computing it through the exact baseline. For addition, the dispatcher [[FloatLib.Floats.Formats.BinaryInterchange.Model.AddBackend.word]] tries the specialized kernel the descriptor is eligible for and falls back to the width-generic exact baseline [[FloatLib.Floats.Formats.BinaryInterchange.Model.AddBackend.generic]] when it declines. The proof of [[FloatLib.Floats.Formats.BinaryInterchange.Model.AddBackend.word_eq_spec]] follows the same branches and discharges each with its local refinement theorem. The result holds for every format descriptor, not only the named ones.

```lean
open FloatLib.Floats.Formats.BinaryInterchange in
example (fmt : FloatFormat) (x y : Model fmt) :
    Model.AddBackend.word x y = Model.Spec.add x y :=
  Model.AddBackend.word_eq_spec x y
```

Following the branches is also enough to see why execution does not need a comparison against the reference on every call. On an accepted branch the refinement theorem already supplies the equality for all operands satisfying that branch's premises. On a declined branch the dispatcher calls the proved fallback. The proof combines these cases before compilation; the running program makes the input checks and computes one branch. The runtime quotient certificate in [chapter 13](#/chapter/kernels-fixed-word-algorithms) is a different construction: there, checking a proposed answer is an explicit part of the algorithm.

The same organization extends across the library. `Numerics` defines exact values and rounding independently of storage formats. `Kernels` implements arithmetic using those definitions, and `Floats` connects the kernels to formats and public operations. The dependency direction keeps a theorem about an exact integer or a rounding grid independent of the formats that later use it.

Choosing the [runtime module](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Runtime.lean) for a smaller import still gives us arithmetic backed by capabilities and conversion backed by quantizer contracts: constructing those operations requires their certificates. The [full module](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat.lean) adds the public specification equations, proof automation, and inspection commands. A program that only computes can use the same certified arithmetic without importing all the tools for proving further statements about it.

## Public and private imports

Lean's module system distinguishes an interface from the dependencies used to implement it. A `public import` makes the imported declarations available to clients; a plain `import` is local to the module. FloatLib uses `@[expose] public section` for its declarations and `public meta section` for elaborator code. These choices let a client use an operation without also importing every lemma used to prove its implementation correct.

Broad imports are convenient when exploring the library: `import FloatLib` supplies the formats and proof tools used throughout this guide. For a smaller program, a format-family import or an individual runtime module makes the dependencies more specific. Within an implementation, importing the decoder it uses directly also makes it easier to see which definitions an argument depends on.

<a id="what-csimp-does-and-what-it-does-not"></a>

## Compiler replacements with csimp

Reference definitions often compute on `Nat` and `Int` and allocate decoded records or wide intermediate integers. A compiler replacement can avoid those allocations while preserving the result. A `@[csimp]` equation proves two Lean definitions equal and instructs the compiler to replace the first with the second in generated code. Lean's kernel checks the equation before the compiler uses it. [The kernel source tour](#/chapter/kernels-fixed-word-algorithms/kernels-fixed-word-algorithms-and-limb-arrays) describes these replacements in the arithmetic kernels.

For addition, [[FloatLib.Floats.Formats.BinaryInterchange.Model.FiniteKernel.add_eq_addRuntime]] states `@add? = @addRuntime?`. On IEEE formats, the compiled implementation passes decoded fields directly to the finite adder, avoiding intermediate `Components` records. Other encodings use the descriptor-aware decoder. The equality is proved by `addRuntime_eq`.

For integer square root, [[FloatLib.Numerics.FixedWord.IntegerSquareRoot.natSqrt_eq_sqrtNat]] states `Nat.sqrt = sqrtNat`. Every compiled `Nat.sqrt` in a module that imports `FloatLib.Kernels` therefore takes a machine-word path when the input is below $2^{64}$ and the unchanged logical definition otherwise. This import changes the compiled implementation of `Nat.sqrt` in client code too, as the [module docstring](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels.lean) records.

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

The `#check` lets us inspect the equation the compiler uses. The `#eval` goes through the replaced machine-word path and agrees with the mathematical square root. We can call the readable definition while the compiler uses the replacement justified by that equation. The axiom list names the three standard axioms of classical mathematics that Mathlib itself assumes.

With `@[csimp]`, correctness of the compiled replacement depends on the compiler honouring a proved equation between two Lean definitions. The attributes `@[implemented_by]` and `@[extern]` can also change execution, but they do not require such an equation. `#print axioms` and `Lean.collectAxioms` follow the logical definition, so their output alone cannot establish that either kind of replacement agrees with it.

The posit decoder [[FloatLib.Floats.Formats.Posit.Model.toDyadic?]] uses `@[implemented_by]` for a one-pass compiled implementation. Its private theorem `toDyadicImpl?_eq_toDyadic?`, in the [decoder implementation](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Model/Decode.lean), proves that the replacement agrees with the logical decoder. That theorem supplies the mathematical justification, although the attribute itself does not require it. [Chapter 11](#/chapter/posits-and-the-quire) explains the decoding algorithm.

<a id="why-this-is-not-extraction"></a>

## Lean compilation and code extraction

Extraction, in the sense of Coq's or Isabelle's code generators, translates definitions that were proved correct into a program in another language and trusts the translator. The compiler for that target language may then optimize the generated program. FloatLib states its refinement equations within Lean. The fast arithmetic kernel is itself a Lean definition, compiled by Lean's own compiler [@moura2021lean4], and the certificate is an equation between two Lean terms that Lean's kernel checked. Lean's compiler takes these definitions directly, including replacements justified by `@[csimp]`; correctness at runtime still depends on the compiler preserving their semantics.

<a id="the-check-that-enforces-the-split"></a>

## When an executable definition needs a proof

Some executable types carry a proof that their stored code is valid. Constructing such a value requires a range argument even in a program that only computes. The [packed posit backend](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Configured/Backend/Runtime.lean) imports the range lemmas needed to construct its packed posit codes, reusing the existing proofs. This is an exception to the usual separation of runtime and proof imports. The proof is needed when Lean checks the definition and is erased during compilation, just like the certificate fields discussed earlier.

<a id="the-trust-surface"></a>

## Following a theorem's assumptions

`#print axioms` follows the dependencies of a logical theorem. For a generic statement about a certified operation, the implementation's certificate is an argument, so its assumptions need to be inspected separately. These two declarations are worth reading together; we'll see why the shorter axiom list needs a little explanation:

```lean
#print axioms FloatLib.Floats.Formats.BinaryInterchange.Model.AddBackend.word_eq_spec
-- 'FloatLib.Floats.Formats.BinaryInterchange.Model.AddBackend.word_eq_spec' depends on axioms: [propext,
--  Classical.choice,
--  Quot.sound]

#print axioms FloatLib.Floats.ExecFloat.Proof.add_eq_spec
-- 'FloatLib.Floats.ExecFloat.Proof.add_eq_spec' does not depend on any axioms
```

`add_eq_spec` is stated for every format at once and is assembled from two fields of whatever capability the format supplies, `execute_eq_implementation` and the selected certificate's `run_eq_spec`. Its own proof term therefore uses no axioms. To understand a particular format's assumptions, inspect its arithmetic certificate as well: the first command does this for the binary addition dispatcher and reports `propext`, `Classical.choice`, and `Quot.sound`, the usual axioms of classical mathematics in Lean. Native execution checks used in tests are separate from these library proofs.

For a useful finite check, we are happy to use `native_decide`: native evaluation can make checking the proposition much faster than reducing it in Lean's kernel. That saves build time; it does not make an addition faster when we run FloatLib. The tradeoff is that we trust the compiler and evaluator for that check. We keep those uses visible in the [testing guide](https://github.com/lean-dojo/FloatLib/blob/main/tests/README.md#trust-surface), alongside the general arithmetic proofs that do not use native evaluation.

The [unchecked host-arithmetic module](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/NativeFPU/Unchecked.lean) provides `NativeFPU.Unchecked.add32` and corresponding functions for the other host operations. Each checks a guard before calling one host `Float32` or `Float` operation; exceptional cases use the proved software implementation. [Chapter 15](#/chapter/performance/comparing-with-leans-native-floats) shows the guard and where host and library disagree.

Applications can call the unchecked functions explicitly, accepting the host assumptions in place of a refinement theorem. These functions are outside the certified candidate list, cannot be selected by a policy, and require a separate import. Comparing their outputs with the proved kernels can find disagreements, but does not supply the missing refinement theorem.

For certified software addition, we use `Configured.Backend.wordAdd`, which adapts the word kernel to the configured format and carrier. The theorem [[FloatLib.Floats.Formats.BinaryInterchange.Configured.Backend.wordAdd_eq_spec]] proves agreement with reference addition. The separate `Unchecked` functions invoke host arithmetic under the guards described above. Choosing them changes the assumptions behind a calculation.

<a id="how-the-website-examples-are-checked"></a>

<a id="what-the-split-buys-and-what-it-does-not"></a>

## Using numerical theorems with executable arithmetic

We can now leave the carries, guard bits, and sticky bits with the arithmetic kernel's refinement proof. That proof handles the low-order information needed to round correctly. Once it establishes equality with the reference operation, we can use numerical theorems about the reference without repeating the bit-level argument. [Chapter 06](#/chapter/the-numerical-models) states [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt]] about `Model.add`. The theorem needs the format and finiteness hypotheses below, but does not depend on which arithmetic kernel binary32 runs.

```lean
open FloatLib.Floats.Formats.BinaryInterchange in
example (x y : Model FloatFormat.binary32)
    (hx : Model.isFinite x = true) (hy : Model.isFinite y = true)
    (hfin : Model.isFinite (Model.add x y) = true) :
    Model.toReal (Model.add x y) =
      Model.roundAt FloatFormat.binary32 (Model.toReal x + Model.toReal y) :=
  Model.toReal_add_eq_roundAt x y rfl hx hy hfin
```

The three hypotheses say that both operands and the sum are finite. If the sum overflows, the result is an infinity and has no real value; [chapter 06](#/chapter/the-numerical-models) treats that case separately. The `rfl` proves that binary32 is an IEEE format, which Lean checks by computation. `Model.add` is by definition the dispatcher `AddBackend.word` from earlier in this chapter. Combining this theorem with `word_eq_spec` and the arithmetic kernel's refinement theorem gives the result we need: the decoded word returned by the fast kernel is exactly $\mathrm{round}(\mathrm{decode}(x) + \mathrm{decode}(y))$.
