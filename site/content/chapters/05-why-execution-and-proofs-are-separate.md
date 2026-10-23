---
number: "05"
slug: why-execution-and-proofs-are-separate
title: Executable arithmetic and its proofs
summary: An equation between an implementation and its reference operation lets numerical proofs apply to executable arithmetic.
phases: [execution, trust]
---

When we write `x + y` on a FloatLib type, we call an implementation selected for that format. We can reason about its result using a reference operation that decodes the operands, computes exactly, and rounds once: a theorem says the two return the same stored word. The reference makes the arithmetic meaning explicit; the implementation can use packed words, carries, and specialized rounding routines. Once we have proved them equal, we can use the reference in later proofs without repeating the word-level argument.

Lean's kernel is the trusted checker that accepts or rejects proof terms, reducing definitions as needed. An arithmetic kernel is an implementation of an operation for a class of formats. The distinction matters here: Lean's kernel checks the equations about arithmetic kernels, while the compiler translates their executable definitions into code.

## From addition to its reference operation

`ExecFloat F` stores one value in format `F`. For binary32 it holds a packed `UInt32`, while the reference model uses an exact-width bit vector, and other formats can use wider words or arrays of limbs, as the [storage definitions](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/Storage/Core.lean) specify. So the representation can change while the format's numerical meaning stays fixed.

Behind the notation `x + y` sits [[FloatLib.Floats.ExecFloat.add]], which calls the implementation selected for `F`, and [[FloatLib.Floats.ExecFloat.Proof.add_eq_spec]] says that this call equals [[FloatLib.Floats.ExecFloat.Spec.add]], the format's reference operation. For a binary format the reference is a short Lean function with no floating point inside it. It decodes both operands to exact dyadics, adds them exactly, rounds once and packs the result, and for binary32 the descriptor fixes 8 exponent bits and 23 fraction bits. For our sum, we can inspect the packed bits and decimal display, then apply the refinement equation to arbitrary operands:

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

Each `#eval` line compiles and runs the implementation selected for binary32. The first prints the sum's bits as an integer, $1050253722$, which is `0x3e99999a` in hex. The second prints `0.3`, the shortest decimal that reads back as that word, and the word's exact value is $5033165 \cdot 2^{-24}$. Round the literal `0.3` to binary32 and it prints the same. None of these words represents the rational three tenths exactly, and [Chapter 02](#/chapter/from-reals-to-machine-numbers) explains why.

The evaluations only compute one sum, though. The `example` is the part that proves equality for arbitrary inputs, relating the selected Lean implementation to `Spec.add` for every pair of operands.

We can also derive the stored answer using exact integer arithmetic. In binary32 the operands have exact values $13421773 \cdot 2^{-27}$ and $13421773 \cdot 2^{-26}$. Put them at the same scale and their sum is

$$
(13421773 + 2 \cdot 13421773)\,2^{-27} = 40265319 \cdot 2^{-27}.
$$

This sum lies between $1/4$ and $1/2$, where the binary32 grid spacing is $2^{-25}$, so measured in units of that spacing the exact sum is $40265319/4 = 10066329.75$. Nearest rounding picks the integer $10066330$ and gives $10066330 \cdot 2^{-25} = 5033165 \cdot 2^{-24}$, the stored answer. The order of events matters here. Both literals were already rounded when they became operands, and the addition's single rounding applies to the exact sum of those operands. So a refinement theorem has to keep that order if it's going to describe the program accurately.

As for the notation itself, by definition `x + y` unfolds to the public operation, so reflexivity proves this equality:

```lean
example (x y : Binary32) : x + y = ExecFloat.add x y := rfl
```

You can also pair a value with proofs about it, and those proof fields add no runtime data to the `ExecFloat F` value, because Lean erases fields in `Prop` during compilation.

## Certifying an implementation

To register an implementation as a candidate, we package it with its proof in [[FloatLib.Floats.ExecFloat.Backend.Certified]]. A `Certified spec` is a record with three fields, which hold a cost estimate for the planner, an executable `run`, and a proof `run_eq_spec : run = spec`. You can't build the record without the equation, so registering a faster implementation requires its correctness proof. The proof is a `Prop` field, which the compiler erases, so calling `run` executes the implementation without ever evaluating the proof.

```lean
open FloatLib.Floats.ExecFloat in
example {α : Type} (spec : α) (certified : Backend.Certified spec) :
    certified.run = spec :=
  certified.run_eq_spec
```

For a binary operation, `α` in the certificate is a function type such as `Model fmt → Model fmt → Model fmt`, and the equation `run = spec` identifies the whole function. Apply both sides to particular `x` and `y` and you get `run x y = spec x y`. Going the other way, a backend that proves that equation for every pair can use function extensionality, `funext`, to build the function equality, which is the step the `Certified.binary` constructor performs. A caller can then rewrite an operation inside a larger expression without repeating the backend's proof about carries.

What the equation preserves depends on the result type. When the result is a `Model fmt`, equality compares the packed word, down to a zero's sign and a NaN's encoding. An equation between decoded real values would be weaker, because decoding alone can't tell those words apart.

A format registers a [[FloatLib.Floats.ExecFloat.Capability]] for each of the six operations, add, sub, mul, div, sqrt and fma. Each capability stores the specification, a list of certified candidates with a mandatory exact baseline, and the planner's choice among them. That planner is [[FloatLib.Floats.ExecFloat.Backend.selectCertified]], which checks the candidates and keeps the one with the lowest estimated cost that the policy in scope, [[FloatLib.Floats.ExecFloat.Backend.PolicyFor]], permits. A policy is a cost model that can, for example, cap the temporary memory a candidate may use.

Every candidate already carries a proof that it agrees with the specification, so choosing among them can't change the result, and [[FloatLib.Floats.ExecFloat.Backend.selectCertified_run_eq_spec]] proves this for any policy and any candidate list.

```lean
open FloatLib.Floats.ExecFloat in
example {α : Type} (spec : α) (policy : Backend.Policy)
    (candidates : Backend.CandidateSet (Backend.Certified spec)) :
    (Backend.selectCertified policy candidates).run = spec :=
  Backend.selectCertified_run_eq_spec policy candidates
```

The reference itself is always one of the candidates. `Backend.Certified.reference` uses the specification as its own baseline, with a proof by `rfl`, and for binary formats the exact generic backend is always present as the mandatory baseline. If no specialized arithmetic kernel is eligible for a format, this baseline computes the result. It's also where the dispatchers in the next section go whenever a specialized kernel declines an input.

Changing the cost estimates or policy can select a different candidate, but that candidate must carry the same equation relating its result to the specification. Two more fields of the capability, [[FloatLib.Floats.ExecFloat.Capability.implementation_is_selected]] and [[FloatLib.Floats.ExecFloat.Capability.execute_eq_implementation]], prove that public execution and the selected implementation return the same result.

To see which implementation is registered for each operation, run the inspection command `#float_info`. For `Binary32` it prints `add, sub, mul, div, sqrt, fma = fixed-format word kernel (UInt32)`. That line describes the selected Lean definitions, and looking at the generated code is another matter. All six equations also come as one statement, [[FloatLib.Floats.ExecFloat.Proof.fullArithmeticCertificate]], that ranges over the six operations at once. It's stated for the format descriptor, which is why the block below names `Binary.Family 8 23` where the earlier ones named `Binary 8 23`. The value type `Binary 8 23` is `ExecFloat` applied to that family.

```lean
example : ExecFloat.Proof.FullArithmeticCertificate (ExecFloat.Binary.Family 8 23) :=
  ExecFloat.Proof.fullArithmeticCertificate _
```

## Runtime.lean and Proof.lean

Executable definitions usually live in `Runtime.lean` and their refinement theorems in a sibling `Proof.lean`, as in [Figure 5.1](#/chapter/why-execution-and-proofs-are-separate/figure-ch05-runtime-proof-split). A runtime file imports the decoders, integer operations, rounding rules and shared types it needs to compute. Its proof file imports the runtime file along with the lemmas and Mathlib theories needed to justify the result. Both can use shared definitions such as the storage types above.

![Runtime.lean supplies executable definitions; Proof.lean establishes their equality with the reference operation](assets/ch05-runtime-proof-split.png "An executable definition and its refinement theorem have different jobs. The proof connects the runtime result to the reference operation.")

Which tools a client loads depends on what it imports. The [runtime module](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Runtime.lean), `FloatLib.Floats.ExecFloat.Runtime`, supplies arithmetic backed by capabilities and conversion backed by quantizer contracts, although constructing those operations still requires their certificates. The [full module](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat.lean) adds the public specification equations, proof automation and inspection commands on top. `import FloatLib` brings in the format families too, which makes it the convenient choice for exploring the guide's examples.

<a id="public-and-private-imports"></a>

Lean's module system tells an interface apart from the dependencies used to implement it. A `public import` makes the imported declarations available to clients, and a plain `import` stays local to the module. We use `@[expose] public section` for FloatLib's declarations and `public meta section` for elaborator code, so a client can use an operation without importing every lemma we used to prove it correct.

<a id="when-an-executable-definition-needs-a-proof"></a>

Some executable types carry a proof that their stored code is valid, so constructing such a value needs a range argument even in a program that only computes. The [packed posit backend](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Configured/Backend/Runtime.lean), for example, imports the range lemmas it needs to construct its codes. Lean needs those proofs when it checks the definition, and compilation erases them, just like certificate fields.

When we improve an algorithm, we change its runtime definition and may have to revise its refinement proof. Numerical theorems keep using the same reference operation, though, so the word-level proof work stays with the implementation that changed.

You can see this split in the one-word multiplication kernel, whose runtime module defines two things. One is the eligibility predicate [[FloatLib.Floats.Formats.BinaryInterchange.Model.NativeSmallWordMul.Eligible]], a decidable proposition about the format descriptor. It requires an IEEE encoding, at most 64 encoded bits, at most 30 exponent bits and at most 31 fraction bits. The other is the arithmetic kernel `mulNormal?`, which multiplies normal operands in `UInt64` arithmetic and returns `none` for any operand or result outside the normal range it handles. In the [refinement proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/Word/Small/Mul/Proof.lean) we establish `mulNormal_refines`, which says that whenever the arithmetic kernel accepts, its answer is the answer of the format-generic finite kernel.

```lean
open FloatLib.Floats.Formats.BinaryInterchange in
example {fmt : FloatFormat} (h : Model.NativeSmallWordMul.Eligible fmt)
    (x y r : Model fmt) (hr : Model.NativeSmallWordMul.mulNormal? x y = some r) :
    Model.FiniteKernel.mul? x y = some r :=
  Model.NativeSmallWordMul.mulNormal_refines h x y r hr
```

That 31-bit fraction limit comes from the multiplication and has nothing to do with the width of the stored result. With the hidden leading bit included, each normalized significand is below $2^{32}$, so their exact product is below $2^{64}$ and fits the working word. A format can occupy at most 64 bits and still have too many fraction bits for this product bound, so the two conditions do different jobs. The encoding width makes field decoding possible, and the fraction width makes the intermediate arithmetic exact. Even after the multiplication, the kernel has to check whether normalization and rounding produce a result in the range it handles.

In the theorem, the premise `mulNormal? x y = some r` records that this particular call passed those checks. A `none` means the partial kernel declined the call, which isn't the same thing as an IEEE invalid-operation result. Even two normal inputs can have a product below the normal range, and the reference operation still has an answer in that case, which the total dispatcher must compute. Dividing the work this way lets the local proof assume its acceptance premise, while the dispatch proof establishes correctness for every input, including the ones the local kernel never handles.

So when a kernel declines an input, the dispatcher computes it through the exact baseline. For addition, [[FloatLib.Floats.Formats.BinaryInterchange.Model.AddBackend.word]] tries the specialized kernel the descriptor is eligible for and, when that kernel declines, falls back to the width-generic exact baseline [[FloatLib.Floats.Formats.BinaryInterchange.Model.AddBackend.generic]]. Our proof of [[FloatLib.Floats.Formats.BinaryInterchange.Model.AddBackend.word_eq_spec]] follows the same branches and discharges each one with its local refinement theorem, and it holds for every format descriptor, named or not.

```lean
open FloatLib.Floats.Formats.BinaryInterchange in
example (fmt : FloatFormat) (x y : Model fmt) :
    Model.AddBackend.word x y = Model.Spec.add x y :=
  Model.AddBackend.word_eq_spec x y
```

This dispatcher doesn't compare its answer with the reference on every call. On an accepted branch, the refinement theorem already supplies the equality for all operands that satisfy the branch's premises, and on a declined branch, the dispatcher calls the proved fallback. Our proof combines these cases before compilation, so the running program just makes the input checks and computes one branch. The runtime quotient certificate in [chapter 15](#/chapter/kernels-fixed-word-algorithms) is built differently, because there checking a proposed answer is part of the algorithm itself.

## Compiler replacements with csimp

Reference definitions often compute on `Nat` and `Int` and allocate decoded records or wide intermediate integers. A compiler replacement can avoid those allocations and give the same result. A `@[csimp]` equation proves two Lean definitions equal and tells the compiler to replace the first with the second in generated code, and Lean's kernel checks the equation before the compiler uses it. [The kernel source tour](#/chapter/kernels-fixed-word-algorithms/kernels-fixed-word-algorithms-and-limb-arrays) goes through these replacements in the arithmetic kernels.

For addition, [[FloatLib.Floats.Formats.BinaryInterchange.Model.FiniteKernel.add_eq_addRuntime]] states `@add? = @addRuntime?`. On IEEE formats the compiled implementation hands decoded fields straight to the finite adder and skips the intermediate `Components` records. Other encodings use the descriptor-aware decoder, and we prove the equality with `addRuntime_eq`.

The integer square root replacement reaches further. [[FloatLib.Numerics.FixedWord.IntegerSquareRoot.natSqrt_eq_sqrtNat]] states `Nat.sqrt = sqrtNat`, so in a module that imports `FloatLib.Kernels`, every compiled `Nat.sqrt` takes a machine-word path when the input is below $2^{64}$. Above that it checks an increasing-precision Newton candidate and falls back to `Nat.sqrt.iter` if the check fails. As the [module docstring](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels.lean) records, this import changes the compiled implementation of `Nat.sqrt` in client code too.

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

With `#check` you can inspect the equation the compiler uses, and our `#eval` goes through the replaced machine-word path and agrees with the mathematical square root. You call the readable definition, and the compiler uses the replacement that equation justifies. The axiom list names the three standard axioms of classical mathematics that Mathlib itself assumes. With `@[csimp]`, correctness of the compiled replacement rests on the compiler honouring a proved equation between two Lean definitions.

The attributes `@[implemented_by]` and `@[extern]` can also change execution, and neither requires such an equation. `#print axioms` and `Lean.collectAxioms` follow the logical definition, so their output alone can't establish that either kind of replacement agrees with it. Our posit decoder [[FloatLib.Floats.Formats.Posit.Model.toDyadic?]] uses `@[implemented_by]` for a one-pass compiled implementation. A private theorem in the [decoder implementation](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Posit/Model/Decode.lean), `Internal.toDyadic?_eq`, proves that the replacement agrees with the logical decoder. The attribute doesn't require that theorem, but it's what justifies the replacement mathematically, and [Chapter 13](#/chapter/posits-and-the-quire) explains the decoding algorithm.

<a id="lean-compilation-and-code-extraction"></a>

Extraction, in the sense of Coq's or Isabelle's code generators, translates definitions that were proved correct into a program in another language and trusts the translator. The target language's compiler may then optimize the generated program. We state FloatLib's refinement equations inside Lean. The fast arithmetic kernel is itself a Lean definition, compiled by Lean's own compiler [@moura2021lean4], and its certificate is an equation between two Lean terms that Lean's kernel checked. Lean's compiler takes these definitions as they are, replacements justified by `@[csimp]` included. Correctness at runtime still depends on the compiler preserving their semantics.

## Following a theorem's assumptions

`#print axioms` follows the dependencies of a logical theorem. In a generic statement about a certified operation the implementation's certificate is an argument, so you have to inspect its assumptions on their own. The following declarations illustrate why the generic theorem has a shorter axiom list than its concrete binary implementation:

```lean
#print axioms FloatLib.Floats.Formats.BinaryInterchange.Model.AddBackend.word_eq_spec
-- 'FloatLib.Floats.Formats.BinaryInterchange.Model.AddBackend.word_eq_spec' depends on axioms: [propext,
--  Classical.choice,
--  Quot.sound]

#print axioms FloatLib.Floats.ExecFloat.Proof.add_eq_spec
-- 'FloatLib.Floats.ExecFloat.Proof.add_eq_spec' does not depend on any axioms
```

`add_eq_spec` is stated for every format at once. We assemble it from two fields of whatever capability the format supplies, `execute_eq_implementation` and the selected certificate's `run_eq_spec`, so its own proof term uses no axioms. To see a particular format's assumptions, inspect its arithmetic certificate as well. The first command does this for the binary addition dispatcher and reports `propext`, `Classical.choice`, and `Quot.sound`, the usual axioms of classical mathematics in Lean.

Native execution checks in the tests sit outside these library proofs. For some finite checks we use `native_decide`, because native evaluation can check the proposition much faster than reducing it in Lean's kernel. That saves build time, though it doesn't make an addition any faster when you run FloatLib, and in exchange we trust the compiler and evaluator for that check. We keep those uses visible in the [testing guide](https://github.com/lean-dojo/FloatLib/blob/main/tests/README.md#trust-surface), next to the general arithmetic proofs that don't use native evaluation.

There's also an [unchecked host-arithmetic module](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/NativeFPU/Unchecked.lean). It provides `NativeFPU.Unchecked.add32` and matching functions for the other host operations, and each one checks a guard before calling one host `Float32` or `Float` operation and sends exceptional cases to the proved software implementation. [Chapter 18](#/chapter/lean-native-floats/opting-into-guarded-host-operations) shows the guard and where host and library disagree. An application can call the unchecked functions by name and accept the host assumptions in place of a refinement theorem. They sit outside the certified candidate list, no policy can select them, and they need their own import. Comparing their outputs with the proved kernels can find disagreements, but it can't supply the missing refinement theorem.

## Using numerical theorems with executable arithmetic

Once the refinement proof connects an implementation to its reference, numerical theorems can use that reference without repeating the argument about carries and rounding bits. [Chapter 06](#/chapter/the-numerical-models/the-rounding-contract-as-a-statement-about-reals) applies this to the real value of a sum. The theorem there asks for a conventional IEEE descriptor, finite operands and a finite result. Those conditions are about what the arithmetic means, whichever kernel was selected. The [configured-value recipe](#/chapter/further-examples/the-result-as-a-real-number) then carries the result back to ordinary `Binary32` arithmetic.
