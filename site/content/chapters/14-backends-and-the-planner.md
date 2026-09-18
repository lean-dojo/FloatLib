---
number: "14"
slug: backends-and-the-planner
title: Choosing an arithmetic backend
summary: The planner chooses a proved implementation using estimated computation and memory costs, while host arithmetic requires an explicit unchecked call.
phases: [backends, planner-and-configured, execution]
---

Once several proved implementations can do the same operation, we still have a choice to make:
a lookup table for a tiny format, a word kernel, a fixed-limb kernel, or the exact generic
baseline. They satisfy the same specification, but their setup costs, memory use, and costs per
call differ. The planner chooses among those available for your format, operation, and storage
representation. The kernels described in [chapter 13](#/chapter/kernels-fixed-word-algorithms)
supply the arithmetic; the policy tells the planner how to weigh their costs for the expected
workload.

Each candidate includes a proof of correctness. A cost estimate can therefore affect performance without changing the specified result. GMP also chooses algorithms by size [@gmpManual], and FFTW separates a transform description from its execution plan [@fftwPlanner]. FloatLib additionally requires a proof that each candidate's `run` equals the common specification.

<a id="what-can-i-choose"></a>
<a id="what-can-we-choose"></a>

## Choosing a backend

The automatic planner ranks the certified kernels available for your format and storage.
Its score is an engineering estimate. It does not time the alternatives on your machine,
read the benchmark results, or promise the fastest measured implementation.

| Choice | How to request it | What changes |
| --- | --- | --- |
| Favor a few calls | Open the `PlanningLatency` scope | Avoids setup that may not pay back |
| Favor repeated calls | Open the `PlanningThroughput` scope | Amortizes setup over more calls and allows larger tables |
| Set your own workload and memory limits | Supply a local `Backend.PolicyFor` instance | Changes the scores and which candidates fit the limits |
| Store wide binary values as limbs | Use `ExecFloat.BinaryLimbs` | Makes eligible wide-limb kernels available |
| Use the host FPU at 32 or 64 bits | Import `NativeFPU.Unchecked` and call its named functions | Uses guarded host arithmetic without a FloatLib refinement certificate |

The [policy examples below](#/chapter/backends-and-the-planner/changing-the-workload-without-changing-the-mathematics)
show the scopes in use, and the [host example](#/chapter/backends-and-the-planner/using-the-host-fpu)
shows the explicit import and call.

**Binary32 and binary64 already select their fixed-format software kernels.** In the
current candidate sets, those kernels beat the exact baseline under every policy;
changing to the throughput profile therefore leaves these two formats on the same
kernels. They still perform floating point arithmetic in software. The host FPU is a
separate choice, and SoftFloat, MPFR, and Universal are comparison libraries rather
than selectable FloatLib backends.

[Chapter 15](#/chapter/performance) compares measured execution times.

<a id="why-a-ladder-and-not-one-kernel"></a>

## Why different widths use different kernels

The generic baseline computes on `Nat` significands to handle every width. Its wide intermediates
require heap allocations. We can see their effect in the [calibrated cost model](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Descriptor/Plan/Estimates.lean):
it estimates addition at about 4.1 microseconds for 256 bits and 5.3 microseconds for 4096 bits.
Increasing the width sixteenfold changes the estimate much less, because the model assigns most
of the cost to fixed allocation overhead.

The specialized representations avoid different costs. A table replaces the arithmetic with one index computation and one byte load. A one-word kernel avoids allocation by keeping every field, aligned significand, and rounding decision in a `UInt64`. A two-word kernel keeps binary128 in a pair of machine words rather than an arbitrary-precision integer. A limb-array kernel keeps a 4096-bit significand in one mutable array instead of allocating a fresh bignum for every shift. The generic path uses arbitrary-precision intermediates to handle every descriptor and exceptional case. For addition, each implementation proves agreement with the same reference function, `ExecFloat.Spec.add`.

<a id="the-rungs"></a>

## Available kernels

Formats of at most eight encoded bits are offered exhaustive tables, built in the [configured byte-table implementation](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/ByteTable). A table is generated from the reference operation itself on first use, so there is no second arithmetic to trust, and [[FloatLib.Floats.Formats.BinaryInterchange.Configured.ByteTable.runBinary_eq_lift]], `runUnary_eq_lift`, and `runTernary_eq_lift` say that reading the generated entry recovers the reference result. A two-operand table for an 8-bit format has $2^{16}$ entries and a three-operand table $2^{24}$, which is where the resource policy below starts to matter.

For an encoded format with $n$ possible words, a binary table puts the answer for operand codes $i$ and $j$ at index $in+j$. Table construction recovers those operands by quotient and remainder on division by $n$, evaluates the model operation, and stores its encoded result. Lookup uses the inverse calculation. The indexing proof establishes that the native index does not wrap and lies inside the table; the encoding's round-trip laws then identify the loaded byte with the specified result. All encoded operands participate, including signed zeros, infinities, and NaNs when the descriptor has them. These tables store the value-only operation's answers. Their lookup certificates do not add an exception-status word to the result.

Formats of at most 64 bits can use the word kernels in the [word-kernel directory](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/ExecFloat/Backends/Word), subject to the capacity bounds below. For 8-bit formats, the planner also considers the table. The [parameterized word implementation](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/ExecFloat/Backends/Word/Small) works across formats: for any IEEE descriptor whose encoding fits a word it decodes fields with shifts, aligns, combines signed magnitudes, and rounds without allocating a `Nat`. Its capacity bounds differ by operation because the intermediates differ: addition and subtraction admit up to 30 exponent bits and 61 fraction bits, and multiplication admits 31 fraction bits because a 32-bit normalized significand still has an exact 64-bit product. When a one-word format has between 32 and 61 fraction bits the product no longer fits a word, so the [two-word multiplication kernel](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/ExecFloat/Backends/Word/TwoWordMul) forms an exact `64 x 64 -> 128` product instead.

Division admits every IEEE descriptor with at most 64 encoded bits, the condition
`NativeSmallWord.StorageEligible`. The sign and at least two exponent bits leave at most
61 fraction bits, which suffices for the restoring quotient's capacity proof. Its
normal-input and normal-result checks still send declined calls to the exact baseline.

The [binary32 kernels](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/ExecFloat/Backends/Word/Narrow) and [binary64 kernels](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/ExecFloat/Backends/Word/Full) contain specializations for exactly those layouts. They also reuse the parameterized kernels. Binary64 addition first tries the parameterized [small-word addition](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/ExecFloat/Backends/Word/Small/Add) kernel, whose 61-fraction-bit contract admits binary64, and runs its fixed-format code on inputs that kernel declines. Its proof applies the parameterized kernel's refinement theorem on accepted inputs, leaving the declined cases for its own arithmetic and proof.

Binary64 multiplication has its own [dispatch sequence](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/Dispatch/Mul/Runtime.lean). It first tries `NativeTwoWordMul.mulNormal?`. If that declines, it tries the binary64 `mulNormalLimb?` implementation in [Word/Full/Core](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/Word/Full/Core/Runtime.lean); if both decline, the generic exact kernel supplies the result. A planner label therefore describes the complete dispatch function, including its fallbacks, rather than one arithmetic routine.

From 65 to 128 bits, when the fraction is wider than one word, the [two-limb `NativePair` kernel](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/ExecFloat/Backends/FixedLimb/Pair) holds the value in two `UInt64` limbs with every field position derived from the descriptor. That covers binary128 and every `ExecFloat.Binary e f` with $65 \le f$ and $e + f \le 127$. All six operations are implemented. Division checks a radix-$2^{32}$ quotient candidate against an independent Euclidean certificate and replaces a rejected candidate with a proved restoring result. Square root declines two kinds of layout and sends them to the exact baseline: fractions wider than 124 bits, where the doubled remainder would no longer fit the two-word state, and layouts whose exponent bias does not exceed the fraction width, where the kernel's exponent arithmetic does not apply.

Above 128 bits, eligibility also depends on the carrier, the runtime representation in which a value is stored. `ExecFloat.Binary` stores the exact-width proof model itself, the same structure the theorems are stated about, and on that carrier no specialized kernel is eligible, so all six operations run the exact baseline. `ExecFloat.BinaryLimbs` names the alternative carrier, an array of 32-bit limbs, with public arithmetic capabilities that use the automatic planner. For eligible IEEE descriptors, its candidate set also offers the [wide-limb backend](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/ExecFloat/Backends/WideLimb) for addition, subtraction, multiplication, and fused multiply-add. These kernels operate directly on the array when their normal-input and normal-result guards accept the call; declined calls, and all division and square-root calls, use the exact baseline. On the accepted path alignment jams the discarded bits into one sticky bit, rounding reads the guard, sticky, and parity bits from the limbs, and the significand is never converted to a `Nat`. The limbs are 32 bits rather than 64 for the boxing reason [chapter 13](#/chapter/kernels-fixed-word-algorithms) gives. The refinement theorems are [[FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb.toModel_add]], `toModel_sub`, `toModel_mul`, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb.toModel_fma]].

The [generic baseline](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/ExecFloat/Backends/Generic) is present for every descriptor. It computes exact intermediate values and implements the complete exceptional-value policy, and every specialized kernel returns to it when it declines an input, so the dispatchers never contain a second implementation of NaN or infinity handling.

For addition, we can read the default choices in [Figure 14.1](#/chapter/backends-and-the-planner/figure-ch09-backend-ladder): the standard packed types select word or fixed-limb kernels through binary128. At 256 bits, `ExecFloat.Binary 19 236` selects the baseline and `ExecFloat.BinaryLimbs 19 236` selects wide-limb addition. Both are ordinary public arithmetic calls on the same numerical layout, stored differently.

![Available addition kernels and their requirements, with the default choices for binary16 through binary128 and the two 256-bit storage representations](assets/ch09-backend-ladder.png "Addition kernels, eligibility conditions, and default choices. At 256 bits, the storage carrier determines whether the wide-limb kernel is available.")

We'll name four executable formats, then run the same addition on E4M3 and binary128.
Adding these two representable values gives the same exact result through different kernels:

```lean
open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

abbrev E4M3 := ExecFloat.Binary (exponentBits := 4) (fractionBits := 3)
abbrev Binary32 := ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)
abbrev Binary128 := ExecFloat.Binary (exponentBits := 15) (fractionBits := 112)
abbrev Binary256 := ExecFloat.Binary (exponentBits := 19) (fractionBits := 236)

#eval (1.5 : E4M3) + 2.25
-- 3.75
#eval (1.5 : Binary128) + 2.25
-- 3.75
```

Under the default policy, the 8-bit addition runs a machine-word kernel and the binary128 addition runs a two-limb kernel. Both inputs and the exact sum are representable in each format, so neither call needs an inexact rounding.

<a id="eligibility-is-a-statement-about-the-descriptor"></a>

## Which formats a kernel supports

A kernel checks the descriptor's fields, so a custom `ExecFloat.Binary` with the same layout as a standard format qualifies for the same kernel. Each kernel states its requirements as a proposition that Lean can decide.

For word storage, `StorageEligible` says the encoding is IEEE and fits in 64 bits; division uses this condition directly. The narrower [[FloatLib.Floats.Formats.BinaryInterchange.Model.NativeSmallWordAdd.Eligible]] and [[FloatLib.Floats.Formats.BinaryInterchange.Model.NativeSmallWordMul.Eligible]] add the per-operation capacity bounds from the previous section; [[FloatLib.Floats.Formats.BinaryInterchange.Model.NativeTwoWordMul.Eligible]] does the same for the two-word product. The division theorem `divNormal_refines_of_storage` needs only `StorageEligible`. For the fixed-format specializations, [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.IsBinary32]] and `IsBinary64` check layout equalities. The two-limb condition [[FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair.Eligible]] is `isIEEE ∧ 64 < fracWidth ∧ bitWidth ≤ 128`. For limb arrays, [[FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb.Eligible]] is `isIEEE ∧ 128 < bitWidth ∧ expWidth ≤ 32`.

```lean
example : Model.NativeSmallWord.StorageEligible FloatFormat.binary16 := by decide
example : Model.NativeSmallWordAdd.Eligible FloatFormat.binary64 := by decide
example : ¬ Model.NativeSmallWord.Eligible FloatFormat.binary64 := by decide
example : Model.NativeTwoWordMul.Eligible FloatFormat.binary64 := by decide
example : Model.NativePair.Eligible FloatFormat.binary128 := by decide
example : ¬ Model.NativePair.Eligible (FloatFormat.ieee 15 64) := by decide
example : Model.WideLimb.Eligible (FloatFormat.ieee 19 236) := by decide
example : ¬ Model.WideLimb.Eligible FloatFormat.binary128 := by decide
```

A format can qualify for a kernel even when some of its operands need a fallback. The planner selects a proved dispatcher that includes both the partial fast kernel and the correct fallback. It checks the format requirements first; the selected function then checks each call's operands. When the planner reports a word kernel, it names this combined function. An exceptional input may still use its fallback.

The negative `NativePair.Eligible` example has an 80-bit layout with a 64-bit fraction. That fraction fills the low word exactly and leaves no fraction bits in the high word, while the pair kernel assumes the high word holds sign, exponent, and the top of the fraction (for narrower fractions the exponent field would typically straddle the word boundary). The failed capacity predicate excludes this layout from the pair candidate list, leaving it on the exact baseline.

These predicates also affect specialization. Their `Decidable` instances use explicit `if h : ... then isTrue h else isFalse h` branches. With `inferInstanceAs`, an auxiliary definition can hide the conditional; exposing it gives the compiler a branch it can inline and evaluate for a closed descriptor. At a specialized call site, that eligibility test can disappear. The planner's cached selection check, described below, is a separate step.

For each operation, [[FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Plan.structuralRoute?]] chooses at most one of three kernel types: fixed format, machine word, or fixed limbs. It tries them in the same order as the executable dispatcher. This identifies a candidate for the configured format; whether that candidate runs also depends on the storage plan and the policy comparison.

```lean
#eval Descriptor.Plan.structuralRoute? (FloatFormat.ieee 4 3) .add
-- some (FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Plan.StructuralRoute.nativeWord)
#eval Descriptor.Plan.structuralRoute? FloatFormat.binary32 .add
-- some (FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Plan.StructuralRoute.fixedFormat)
#eval Descriptor.Plan.structuralRoute? (FloatFormat.ieee 11 40) .add
-- some (FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Plan.StructuralRoute.nativeWord)
#eval Descriptor.Plan.structuralRoute? (FloatFormat.ieee 11 40) .mul
-- some (FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Plan.StructuralRoute.fixedLimbs)
#eval Descriptor.Plan.structuralRoute? FloatFormat.binary128 .add
-- some (FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Plan.StructuralRoute.fixedLimbs)
#eval Descriptor.Plan.structuralRoute? (FloatFormat.ieee 19 236) .add
-- none
```

The 52-bit layout with 40 fraction bits adds in one word but multiplies through the two-word product. The planner classifies that product as fixed-limb code even though the format itself fits one word. A `none` means none of these three kernel types applies. The illustrated 256-bit descriptor uses the exact baseline on the proof-model carrier; a limb-array carrier can also offer a wide-limb candidate. Byte tables are another alternative determined by the storage representation.

<a id="what-a-candidate-advertises"></a>

## Estimating computation and memory costs

To compare the alternatives, we give every implementation a
[[FloatLib.Floats.ExecFloat.Backend.Candidate]] record with its name,
[[FloatLib.Floats.ExecFloat.Backend.KernelClass]], storage class, and estimated costs. The estimates
separate what we pay once from what we pay on every call: steady cost per call, conversion cost,
setup cost and allocations, resident and temporary bytes, and allocations per call.

The conversion cost, called *marshalling* in the record, accounts for moving operands and the result between the stored representation and the proof model. The estimates charge one unit per value on packed carriers and zero for byte-table lookups and accepted limb-kernel paths, which operate on stored values directly. A declined wide-limb call still converts through the proof model for the exact fallback. Setup cost matters for tables: a 64 KiB table is expensive to build but cheap to read, so the expected number of calls determines whether it is worth building. Allocations receive a separate penalty because they dominate the generic addition cost in the measurements used to choose the estimates.

The kernel class names the algorithm family: `exhaustiveTable`, `fixedFormat`, `nativeWord`, `fixedLimbs`, `wideLimbs`, or `generic`. A family can also supply a `custom` label. These names appear in `#float_info`; their `rank` breaks ties when candidates have equal scores. The display strings you will see below are "exhaustive encoded-value table", "fixed-format word kernel", "machine-word kernel", "fixed-limb kernel", "wide-limb kernel", and "exact baseline".

A [[FloatLib.Floats.ExecFloat.Backend.Policy]] sets the expected workload and memory limits. Three are built in: `latency` expects one call, [[FloatLib.Floats.ExecFloat.Backend.Policy.default]] (the balanced profile) expects 100,000, and `throughput` expects 5,000,000. The first two allow 1 MiB of resident memory per candidate; throughput raises that to 16 MiB. All three allow 64 MiB of temporary memory, charge 32 units per allocation, and count memory in 64-byte blocks.

The [policy definition](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/Selection/Policy.lean) defines these numbers as format-independent workload settings and relative weights. Their effect can be checked from the table sizes. One MiB admits every unary and binary byte-result table through eight encoded bits (a 65,536-entry byte table is 64 KiB) and the ternary tables through six bits, while rejecting an eight-bit FMA table, whose $2^{24}$ entries would take 16 MiB; the throughput profile raises the ceiling to exactly that figure, so that every exhaustive table over a byte-sized carrier becomes admissible and the cost model alone decides whether it amortizes. For the E4M3 addition estimates, the 65,536-entry binary table breaks even at 120,238 calls, beyond the balanced horizon of 100,000. Its square-root table amortizes much earlier, so the default policy selects that unary table while keeping addition on a word kernel. The 32-unit allocation charge and the 64-byte memory block are relative weights that the file states without a derivation; they define the candidate ordering, with no claim that a score is a time in nanoseconds. Fixed tie-breaking makes the selection reproducible for the same inputs to the planner.

<a id="the-selector"></a>

## How the planner chooses

The [scoring function](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/Selection/Scoring.lean) is a weighted sum. Warm cost is steady cost plus marshalling plus penalties for allocations and temporary memory blocks; cold cost is setup plus penalties for setup allocations and resident memory blocks; and

$$\mathrm{score} = \mathrm{expectedCalls} \cdot \mathrm{warmCost} + \mathrm{coldCost}.$$

Before scoring an alternative, `admissible` rejects it if its estimated resident or temporary bytes exceed the policy's limits. `consider_rejects_excess_residency` proves that such a candidate cannot replace the current choice. This is how one 8-bit format can have a tabulated square root and an algorithmic FMA: the 256-entry unary table and the 65,536-entry binary tables fit under 1 MiB, but the $2^{24}$-entry ternary table does not. The same memory check admits the smaller tables and rejects the FMA table.

[[FloatLib.Floats.ExecFloat.Backend.selectCertified]] starts with the required baseline and considers each alternative in turn, keeping the one with the lower score. The baseline remains available even if its estimated memory use exceeds the policy's limits, so selection always has a result. The limits filter alternatives; they do not guarantee a cap on the selected operation's memory use. `preferOnEqualScore` breaks ties in a fixed order: warm cost first, then marshalling, allocations, temporary bytes, resident bytes, cold cost, and finally kernel-class rank. The same descriptor, storage plan, candidate estimates, and policy therefore produce the same selection across machines and builds.

The fold operates on a [[FloatLib.Floats.ExecFloat.Backend.CandidateSet]] of [[FloatLib.Floats.ExecFloat.Backend.Certified]] values. A `Certified spec` is a record with an executable `run`, the estimate, and a proof `run_eq_spec : run = spec`; no constructor omits the proof. Two theorems connect selection to execution and reporting. [[FloatLib.Floats.ExecFloat.Backend.selectCertified_run_eq_spec]] says that whatever the fold returns satisfies `run = spec`, by using the selected candidate's certificate. This numerical equality holds independently of how accurately the estimates predict runtime. [[FloatLib.Floats.ExecFloat.Backend.selectCertified_estimate]] says that erasing the proofs and folding over the estimates alone gives the same answer, which lets an inspection tool report the plan without running the kernels.

```lean
open FloatLib.Floats.ExecFloat.Backend in
example {α : Type} {spec : α} (policy : Policy) (candidates : CandidateSet (Certified spec)) :
    (selectCertified policy candidates).run = spec :=
  selectCertified_run_eq_spec policy candidates
```

To prove numerical correctness, we read `run_eq_spec` from the chosen record; the quality of the cost estimates is irrelevant to that equation. To prove which implementation was selected, we follow the fold's comparisons. For performance, we also need to know that the compiled call uses the function whose cost was estimated: two algorithms can return identical answers at very different costs. The execution equations below connect the selected implementation to the function called.

The candidate lists for configured binary formats are assembled per operation in the [configured planner](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/Plan). `addCandidates` and its siblings pair the descriptor's structural candidate with the exact generic baseline. [[FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.automaticAddCandidates]] then checks the storage plan and adds a byte table when the carrier is a byte, or a wide-limb candidate when the carrier is a limb array and the descriptor is eligible. Ineligible candidates are removed before scoring. The planner for binary32 therefore sees one alternative plus the baseline, while a 4096-bit format on the proof-model carrier sees the baseline alone.

<a id="selection-happens-when-the-type-is-elaborated"></a>

<a id="the-type-fixes-the-configuration-selection-is-cached"></a>

## Choosing and caching an implementation

When you write arithmetic on `ExecFloat.Binary 8 23`, Lean knows the widths while elaborating the expression and finding its typeclass instances. `forKnownWidth` chooses storage from the encoded width: a byte up to 8 bits, then `UInt16`, `UInt32`, `UInt64`, and the proof model itself above 64. Any candidate selection that remains in the executable code is cached.

A [[FloatLib.Floats.ExecFloat.Capability]] instance for each operation records the specification, the candidate set, a memoized `Thunk` holding the selected certificate, and an `execute` function, with two equations: `implementation_is_selected`, saying the stored certificate is the planner's winner under the policy in scope, and `execute_eq_implementation`, saying the function public arithmetic calls is that certificate's `run`. Composed, they give [[FloatLib.Floats.ExecFloat.Capability.run_eq_spec]], from which [[FloatLib.Floats.ExecFloat.Proof.add_eq_spec]] and its siblings are built. The equation holds whenever the capability instance is available, whatever implementation it selects.

```lean
example (x y : E4M3) : x + y = ExecFloat.Spec.add x y :=
  ExecFloat.Proof.add_eq_spec x y

example (x y : Binary256) : x + y = ExecFloat.Spec.add x y :=
  ExecFloat.Proof.add_eq_spec x y
```

The selected certificate is cached in its capability's `Thunk`, so repeated calls through that capability share the result. Different storage plans or policies can have different selections and caches. Within a selected kernel, specialization can fold layout constants and eligibility branches at a closed-format call site; [[FloatLib.Floats.Formats.BinaryInterchange.Model.AddBackend.word_eq_spec]] proves that the resulting composite implements the specification for every input.

Machine-word plans and pair-eligible proof-model plans can also call a winning structural kernel directly. [[FloatLib.Floats.Formats.BinaryInterchange.Configured.StoragePlan.firstOrderDispatch]] checks only the storage; `Plan.firstOrderSelected` additionally checks that the structural candidate is admissible and wins the policy comparison. The direct branch calls that candidate's function, and the fallback calls `selection.get.run`. For example, an eight-bit IEEE descriptor stored in `UInt16` selects and executes generic FMA and square root: word storage alone does not choose the kernel.

At eight encoded bits, the square-root word estimate is 30 units of arithmetic plus two units of conversion, while the baseline estimate is 29 plus the same two. Both have zero cold cost. The baseline therefore wins even though a word implementation is available. `firstOrderDispatch` alone would miss this distinction; the additional policy comparison in `firstOrderSelected` is what keeps the direct branch tied to the selected candidate. Byte and limb plans keep the memoized selected entry, which can hold a table or a wide-limb candidate.

For closed automatic calls, the generated code caches the direct-dispatch decision and checks it on each call, so some dispatch overhead remains. This describes calls with a fixed descriptor and policy. The selection and execution equations also apply when those parameters vary at runtime.

For binary32 and binary64, each operation compiles to a C function over `uint32_t` or `uint64_t`. Their first-order instances in the [fixed-format dispatch](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/NativeDispatch.lean) name the fixed-format certificate directly, and [[FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.selectCertified_binary32AddCandidates]] and its eleven siblings prove that the planner picks that certificate under every policy, by cost dominance through `selectCertified_cons_of_dominant`. Whatever profile is in scope, binary32 and binary64 run the proved fixed-format software.

```lean
open FloatLib.Floats.ExecFloat.Backend in
theorem binary32_add_selects_software (policy : Policy)
    (h : FloatFormat.binary32.bitWidth ≤ 32) :
    selectCertified policy (Configured.Plan.binary32AddCandidates h) =
      Configured.Plan.softwareAdd32Certified h :=
  Configured.Plan.selectCertified_binary32AddCandidates policy h
```

The hypothesis `h` proves that the layout fits the `word32` storage plan. `StoragePlan.forKnownWidth` supplies this proof for a 32-bit width, and a caller can also prove it with `decide`. It adds no restriction on the operands.

<a id="asking-what-was-chosen"></a>

## Inspecting the selected backend

`selectedCandidate` exposes the estimate attached to the selected certificate. The equation `selected_eq_planner` identifies it with the planner's answer, so inspecting its kernel class reports the selected implementation without running the arithmetic. The capability classes are indexed by the encoded-format family underneath the public value type: `ExecFloat.Binary.Family` for the calls below, or `ExecFloat.Binary.LimbFamily` for the limb carrier.

```lean
#eval (ExecFloat.Add.selectedCandidate (F := ExecFloat.Binary.Family 5 10)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.nativeWord
#eval (ExecFloat.Add.selectedCandidate (F := ExecFloat.Binary.Family 8 23)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.fixedFormat
#eval (ExecFloat.Add.selectedCandidate (F := ExecFloat.Binary.Family 11 52)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.fixedFormat
#eval (ExecFloat.Add.selectedCandidate (F := ExecFloat.Binary.Family 15 80)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.fixedLimbs
#eval (ExecFloat.Add.selectedCandidate (F := ExecFloat.Binary.Family 15 112)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.fixedLimbs
#eval (ExecFloat.Add.selectedCandidate (F := ExecFloat.Binary.Family 15 64)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.generic
#eval (ExecFloat.Add.selectedCandidate (F := ExecFloat.Binary.Family 19 236)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.generic
```

The 80-bit layout from the eligibility section shows up here as `generic`, as the pair predicate said it would. On the 8-bit format, table, word, and baseline candidates can compete, with different results for different operations:

```lean
#eval (ExecFloat.Add.selectedCandidate (F := ExecFloat.Binary.Family 4 3)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.nativeWord
#eval (ExecFloat.Sqrt.selectedCandidate (F := ExecFloat.Binary.Family 4 3)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.exhaustiveTable
#eval (ExecFloat.Fma.selectedCandidate (F := ExecFloat.Binary.Family 4 3)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.generic
```

When we want to know which implementation an arithmetic expression will use, `#float_info`
lets us inspect the choice. It synthesizes the capability instances for the six operations and
reads the selected candidate from each. Its execution section looks like this:

```lean
#float_info E4M3
-- Execution:
--   carrier: packed persistent storage; the exact binary descriptor is retained as the proof model
--   dispatch: representation-aware certified selection among direct tables, word, limb, and exact baseline kernels
--   backends: add, sub, mul, div = machine-word kernel (UInt8); sqrt = exhaustive encoded-value table (UInt8); fma = exact baseline (UInt8)
#float_info Binary32
-- Execution:
--   carrier: packed persistent storage; the exact binary descriptor is retained as the proof model
--   dispatch: representation-aware certified selection among direct tables, word, limb, and exact baseline kernels
--   backends: add, sub, mul, div, sqrt, fma = fixed-format word kernel (UInt32)
```

`#float_info! E4M3` adds the planner's arithmetic for every operation. For square root the table wins with a score of 305,924 for 100,000 expected calls, that is $100000 \times 3 + 5924$, against 3,200,000 for the machine-word kernel and 3,100,000 for the exact baseline; on an 8-bit format the word kernel's square root is calibrated at 30 units against 29 for the baseline, so the table's only real competitor there is the baseline. For addition the table loses: a setup estimate of 1,441,792 units for 65,536 entries gives 1,742,848 against 1,500,000 for the machine-word kernel. For FMA the table is rejected before scoring, 16,777,216 resident bytes against a ceiling of 1,048,576. `breakEvenCalls` computes the call count at which the setup cost is recovered by savings on warm calls. The configured estimates include the costs the planner actually scores: they add the carrier adapter cost to the word kernel, one unit per value, so two for square root and three for addition, and they are indexed by the byte plan, which needs the `bitWidth ≤ 8` witness below.

```lean
theorem e4m3_byte : (FloatFormat.ieee 4 3).bitWidth ≤ 8 := by decide

open FloatLib.Floats.ExecFloat.Backend in
#eval Candidate.breakEvenCalls Policy.default
  (Configured.Plan.directByteEstimate (FloatFormat.ieee 4 3) .sqrt)
  (Configured.Plan.structuralEstimate (.byte e4m3_byte) .sqrt .nativeWord)
-- some 205
open FloatLib.Floats.ExecFloat.Backend in
#eval Candidate.breakEvenCalls Policy.default
  (Configured.Plan.directByteEstimate (FloatFormat.ieee 4 3) .add)
  (Configured.Plan.structuralEstimate (.byte e4m3_byte) .add .nativeWord)
-- some 120238
#eval (Configured.Plan.directByteEstimate (FloatFormat.ieee 4 3) .fma).residentBytes
-- 16777216
```

We can work through the first break-even calculation by counting what square root's table
costs to build and to use. Its cold cost is $256\cdot23+32+256/64=5924$: generation of 256 answers,
one setup allocation, and four resident-memory blocks. Its warm cost is three, against the word
candidate's $30+2=32$, so it saves 29 units per call and recovers its setup after
$\lceil5924/29\rceil=205$ calls. The exact baseline costs only 31 units per call, however. Against
that competitor the same table needs $\lceil5924/28\rceil=212$ calls. The table beats the word
kernel at 205 calls, but needs 212 calls to beat both alternatives.

For addition, the table's cold cost is $65536\cdot22+32+65536/64=1442848$. The word candidate costs $12+3=15$ per call, so the table saves 12 and needs $\lceil1442848/12\rceil=120238$ calls. At the balanced horizon its score is $100000\cdot3+1442848=1742848$, still above the word candidate's $100000\cdot15=1500000$. These are calculations in the declared cost model, not measured timings. A `none` means the candidate has no warm-cost advantage in this model, so increasing the expected call count cannot recover its setup cost.

<a id="changing-the-workload-without-changing-the-mathematics"></a>

## Setting the expected workload

The policy is a typeclass, [[FloatLib.Floats.ExecFloat.Backend.PolicyFor]], with a low-priority default instance for the balanced profile. Two scoped instances, `PlanningLatency.policy` and `PlanningThroughput.policy`, switch every format at once, and `custom` builds a local instance for one family from any `Policy`.

Try moving one of the selected-candidate queries between the two scopes. Keeping the query
fixed lets us see what changes when we change the expected workload.

```lean
section FirstCall
open scoped FloatLib.Floats.ExecFloat.Backend.PlanningLatency
#eval (ExecFloat.Sqrt.selectedCandidate (F := ExecFloat.Binary.Family 4 3)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.generic
end FirstCall

section Sustained
open scoped FloatLib.Floats.ExecFloat.Backend.PlanningThroughput
#eval (ExecFloat.Add.selectedCandidate (F := ExecFloat.Binary.Family 4 3)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.exhaustiveTable
#eval (ExecFloat.Fma.selectedCandidate (F := ExecFloat.Binary.Family 4 3)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.generic
end Sustained
```

Under the latency profile even the 256-entry square-root table is not worth building for one
call. Under the throughput profile the 16 MiB ceiling admits the FMA table, but its setup still
does not amortize over five million calls, so FMA stays on the exact baseline while addition
moves to its table. We can switch scopes without changing the value type, the literals, or any
theorem: arithmetic on the same type under a different policy still satisfies
`ExecFloat.Proof.add_eq_spec`, because every candidate was proved equal to the same specification
before the policy chose among them.

<a id="the-limb-carrier-at-this-revision"></a>

## Choosing the limb carrier

We can also keep the same addition and change how its values are stored. `ExecFloat.BinaryLimbs`
keeps a wide value in an array of 32-bit limbs between calls. Literals, ordinary arithmetic,
and the public specification equations work on this carrier too:

```lean
abbrev Limb256 := ExecFloat.BinaryLimbs (exponentBits := 19) (fractionBits := 236)

#eval (1.5 : Limb256) + 2.25
-- 3.75

example (x y : Limb256) : x + y = ExecFloat.Spec.add x y :=
  ExecFloat.Proof.add_eq_spec x y
```

For this 256-bit descriptor with IEEE encoding, the default policy selects wide-limb addition, subtraction, multiplication, and fused multiply-add. Division and square root use the exact baseline, rebuilding the proof model from the stored limbs. We can inspect those choices through the public family:

```lean
#eval (ExecFloat.Add.selectedCandidate (F := ExecFloat.Binary.LimbFamily 19 236)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.wideLimbs
#eval (ExecFloat.Div.selectedCandidate (F := ExecFloat.Binary.LimbFamily 19 236)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.generic
#eval (ExecFloat.Sqrt.selectedCandidate (F := ExecFloat.Binary.LimbFamily 19 236)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.generic
```

The storage plan explains why `Binary256` and `Limb256` select different addition kernels. `.wide` stores `Model format` directly; it is the plan `ExecFloat.Binary` uses above 64 bits. `.limbs` stores `Model.WideLimb.Value format` and requires a proof that the encoded width exceeds 128 bits. The two plans share a descriptor but offer different candidate sets. Here is the underlying fold for the same choices:

```lean
abbrev B256 : FloatFormat := FloatFormat.ieee 19 236
theorem b256_wide : 128 < B256.bitWidth := by decide

open FloatLib.Floats.ExecFloat.Backend in
#eval (selectCertified Policy.default
  (Configured.Plan.automaticAddCandidates B256 (.limbs b256_wide))).estimate.kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.wideLimbs
open FloatLib.Floats.ExecFloat.Backend in
#eval (selectCertified Policy.default
  (Configured.Plan.automaticDivCandidates B256 (.limbs b256_wide))).estimate.kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.generic
open FloatLib.Floats.ExecFloat.Backend in
#eval (selectCertified Policy.default
  (Configured.Plan.automaticAddCandidates B256 .wide)).estimate.kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.generic
```

[[FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.wideLimbAdd?]] and its siblings offer limb kernels only for IEEE descriptors wider than 128 bits with at most 32 exponent bits. A limb carrier outside that eligibility predicate still has arithmetic through the baseline. Selection also respects the `PolicyFor` instance in scope, including its resource limits. Even when a wide-limb candidate wins, its operand guards can send an individual call to the baseline; the public equation above covers both paths.

The [planner instances](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/Plan/Instances.lean) connect the public limb family to the automatic capabilities, carrying through the policy and proofs. [Chapter 01](#/chapter/using-the-library/a-tour-of-the-codebase) follows that connection in the source.

<a id="execfloat-the-carrier-and-its-backends"></a>

## Following a public arithmetic call

[[FloatLib.Floats.ExecFloat]] is defined as a subtype of the family's `FormatCode F` with a proof-only tag, so the runtime representation is exactly the chosen stored value. [[FloatLib.Floats.ExecFloat.Capability]] contains a specification, a [[FloatLib.Floats.ExecFloat.Backend.CandidateSet]] of [[FloatLib.Floats.ExecFloat.Backend.Certified]] kernels each carrying [[FloatLib.Floats.ExecFloat.Backend.Certified.run_eq_spec]], and the cached selection. Two equality fields connect this selection to execution: [[FloatLib.Floats.ExecFloat.Capability.implementation_is_selected]] and [[FloatLib.Floats.ExecFloat.Capability.execute_eq_implementation]].

[[FloatLib.Floats.ExecFloat.add]] and the other five operations use the capability. The specification module holds [[FloatLib.Floats.ExecFloat.Spec.add]] and its siblings, and the proof module states the six public equations, [[FloatLib.Floats.ExecFloat.Proof.add_eq_spec]] through [[FloatLib.Floats.ExecFloat.Proof.fma_eq_spec]]. [[FloatLib.Floats.ExecFloat.Proof.fullArithmeticCertificate]] collects these equations. The public equation applies directly to binary32 `+`. The two `#print axioms` commands show the dependencies of that equation and of the real-number theorem:

```lean
open FloatLib.Floats

example (x y : Binary32) : x + y = ExecFloat.Spec.add x y :=
  ExecFloat.Proof.add_eq_spec x y

#print axioms FloatLib.Floats.ExecFloat.Proof.add_eq_spec
-- 'FloatLib.Floats.ExecFloat.Proof.add_eq_spec' does not depend on any axioms

#print axioms FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt
-- 'FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt' depends on axioms: [propext,
--  Classical.choice,
--  Quot.sound]
```

The `example` type-checks because the `Add` instance on `Binary32` unfolds to [[FloatLib.Floats.ExecFloat.add]], the certified dispatch, so a theorem about `ExecFloat.add` is a theorem about `x + y`. The public equation is the projection of a certificate that the format constructed with its proof inside, so it needs no axioms at all; the real-number theorem quantifies over $\mathbb{R}$ and inherits the three axioms Mathlib's construction of the reals rests on: propositional extensionality, quotient soundness, and choice.

To follow the execution equation in the source, start with the [public dispatch](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Dispatch.lean): addition calls `Capability.run`, which uses the capability's `execute` field. `execute_eq_implementation` identifies that function with the stored certified implementation's `run`, and the implementation's own `run_eq_spec` closes the chain. `Capability.run_eq_spec` composes those two equalities, and `Proof.add_eq_spec` exposes the result under the public operation name. The separate field `implementation_is_selected` states that the stored certificate also matches the advertised planner choice. No input enumeration occurs in this proof. A different cost estimate may select another candidate, but every candidate admitted to the set already proves equality with the same specification, so changing the selection preserves the public equation.

Public `BinaryLimbs` arithmetic reaches the planner through the [planner instances](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/Plan/Instances.lean). Their heads name `Family format (Model.WideLimb.Value format) (.limbs h)`, the family shape exposed when the limb plan and `Code` reduce. This lets typeclass search find them directly. Each forwards to its `automatic*Capability` for `.limbs h`, passing through the family's `PolicyFor` instance and reusing the selected certificate and execution proofs. Alongside them, `limbCodec` supplies the model codec for the concrete carrier type, so literal construction and conversion work too.

<a id="the-host-fpu-is-a-separate-door"></a>

## Using the host FPU

Lean's `Float` and `Float32` expose host arithmetic, which offers a faster path for ordinary binary32 and binary64 operations. To include it in the planner, we would need a `Backend.Certified` value proving `run = spec` as a Lean equality.

That theorem would have to establish exact packed-word equality with the specification on every guarded finite input, including overflow, underflow, and signed zeros. It would also need the side conditions in Lean's logical model of multiplication and division, assuming the process uses round-to-nearest-even with gradual underflow. FloatLib supplies no such host-refinement theorem, so host operations are available only through the explicitly unchecked interface.

To choose guarded host arithmetic, import its separate module and name the operation at
the call site. This import leaves ordinary `+` on the certified software path:

```
import FloatLib
import FloatLib.Floats.Formats.BinaryInterchange.Configured.NativeFPU.Unchecked

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange.Configured

def hostAdd32 (x y : ExecFloat.Binary 8 23) : ExecFloat.Binary 8 23 :=
  NativeFPU.Unchecked.add32 x y
```

The module provides `NativeFPU.Unchecked.add32`, `sub32`, `mul32`, `div32`, and `sqrt32` and their binary64 counterparts, and no FMA; [chapter 15](#/chapter/performance/comparing-with-leans-native-floats) describes each function's guard and the assumptions under which it agrees with the proved kernels. These are direct calls rather than compiler replacements: there is no `@[implemented_by]` behind the binary kernels, and [chapter 05](#/chapter/why-execution-and-proofs-are-separate) explains the posit decoder's use of that attribute.
