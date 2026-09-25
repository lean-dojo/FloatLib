---
number: "16"
slug: backends-and-the-planner
title: Choosing an arithmetic backend
summary: The planner chooses a proved implementation using estimated computation and memory costs, while host arithmetic requires an explicit unchecked call.
phases: [backends, planner-and-configured, execution]
---

Once several proved implementations can do the same operation, we still have a choice to make:
a lookup table for a tiny format, a word kernel, a fixed-limb kernel, or the exact generic
baseline. They satisfy the same specification, but their setup costs, memory use, and costs per
call differ. The planner chooses among those available for your format, operation, and storage
representation. The kernels described in [chapter 15](#/chapter/kernels-fixed-word-algorithms)
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

[Chapter 17](#/chapter/performance) compares measured execution times.

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

The numerical layout and the stored representation determine which candidates are available.
On its byte carrier, E4M3 can offer a table, a word kernel, and the exact baseline. Binary128
can offer a two-limb kernel. Wider values gain limb kernels only when stored on the limb carrier.

| Candidate | Format and storage requirements |
| --- | --- |
| Exhaustive table | At most eight encoded bits, stored as a byte; the policy must admit its memory use |
| Word kernel | IEEE encoding fitting in 64 bits, with per-operation bounds on the intermediates |
| Fixed-format kernel | Exactly the binary32 or binary64 layout |
| Two-limb `NativePair` | IEEE encoding, more than 64 fraction bits, at most 128 encoded bits |
| Wide-limb kernel | IEEE encoding wider than 128 bits, at most 32 exponent bits, stored as a limb array |
| Exact baseline | Every descriptor; also supplies the fallback when a specialized kernel declines a call |

Tables store value-only answers, so their lookup certificates do not supply an exception-status
word. The detailed word and limb guards differ by operation:

<details>
<summary>Kernel algorithms, capacity bounds, and refinement declarations</summary>

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

Above 128 bits, eligibility also depends on the carrier, the runtime representation in which a value is stored. `ExecFloat.Binary` stores the exact-width proof model itself, the same structure the theorems are stated about, and on that carrier no specialized kernel is eligible, so all six operations run the exact baseline. `ExecFloat.BinaryLimbs` names the alternative carrier, an array of 32-bit limbs, with public arithmetic capabilities that use the automatic planner. For eligible IEEE descriptors, its candidate set also offers the [wide-limb backend](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/ExecFloat/Backends/WideLimb) for all six operations.

Addition, subtraction, multiplication, and FMA operate on the array when their normal-input and
normal-result guards accept the call. Their limb arithmetic keeps the significand out of `Nat`;
declined calls use the exact baseline. Division and square root instead read the stored fields
and use arbitrary-precision integer arithmetic: division handles all finite operands, while
square root accepts positive normal operands. Their remaining inputs use the reference
operation. [Chapter 15](#/chapter/kernels-fixed-word-algorithms/division-and-square-root-from-limb-storage)
explains the quotient and root rounding decisions. The refinement theorems
[[FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb.toModel_add]], `toModel_sub`,
`toModel_mul`, `toModel_div`, `toModel_sqrt`, and
[[FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb.toModel_fma]]
cover both accepted and fallback paths.

The [generic baseline](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/ExecFloat/Backends/Generic) is present for every descriptor. It implements exact-value rounding and the complete exceptional-value policy, and every specialized kernel returns to it when it declines an input, so the dispatchers never contain a second implementation of NaN or infinity handling.

The generic baseline preserves exact-value rounding while allowing bounded intermediates.
For IEEE addition, subtraction, and FMA, its
[bounded alignment](#/chapter/kernels-fixed-word-algorithms/bounded-alignment-in-generic-addition)
keeps enough low bits for nearest-even rounding when the scale gap rules out cancellation;
other inputs retain complete alignment. FMA forms the exact product before that step.
The baseline's square root calls the shared
[integer-root dispatcher](#/chapter/kernels-fixed-word-algorithms/increasing-precision-for-arbitrary-precision-square-root),
which uses a native-word iteration or a checked candidate at increasing precision.
These choices happen inside the generic implementation. They do not add a planner
candidate or change the `generic` result of the queries below.

</details>

For addition, the standard packed types select word or fixed-limb kernels through binary128. At 256 bits, `ExecFloat.Binary 19 236` selects the baseline and `ExecFloat.BinaryLimbs 19 236` selects wide-limb addition. Both are ordinary public arithmetic calls on the same numerical layout, stored differently.

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

<details>
<summary>Inspecting structural candidates before selection</summary>

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

</details>

<a id="what-a-candidate-advertises"></a>

## Estimating computation and memory costs

To compare the alternatives, we give every implementation a
[[FloatLib.Floats.ExecFloat.Backend.Candidate]] record with its name,
[[FloatLib.Floats.ExecFloat.Backend.KernelClass]], storage class, and estimated costs. The estimates
separate what we pay once from what we pay on every call: steady cost per call, conversion cost,
setup cost and allocations, resident and temporary bytes, and allocations per call.

The conversion cost, called *marshalling* in the record, accounts for moving operands and the result between the stored representation and the proof model. The estimates charge one unit per value on packed carriers and zero for byte-table lookups and accepted limb-kernel paths, which operate on stored values directly. A declined wide-limb call still converts through the proof model for the exact fallback. Setup cost matters for tables: a 64 KiB table is expensive to build but cheap to read, so the expected number of calls determines whether it is worth building. Allocations receive a separate penalty because they dominate the generic addition cost in the measurements used to choose the estimates.

A [[FloatLib.Floats.ExecFloat.Backend.Policy]] sets the expected workload and memory limits. Three are built in: `latency` expects one call, [[FloatLib.Floats.ExecFloat.Backend.Policy.default]] (the balanced profile) expects 100,000, and `throughput` expects 5,000,000. The first two allow 1 MiB of resident memory per candidate; throughput raises that to 16 MiB. All three allow 64 MiB of temporary memory, charge 32 units per allocation, and count memory in 64-byte blocks.

The [policy definition](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/Selection/Policy.lean)
sets these format-independent workload assumptions and relative weights. It gives no derivation
for the 32-unit allocation charge or the 64-byte memory block. The scores below order candidates
in this declared model; they are not times in nanoseconds. The earlier microsecond estimates
motivate avoiding allocation, but are separate from this configured score calculation.

<a id="the-selector"></a>

## How the planner chooses

The [scoring function](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/Selection/Scoring.lean) is a weighted sum. Warm cost is steady cost plus marshalling plus penalties for allocations and temporary memory blocks; cold cost is setup plus penalties for setup allocations and resident memory blocks; and

$$\mathrm{score} = \mathrm{expectedCalls} \cdot \mathrm{warmCost} + \mathrm{coldCost}.$$

Before scoring an alternative, `admissible` rejects it if its estimated resident or temporary
bytes exceed the policy's limits. `consider_rejects_excess_residency` proves that such a
candidate cannot replace the current choice.

[Figure 16.1](#/chapter/backends-and-the-planner/figure-ch09-backend-ladder) works through
addition on IEEE E4M3 with `UInt8` storage. Under the default policy, the table fits the memory
limit, but its setup cost makes it more expensive than the word kernel over 100,000 calls.

![Three eligible implementations of E4M3 addition, with estimated total costs of 1,500,000 for the word kernel, 1,742,848 for the table, and 2,100,000 for the baseline](assets/ch09-backend-ladder.png "The planner selects the lowest estimated cost among eligible alternatives. These are relative cost units for 100,000 calls, not measured execution times.")

[[FloatLib.Floats.ExecFloat.Backend.selectCertified]] starts with the required baseline and considers each alternative in turn, keeping the one with the lower score. The baseline remains available even if its estimated memory use exceeds the policy's limits, so selection always has a result. The limits filter alternatives; they do not guarantee a cap on the selected operation's memory use. `preferOnEqualScore` breaks ties in a fixed order: warm cost first, then marshalling, allocations, temporary bytes, resident bytes, cold cost, and finally kernel-class rank. The same descriptor, storage plan, candidate estimates, and policy therefore produce the same selection across machines and builds.

The fold operates on a [[FloatLib.Floats.ExecFloat.Backend.CandidateSet]] of [[FloatLib.Floats.ExecFloat.Backend.Certified]] values. A `Certified spec` is a record with an executable `run`, the estimate, and a proof `run_eq_spec : run = spec`; no constructor omits the proof. Two theorems connect selection to execution and reporting. [[FloatLib.Floats.ExecFloat.Backend.selectCertified_run_eq_spec]] says that whatever the fold returns satisfies `run = spec`, by using the selected candidate's certificate. This numerical equality holds independently of how accurately the estimates predict runtime. [[FloatLib.Floats.ExecFloat.Backend.selectCertified_estimate]] says that erasing the proofs and folding over the estimates alone gives the same answer, which lets an inspection tool report the plan without running the kernels.

```lean
open FloatLib.Floats.ExecFloat.Backend in
example {α : Type} {spec : α} (policy : Policy) (candidates : CandidateSet (Certified spec)) :
    (selectCertified policy candidates).run = spec :=
  selectCertified_run_eq_spec policy candidates
```

The selected certificate establishes the numerical result. To explain performance, we must
also connect the selected implementation to the function that a public call executes. We will
follow that connection after working through E4M3's costs.

<a id="asking-what-was-chosen"></a>

## Inspecting the selected backend

`selectedCandidate` exposes the estimate attached to the selected certificate. The equation `selected_eq_planner` identifies it with the planner's answer, so inspecting its kernel class reports the selected implementation without running the arithmetic. The capability classes are indexed by the encoded-format family underneath the public value type: `ExecFloat.Binary.Family` for the calls below, or `ExecFloat.Binary.LimbFamily` for the limb carrier.

<details>
<summary>Selected kernels across standard and custom widths</summary>

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

</details>

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

`#float_info! E4M3` adds the score calculation for every operation. `breakEvenCalls` asks when
one candidate recovers its setup cost relative to another. The estimates include carrier
conversion, one unit per value for the word kernel, and use the byte storage plan certified by
`e4m3_byte` below:

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

For addition, the table's cold cost is $65536\cdot22+32+65536/64=1442848$. The word candidate
costs $12+3=15$ per call, so the table saves 12 and needs $\lceil1442848/12\rceil=120238$ calls.
At the balanced horizon of 100,000 calls, its score is $100000\cdot3+1442848=1742848$, above the
word candidate's $100000\cdot15=1500000$. Square root has already amortized by that horizon:
its table scores $100000\cdot3+5924=305924$, against 3,200,000 for the word candidate and
3,100,000 for the exact baseline.

Memory eligibility explains the FMA result. Unary and binary byte-result tables through eight
encoded bits fit under 1 MiB; the binary table has 65,536 entries and occupies 64 KiB. Ternary
tables fit through six bits, but an eight-bit FMA table needs $2^{24}$ bytes, or 16 MiB, so the
balanced policy rejects it before scoring. The throughput ceiling admits every exhaustive
table over a byte carrier, leaving its setup cost to decide whether it pays back.

A `none` from `breakEvenCalls` means the candidate has no warm-cost advantage in this model,
so increasing the expected call count cannot recover its setup cost. All these calculations
use the declared cost model; the [performance chapter](#/chapter/performance) measures public
calls separately.

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
moves to its table. The value type and literals stay the same. We can now follow the selected
certificate into the public operation and its theorem.

<a id="selection-happens-when-the-type-is-elaborated"></a>
<a id="the-type-fixes-the-configuration-selection-is-cached"></a>
<a id="choosing-and-caching-an-implementation"></a>
<a id="execfloat-the-carrier-and-its-backends"></a>

## Following a public arithmetic call

Writing `(1.5 : E4M3) + 2.25` fixes the descriptor while Lean elaborates the expression and
finds its typeclass instances. `forKnownWidth` chooses a byte up to eight encoded bits, then
`UInt16`, `UInt32`, `UInt64`, and the proof model itself above 64. `ExecFloat` adds a proof-only
tag to the family's `FormatCode F`, so its runtime representation is the chosen stored value.

The addition [[FloatLib.Floats.ExecFloat.Capability]] holds the specification, candidates,
selected certificate, and `execute` function. A memoized `Thunk` caches the certificate, so
repeated calls through this capability share the selection. For default E4M3 addition that
certificate contains the word dispatcher whose score we just calculated. A different policy
or storage plan can have its own selection and cache.

To follow the call in the [public dispatch](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Dispatch.lean),
addition calls `Capability.run`, which uses `execute`. The field `execute_eq_implementation`
identifies that function with the stored certificate's `run`; the certificate's `run_eq_spec`
then identifies its result with the specification. [[FloatLib.Floats.ExecFloat.Capability.run_eq_spec]]
composes those equalities, and [[FloatLib.Floats.ExecFloat.Proof.add_eq_spec]] exposes the result
under the public operation name. The separate field `implementation_is_selected` proves that
the stored certificate is the planner's advertised winner.

```lean
example (x y : E4M3) : x + y = ExecFloat.Spec.add x y :=
  ExecFloat.Proof.add_eq_spec x y

example (x y : Binary256) : x + y = ExecFloat.Spec.add x y :=
  ExecFloat.Proof.add_eq_spec x y
```

The equation covers every pair of operands, including inputs on which the word kernel's guard
chooses the exact fallback. No input enumeration occurs in the proof. The same equation applies
to `Binary256`, whose proof-model carrier selects the baseline.

Within a selected kernel, specialization can fold layout constants and eligibility branches
at a closed-format call site. [[FloatLib.Floats.Formats.BinaryInterchange.Model.AddBackend.word_eq_spec]]
covers the resulting composite. Some plans can call the winning structural kernel directly;
that entry must still check both its eligibility and its policy win. A cached direct-dispatch
decision is checked on each closed automatic call, so dispatch can still contribute to its cost.
The selection and execution equations also apply when the descriptor or policy varies at runtime.

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

For this 256-bit descriptor with IEEE encoding, the default policy selects wide-limb candidates for all six operations. We can inspect addition, division, and square root through the public family:

```lean
#eval (ExecFloat.Add.selectedCandidate (F := ExecFloat.Binary.LimbFamily 19 236)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.wideLimbs
#eval (ExecFloat.Div.selectedCandidate (F := ExecFloat.Binary.LimbFamily 19 236)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.wideLimbs
#eval (ExecFloat.Sqrt.selectedCandidate (F := ExecFloat.Binary.LimbFamily 19 236)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.wideLimbs
```

The storage plan explains why `Binary256` and `Limb256` select different addition kernels. `.wide` stores `Model format` directly; it is the plan `ExecFloat.Binary` uses above 64 bits. `.limbs` stores `Model.WideLimb.Value format` and requires a proof that the encoded width exceeds 128 bits. The two plans share a descriptor but offer different candidate sets. The underlying fold can be inspected too:

<details>
<summary>The candidate fold for limb and proof-model storage</summary>

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
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.wideLimbs
open FloatLib.Floats.ExecFloat.Backend in
#eval (selectCertified Policy.default
  (Configured.Plan.automaticAddCandidates B256 .wide)).estimate.kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.generic
```

</details>

[[FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.wideLimbAdd?]] and its siblings offer limb kernels only for IEEE descriptors wider than 128 bits with at most 32 exponent bits. A limb carrier outside that eligibility predicate still has arithmetic through the baseline. Selection also respects the `PolicyFor` instance in scope, including its resource limits. Even when a wide-limb candidate wins, its operand guards can send an individual call to the baseline; the public equation above covers both paths.

For division and square root, the cost model assigns the direct limb candidate the generic
integer-work estimate, including its internal conversions. The adapted baseline also pays an
estimated cost for converting between the limb carrier and the proof model. This difference
makes the direct candidate win the default selection; it is a planning estimate, not a measured
speedup.

## Implementation reference

<details>
<summary>Candidate records, specialized entries, and instance construction</summary>

The kernel class names the algorithm family: `exhaustiveTable`, `fixedFormat`, `nativeWord`, `fixedLimbs`, `wideLimbs`, or `generic`. A family can also supply a `custom` label. These names appear in `#float_info`; their `rank` breaks ties when candidates have equal scores. Their display strings are "exhaustive encoded-value table", "fixed-format word kernel", "machine-word kernel", "fixed-limb kernel", "wide-limb kernel", and "exact baseline".

The candidate lists for configured binary formats are assembled per operation in the [configured planner](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/Plan). `addCandidates` and its siblings pair the descriptor's structural candidate with the exact generic baseline. [[FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.automaticAddCandidates]] then checks the storage plan and adds a byte table when the carrier is a byte, or a wide-limb candidate when the carrier is a limb array and the descriptor is eligible. Ineligible candidates are removed before scoring. The planner for binary32 therefore sees one alternative plus the baseline, while a 4096-bit format on the proof-model carrier sees the baseline alone.

The eligibility predicates also affect specialization. Their `Decidable` instances use explicit `if h : ... then isTrue h else isFalse h` branches. With `inferInstanceAs`, an auxiliary definition can hide the conditional; exposing it gives the compiler a branch it can inline and evaluate for a closed descriptor. At a specialized call site, that eligibility test can disappear. The planner's cached selection check is a separate step.

Machine-word plans and pair-eligible proof-model plans can also call a winning structural kernel directly. [[FloatLib.Floats.Formats.BinaryInterchange.Configured.StoragePlan.firstOrderDispatch]] checks only the storage; `Plan.firstOrderSelected` additionally checks that the structural candidate is admissible and wins the policy comparison. The direct branch calls that candidate's function, and the fallback calls `selection.get.run`. For example, an eight-bit IEEE descriptor stored in `UInt16` selects and executes generic FMA and square root: word storage alone does not choose the kernel.

At eight encoded bits, the square-root word estimate is 30 units of arithmetic plus two units of conversion, while the baseline estimate is 29 plus the same two. Both have zero cold cost. The baseline therefore wins even though a word implementation is available. `firstOrderDispatch` alone would miss this distinction; the additional policy comparison in `firstOrderSelected` is what keeps the direct branch tied to the selected candidate. Byte and limb plans keep the memoized selected entry, which can hold a table or a wide-limb candidate.

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

An ordinary wide `ExecFloat.Binary` call can enter the selected generic kernel directly.
The [direct-entry guard](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/Plan/FirstOrder.lean),
`firstOrderGenericSelected`, checks that the generic candidate wins on a carrier without
byte-table or limb candidates. `select_add_run_of_firstOrderGeneric` proves that
`Backend.genericAdd` is the winning certificate's stored function. The capability's `execute`
field uses this equality to expose the direct call, allowing the compiler to specialize the
kernel to constant descriptor parameters. The other five operations follow the same pattern
and retain their selected certificates.

Public `BinaryLimbs` arithmetic reaches the planner through the [planner instances](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/Plan/Instances.lean). Their heads name `Family format (Model.WideLimb.Value format) (.limbs h)`, the family shape exposed when the limb plan and `Code` reduce. This lets typeclass search find them directly. Each forwards to its `automatic*Capability` for `.limbs h`, passing through the family's `PolicyFor` instance and reusing the selected certificate and execution proofs. Alongside them, `limbCodec` supplies the model codec for the concrete carrier type, so literal construction and conversion work too.

</details>

<details>
<summary>Public equations and their axiom dependencies</summary>

[[FloatLib.Floats.ExecFloat.add]] and the other five operations use the capability. The specification module holds [[FloatLib.Floats.ExecFloat.Spec.add]] and its siblings, and the proof module states the six public equations, [[FloatLib.Floats.ExecFloat.Proof.add_eq_spec]] through [[FloatLib.Floats.ExecFloat.Proof.fma_eq_spec]]. [[FloatLib.Floats.ExecFloat.Proof.fullArithmeticCertificate]] collects these equations. The same public equation applies directly to binary32 `+`. The two `#print axioms` commands show the dependencies of that equation and of the real-number theorem:

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

</details>

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

The [native-floats chapter](#/chapter/lean-native-floats/opting-into-guarded-host-operations)
works through the guards, NaN payload handling, and required process settings. The ten named
functions cover addition, subtraction, multiplication, division, and square root at both host
widths; there is no unchecked FMA. They are explicit calls, with no `@[implemented_by]`
substitution behind the certified binary operations.
