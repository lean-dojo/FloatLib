---
number: "16"
slug: backends-and-the-planner
title: Choosing an arithmetic backend
summary: The planner chooses a proved implementation from estimated computation and memory costs, and you get raw host results only by calling the unchecked function yourself.
phases: [backends, planner-and-configured, execution]
---

A lookup table, a word kernel, and the exact generic baseline can all implement the same arithmetic operation. They satisfy the same specification, but their setup costs, memory use, and costs per call differ. The planner chooses among those available for the format, operation, and storage representation. The [kernels from chapter 15](#/chapter/kernels-fixed-word-algorithms) supply the arithmetic; the policy tells the planner how to weigh their costs for the expected workload.

For an eight-bit format, there are 256 codes and 65,536 ordered operand pairs. We can calculate every addition once, store the answers in 64 KiB, and replace each later addition with a table lookup. That saves arithmetic on every call, but first we have to generate the table. For IEEE E4M3, the default policy estimates that a word kernel is cheaper over 100,000 calls; the throughput policy, expecting five million calls, selects the table instead.

Each candidate carries a proof that its `run` equals the common specification, and the planner keeps that proof when it chooses a candidate. A bad cost estimate can select slow code, but the selected operation still has to return the specified result. GMP also chooses algorithms by size [@gmpManual], and FFTW separates a transform description from its execution plan [@fftwPlanner].

<a id="what-can-we-choose"></a>

## Choosing a backend

The planner ranks the certified kernels available for your format and storage using declared cost estimates. It doesn't time alternatives on your machine or learn from benchmark results. The workload you expect therefore matters: a table that pays for itself after thousands of calls is expensive for a calculation you run once.

| Choice | How to request it | What changes |
| --- | --- | --- |
| Favor a few calls | Open the `PlanningLatency` scope | Avoids setup that may not pay back |
| Favor repeated calls | Open the `PlanningThroughput` scope | Amortizes setup over more calls and allows larger tables |
| Set your own workload and memory limits | Supply a local `Backend.PolicyFor` instance | Changes the scores and which candidates fit the limits |
| Store wide binary values as limbs | Use `ExecFloat.BinaryLimbs` | Makes eligible wide-limb kernels available |
| Use direct host FPU operations at 32 or 64 bits | Import `NativeFPU.Unchecked` and call its named functions | Uses guarded host arithmetic without a FloatLib refinement certificate |

You can see the scopes in use in the [policy examples below](#/chapter/backends-and-the-planner/changing-the-workload-without-changing-the-mathematics), and the import and call in the [host example](#/chapter/backends-and-the-planner/using-the-host-fpu).

Binary32 and binary64 already select their fixed-format software kernels. In the current candidate sets those kernels beat the exact baseline under every policy, so switching to the throughput profile leaves these two formats on the same kernels.

Some quotient and square-root kernels use host floating-point operations to propose a candidate, check it with exact integer arithmetic, and fall back if it's rejected. Their refinement proofs cover both paths and don't assume the proposal is accurate. Getting host arithmetic results back as they are is still something you ask for by name, through `NativeFPU.Unchecked`. SoftFloat, MPFR, and Universal are libraries we compare against, and you can't select them as FloatLib backends. [Chapter 17](#/chapter/performance) compares measured execution times.

## Why different widths use different kernels

To handle every width, the generic baseline computes on `Nat` significands, and its wide intermediates need heap allocations. You can see what that costs in the [calibrated cost model](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Descriptor/Plan/Estimates.lean), which estimates addition at about 4.1 microseconds for 256 bits and 5.3 microseconds for 4096 bits. Making the width sixteen times larger changes the estimate far less than that, because the model puts most of the cost in fixed allocation overhead.

Each specialized representation avoids a different cost. A table replaces the arithmetic with one index computation and one byte load. A one-word kernel avoids allocation by keeping every field, aligned significand, and rounding decision in a `UInt64`. A two-word kernel keeps binary128 in a pair of machine words, where the baseline would use an arbitrary-precision integer. A limb-array kernel keeps a 4096-bit significand in one mutable array and doesn't allocate a fresh bignum for every shift. The generic path uses arbitrary-precision intermediates to handle every descriptor and exceptional case. For addition, every one of them proves agreement with the same reference function, `ExecFloat.Spec.add`.

## Available kernels

Which candidates are available depends on the numerical layout and the stored representation. On its byte carrier, E4M3 can offer a table, a word kernel, and the exact baseline. Binary128 can offer a two-limb kernel. Wider values get limb kernels only when they're stored on the limb carrier.

| Candidate | Format and storage requirements |
| --- | --- |
| Exhaustive table | At most eight encoded bits, stored as a byte; the policy must admit its memory use |
| Word kernel | IEEE encoding fitting in 64 bits, with per-operation bounds on the intermediates |
| Fixed-format kernel | Exactly the binary32 or binary64 layout |
| Two-limb `NativePair` | IEEE encoding, more than 64 fraction bits, at most 128 encoded bits |
| Wide-limb kernel | IEEE encoding wider than 128 bits, at most 32 exponent bits, stored as a limb array |
| Exact baseline | Every descriptor; also supplies the fallback when a specialized kernel declines a call |

Tables store value-only answers, so their lookup certificates don't supply an exception-status word. The detailed word and limb guards differ by operation:

<details>
<summary>Kernel algorithms, capacity bounds, and refinement declarations</summary>

Formats of at most eight encoded bits get exhaustive tables, built in the [configured byte-table implementation](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/ByteTable). On first use, we generate each table by evaluating the reference operation itself. The lookup proof then needs to justify indexing and encoding, without certifying another arithmetic algorithm. [[FloatLib.Floats.Formats.BinaryInterchange.Configured.ByteTable.runBinary_eq_lift]], `runUnary_eq_lift`, and `runTernary_eq_lift` say that reading the generated entry recovers the reference result. For an 8-bit format a two-operand table has $2^{16}$ entries and a three-operand table $2^{24}$, and that's where the resource policy below starts to matter.

Say the format has $n$ possible words. A binary table puts the answer for operand codes $i$ and $j$ at index $in+j$. To build the table we recover those operands by quotient and remainder on division by $n$, evaluate the model operation, and store its encoded result, and lookup does the inverse calculation. Our indexing proof shows that the native index doesn't wrap and lies inside the table, and the encoding's round-trip laws then identify the loaded byte with the specified result. Every encoded operand takes part, signed zeros, infinities, and NaNs included when the descriptor has them.

Formats of at most 64 bits can use the word kernels in the [word-kernel directory](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/ExecFloat/Backends/Word), subject to the capacity bounds below, and for 8-bit formats the planner also considers the table. Our [parameterized word implementation](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/ExecFloat/Backends/Word/Small) works across formats. For any IEEE descriptor whose encoding fits a word, it decodes fields with shifts, aligns, combines signed magnitudes, and rounds, all without allocating a `Nat`. Its capacity bounds differ by operation because the intermediates differ. Addition and subtraction admit up to 30 exponent bits and 61 fraction bits. Multiplication admits 31 fraction bits, because a 32-bit normalized significand still has an exact 64-bit product. Between 32 and 61 fraction bits the product of a one-word format no longer fits a word, so the [two-word multiplication kernel](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/ExecFloat/Backends/Word/TwoWordMul) forms an exact `64 x 64 -> 128` product.

Division admits every IEEE descriptor with at most 64 encoded bits, the condition `NativeSmallWord.StorageEligible`. Once the sign and at least two exponent bits are taken out, at most 61 fraction bits are left, which is enough for the restoring quotient's capacity proof. Its normal-input and normal-result checks still send declined calls to the exact baseline.

In the [binary32 kernels](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/ExecFloat/Backends/Word/Narrow) and [binary64 kernels](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/ExecFloat/Backends/Word/Full) you'll find specializations for those two layouts, and they reuse the parameterized kernels too. Binary64 addition first tries the parameterized [small-word addition](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/ExecFloat/Backends/Word/Small/Add) kernel, whose 61-fraction-bit contract admits binary64, and on the inputs that kernel declines, it runs its own fixed-format code. Its proof applies the parameterized kernel's refinement theorem on accepted inputs and handles the declined cases with its own arithmetic and proof.

Binary64 multiplication has its own [dispatch sequence](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/Dispatch/Mul/Runtime.lean), so let's follow one product through it. It tries `NativeTwoWordMul.mulNormal?` first, and if that declines, it tries the binary64 `mulNormalLimb?` implementation in the [full-word core](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/Word/Full/Core/Runtime.lean). If both decline, the generic exact kernel supplies the result. So a planner label names the complete dispatch function, fallbacks included, and not a single arithmetic routine.

From 65 to 128 bits, when the fraction is wider than one word, the [two-limb `NativePair` kernel](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/ExecFloat/Backends/FixedLimb/Pair) holds the value in two `UInt64` limbs with every field position derived from the descriptor. That covers binary128 and every `ExecFloat.Binary e f` with $65 \le f$ and $e + f \le 127$, and all six operations are implemented. Division checks a radix-$2^{32}$ quotient candidate against an independent Euclidean certificate and replaces a rejected candidate with a proved restoring result. Square root declines two kinds of layout and sends them to the exact baseline. One has a fraction wider than 124 bits, where the doubled remainder would no longer fit the two-word state. The other has an exponent bias that doesn't exceed the fraction width, where the kernel's exponent arithmetic doesn't apply.

Above 128 bits, eligibility also depends on the carrier, the runtime representation a value is stored in. `ExecFloat.Binary` stores the exact-width proof model itself, the same structure the theorems are stated about. No specialized kernel is eligible on that carrier, so all six operations run the exact baseline. The other carrier is `ExecFloat.BinaryLimbs`, an array of 32-bit limbs whose public arithmetic capabilities use the automatic planner. For eligible IEEE descriptors its candidate set also offers the [wide-limb backend](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/ExecFloat/Backends/WideLimb) for all six operations.

Addition, subtraction, multiplication, and FMA work on the array when their normal-input and normal-result guards accept the call. Their limb arithmetic keeps the significand out of `Nat`, and declined calls use the exact baseline. Division and square root read the stored fields and use arbitrary-precision integer arithmetic. Division handles all finite operands and square root accepts positive normal operands, and their remaining inputs use the reference operation. [Chapter 15](#/chapter/kernels-fixed-word-algorithms/division-and-square-root-from-limb-storage) explains the quotient and root rounding decisions. The refinement theorems [[FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb.toModel_add]], `toModel_sub`, `toModel_mul`, `toModel_div`, `toModel_sqrt`, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb.toModel_fma]] cover both the accepted and the fallback paths.

Every descriptor has the [generic baseline](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/ExecFloat/Backends/Generic), which implements exact-value rounding and the complete exceptional-value policy. Every specialized kernel falls back to it when it declines an input, so no dispatcher contains a second implementation of NaN or infinity handling.

Exact-value rounding doesn't stop the baseline from using bounded intermediates. For IEEE addition, subtraction, and FMA, its [bounded alignment](#/chapter/kernels-fixed-word-algorithms/bounded-alignment-in-generic-addition) keeps enough low bits for nearest-even rounding when the scale gap rules out cancellation. Other inputs keep complete alignment, and FMA forms the exact product before that step. For square root the baseline calls the shared [integer-root dispatcher](#/chapter/kernels-fixed-word-algorithms/increasing-precision-for-arbitrary-precision-square-root), which uses a native-word iteration or a checked candidate at increasing precision. All of these choices happen inside the generic implementation, so they don't add a planner candidate or change the `generic` result of the queries below.

</details>

Up through binary128, the standard packed types select word or fixed-limb kernels for addition. At 256 bits, `Binary256` selects the baseline and `ExecFloat.BinaryLimbs 19 236` selects wide-limb addition. Both are ordinary public arithmetic calls on the same numerical layout, and only the storage differs.

We'll name one executable format, `E4M3IEEE`, with four exponent and three fraction bits and the IEEE encoding. Unlike OCP's E4M3FN of [chapter 11](#/chapter/low-precision-formats-for-machine-learning), it has infinities. Then we run the same addition on it and on binary128. The two representable values add to the same exact result through different kernels:

```lean
open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

abbrev E4M3IEEE := ExecFloat.Binary (exponentBits := 4) (fractionBits := 3)

#eval (1.5 : E4M3IEEE) + 2.25
-- 3.75
#eval (1.5 : Binary128) + 2.25
-- 3.75
```

Under the default policy the 8-bit addition runs a machine-word kernel and the binary128 addition runs a two-limb kernel, so the same answer comes out of two quite different pieces of code. Both inputs and the exact sum are representable in each format, so neither call has to round.

## Which formats a kernel supports

Kernels check the descriptor's fields, so a custom `ExecFloat.Binary` with the same layout as a standard format qualifies for the same kernel, and each kernel states its requirements as a proposition Lean can decide.

For word storage, `StorageEligible` says the encoding is IEEE and fits in 64 bits. Division uses that condition alone, and its theorem `divNormal_refines_of_storage` needs only `StorageEligible`. The narrower [[FloatLib.Floats.Formats.BinaryInterchange.Model.NativeSmallWordAdd.Eligible]] and [[FloatLib.Floats.Formats.BinaryInterchange.Model.NativeSmallWordMul.Eligible]] add the per-operation capacity bounds from the previous section, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.NativeTwoWordMul.Eligible]] does the same for the two-word product. For the fixed-format specializations, [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.IsBinary32]] and `IsBinary64` check layout equalities. The two-limb condition [[FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair.Eligible]] is `isIEEE ∧ 64 < fracWidth ∧ bitWidth ≤ 128`, and for limb arrays [[FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb.Eligible]] is `isIEEE ∧ 128 < bitWidth ∧ expWidth ≤ 32`.

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

A format can qualify for a kernel even when some of its operands need a fallback. The planner selects a proved dispatcher that includes both the partial fast kernel and the correct fallback. It checks the format requirements first, and the selected function then checks each call's operands. So when the planner reports a word kernel, it's naming this combined function, and an exceptional input may still go to the fallback.

Take the negative `NativePair.Eligible` example, an 80-bit layout with a 64-bit fraction. That fraction fills the low word exactly and leaves no fraction bits in the high word, but the pair kernel assumes the high word holds sign, exponent, and the top of the fraction. For narrower fractions the exponent field would typically straddle the word boundary. Because the capacity predicate fails, this layout never makes the pair candidate list and stays on the exact baseline.

<details>
<summary>Inspecting structural candidates before selection</summary>

For each operation, [[FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Plan.structuralRoute?]] chooses at most one of three kernel types, fixed format, machine word, or fixed limbs. It tries them in the same order as the executable dispatcher, and that identifies a candidate for the configured format. Whether the candidate runs also depends on the storage plan and the policy comparison.

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

The 52-bit layout with 40 fraction bits fits in one word, but its exact significand product doesn't. It therefore adds in one word and multiplies through the two-word product. The planner classifies that product as fixed-limb code even though the stored format itself fits one word. A `none` means none of the three kernel types applies. On the proof-model carrier the 256-bit descriptor shown here uses the exact baseline, and a limb-array carrier can also offer a wide-limb candidate. Byte tables are another alternative that depends on the storage representation.

</details>

## Estimating computation and memory costs

To compare the alternatives, we give every implementation a [[FloatLib.Floats.ExecFloat.Backend.Candidate]] record with its name, [[FloatLib.Floats.ExecFloat.Backend.KernelClass]], storage class, and estimated costs. Those estimates keep what we pay once apart from what we pay on every call, and they record steady cost per call, conversion cost, setup cost and allocations, resident and temporary bytes, and allocations per call.

Conversion cost, which the record calls *marshalling*, accounts for moving operands and the result between the stored representation and the proof model. We charge one unit per value on packed carriers. Byte-table lookups and accepted limb-kernel paths have zero marshalling cost, since they work on the stored values, while a declined wide-limb call still converts through the proof model for the exact fallback.

Setup cost matters for tables. A 64 KiB table is expensive to build but cheap to read, so the expected number of calls decides whether it's worth building. Allocations get a penalty of their own because, in the measurements we used to choose the estimates, they dominate the generic addition cost.

A [[FloatLib.Floats.ExecFloat.Backend.Policy]] sets the expected workload and memory limits, and three come built in. `latency` expects one call, the balanced profile [[FloatLib.Floats.ExecFloat.Backend.Policy.default]] expects 100,000, and `throughput` expects 5,000,000. Latency and the balanced profile allow 1 MiB of resident memory per candidate, and throughput raises that to 16 MiB. All three allow 64 MiB of temporary memory, charge 32 units per allocation, and count memory in 64-byte blocks.

These workload assumptions and weights are defined in the [policy](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/Selection/Policy.lean). The 32-unit allocation charge and 64-byte memory block are parameters of that model, and its scores are relative costs rather than nanoseconds. The microsecond estimates from earlier are the reason to avoid allocation, but they don't feed into this configured score calculation.

## How the planner chooses

Our [scoring function](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/Selection/Scoring.lean) is a weighted sum. Warm cost is steady cost plus marshalling plus penalties for allocations and temporary memory blocks, and cold cost is setup plus penalties for setup allocations and resident memory blocks. The score combines them as

$$\mathrm{score} = \mathrm{expectedCalls} \cdot \mathrm{warmCost} + \mathrm{coldCost}.$$

Before an alternative is scored, `admissible` rejects it if its estimated resident or temporary bytes exceed the policy's limits, and `consider_rejects_excess_residency` proves that such a candidate can't replace the current choice. [Figure 16.1](#/chapter/backends-and-the-planner/figure-ch09-backend-ladder) works through addition on IEEE E4M3 with `UInt8` storage. Under the default policy the table fits the memory limit, but over 100,000 calls its setup cost makes it more expensive than the word kernel.

![Three eligible implementations of E4M3 addition, with estimated total costs of 1,500,000 for the word kernel, 1,742,848 for the table, and 2,100,000 for the baseline](assets/ch09-backend-ladder.png "The planner selects the lowest estimated cost among eligible alternatives. These are relative cost units for 100,000 calls, not measured execution times.")

[[FloatLib.Floats.ExecFloat.Backend.selectCertified]] starts with the required baseline and considers each alternative in turn, keeping whichever has the lower score. The baseline stays available even if its estimated memory use exceeds the policy's limits, so selection always has a result. That also means the limits only filter alternatives and don't guarantee a cap on the selected operation's memory use. `preferOnEqualScore` breaks ties in a fixed order, with warm cost first, then marshalling, allocations, temporary bytes, resident bytes, cold cost, and finally kernel-class rank. Given the same descriptor, storage plan, candidate estimates, and policy, you get the same selection on every machine and build.

The fold runs over a [[FloatLib.Floats.ExecFloat.Backend.CandidateSet]] of [[FloatLib.Floats.ExecFloat.Backend.Certified]] values. A `Certified spec` is a record with an executable `run`, the estimate, and a proof `run_eq_spec : run = spec`, and no constructor leaves the proof out. Two theorems connect selection to execution and reporting. [[FloatLib.Floats.ExecFloat.Backend.selectCertified_run_eq_spec]] says that whatever the fold returns satisfies `run = spec`, using the selected candidate's certificate, and that holds however well or badly the estimates predict runtime. [[FloatLib.Floats.ExecFloat.Backend.selectCertified_estimate]] says that erasing the proofs and folding over the estimates alone gives the same answer, which is what lets an inspection tool report the plan without running the kernels.

```lean
open FloatLib.Floats.ExecFloat.Backend in
example {α : Type} {spec : α} (policy : Policy) (candidates : CandidateSet (Certified spec)) :
    (selectCertified policy candidates).run = spec :=
  selectCertified_run_eq_spec policy candidates
```

To apply this selection theorem to an ordinary `+` expression, we still need to identify the function that the public call executes. The capability records below supply that equality.

## Inspecting the selected backend

`selectedCandidate` exposes the estimate attached to the selected certificate. The equation `selected_eq_planner` identifies it with the planner's answer, so you can read the selected implementation off its kernel class without running any arithmetic. Capability classes are indexed by the encoded-format family underneath the public value type. That's `ExecFloat.Binary.Family` for the calls below, or `ExecFloat.Binary.LimbFamily` for the limb carrier.

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

Here the 80-bit layout from the eligibility section shows up as `generic`, as the pair predicate said it would. On the 8-bit format, table, word, and baseline candidates can all compete, and different operations pick different winners:

```lean
#eval (ExecFloat.Add.selectedCandidate (F := ExecFloat.Binary.Family 4 3)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.nativeWord
#eval (ExecFloat.Sqrt.selectedCandidate (F := ExecFloat.Binary.Family 4 3)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.exhaustiveTable
#eval (ExecFloat.Fma.selectedCandidate (F := ExecFloat.Binary.Family 4 3)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.generic
```

If you want to know which implementation an arithmetic expression will use, ask `#float_info`. It synthesizes the capability instances for the six operations and reads the selected candidate from each. Its execution section looks like this:

```lean
#float_info E4M3IEEE
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

`#float_info! E4M3IEEE` adds the score calculation for every operation. `breakEvenCalls` asks when one candidate recovers its setup cost relative to another. Its estimates include carrier conversion, one unit per value for the word kernel, and use the byte storage plan certified by `e4m3_byte` below:

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

Let's work through the first break-even calculation by counting what square root's table costs to build and to use. Its cold cost is $256\cdot23+32+256/64=5924$, which covers generating 256 answers, one setup allocation, and four resident-memory blocks. Its warm cost is three, against the word candidate's $30+2=32$, so it saves 29 units per call and recovers its setup after $\lceil5924/29\rceil=205$ calls. But the exact baseline costs only 31 units per call, and against that competitor the same table needs $\lceil5924/28\rceil=212$ calls. So the table beats the word kernel at 205 calls and needs 212 calls to beat both alternatives.

For addition, the table's cold cost is $65536\cdot22+32+65536/64=1442848$. Each call costs the word candidate $12+3=15$, so the table saves 12 and needs $\lceil1442848/12\rceil=120238$ calls. At the balanced horizon of 100,000 calls its score is $100000\cdot3+1442848=1742848$, above the word candidate's $100000\cdot15=1500000$. Square root has paid off its table well before that horizon, with a score of $100000\cdot3+5924=305924$ against 3,200,000 for the word candidate and 3,100,000 for the exact baseline.

Memory is what explains the FMA result. Unary and binary byte-result tables through eight encoded bits fit under 1 MiB, and the binary table has 65,536 entries and occupies 64 KiB. Ternary tables fit through six bits, but an eight-bit FMA table needs $2^{24}$ bytes, or 16 MiB, so the balanced policy rejects it before scoring. Under the throughput ceiling every exhaustive table over a byte carrier is admitted, and its setup cost decides whether it pays back. If `breakEvenCalls` returns `none`, the candidate has no warm-cost advantage in this model, and no expected call count will recover its setup cost. All of these calculations use the declared cost model, and public calls are measured in the [performance chapter](#/chapter/performance).

<a id="changing-the-workload-without-changing-the-mathematics"></a>

## Setting the expected workload

Policies come from a typeclass, [[FloatLib.Floats.ExecFloat.Backend.PolicyFor]], with a low-priority default instance for the balanced profile. Two scoped instances, `PlanningLatency.policy` and `PlanningThroughput.policy`, switch every format at once, and `custom` builds a local instance for one family from any `Policy`. Let's keep the format fixed and change only the policy in scope:

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

Under the latency profile even the 256-entry square-root table isn't worth building for one call. Under the throughput profile the 16 MiB ceiling admits the FMA table, but its setup still doesn't pay off over five million calls, so FMA stays on the exact baseline while addition moves to its table. Both scopes keep the same value type, literals, and reference operation.

<a id="choosing-and-caching-an-implementation"></a>

## Following a public arithmetic call

In `(1.5 : E4M3IEEE) + 2.25`, the descriptor is fixed while Lean elaborates the expression and finds its typeclass instances. `forKnownWidth` chooses a byte up to eight encoded bits, then `UInt16`, `UInt32`, and `UInt64`, so our E4M3 value lives in a byte. Eligible layouts from 65 through 128 bits use the `.pair` plan, which stores two native words, and wider or ineligible layouts keep the proof model. `ExecFloat` adds a proof-only tag to the family's `FormatCode F`, so at runtime it's just the chosen stored value. For addition, the [[FloatLib.Floats.ExecFloat.Capability]] holds the specification, candidates, selected certificate, and `execute` function. A memoized `Thunk` caches the certificate, so repeated calls through this capability share one selection. For default E4M3 addition that certificate contains the word dispatcher whose score we calculated above, and a different policy or storage plan can have its own selection and cache.

In the [public dispatch](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Dispatch.lean), addition calls `Capability.run`, which uses `execute`. The field `execute_eq_implementation` identifies that function with the stored certificate's `run`, and then the certificate's `run_eq_spec` identifies its result with the specification. [[FloatLib.Floats.ExecFloat.Capability.run_eq_spec]] composes those equalities, and [[FloatLib.Floats.ExecFloat.Proof.add_eq_spec]] exposes the result under the public operation name. Another field, `implementation_is_selected`, proves that the stored certificate is the planner's advertised winner.

```lean
example (x y : E4M3IEEE) : x + y = ExecFloat.Spec.add x y :=
  ExecFloat.Proof.add_eq_spec x y

example (x y : Binary256) : x + y = ExecFloat.Spec.add x y :=
  ExecFloat.Proof.add_eq_spec x y
```

That equation covers every pair of operands, including inputs where the word kernel's guard picks the exact fallback. The proof enumerates nothing, and it applies just as well to `Binary256`, whose proof-model carrier selects the baseline. Inside a selected kernel, specialization can fold layout constants and eligibility branches at a closed-format call site, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.AddBackend.word_eq_spec]] covers the resulting composite. Some plans can call the winning structural kernel directly, but that entry still has to check both its eligibility and its policy win. Each closed automatic call checks a cached direct-dispatch decision, so dispatch can still add to its cost. The selection and execution equations also apply when the descriptor or policy varies at runtime.

## Choosing the limb carrier

`ExecFloat.BinaryLimbs` stores a wide value in an array of 32-bit limbs between calls. Literals, ordinary arithmetic, and the public specification equations all work on this carrier too:

```lean
abbrev Limb256 := ExecFloat.BinaryLimbs (exponentBits := 19) (fractionBits := 236)

#eval (1.5 : Limb256) + 2.25
-- 3.75

example (x y : Limb256) : x + y = ExecFloat.Spec.add x y :=
  ExecFloat.Proof.add_eq_spec x y
```

For this 256-bit descriptor with IEEE encoding, the default policy selects wide-limb candidates for all six operations. Here are addition, division, and square root through the public family:

```lean
#eval (ExecFloat.Add.selectedCandidate (F := ExecFloat.Binary.LimbFamily 19 236)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.wideLimbs
#eval (ExecFloat.Div.selectedCandidate (F := ExecFloat.Binary.LimbFamily 19 236)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.wideLimbs
#eval (ExecFloat.Sqrt.selectedCandidate (F := ExecFloat.Binary.LimbFamily 19 236)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.wideLimbs
```

`Binary256` and `Limb256` select different addition kernels because their storage plans differ. `.wide` stores `Model format` itself and is the default for this 256-bit layout, while `.limbs` stores `Model.WideLimb.Value format` and requires a proof that the encoded width exceeds 128 bits. So the two plans share a descriptor but offer different candidate sets. You can inspect the underlying fold too:

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

[[FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.wideLimbAdd?]] and its siblings offer limb kernels only for IEEE descriptors wider than 128 bits with at most 32 exponent bits. A limb carrier outside that eligibility predicate still gets arithmetic, through the baseline. Selection also respects the `PolicyFor` instance in scope, resource limits included. Even when a wide-limb candidate wins, its operand guards can send an individual call to the baseline, and the public equation above covers that path too.

For division and square root, the cost model gives the direct limb candidate the generic integer-work estimate, internal conversions included. The adapted baseline also pays an estimated cost for converting between the limb carrier and the proof model, and that difference is what makes the direct candidate win the default selection. It's a difference in planning estimates, so don't read it as a measured speedup :)

## Implementation reference

<details>
<summary>Candidate records, specialized entries, and instance construction</summary>

A kernel class names the algorithm family. The classes are `exhaustiveTable`, `fixedFormat`, `nativeWord`, `fixedLimbs`, `wideLimbs`, and `generic`, and a family can also supply a `custom` label. These names appear in `#float_info`, and their `rank` breaks ties when candidates have equal scores. Their display strings are "exhaustive encoded-value table", "fixed-format word kernel", "machine-word kernel", "fixed-limb kernel", "wide-limb kernel", and "exact baseline". For configured binary formats, the [configured planner](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/Plan) assembles the candidate lists per operation. `addCandidates` and its siblings pair the descriptor's structural candidate with the exact generic baseline, and [[FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.automaticAddCandidates]] then checks the storage plan. It adds a byte table when the carrier is a byte, or a wide-limb candidate when the carrier is a limb array and the descriptor is eligible.

Ineligible candidates are dropped before scoring. So for binary32 the planner sees one alternative plus the baseline, and a 4096-bit format on the proof-model carrier sees the baseline alone.

Eligibility predicates also affect specialization. Their `Decidable` instances are written as `if h : ... then isTrue h else isFalse h` branches. With `inferInstanceAs`, an auxiliary definition can hide the conditional, and exposing it gives the compiler a branch it can inline and evaluate for a closed descriptor. At a specialized call site that eligibility test can disappear, though the planner's cached selection check is a different step.

Machine-word plans and pair-eligible proof-model plans can also call a winning structural kernel directly. [[FloatLib.Floats.Formats.BinaryInterchange.Configured.StoragePlan.firstOrderDispatch]] checks only the storage, and `Plan.firstOrderSelected` also checks that the structural candidate is admissible and wins the policy comparison. The direct branch calls that candidate's function, and the fallback calls `selection.get.run`. An eight-bit IEEE descriptor stored in `UInt16`, for example, selects and executes generic FMA and square root, because word storage alone doesn't choose the kernel. At eight encoded bits the square-root word estimate is 30 units of arithmetic plus two units of conversion. For the baseline it's 29 plus the same two, and both have zero cold cost. So the baseline wins, even though a word implementation is available. `firstOrderDispatch` alone would miss this, and it's the extra policy comparison in `firstOrderSelected` that keeps the direct branch tied to the selected candidate. Byte and limb plans keep the memoized selected entry, which can hold a table or a wide-limb candidate.

For binary32 and binary64, each operation compiles to a C function over `uint32_t` or `uint64_t`. Their first-order instances in the [fixed-format dispatch](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/NativeDispatch.lean) name the fixed-format certificate themselves. [[FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.selectCertified_binary32AddCandidates]] and its eleven siblings prove that the planner picks that certificate under every policy, and they do it by cost dominance, through `selectCertified_cons_of_dominant`. Whatever profile is in scope, binary32 and binary64 run the proved fixed-format software.

```lean
open FloatLib.Floats.ExecFloat.Backend in
theorem binary32_add_selects_software (policy : Policy)
    (h : FloatFormat.binary32.bitWidth ≤ 32) :
    selectCertified policy (Configured.Plan.binary32AddCandidates h) =
      Configured.Plan.softwareAdd32Certified h :=
  Configured.Plan.selectCertified_binary32AddCandidates policy h
```

Hypothesis `h` proves that the layout fits the `word32` storage plan. `StoragePlan.forKnownWidth` supplies this proof for a 32-bit width, and you can also prove it with `decide`. It puts no restriction on the operands.

There's a direct path for wide formats too, since an ordinary wide `ExecFloat.Binary` call can enter the selected generic kernel directly. The [direct-entry guard](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/Plan/FirstOrder.lean), `firstOrderGenericSelected`, checks that the generic candidate wins on a carrier without byte-table or limb candidates, and then `select_add_run_of_firstOrderGeneric` proves that `Backend.genericAdd` is the winning certificate's stored function. The capability's `execute` field uses this equality to expose the direct call, so the compiler can specialize the kernel to constant descriptor parameters. Each of the other five operations follows the same pattern and keeps its selected certificate.

Public `BinaryLimbs` arithmetic, for its part, reaches the planner through the [planner instances](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/Plan/Instances.lean). Their heads name `Family format (Model.WideLimb.Value format) (.limbs h)`, the family shape you get when the limb plan and `Code` reduce, and that's what lets typeclass search find them. Each one forwards to its `automatic*Capability` for `.limbs h`, passing through the family's `PolicyFor` instance and reusing the selected certificate and execution proofs. Alongside them, `limbCodec` supplies the model codec for the concrete carrier type, so literal construction and conversion work too.

</details>

<details>
<summary>Public equations and their axiom dependencies</summary>

[[FloatLib.Floats.ExecFloat.add]] and the other five operations use the capability. The specification module holds [[FloatLib.Floats.ExecFloat.Spec.add]] and its siblings, and the proof module states the six public equations, [[FloatLib.Floats.ExecFloat.Proof.add_eq_spec]] through [[FloatLib.Floats.ExecFloat.Proof.fma_eq_spec]], which [[FloatLib.Floats.ExecFloat.Proof.fullArithmeticCertificate]] collects. For binary32 `+`, the same public equation applies as it stands. Below, two `#print axioms` commands show the dependencies of that equation and of the real-number theorem:

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

That `example` type-checks because the `Add` instance on `Binary32` unfolds to [[FloatLib.Floats.ExecFloat.add]], the certified dispatch, so a theorem about `ExecFloat.add` is a theorem about `x + y`.

The public equation is the projection of a certificate the format built with its proof inside, which is why it needs no axioms at all. The real-number theorem quantifies over $\mathbb{R}$ and inherits the three axioms Mathlib's construction of the reals rests on: propositional extensionality, quotient soundness, and choice.

</details>

## Using the host FPU

Lean's `Float` and `Float32` expose host arithmetic, a faster path for ordinary binary32 and binary64 operations. To put it in the planner we'd need a `Backend.Certified` value proving `run = spec` as a Lean equality. That theorem would have to establish exact packed-word equality with the specification on every guarded finite input, overflow, underflow, and signed zeros included. It would also need the side conditions in Lean's logical model of multiplication and division, and it would have to assume the process uses round-to-nearest-even with gradual underflow. FloatLib doesn't supply such a host-refinement theorem, so these host results are only available through the unchecked interface.

To choose guarded host arithmetic, import its own module and name the operation at the call site. The import leaves ordinary `+` on the certified software path:

```
import FloatLib
import FloatLib.Floats.Formats.BinaryInterchange.Configured.NativeFPU.Unchecked

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange.Configured

def hostAdd32 (x y : Binary32) : Binary32 :=
  NativeFPU.Unchecked.add32 x y
```

The [native-floats chapter](#/chapter/lean-native-floats/opting-into-guarded-host-operations) works through the guards, NaN payload handling, and required process settings. The ten named functions cover addition, subtraction, multiplication, division, and square root at both host widths, and there's no unchecked FMA. You call them by name, and no `@[implemented_by]` substitution sits behind the certified binary operations.
