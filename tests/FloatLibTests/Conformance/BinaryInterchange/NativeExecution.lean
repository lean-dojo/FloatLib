/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Dispatch
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.NativeDispatch
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.NativeFPU.Unchecked
public import FloatLibTests.Accounting
public import FloatLibTests.Fixtures.NativeIEEE

/-!
# Binary32 and binary64 host checks

Public configured arithmetic now executes the proved fixed-word kernels in both logical and
compiled code. Guarded host `float` and `double` functions remain available through the explicit
`NativeFPU.Unchecked` opt-in; they are not installed through `@[implemented_by]`.

The corpus covers ordinary values, half-ULP ties, cancellation, subnormal inputs and outputs,
signed zero, overflow, infinities, and NaNs. Subnormal cases also detect flush-to-zero and
denormals-are-zero environments. Exceptional inputs must take the software branch to preserve
payload and invalid-result policies.

The dispatch half calls all six public `ExecFloat` operations for both widths, including FMA. The
host half separately calls the five operations exposed by `NativeFPU.Unchecked`; no unchecked FMA
exists.

These samples validate the explicit host/compiler/runtime/FPU boundary. They do not turn host
agreement into a proof.
-/

@[expose] public section

-- Keep lazy regression bodies out of module initialization, including closed subexpressions.
-- This affects native code generation only; elaboration and kernel checking are unchanged.
set_option compiler.extract_closed false

namespace FloatLibTests.Conformance.BinaryInterchange.NativeExecution

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange.Configured
open FloatLibTests.Accounting
open FloatLibTests.Fixtures.NativeIEEE

abbrev Binary32 := ExecFloat.Binary 8 23
abbrev Binary64 := ExecFloat.Binary 11 52

/-- Count disagreements between two binary operations over the shared named edge cases. -/
@[inline] def pairFailures {Word Value : Type}
    (cases : EdgeCases Word) (ofBits : Word → Value) (same : Value → Value → Bool)
    (native software : Value → Value → Value) : Nat :=
  countWhereFailures (arithmeticPairs cases) fun pair =>
    let left := ofBits pair.1
    let right := ofBits pair.2
    same (native left right) (software left right)

/-- Count disagreements between two unary operations over the shared square-root edge cases. -/
@[inline] def sqrtFailures {Word Value : Type}
    (cases : EdgeCases Word) (ofBits : Word → Value) (same : Value → Value → Bool)
    (native software : Value → Value) : Nat :=
  countWhereFailures (squareRootInputs cases) fun bits =>
    let value := ofBits bits
    same (native value) (software value)

/-- Ternary samples spanning ordinary arithmetic, cancellation, range boundaries, and NaNs. -/
def fmaInputs {Word : Type} (cases : EdgeCases Word) : List (Word × Word × Word) :=
  [ (cases.one, cases.two, cases.half)
  , (cases.one, cases.halfUlpAtOne, cases.negativeOne)
  , (cases.nextAboveOne, cases.negativeOne, cases.one)
  , (cases.negativeOne, cases.one, cases.one)
  , (cases.smallestSubnormal, cases.nextSubnormal, cases.negativeSmallestSubnormal)
  , (cases.negativeSmallestSubnormal, cases.smallestSubnormal, cases.smallestSubnormal)
  , (cases.smallestNormal, cases.half, cases.smallestSubnormal)
  , (cases.largestSubnormal, cases.smallestNormal, cases.negativeSmallestSubnormal)
  , (cases.largestFinite, cases.two, cases.negativeInfinity)
  , (cases.positiveZero, cases.negativeZero, cases.negativeZero)
  , (cases.positiveInfinity, cases.positiveZero, cases.one)
  , (cases.positiveInfinity, cases.one, cases.negativeInfinity)
  , (cases.quietNaN, cases.one, cases.two)
  , (cases.signalingNaN, cases.negativeInfinity, cases.quietNaN)
  ]

/-- Count disagreements between two fused operations over the shared ternary edge cases. -/
@[inline] def fmaFailures {Word Value : Type}
    (cases : EdgeCases Word) (ofBits : Word → Value) (same : Value → Value → Bool)
    (native software : Value → Value → Value → Value) : Nat :=
  countWhereFailures (fmaInputs cases) fun (leftBits, rightBits, addendBits) =>
    let left := ofBits leftBits
    let right := ofBits rightBits
    let addend := ofBits addendBits
    same (native left right addend) (software left right addend)

/-- Sampled disagreements between the unchecked binary32 host API and proved software. -/
def binary32UncheckedFailures : Thunk Nat := ⟨fun _ =>
  let ofBits : UInt32 → Binary32 := NativeFPU.ofBinary32Bits
  let same (left right : Binary32) : Bool := left.raw.1 == right.raw.1
  pairFailures binary32Cases ofBits same NativeFPU.Unchecked.add32 Backend.wordAdd +
  pairFailures binary32Cases ofBits same NativeFPU.Unchecked.sub32 Backend.wordSub +
  pairFailures binary32Cases ofBits same NativeFPU.Unchecked.mul32 Backend.wordMul +
  pairFailures binary32Cases ofBits same NativeFPU.Unchecked.div32 Backend.wordDiv +
  sqrtFailures binary32Cases ofBits same NativeFPU.Unchecked.sqrt32 Backend.wordSqrt⟩

/-- Sampled disagreements between public binary32 dispatch and the selected software kernels. -/
def binary32DispatchFailures : Thunk Nat := ⟨fun _ =>
  let ofBits : UInt32 → Binary32 := NativeFPU.ofBinary32Bits
  let same (left right : Binary32) : Bool := left.raw.1 == right.raw.1
  pairFailures binary32Cases ofBits same ExecFloat.add Backend.wordAdd +
  pairFailures binary32Cases ofBits same ExecFloat.sub Backend.wordSub +
  pairFailures binary32Cases ofBits same ExecFloat.mul Backend.wordMul +
  pairFailures binary32Cases ofBits same ExecFloat.div Backend.wordDiv +
  sqrtFailures binary32Cases ofBits same ExecFloat.sqrt Backend.wordSqrt +
  fmaFailures binary32Cases ofBits same ExecFloat.fma Backend.wordFma⟩

/-- Sampled disagreements between the unchecked binary64 host API and proved software. -/
def binary64UncheckedFailures : Thunk Nat := ⟨fun _ =>
  let ofBits : UInt64 → Binary64 := NativeFPU.ofBinary64Bits
  let same (left right : Binary64) : Bool := left.raw.1 == right.raw.1
  pairFailures binary64Cases ofBits same NativeFPU.Unchecked.add64 Backend.wordAdd +
  pairFailures binary64Cases ofBits same NativeFPU.Unchecked.sub64 Backend.wordSub +
  pairFailures binary64Cases ofBits same NativeFPU.Unchecked.mul64 Backend.wordMul +
  pairFailures binary64Cases ofBits same NativeFPU.Unchecked.div64 Backend.wordDiv +
  sqrtFailures binary64Cases ofBits same NativeFPU.Unchecked.sqrt64 Backend.wordSqrt⟩

/-- Bit equality of two stored binary64 words. -/
def sameBinary64 (left right : Binary64) : Bool := left.raw.1 == right.raw.1

/-!
The six binary64 dispatch comparisons are separate definitions on purpose. Each public operation
inlines its selected word kernel at the call site, so one definition containing all six exceeds
the compiler's per-definition budget; six small definitions compile in ordinary time.
-/

/-- Sampled disagreements between public binary64 addition and the selected software kernel. -/
def binary64AddFailures : Thunk Nat := ⟨fun _ =>
  let ofBits : UInt64 → Binary64 := NativeFPU.ofBinary64Bits
  pairFailures binary64Cases ofBits sameBinary64 ExecFloat.add Backend.wordAdd⟩

/-- Sampled disagreements between public binary64 subtraction and the selected kernel. -/
def binary64SubFailures : Thunk Nat := ⟨fun _ =>
  let ofBits : UInt64 → Binary64 := NativeFPU.ofBinary64Bits
  pairFailures binary64Cases ofBits sameBinary64 ExecFloat.sub Backend.wordSub⟩

/-- Sampled disagreements between public binary64 multiplication and the selected kernel. -/
def binary64MulFailures : Thunk Nat := ⟨fun _ =>
  let ofBits : UInt64 → Binary64 := NativeFPU.ofBinary64Bits
  pairFailures binary64Cases ofBits sameBinary64 ExecFloat.mul Backend.wordMul⟩

/-- Sampled disagreements between public binary64 division and the selected kernel. -/
def binary64DivFailures : Thunk Nat := ⟨fun _ =>
  let ofBits : UInt64 → Binary64 := NativeFPU.ofBinary64Bits
  pairFailures binary64Cases ofBits sameBinary64 ExecFloat.div Backend.wordDiv⟩

/-- Sampled disagreements between public binary64 square root and the selected kernel. -/
def binary64SqrtFailures : Thunk Nat := ⟨fun _ =>
  let ofBits : UInt64 → Binary64 := NativeFPU.ofBinary64Bits
  sqrtFailures binary64Cases ofBits sameBinary64 ExecFloat.sqrt Backend.wordSqrt⟩

/-- Sampled disagreements between public binary64 fused multiply-add and the selected kernel. -/
def binary64FmaFailures : Thunk Nat := ⟨fun _ =>
  let ofBits : UInt64 → Binary64 := NativeFPU.ofBinary64Bits
  fmaFailures binary64Cases ofBits sameBinary64 ExecFloat.fma Backend.wordFma⟩

/-- Sampled disagreements between public binary64 dispatch and the selected software kernels. -/
def binary64DispatchFailures : Thunk Nat := ⟨fun _ =>
  binary64AddFailures.get + binary64SubFailures.get + binary64MulFailures.get + binary64DivFailures.get +
    binary64SqrtFailures.get + binary64FmaFailures.get⟩

/-- Total sampled disagreements across configured paths and explicit host functions. -/
def totalFailures : Thunk Nat := ⟨fun _ =>
  binary32DispatchFailures.get + binary64DispatchFailures.get +
    binary32UncheckedFailures.get + binary64UncheckedFailures.get⟩

/--
Human-readable native-backend conformance result.

This report executes configured operations and the explicit host `Float32` and `Float` functions,
comparing their bits with the proved software kernels. A nonzero unchecked count means the
compiler/runtime, processor, or active floating-point environment disagrees with the software
kernel.
-/
def report : Thunk String := ⟨fun _ =>
  s!"dispatch32={binary32DispatchFailures.get},dispatch64={binary64DispatchFailures.get}," ++
    s!"unchecked32={binary32UncheckedFailures.get}," ++
    s!"unchecked64={binary64UncheckedFailures.get}," ++
    s!"TOTAL: {totalFailures.get}"⟩

end FloatLibTests.Conformance.BinaryInterchange.NativeExecution
