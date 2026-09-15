/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module


/-!
# Backend-selection metadata

Candidate metadata records the operation, storage shape, algorithm family, warm and cold costs,
allocations, and memory use. It is deliberately format-independent so binary, posit, and future
families can report plans through one interface.

Estimates do not establish numerical correctness or eligibility. The family supplies eligible
candidates with refinement proofs; selection and inspection use this metadata to compare their
estimated costs.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Backend

universe u v

/-- Universal operation whose implementation is being selected. -/
inductive Operation where
  | add
  | sub
  | mul
  | div
  | sqrt
  | fma
  deriving DecidableEq, Repr

namespace Operation

/-- Every universal operation, in stable user-facing display order. -/
def all : List Operation :=
  [.add, .sub, .mul, .div, .sqrt, .fma]

/-- Stable user-facing name of an operation. -/
def label : Operation → String
  | .add => "add"
  | .sub => "sub"
  | .mul => "mul"
  | .div => "div"
  | .sqrt => "sqrt"
  | .fma => "fma"

/-- Stable expanded name for prose and inspectable implementation names. -/
def longLabel : Operation → String
  | .add => "addition"
  | .sub => "subtraction"
  | .mul => "multiplication"
  | .div => "division"
  | .sqrt => "square root"
  | .fma => "fused multiply-add"

/-- Number of encoded operands consumed by an operation. -/
@[inline] def arity : Operation → Nat
  | .sqrt => 1
  | .add | .sub | .mul | .div => 2
  | .fma => 3

end Operation

/--
Persistent runtime-storage class.

This is descriptive metadata. The authoritative carrier remains `FormatCode F`, so custom
families may use storage not covered by these common classes and report `.custom`.
-/
inductive StorageClass where
  | byte
  | word16
  | word32
  | word64
  | fixedLimbs (count : Nat)
  | wideLimbs
  | custom
  deriving DecidableEq, Repr

namespace StorageClass

/-- Smallest common storage class that can contain `bits` encoded bits. -/
@[inline] def forBitWidth (bits : Nat) : StorageClass :=
  if bits ≤ 8 then
    .byte
  else if bits ≤ 16 then
    .word16
  else if bits ≤ 32 then
    .word32
  else if bits ≤ 64 then
    .word64
  else if bits ≤ 128 then
    .fixedLimbs 2
  else if bits ≤ 256 then
    .fixedLimbs 4
  else
    .wideLimbs

/-- Human-readable storage name used by inspection tools. -/
def display : StorageClass → String
  | .byte => "UInt8"
  | .word16 => "UInt16"
  | .word32 => "UInt32"
  | .word64 => "UInt64"
  | .fixedLimbs count => s!"{count} fixed UInt64 limbs"
  | .wideLimbs => "runtime-sized limb buffer"
  | .custom => "family-defined storage"

end StorageClass

/-- Algorithm family selected for one executable operation. -/
inductive KernelClass where
  /-- Exhaustive lookup table over encoded operands. -/
  | exhaustiveTable
  /-- Monomorphic kernel specialized to one exact format. -/
  | fixedFormat
  /-- Parameterized kernel operating within one machine word. -/
  | nativeWord
  /-- Kernel over a compile-time fixed number of machine-word limbs. -/
  | fixedLimbs
  /-- Kernel over a runtime-sized limb buffer. -/
  | wideLimbs
  /-- Width-generic exact executable baseline. -/
  | generic
  /--
  Family-defined algorithm class.

  The label is shown by inspection tools. `tieRank` is used only after equal total scores; custom
  ranks start at seven, above every built-in class.
  -/
  | custom (label : String) (tieRank : Nat)
  deriving DecidableEq, Repr

namespace KernelClass

/--
Stable tie-breaking rank.

The score decides normal comparisons. This rank only makes equal-score selection deterministic
and favors the more specialized representation.
-/
@[inline] def rank : KernelClass → Nat
  | .exhaustiveTable => 0
  | .fixedFormat => 2
  | .nativeWord => 3
  | .fixedLimbs => 4
  | .wideLimbs => 5
  | .generic => 6
  | .custom _ tieRank => 7 + tieRank

/-- User-facing name of a kernel class. -/
def display : KernelClass → String
  | .exhaustiveTable => "exhaustive encoded-value table"
  | .fixedFormat => "fixed-format word kernel"
  | .nativeWord => "machine-word kernel"
  | .fixedLimbs => "fixed-limb kernel"
  | .wideLimbs => "wide-limb kernel"
  | .generic => "exact baseline"
  | .custom label _ => label

end KernelClass

/--
Static engineering estimate for one certified candidate.

All work units are relative and family-calibrated. `steadyCost`, `marshallingCost`, `allocations`,
and `temporaryBytes` estimate one warm call. Marshalling covers carrier-to-working-representation
conversion and repacking of the result; keeping it separate prevents a fast arithmetic kernel
behind expensive `Nat` or proof-model conversion from appearing artificially cheap.

`setupCost` and `setupAllocations` estimate one-time initialization such as lazy table generation.
`residentBytes` and `temporaryBytes` also participate in hard memory limits.
-/
structure Candidate where
  /-- Stable family-defined name shown by inspection and benchmark tools. -/
  name : String
  /-- Algorithm family used for deterministic tie-breaking and user-facing reports. -/
  kind : KernelClass
  /-- Persistent carrier consumed by this kernel without changing the public value type. -/
  storage : StorageClass := .custom
  /-- Relative arithmetic work performed by one warm call, excluding representation conversion. -/
  steadyCost : Nat
  /-- Total per-call cost of decoding operands and repacking the result. -/
  marshallingCost : Nat := 0
  /-- Relative one-time work needed to initialize the candidate. -/
  setupCost : Nat := 0
  /-- Estimated number of heap allocations during one-time initialization. -/
  setupAllocations : Nat := 0
  /-- Estimated persistent bytes retained after initialization. -/
  residentBytes : Nat := 0
  /-- Estimated peak temporary workspace for one call, in bytes. -/
  temporaryBytes : Nat := 0
  /-- Estimated number of heap allocations during one warm call. -/
  allocations : Nat := 0
  deriving DecidableEq, Repr

/--
A nonempty collection represented by optional alternatives and a mandatory exact baseline.

The same container carries either inspectable cost estimates or proof-carrying implementations.
Keeping the element type abstract prevents the planner and executable dispatcher from growing
parallel record types whose only difference is their payload.
-/
structure CandidateSet (α : Type u) where
  /-- Optional implementations compared with the mandatory baseline. -/
  alternatives : List α := []
  /-- Mandatory payload used as the initial incumbent, making selection total. -/
  baseline : α
  deriving DecidableEq, Repr

namespace CandidateSet

/-- A candidate set containing only its mandatory baseline. -/
def singleton {α : Type u} (baseline : α) : CandidateSet α where
  baseline

/-- Transform every payload without changing candidate order or the distinguished baseline. -/
def map {α : Type u} {β : Type v}
    (f : α → β) (candidates : CandidateSet α) : CandidateSet β where
  alternatives := candidates.alternatives.map f
  baseline := f candidates.baseline

/-- Optional candidates in planner order, followed by the mandatory exact baseline. -/
def toList {α : Type u} (candidates : CandidateSet α) : List α :=
  candidates.alternatives ++ [candidates.baseline]

end CandidateSet

end FloatLib.Floats.ExecFloat.Backend
