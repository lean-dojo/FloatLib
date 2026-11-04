/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Selection.Metadata
public import FloatLib.Floats.Formats.Posit.Configured.Storage.Family.Proof

/-!
# Cost estimates for configured posit execution

Every number in this module is an engineering prior for the deterministic selector, and nothing
else reads them. They make no claim about performance and appear in no refinement theorem, so
benchmark calibration can change them without touching arithmetic semantics.

There is one estimate for each kind of implementation: the exact reference, the
representation-independent integer kernels, the direct packed-word and packed-pair kernels, and
the exhaustive byte tables. The module depends only on the configured semantic core. Certified
candidates are built in the sibling planner modules.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured.Plan

open FloatLib.Floats.ExecFloat
open FloatLib.Floats.ExecFloat.Backend

/-- Execution-planner storage metadata corresponding to a posit carrier plan. -/
@[inline] def storageClass {format : Format} : StoragePlan format → StorageClass
  | .byte _ => .byte
  | .word16 _ => .word16
  | .word32 _ => .word32
  | .word64 _ => .word64
  | .pair _ => .fixedLimbs 2
  | .wide => .wideLimbs

/--
Conservative estimate for the exact-rational reference implementation.

The width term models decoding and logarithmic code search. Allocation and temporary-memory
fields account for the reference implementation's use of `Nat` and `Rat`. They are estimates and
don't bound the actual allocations.
-/
def genericEstimate {format : Format}
    (plan : StoragePlan format) (operation : Operation) : Candidate where
  name := "posit exact-rational reference"
  kind := .generic
  storage := storageClass plan
  steadyCost := (operation.arity + 1) * (96 + 16 * format.bits)
  marshallingCost := (operation.arity + 1) * 32
  temporaryBytes := 32 * (format.bits + 1)
  allocations := operation.arity + 2

/--
Engineering estimate for the width-generic exact-integer kernels.

Each operation decodes once and then does exact arithmetic on signed integer significands and
binary exponents. Addition, subtraction, multiplication, and FMA pack the exact dyadic result.
Division rounds a destination-width quotient prefix from the exact remainder, and square root
takes the sticky bit of its integer-root prefix from the exact square remainder. These kernels
allocate and are width-generic, so they aren't native word kernels. The weights are planning
priors, never measurements.
-/
def dyadicEstimate {format : Format}
    (plan : StoragePlan format) (operation : Operation) : Candidate where
  name :=
    match operation with
    | .add => "posit direct exact-dyadic sum"
    | .sub => "posit direct exact-dyadic difference"
    | .mul => "posit direct exact-dyadic product"
    | .fma => "posit direct exact-dyadic fused accumulation"
    | .div => "posit width-generic quotient-prefix"
    | .sqrt => "posit width-generic integer-root prefix"
  kind := .custom "width-generic exact-integer kernel" 0
  storage := storageClass plan
  steadyCost :=
    match operation with
    | .add | .sub => 64 + 10 * format.bits
    | .mul => 56 + 8 * format.bits
    | .fma => 80 + 16 * format.bits
    | .div | .sqrt => 96 + 20 * format.bits
  marshallingCost := 24
  temporaryBytes :=
    (match operation with
      | .fma => 24
      | _ => 16) * (format.bits + 1)
  allocations :=
    match operation with
    | .fma => 3
    | _ => 2

/--
Engineering estimate for exact arithmetic with two-limb guard/sticky rounding.

This tier covers formats of at most 128 bits. Each operand becomes a mathematical posit model
once, and the retained result prefix stays in a pair of `UInt64` limbs while it is rounded.
Division and square root have no two-limb candidates, because `GeneralCandidates` already offers
their width-generic quotient-prefix and root-prefix kernels. The only callers, `nativeLimbAdd?`,
`nativeLimbSub?`, `nativeLimbMul?` and `nativeLimbFma?`, never ask for the `.div` and `.sqrt`
rows, which describe no kernel.
-/
def nativeLimbEstimate {format : Format}
    (plan : StoragePlan format) (operation : Operation) : Candidate where
  name :=
    match operation with
    | .add => "posit two-limb rounded exact sum"
    | .sub => "posit two-limb rounded exact difference"
    | .mul => "posit two-limb rounded exact product"
    | .fma => "posit two-limb rounded exact fused accumulation"
    | .div => "posit two-limb rounded exact quotient"
    | .sqrt => "posit two-limb rounded exact square root"
  kind := .custom "two-limb direct-candidate kernel" 0
  storage := storageClass plan
  steadyCost :=
    match operation with
    | .add | .sub => 44 + 3 * format.bits
    | .mul => 48 + 4 * format.bits
    | .fma => 68 + 6 * format.bits
    | .div | .sqrt => 88 + 10 * format.bits
  marshallingCost := 20
  temporaryBytes :=
    (match operation with
      | .fma => 18
      | _ => 14) * (format.bits + 1)
  allocations :=
    match operation with
    | .fma => 2
    | _ => 1

/--
Engineering estimate for the built-in packed-storage native-word kernel.

Operand words are zero-extended from `UInt8`, `UInt16`, `UInt32`, or `UInt64`, and no input
`BitVec` model is built. Rounding returns the complete encoding and packs it into the selected
built-in carrier. None of the six core operations builds an output `Model`, because proved
code-level boundaries handle the sign, zero, and NaR encodings of the result. Exact dyadic
intermediates may still allocate.
-/
def storedNativeWordEstimate {format : Format}
    (plan : StoragePlan format) (operation : Operation) : Candidate where
  name :=
    match operation with
    | .add => "posit direct packed-word exact sum"
    | .sub => "posit direct packed-word exact difference"
    | .mul => "posit direct packed-word exact product"
    | .fma => "posit direct packed-word exact fused accumulation"
    | .div => "posit direct packed-word exact quotient"
    | .sqrt => "posit direct packed-word exact square root"
  kind := .custom "direct packed-word kernel" 0
  storage := storageClass plan
  steadyCost :=
    match operation with
    | .add | .sub => 24 + 2 * format.bits
    | .mul => 28 + 3 * format.bits
    | .fma => 40 + 4 * format.bits
    | .div | .sqrt => 64 + 8 * format.bits
  marshallingCost := 4
  temporaryBytes :=
    (match operation with
      | .fma => 14
      | _ => 10) * (format.bits + 1)
  allocations :=
    match operation with
    | .fma => 2
    | _ => 1

/--
Engineering estimate for the direct built-in two-limb storage kernel.

Formats from 65 through 128 bits use two `UInt64` limbs by default, which these kernels decode
without building an input `Model`. Exact dyadic intermediates can allocate too, so the
estimate credits the lower carrier overhead without assuming allocation-free arithmetic. The
dispatcher prices addition, subtraction, multiplication, square root and FMA with it. Pair
division builds a result model before packing its code, so `dyadicEstimate` prices it and the
`.div` row goes unused.
-/
def storedNativeLimbEstimate {format : Format}
    (operation : Operation) : Candidate where
  name :=
    match operation with
    | .add => "posit direct packed-pair exact sum"
    | .sub => "posit direct packed-pair exact difference"
    | .mul => "posit direct packed-pair exact product"
    | .fma => "posit direct packed-pair exact fused accumulation"
    | .div => "posit direct packed-pair exact quotient"
    | .sqrt => "posit direct packed-pair exact square root"
  kind := .custom "direct packed-pair kernel" 0
  storage := .fixedLimbs 2
  steadyCost :=
    match operation with
    | .add | .sub => 32 + 3 * format.bits
    | .mul => 36 + 4 * format.bits
    | .fma => 54 + 6 * format.bits
    | .div | .sqrt => 76 + 10 * format.bits
  marshallingCost := 6
  temporaryBytes :=
    (match operation with
      | .fma => 16
      | _ => 12) * (format.bits + 1)
  allocations :=
    match operation with
    | .fma => 2
    | _ => 1

/-- Number of encoded entries in a dense table for one operation arity. -/
@[inline] def tableEntries (format : Format) (operation : Operation) : Nat :=
  format.modulus ^ operation.arity

/--
Conservative setup-cost prior for the certified generator used to populate a posit byte table.

The generator is the model-valued direct exact-dyadic kernel: it decodes each entry into the
shared exact-dyadic carrier and performs the complete exact operation before packing the result
byte. Charging the generator's estimated cost per entry accounts for table construction as
well as lookup when the planner compares expected workloads.
-/
@[inline] def tableGeneratorEstimate
    (format : Format) (width_le : format.bits ≤ 8) (operation : Operation) : Candidate :=
  match operation with
  | .add | .sub | .mul | .div | .sqrt | .fma =>
      dyadicEstimate (.byte width_le) operation

/--
Engineering estimate for an exhaustive byte-result table.

Setup is charged one call of the operation's rational-free certified integer generator per entry.
After construction, a lookup is native index arithmetic and a byte load. Ternary lookups get a
larger weight in every byte-sized format, for their extra index arithmetic. `residentBytes`
counts the table payload bytes exactly and leaves out array headers and other runtime
bookkeeping.
-/
def tableEstimate (format : Format) (width_le : format.bits ≤ 8)
    (operation : Operation) : Candidate :=
  let entries := tableEntries format operation
  let generator := tableGeneratorEstimate format width_le operation
  {
    name := "posit exhaustive encoded-value table"
    kind := .exhaustiveTable
    storage := .byte
    steadyCost :=
      if operation.arity = 3 then
        200
      else
        operation.arity + 2
    setupCost :=
      entries * (generator.steadyCost + generator.marshallingCost)
    setupAllocations := entries * generator.allocations
    residentBytes := entries
  }

end FloatLib.Floats.Formats.Posit.Configured.Plan
