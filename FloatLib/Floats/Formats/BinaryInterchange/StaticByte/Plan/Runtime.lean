/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.Core.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Selection.Certified

/-!
# Static-byte planning runtime

Nominal binary formats of at most eight bits use cost estimates, table candidates, profile
selection, and dispatch specialized to static-byte storage.

Correctness theorems live in `Plan.Proof`, while capability construction lives in
`Plan.Construction`. This runtime layer can therefore be reused without importing either module.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.StaticByte

universe u

namespace Plans

/--
Cost estimate for evaluating the exact baseline directly.

This is the mandatory proved implementation in table-backed plans. The constants are calibration
inputs, not semantic facts; changing them can alter a plan without changing any refinement theorem.
-/
def exactEstimate (operation : FloatLib.Floats.ExecFloat.Backend.Operation) :
    FloatLib.Floats.ExecFloat.Backend.Candidate where
  name := s!"static-byte exact {operation.longLabel} baseline"
  kind := .generic
  steadyCost := 512
  allocations := 4

/--
Estimate a dense byte-result table from the format width and operation arity.

Table construction evaluates a certified kernel once per entry. `residentBytes` counts the
result bytes in the cached `ByteArray`; it excludes object and allocator overhead.
-/
def tableEstimate (format : FloatFormat) (name : String)
    (operation : FloatLib.Floats.ExecFloat.Backend.Operation) :
    FloatLib.Floats.ExecFloat.Backend.Candidate :=
  let entries := (2 ^ format.bitWidth) ^ operation.arity
  let generator := exactEstimate operation
  { name
    kind := .exhaustiveTable
    steadyCost := 4
    setupCost := entries * generator.steadyCost
    setupAllocations := 1 + entries * generator.allocations
    residentBytes := entries }

/-- Certify a binary kernel with the table cost estimate. -/
@[inline] def binaryTableCertified {F : Type u} [Family F]
    (name : String)
    (operation : FloatLib.Floats.ExecFloat.Backend.Operation)
    (spec run :
      FloatLib.Floats.ExecFloat F →
        FloatLib.Floats.ExecFloat F →
          FloatLib.Floats.ExecFloat F)
    (run_eq_spec : ∀ left right, run left right = spec left right) :
    FloatLib.Floats.ExecFloat.Backend.Certified spec :=
  FloatLib.Floats.ExecFloat.Backend.Certified.binary
    (tableEstimate (Family.format (F := F)) name operation) spec run run_eq_spec

/-- Certified binary table candidate paired with the executable exact baseline. -/
def binaryTable {F : Type u} [Family F]
    (name : String)
    (operation : FloatLib.Floats.ExecFloat.Backend.Operation)
    (spec run :
      FloatLib.Floats.ExecFloat F →
        FloatLib.Floats.ExecFloat F →
          FloatLib.Floats.ExecFloat F)
    (run_eq_spec : ∀ left right, run left right = spec left right) :
    FloatLib.Floats.ExecFloat.Backend.CandidateSet
      (FloatLib.Floats.ExecFloat.Backend.Certified spec) where
  alternatives := [
    binaryTableCertified name operation spec run run_eq_spec
  ]
  baseline := FloatLib.Floats.ExecFloat.Backend.Certified.binary
    (exactEstimate operation) spec spec (fun _ _ => rfl)

/-- Certify a unary kernel with the table cost estimate. -/
@[inline] def unaryTableCertified {F : Type u} [Family F]
    (name : String)
    (operation : FloatLib.Floats.ExecFloat.Backend.Operation)
    (spec run : FloatLib.Floats.ExecFloat F → FloatLib.Floats.ExecFloat F)
    (run_eq_spec : ∀ value, run value = spec value) :
    FloatLib.Floats.ExecFloat.Backend.Certified spec :=
  FloatLib.Floats.ExecFloat.Backend.Certified.unary
    (tableEstimate (Family.format (F := F)) name operation) spec run run_eq_spec

/-- Certified unary table candidate paired with the executable exact baseline. -/
def unaryTable {F : Type u} [Family F]
    (name : String)
    (operation : FloatLib.Floats.ExecFloat.Backend.Operation)
    (spec run : FloatLib.Floats.ExecFloat F → FloatLib.Floats.ExecFloat F)
    (run_eq_spec : ∀ value, run value = spec value) :
    FloatLib.Floats.ExecFloat.Backend.CandidateSet
      (FloatLib.Floats.ExecFloat.Backend.Certified spec) where
  alternatives := [
    unaryTableCertified name operation spec run run_eq_spec
  ]
  baseline := FloatLib.Floats.ExecFloat.Backend.Certified.unary
    (exactEstimate operation) spec spec (fun _ => rfl)

/-- Certify a ternary kernel with the table cost estimate. -/
@[inline] def ternaryTableCertified {F : Type u} [Family F]
    (name : String)
    (operation : FloatLib.Floats.ExecFloat.Backend.Operation)
    (spec run :
      FloatLib.Floats.ExecFloat F →
        FloatLib.Floats.ExecFloat F →
          FloatLib.Floats.ExecFloat F →
            FloatLib.Floats.ExecFloat F)
    (run_eq_spec : ∀ left right addend, run left right addend = spec left right addend) :
    FloatLib.Floats.ExecFloat.Backend.Certified spec :=
  FloatLib.Floats.ExecFloat.Backend.Certified.ternary
    (tableEstimate (Family.format (F := F)) name operation) spec run run_eq_spec

/--
Certified ternary table candidate paired with a first-order executable exact baseline.

Keeping the baseline as a named proved kernel matters for formats whose balanced policy rejects a
large FMA table: public execution can then specialize to that kernel without calling the generic
family specification through a boxed dictionary.
-/
def ternaryTable {F : Type u} [Family F]
    (name : String)
    (operation : FloatLib.Floats.ExecFloat.Backend.Operation)
    (spec tableRun exactRun :
      FloatLib.Floats.ExecFloat F →
        FloatLib.Floats.ExecFloat F →
          FloatLib.Floats.ExecFloat F →
            FloatLib.Floats.ExecFloat F)
    (tableRun_eq_spec :
      ∀ left right addend,
        tableRun left right addend = spec left right addend)
    (exactRun_eq_spec :
      ∀ left right addend,
        exactRun left right addend = spec left right addend) :
    FloatLib.Floats.ExecFloat.Backend.CandidateSet
      (FloatLib.Floats.ExecFloat.Backend.Certified spec) where
  alternatives := [
    ternaryTableCertified name operation spec tableRun tableRun_eq_spec
  ]
  baseline := FloatLib.Floats.ExecFloat.Backend.Certified.ternary
    (exactEstimate operation) spec exactRun exactRun_eq_spec

/--
Whether the shared planner selects the exhaustive table over the exact baseline.

Static-byte portfolios contain exactly one optional table candidate. Repeating the selector's
single comparison as a `Bool` lets a monomorphic operation branch between two named first-order
kernels without projecting an executable closure from `Certified`. The cost calculation remains
identical to `Backend.selectCertified`, so planning reports and execution use the same choice.
-/
@[inline] def tablePreferred (format : FloatFormat)
    (policy : FloatLib.Floats.ExecFloat.Backend.Policy)
    (name : String)
    (operation : FloatLib.Floats.ExecFloat.Backend.Operation) : Bool :=
  let table := tableEstimate format name operation
  let baseline := exactEstimate operation
  table.admissible policy && table.better policy baseline

/--
Certified table choices for the three built-in planning profiles.

Closed nominal formats provide these three bits once per operation. Their equality fields prove
that the literals are exactly the result of the shared cost model. The compiler can then reduce a
built-in profile to a direct kernel while a custom profile retains the general runtime comparison.
-/
structure BuiltinSelection (format : FloatFormat)
    (name : String)
    (operation : FloatLib.Floats.ExecFloat.Backend.Operation) where
  /-- Whether the latency profile selects the table. -/
  latency : Bool
  /-- Whether the balanced profile selects the table. -/
  balanced : Bool
  /-- Whether the throughput profile selects the table. -/
  throughput : Bool
  /-- The stored latency choice agrees with the cost model. -/
  latency_eq :
    latency = tablePreferred format
      FloatLib.Floats.ExecFloat.Backend.Policy.latency name operation
  /-- The stored balanced choice agrees with the cost model. -/
  balanced_eq :
    balanced = tablePreferred format
      FloatLib.Floats.ExecFloat.Backend.Policy.default name operation
  /-- The stored throughput choice agrees with the cost model. -/
  throughput_eq :
    throughput = tablePreferred format
      FloatLib.Floats.ExecFloat.Backend.Policy.throughput name operation

attribute [nolint simpNF] BuiltinSelection.mk.injEq

/-- The latency profile rejects a table accepted by balanced and throughput planning. -/
@[always_inline] def BuiltinSelection.balancedAndThroughput {format : FloatFormat}
    {name : String}
    {operation : FloatLib.Floats.ExecFloat.Backend.Operation}
    (latency_eq :
      false = tablePreferred format
        FloatLib.Floats.ExecFloat.Backend.Policy.latency name operation)
    (balanced_eq :
      true = tablePreferred format
        FloatLib.Floats.ExecFloat.Backend.Policy.default name operation)
    (throughput_eq :
      true = tablePreferred format
        FloatLib.Floats.ExecFloat.Backend.Policy.throughput name operation) :
    BuiltinSelection format name operation where
  latency := false
  balanced := true
  throughput := true
  latency_eq := latency_eq
  balanced_eq := balanced_eq
  throughput_eq := throughput_eq

/-- Among the built-in profiles, only throughput selects this table. -/
@[always_inline] def BuiltinSelection.throughputOnly {format : FloatFormat}
    {name : String}
    {operation : FloatLib.Floats.ExecFloat.Backend.Operation}
    (latency_eq :
      false = tablePreferred format
        FloatLib.Floats.ExecFloat.Backend.Policy.latency name operation)
    (balanced_eq :
      false = tablePreferred format
        FloatLib.Floats.ExecFloat.Backend.Policy.default name operation)
    (throughput_eq :
      true = tablePreferred format
        FloatLib.Floats.ExecFloat.Backend.Policy.throughput name operation) :
    BuiltinSelection format name operation where
  latency := false
  balanced := false
  throughput := true
  latency_eq := latency_eq
  balanced_eq := balanced_eq
  throughput_eq := throughput_eq

/--
Choose a table from a statically recognizable profile or evaluate an application-defined policy.
-/
@[always_inline] def BuiltinSelection.select {format : FloatFormat}
    {name : String}
    {operation : FloatLib.Floats.ExecFloat.Backend.Operation}
    (selection : BuiltinSelection format name operation) :
    FloatLib.Floats.ExecFloat.Backend.PolicyProfile → Bool
  | .latency => selection.latency
  | .balanced => selection.balanced
  | .throughput => selection.throughput
  | .custom policy => tablePreferred format policy name operation


/-- Execute the supplied binary table kernel or baseline according to the planning profile. -/
@[always_inline] def executeBinary {F : Type u} [Family F]
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor F]
    (name : String)
    (operation : FloatLib.Floats.ExecFloat.Backend.Operation)
    (selection : BuiltinSelection (Family.format (F := F)) name operation)
    (spec run :
      FloatLib.Floats.ExecFloat F →
        FloatLib.Floats.ExecFloat F →
          FloatLib.Floats.ExecFloat F)
    (left right : FloatLib.Floats.ExecFloat F) : FloatLib.Floats.ExecFloat F :=
  if selection.select
      (FloatLib.Floats.ExecFloat.Backend.PolicyFor.profile F (self := planning)) then
    run left right
  else
    spec left right

/-- Execute the supplied unary table kernel or baseline according to the planning profile. -/
@[always_inline] def executeUnary {F : Type u} [Family F]
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor F]
    (name : String)
    (operation : FloatLib.Floats.ExecFloat.Backend.Operation)
    (selection : BuiltinSelection (Family.format (F := F)) name operation)
    (spec run :
      FloatLib.Floats.ExecFloat F → FloatLib.Floats.ExecFloat F)
    (value : FloatLib.Floats.ExecFloat F) : FloatLib.Floats.ExecFloat F :=
  if selection.select
      (FloatLib.Floats.ExecFloat.Backend.PolicyFor.profile F (self := planning)) then
    run value
  else
    spec value

/-- Execute the supplied ternary table kernel or baseline according to the planning profile. -/
@[always_inline] def executeTernary {F : Type u} [Family F]
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor F]
    (name : String)
    (operation : FloatLib.Floats.ExecFloat.Backend.Operation)
    (selection : BuiltinSelection (Family.format (F := F)) name operation)
    (tableRun exactRun :
      FloatLib.Floats.ExecFloat F →
        FloatLib.Floats.ExecFloat F →
          FloatLib.Floats.ExecFloat F →
            FloatLib.Floats.ExecFloat F)
    (left right addend : FloatLib.Floats.ExecFloat F) :
    FloatLib.Floats.ExecFloat F :=
  if selection.select
      (FloatLib.Floats.ExecFloat.Backend.PolicyFor.profile F (self := planning)) then
    tableRun left right addend
  else
    exactRun left right addend

end Plans

end FloatLib.Floats.Formats.BinaryInterchange.StaticByte
