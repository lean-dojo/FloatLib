/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured
public import FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Backends
public import FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Plan.Instances
public import FloatLib.Floats.Formats.OCP.FP8.E4M3FN
public import FloatLib.Floats.Formats.OCP.MX.E2M1
public import FloatLib.Floats.ExecFloat.Backends.Selection.Report

/-!
# Automatic dispatch across format families

These kernel-checked regressions verify that the universal planner is not an IEEE-format switch.
Every configured binary family, regardless of width, carrier, exceptional-value encoding, or
custom exponent bias, receives the same six policy-dependent capability instances. Descriptor
and nominal OCP formats use the same `PolicyFor` mechanism, and custom carriers exercise it in
`Execution.Capabilities`.

The selector minimizes a workload-weighted cost among already-certified candidates. These tests
therefore check both halves of the contract:

* public execution is exactly the certificate selected by the planner for every configured
  carrier and descriptor; and
* closed representative formats reduce to different kernels when width, representation, or the
  expected workload changes.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Execution.AutomaticDispatch

open FloatLib.Floats
open FloatLib.Floats.ExecFloat.Backend
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.OCP.FP8
open FloatLib.Floats.Formats.OCP.MX
open FloatLib.Numerics

/-! ## Workload crossover and resource ceilings -/

/--
The cost model amortizes setup over the requested calls, but a cheap candidate cannot bypass
either memory ceiling. The report preserves the reason for each rejected candidate.
-/
example :
    let policy : Policy :=
      { expectedCalls := 10, allocationPenalty := 10, memoryBlockBytes := 64
        temporaryBlockPenalty := 1, residentBlockPenalty := 1
        maxTemporaryBytes := 128, maxResidentBytes := 64 }
    let direct : Candidate := { name := "direct", kind := .custom "direct" 0, steadyCost := 10 }
    let lazy : Candidate :=
      { name := "lazy", kind := .custom "lazy" 1, steadyCost := 1, setupCost := 1000 }
    let baseline : Candidate := { name := "baseline", kind := .generic, steadyCost := 100 }
    let candidates : CandidateSet Candidate := { alternatives := [lazy, direct], baseline }
    let warm := { policy with expectedCalls := 1000 }
    let resident := { direct with steadyCost := 0, residentBytes := 65 }
    let temporary := { direct with steadyCost := 0, temporaryBytes := 129 }
    let constrained : CandidateSet Candidate :=
      { alternatives := [resident, temporary, direct], baseline }
    selectCandidate policy candidates = direct ∧
      selectCandidate warm candidates = lazy ∧
      selectCandidate warm constrained = direct ∧
      (selectionReport warm constrained).assessments.map (·.status) =
        [ .rejectedResidentMemory 65 64, .rejectedTemporaryMemory 129 128
        , .selected, .notPreferred ] ∧
      policy.memoryBlocks 65 = 2 := by
  decide +kernel

/-! ## The planner is universal over configured carriers -/

section EveryConfiguredCarrier

variable (format : FloatFormat) (plan : Configured.StoragePlan format) (code : Type)
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]
    [planning : PolicyFor (Configured.Family format code plan)]

/-- Configured addition executes precisely the certificate selected from its complete portfolio. -/
example :
    ExecFloat.Add.selected (F := Configured.Family format code plan) =
      selectCertified planning.policy (Configured.Plan.addCandidates format plan) := by
  exact ExecFloat.Add.selected_eq_planner

/-- Configured subtraction executes precisely the selected certified implementation. -/
example :
    ExecFloat.Sub.selected (F := Configured.Family format code plan) =
      selectCertified planning.policy (Configured.Plan.subCandidates format plan) := by
  exact ExecFloat.Sub.selected_eq_planner

/-- Configured multiplication executes precisely the selected certified implementation. -/
example :
    ExecFloat.Mul.selected (F := Configured.Family format code plan) =
      selectCertified planning.policy (Configured.Plan.mulCandidates format plan) := by
  exact ExecFloat.Mul.selected_eq_planner

/-- Configured division executes precisely the selected certified implementation. -/
example :
    ExecFloat.Div.selected (F := Configured.Family format code plan) =
      selectCertified planning.policy (Configured.Plan.divCandidates format plan) := by
  exact ExecFloat.Div.selected_eq_planner

/-- Configured square root executes precisely the selected certified implementation. -/
example :
    ExecFloat.Sqrt.selected (F := Configured.Family format code plan) =
      selectCertified planning.policy (Configured.Plan.sqrtCandidates format plan) := by
  exact ExecFloat.Sqrt.selected_eq_planner

/-- Configured FMA executes precisely the selected certified implementation. -/
example :
    ExecFloat.Fma.selected (F := Configured.Family format code plan) =
      selectCertified planning.policy (Configured.Plan.fmaCandidates format plan) := by
  exact ExecFloat.Fma.selected_eq_planner

end EveryConfiguredCarrier

/-! ## The planner is universal over binary descriptors -/

section EveryBinaryDescriptor

variable (format : FloatFormat)
    [planning : PolicyFor (Descriptor format)]

/-- Arbitrary-format addition executes precisely the planner's selected certificate. -/
example :
    ExecFloat.Add.selected (F := Descriptor format) =
      selectCertified planning.policy (Descriptor.Plan.addCandidates format) := by
  exact ExecFloat.Add.selected_eq_planner

/-- Arbitrary-format subtraction executes precisely the planner's selected certificate. -/
example :
    ExecFloat.Sub.selected (F := Descriptor format) =
      selectCertified planning.policy (Descriptor.Plan.subCandidates format) := by
  exact ExecFloat.Sub.selected_eq_planner

/-- Arbitrary-format multiplication executes precisely the planner's selected certificate. -/
example :
    ExecFloat.Mul.selected (F := Descriptor format) =
      selectCertified planning.policy (Descriptor.Plan.mulCandidates format) := by
  exact ExecFloat.Mul.selected_eq_planner

/-- Arbitrary-format division executes precisely the planner's selected certificate. -/
example :
    ExecFloat.Div.selected (F := Descriptor format) =
      selectCertified planning.policy (Descriptor.Plan.divCandidates format) := by
  exact ExecFloat.Div.selected_eq_planner

/-- Arbitrary-format square root executes precisely the planner's selected certificate. -/
example :
    ExecFloat.Sqrt.selected (F := Descriptor format) =
      selectCertified planning.policy (Descriptor.Plan.sqrtCandidates format) := by
  exact ExecFloat.Sqrt.selected_eq_planner

/-- Arbitrary-format fused multiply-add executes precisely the planner's selected certificate. -/
example :
    ExecFloat.Fma.selected (F := Descriptor format) =
      selectCertified planning.policy (Descriptor.Plan.fmaCandidates format) := by
  exact ExecFloat.Fma.selected_eq_planner

end EveryBinaryDescriptor

/-! ## Closed structural selections -/

/-- Families below are definitionally the same families used by the public `ExecFloat.Binary` type. -/
private abbrev TinyBinary := ExecFloat.Binary.Family 2 1
private abbrev Binary7 := ExecFloat.Binary.Family 3 3
private abbrev Binary8 := ExecFloat.Binary.Family 4 3
private abbrev Binary32 := ExecFloat.Binary.Family 8 23
private abbrev Binary64 := ExecFloat.Binary.Family 11 52
private abbrev Binary128 := ExecFloat.Binary.Family 15 112
private abbrev Binary4096 := ExecFloat.Binary.Family 19 4095
private abbrev FiniteE4M3 :=
  ExecFloat.Binary.Family 4 3 (encoding := .finite)
private abbrev CustomBiasBinary16 :=
  ExecFloat.Binary.Family 5 10 (encoding := .finite) (bias := 11)

/-!
The descriptor planner exposes one truthful structural route, not one candidate per name attached
to the same dispatcher. Tiny formats may additionally expose one exhaustive table.
-/

example :
    [ Descriptor.Plan.structuralRoute? FloatFormat.binary32 .add
    , Descriptor.Plan.structuralRoute? FloatFormat.binary128 .mul
    , Descriptor.Plan.structuralRoute? (FloatFormat.ieee 19 4095) .fma
    ] =
      [ some .fixedFormat, some .fixedLimbs, none ] := by
  rfl

example :
    [ (Descriptor.Plan.addCandidates (FloatFormat.ieee 2 1)).alternatives.length
    , (Descriptor.Plan.addCandidates FloatFormat.binary32).alternatives.length
    , (Descriptor.Plan.mulCandidates FloatFormat.binary128).alternatives.length
    , (Descriptor.Plan.fmaCandidates
        (FloatFormat.ieee 19 4095)).alternatives.length
    ] = [2, 1, 1, 0] := by
  rfl

/-- A configured binary32 value is stored in a `UInt32` carrier chosen from its encoded width. -/
example :
    (ExecFloat.Add.selectedCandidate (F := Binary32)).storage = .word32 := by
  rfl

/-- Public configured binary32 uses certified fixed-format software for all six operations. -/
example :
    [ (ExecFloat.Add.selectedCandidate
        (F := Binary32)).kind
    , (ExecFloat.Sub.selectedCandidate
        (F := Binary32)).kind
    , (ExecFloat.Mul.selectedCandidate
        (F := Binary32)).kind
    , (ExecFloat.Div.selectedCandidate
        (F := Binary32)).kind
    , (ExecFloat.Sqrt.selectedCandidate
        (F := Binary32)).kind
    , (ExecFloat.Fma.selectedCandidate
        (F := Binary32)).kind
    ] =
      [ .fixedFormat, .fixedFormat, .fixedFormat
      , .fixedFormat, .fixedFormat, .fixedFormat
      ] := by
  rfl

/--
A 4,115-bit IEEE encoding with 4,096 significand bits remains supported and, on its default
proof-model carrier, selects the generic exact baselines: the wide-limb kernels require the
opt-in limb carrier of `ExecFloat.BinaryLimbs`, so no certified kernel is eligible here.
-/
example :
    [ (ExecFloat.Add.selectedCandidate
        (F := Binary4096)).kind
    , (ExecFloat.Sub.selectedCandidate
        (F := Binary4096)).kind
    , (ExecFloat.Mul.selectedCandidate
        (F := Binary4096)).kind
    , (ExecFloat.Div.selectedCandidate
        (F := Binary4096)).kind
    , (ExecFloat.Sqrt.selectedCandidate
        (F := Binary4096)).kind
    , (ExecFloat.Fma.selectedCandidate
        (F := Binary4096)).kind
    ] =
      [ .generic, .generic, .generic, .generic, .generic, .generic ] := by
  rfl

/--
The planner treats a custom finite encoding structurally. Its eight encoded bits support direct
tables even though the format is neither IEEE nor a catalog-owned nominal type.
-/
example :
    [ (ExecFloat.Add.selectedCandidate (F := FiniteE4M3)).kind
    , (ExecFloat.Sub.selectedCandidate (F := FiniteE4M3)).kind
    , (ExecFloat.Mul.selectedCandidate (F := FiniteE4M3)).kind
    , (ExecFloat.Div.selectedCandidate (F := FiniteE4M3)).kind
    , (ExecFloat.Sqrt.selectedCandidate (F := FiniteE4M3)).kind
    , (ExecFloat.Fma.selectedCandidate (F := FiniteE4M3)).kind
    ] =
      [ .exhaustiveTable, .exhaustiveTable, .exhaustiveTable
      , .exhaustiveTable, .exhaustiveTable, .generic
      ] := by
  rfl

/--
A nonstandard exponent bias changes semantics but not the planner architecture. The sixteen-bit
finite encoding selects the exact generic implementation because the current proved word kernels
require IEEE exceptional-value semantics. It remains automatically planned and needs no
format-specific registration.
-/
example :
    [ (ExecFloat.Add.selectedCandidate (F := CustomBiasBinary16)).kind
    , (ExecFloat.Mul.selectedCandidate (F := CustomBiasBinary16)).kind
    , (ExecFloat.Div.selectedCandidate (F := CustomBiasBinary16)).kind
    ] = [ .generic, .generic, .generic ] := by
  rfl

/-- Binary64 uses fixed-format software for all six operations. -/
example :
    [ (ExecFloat.Add.selectedCandidate (F := Binary64)).kind
    , (ExecFloat.Sub.selectedCandidate (F := Binary64)).kind
    , (ExecFloat.Mul.selectedCandidate (F := Binary64)).kind
    , (ExecFloat.Div.selectedCandidate (F := Binary64)).kind
    , (ExecFloat.Sqrt.selectedCandidate (F := Binary64)).kind
    , (ExecFloat.Fma.selectedCandidate (F := Binary64)).kind
    ] =
      [ .fixedFormat, .fixedFormat, .fixedFormat
      , .fixedFormat, .fixedFormat, .fixedFormat
      ] := by
  rfl

/-- Binary128 remains an ordinary fixed-limb input to the format-independent planner. -/
example :
    (ExecFloat.Add.selectedCandidate (F := Binary128)).kind = .fixedLimbs := by
  rfl

/--
Balanced OCP FP8 amortizes all admissible direct-byte tables and keeps FMA on the exact baseline.
-/
example :
    [ (ExecFloat.Add.selectedCandidate (F := E4M3FN)).kind
    , (ExecFloat.Sub.selectedCandidate (F := E4M3FN)).kind
    , (ExecFloat.Mul.selectedCandidate (F := E4M3FN)).kind
    , (ExecFloat.Div.selectedCandidate (F := E4M3FN)).kind
    , (ExecFloat.Sqrt.selectedCandidate (F := E4M3FN)).kind
    , (ExecFloat.Fma.selectedCandidate (F := E4M3FN)).kind
    ] =
      [ .exhaustiveTable, .exhaustiveTable, .exhaustiveTable
      , .exhaustiveTable, .exhaustiveTable, .generic
      ] := by
  rfl

/-!
The balanced priors below are intentionally tested at the measured crossover points, not merely
at convenient named formats. Three isolated 100,000-call calibration trials compare first-use
plus warmed execution for every certified candidate. These examples make a future cost-model
change explain which structural selection changed.
-/

/--
At three bits of significand precision, complete FMA lookup still wins over the exact baseline.
The extra table dimension stops paying for itself at four bits, and the five-bit format remains on
the baseline.
-/
example :
    [ (ExecFloat.Fma.selectedCandidate
        (F := Descriptor (FloatFormat.ieee 2 2))).kind
    , (ExecFloat.Fma.selectedCandidate
        (F := Descriptor (FloatFormat.ieee 2 3))).kind
    , (ExecFloat.Fma.selectedCandidate
        (F := Descriptor (FloatFormat.ieee 3 4))).kind
    ] = [ .exhaustiveTable, .generic, .generic ] := by
  rfl

/--
The calibrated eight-bit crossovers are operation-sensitive: OCP E5M2 FMA uses the exact
baseline, while ONNX E5M2FNUZ subtraction amortizes its complete binary table.
-/
example :
    [ (ExecFloat.Fma.selectedCandidate
        (F := Descriptor FloatFormat.e5m2)).kind
    , (ExecFloat.Sub.selectedCandidate
        (F := Descriptor FloatFormat.e5m2fnuz)).kind
    ] = [ .generic, .exhaustiveTable ] := by
  rfl

/-! ## The same format changes plan with the workload -/

namespace LatencyPlan

open scoped FloatLib.Floats.ExecFloat.Backend.PlanningLatency

/--
A first-call configured four-bit IEEE workload avoids table setup. Five operations use their
allocation-free native-word alternatives; FMA uses the lower-latency exact baseline.
-/
example :
    [ (ExecFloat.Add.selectedCandidate (F := TinyBinary)).kind
    , (ExecFloat.Sub.selectedCandidate (F := TinyBinary)).kind
    , (ExecFloat.Mul.selectedCandidate (F := TinyBinary)).kind
    , (ExecFloat.Div.selectedCandidate (F := TinyBinary)).kind
    , (ExecFloat.Sqrt.selectedCandidate (F := TinyBinary)).kind
    , (ExecFloat.Fma.selectedCandidate (F := TinyBinary)).kind
    ] =
      [ .nativeWord, .nativeWord, .nativeWord
      , .nativeWord, .nativeWord, .generic
      ] := by
  rfl

/-- A first-call OCP FP8 workload avoids paying for the lazy 65,536-entry addition table. -/
example :
    (ExecFloat.Add.selectedCandidate (F := E4M3FN)).kind = .generic := by
  rfl

/-- A first-call OCP MX workload avoids setup for all six four-bit operation tables. -/
example :
    [ (ExecFloat.Add.selectedCandidate (F := E2M1)).kind
    , (ExecFloat.Sub.selectedCandidate (F := E2M1)).kind
    , (ExecFloat.Mul.selectedCandidate (F := E2M1)).kind
    , (ExecFloat.Div.selectedCandidate (F := E2M1)).kind
    , (ExecFloat.Sqrt.selectedCandidate (F := E2M1)).kind
    , (ExecFloat.Fma.selectedCandidate (F := E2M1)).kind
    ] =
      [ .generic, .generic, .generic, .generic, .generic, .generic ] := by
  rfl

end LatencyPlan

namespace ThroughputPlan

open scoped FloatLib.Floats.ExecFloat.Backend.PlanningThroughput

/-- Sustained configured four-bit arithmetic amortizes every complete operation table. -/
example :
    [ (ExecFloat.Add.selectedCandidate (F := TinyBinary)).kind
    , (ExecFloat.Sub.selectedCandidate (F := TinyBinary)).kind
    , (ExecFloat.Mul.selectedCandidate (F := TinyBinary)).kind
    , (ExecFloat.Div.selectedCandidate (F := TinyBinary)).kind
    , (ExecFloat.Sqrt.selectedCandidate (F := TinyBinary)).kind
    , (ExecFloat.Fma.selectedCandidate (F := TinyBinary)).kind
    ] =
      [ .exhaustiveTable, .exhaustiveTable, .exhaustiveTable
      , .exhaustiveTable, .exhaustiveTable, .exhaustiveTable
      ] := by
  rfl

/-- Sustained OCP FP8 addition amortizes its direct-byte exhaustive table. -/
example :
    (ExecFloat.Add.selectedCandidate (F := E4M3FN)).kind = .exhaustiveTable := by
  rfl

/--
The sustained profile crosses the measured configured-binary FMA threshold at seven encoded
bits. The seven-bit table occupies two mebibytes and amortizes after roughly 3.5 million calls;
the sixteen-mebibyte eight-bit table remains too expensive to build at the five-million-call
horizon.
-/
example :
    [ (ExecFloat.Fma.selectedCandidate (F := Binary7)).kind
    , (ExecFloat.Fma.selectedCandidate (F := Binary8)).kind
    ] = [ .exhaustiveTable, .generic ] := by
  rfl

/-- Sustained OCP MX arithmetic amortizes every complete four-bit operation table. -/
example :
    [ (ExecFloat.Add.selectedCandidate (F := E2M1)).kind
    , (ExecFloat.Sub.selectedCandidate (F := E2M1)).kind
    , (ExecFloat.Mul.selectedCandidate (F := E2M1)).kind
    , (ExecFloat.Div.selectedCandidate (F := E2M1)).kind
    , (ExecFloat.Sqrt.selectedCandidate (F := E2M1)).kind
    , (ExecFloat.Fma.selectedCandidate (F := E2M1)).kind
    ] =
      [ .exhaustiveTable, .exhaustiveTable, .exhaustiveTable
      , .exhaustiveTable, .exhaustiveTable, .exhaustiveTable
      ] := by
  rfl

/--
An eight-bit descriptor also receives the throughput policy structurally; it is not required to
have a nominal standard-owned wrapper for the table planner to apply.
-/
example :
    (ExecFloat.Add.selectedCandidate
      (F := Descriptor FloatFormat.e4m3fn)).kind = .exhaustiveTable := by
  rfl

/--
The same throughput policy applies to a parameterized non-IEEE configured type. Binary and unary
tables are selected, while the sixteen-megabyte eight-bit FMA table remains too costly to
construct at the sustained profile's call horizon.
-/
example :
    [ (ExecFloat.Add.selectedCandidate (F := FiniteE4M3)).kind
    , (ExecFloat.Sqrt.selectedCandidate (F := FiniteE4M3)).kind
    , (ExecFloat.Fma.selectedCandidate (F := FiniteE4M3)).kind
    ] = [ .exhaustiveTable, .exhaustiveTable, .generic ] := by
  rfl

end ThroughputPlan

end FloatLibTests.Conformance.Execution.AutomaticDispatch
