/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.Selection.Report
public import FloatLib.Floats.Formats.BinaryInterchange.Configured
public import FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Backends
public import FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Plan.Instances
public import FloatLib.Floats.Formats.OCP.FP8.E4M3
public import FloatLib.Floats.Formats.OCP.MX.E2M1

/-!
# Automatic dispatch across format families

These kernel-checked regressions verify that the universal planner is not an IEEE-format switch.
Every configured binary family, regardless of width, carrier, exceptional-value encoding, or
custom exponent bias, receives the same six policy-dependent capability instances. Descriptor
and nominal OCP formats use the same `PolicyFor` mechanism, and custom carriers exercise it in
`Execution.Capabilities`.

The selector minimizes a workload-weighted cost among already-certified candidates. These tests
therefore check both halves of the contract:

* public execution is the certificate the planner selects, for every configured carrier and
  descriptor; and
* closed representative formats reduce to different kernels when width, representation, or the
  expected workload changes.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Execution.AutomaticDispatch

open FloatLib.Floats
open FloatLib.Floats.ExecFloat.Backend
open FloatLib.Floats.Formats.BinaryInterchange
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

/--
Configured addition runs the certificate that the planner selects from the capability's
candidates, whose baseline is the generic kernel of the family's own portfolio.
-/
example :
    ExecFloat.Add.selected (F := Configured.Family format code plan) =
        selectCertified planning.policy
          (ExecFloat.Add.candidates (F := Configured.Family format code plan)) ∧
      (ExecFloat.Add.candidates (F := Configured.Family format code plan)).baseline =
        (Configured.Plan.addCandidates format plan).baseline :=
  ⟨ExecFloat.Add.selected_eq_planner, rfl⟩

/--
Configured subtraction runs the certificate that the planner selects from the capability's
candidates, whose baseline is the generic kernel of the family's own portfolio.
-/
example :
    ExecFloat.Sub.selected (F := Configured.Family format code plan) =
        selectCertified planning.policy
          (ExecFloat.Sub.candidates (F := Configured.Family format code plan)) ∧
      (ExecFloat.Sub.candidates (F := Configured.Family format code plan)).baseline =
        (Configured.Plan.subCandidates format plan).baseline :=
  ⟨ExecFloat.Sub.selected_eq_planner, rfl⟩

/--
Configured multiplication runs the certificate that the planner selects from the capability's
candidates, whose baseline is the generic kernel of the family's own portfolio.
-/
example :
    ExecFloat.Mul.selected (F := Configured.Family format code plan) =
        selectCertified planning.policy
          (ExecFloat.Mul.candidates (F := Configured.Family format code plan)) ∧
      (ExecFloat.Mul.candidates (F := Configured.Family format code plan)).baseline =
        (Configured.Plan.mulCandidates format plan).baseline :=
  ⟨ExecFloat.Mul.selected_eq_planner, rfl⟩

/--
Configured division runs the certificate that the planner selects from the capability's
candidates, whose baseline is the generic kernel of the family's own portfolio.
-/
example :
    ExecFloat.Div.selected (F := Configured.Family format code plan) =
        selectCertified planning.policy
          (ExecFloat.Div.candidates (F := Configured.Family format code plan)) ∧
      (ExecFloat.Div.candidates (F := Configured.Family format code plan)).baseline =
        (Configured.Plan.divCandidates format plan).baseline :=
  ⟨ExecFloat.Div.selected_eq_planner, rfl⟩

/--
Configured square root runs the certificate that the planner selects from the capability's
candidates, whose baseline is the generic kernel of the family's own portfolio.
-/
example :
    ExecFloat.Sqrt.selected (F := Configured.Family format code plan) =
        selectCertified planning.policy
          (ExecFloat.Sqrt.candidates (F := Configured.Family format code plan)) ∧
      (ExecFloat.Sqrt.candidates (F := Configured.Family format code plan)).baseline =
        (Configured.Plan.sqrtCandidates format plan).baseline :=
  ⟨ExecFloat.Sqrt.selected_eq_planner, rfl⟩

/--
Configured FMA runs the certificate that the planner selects from the capability's
candidates, whose baseline is the generic kernel of the family's own portfolio.
-/
example :
    ExecFloat.Fma.selected (F := Configured.Family format code plan) =
        selectCertified planning.policy
          (ExecFloat.Fma.candidates (F := Configured.Family format code plan)) ∧
      (ExecFloat.Fma.candidates (F := Configured.Family format code plan)).baseline =
        (Configured.Plan.fmaCandidates format plan).baseline :=
  ⟨ExecFloat.Fma.selected_eq_planner, rfl⟩

end EveryConfiguredCarrier

/-! ## The planner is universal over binary descriptors -/

section EveryBinaryDescriptor

variable (format : FloatFormat)
    [planning : PolicyFor (Descriptor format)]

/--
Arbitrary-format addition runs the planner's selected certificate, chosen among the tagged
candidates and the generic baseline.
-/
example :
    ExecFloat.Add.selected (F := Descriptor format) =
        selectCertified planning.policy (ExecFloat.Add.candidates (F := Descriptor format)) ∧
      (ExecFloat.Add.candidates (F := Descriptor format)).baseline =
        Descriptor.Plan.addGeneric format :=
  ⟨ExecFloat.Add.selected_eq_planner, rfl⟩

/--
Arbitrary-format subtraction runs the planner's selected certificate, chosen among the tagged
candidates and the generic baseline.
-/
example :
    ExecFloat.Sub.selected (F := Descriptor format) =
        selectCertified planning.policy (ExecFloat.Sub.candidates (F := Descriptor format)) ∧
      (ExecFloat.Sub.candidates (F := Descriptor format)).baseline =
        Descriptor.Plan.subGeneric format :=
  ⟨ExecFloat.Sub.selected_eq_planner, rfl⟩

/--
Arbitrary-format multiplication runs the planner's selected certificate, chosen among the tagged
candidates and the generic baseline.
-/
example :
    ExecFloat.Mul.selected (F := Descriptor format) =
        selectCertified planning.policy (ExecFloat.Mul.candidates (F := Descriptor format)) ∧
      (ExecFloat.Mul.candidates (F := Descriptor format)).baseline =
        Descriptor.Plan.mulGeneric format :=
  ⟨ExecFloat.Mul.selected_eq_planner, rfl⟩

/--
Arbitrary-format division runs the planner's selected certificate, chosen among the tagged
candidates and the generic baseline.
-/
example :
    ExecFloat.Div.selected (F := Descriptor format) =
        selectCertified planning.policy (ExecFloat.Div.candidates (F := Descriptor format)) ∧
      (ExecFloat.Div.candidates (F := Descriptor format)).baseline =
        Descriptor.Plan.divGeneric format :=
  ⟨ExecFloat.Div.selected_eq_planner, rfl⟩

/--
Arbitrary-format square root runs the planner's selected certificate, chosen among the tagged
candidates and the generic baseline.
-/
example :
    ExecFloat.Sqrt.selected (F := Descriptor format) =
        selectCertified planning.policy (ExecFloat.Sqrt.candidates (F := Descriptor format)) ∧
      (ExecFloat.Sqrt.candidates (F := Descriptor format)).baseline =
        Descriptor.Plan.sqrtGeneric format :=
  ⟨ExecFloat.Sqrt.selected_eq_planner, rfl⟩

/--
Arbitrary-format FMA runs the planner's selected certificate, chosen among the tagged
candidates and the generic baseline.
-/
example :
    ExecFloat.Fma.selected (F := Descriptor format) =
        selectCertified planning.policy (ExecFloat.Fma.candidates (F := Descriptor format)) ∧
      (ExecFloat.Fma.candidates (F := Descriptor format)).baseline =
        Descriptor.Plan.fmaGeneric format :=
  ⟨ExecFloat.Fma.selected_eq_planner, rfl⟩

end EveryBinaryDescriptor

/-! ## Closed structural selections -/

/-- Families below are definitionally the same families used by the public `ExecFloat.Binary`
type. -/
private abbrev TinyBinary := ExecFloat.Binary.Family 2 1
private abbrev Binary7 := ExecFloat.Binary.Family 3 3
private abbrev Binary8 := ExecFloat.Binary.Family 4 3
private abbrev Binary32Family := ExecFloat.Binary.Family 8 23
private abbrev Binary64Family := ExecFloat.Binary.Family 11 52
private abbrev Binary128Family := ExecFloat.Binary.Family 15 112
private abbrev Binary4096 := ExecFloat.Binary.Family 19 4095
private abbrev FiniteE4M3 :=
  ExecFloat.Binary.Family 4 3 (encoding := .finite)
private abbrev CustomBiasBinary16 :=
  ExecFloat.Binary.Family 5 10 (encoding := .finite) (bias := 11)

/-!
The descriptor planner exposes a single structural route, so names attached to the same
dispatcher do not each add a candidate. Tiny formats may also expose one exhaustive table.
-/

example :
    [ Descriptor.Plan.structuralRoute? FloatFormat.binary32 .add
    , Descriptor.Plan.structuralRoute? FloatFormat.binary128 .mul
    , Descriptor.Plan.structuralRoute? (FloatFormat.ieee 19 4095) .fma
    ] =
      [ some .fixedFormat, some .fixedLimbs, none ] := by
  rfl

example :
    [ (ExecFloat.Add.candidates (F := Descriptor (FloatFormat.ieee 2 1))).alternatives.length
    , (ExecFloat.Add.candidates (F := Descriptor FloatFormat.binary32)).alternatives.length
    , (ExecFloat.Mul.candidates (F := Descriptor FloatFormat.binary128)).alternatives.length
    , (ExecFloat.Fma.candidates
        (F := Descriptor (FloatFormat.ieee 19 4095))).alternatives.length
    ] = [2, 1, 1, 0] := by
  decide +kernel

/-- A configured binary32 value is stored in a `UInt32` carrier chosen from its encoded width. -/
example :
    (ExecFloat.Add.selectedCandidate (F := Binary32Family)).storage = .word32 := by
  rfl

/--
A static-byte family reports its `UInt8` carrier for the table candidate and for the exact
baseline, which decodes to the proof model only while it computes.
-/
example :
    [ (ExecFloat.Add.selectedCandidate (F := E4M3.Family)).storage
    , (ExecFloat.Fma.selectedCandidate (F := E4M3.Family)).storage
    , (StaticByte.Plans.exactEstimate .add).storage
    , (StaticByte.Plans.tableEstimate FloatFormat.e4m3 "table" .add).storage
    ] = [.byte, .byte, .byte, .byte] := by
  rfl

/--
The direct binary64 multiplication, division, and fused multiply-add kernels read stored words
with the binary64 layout. They take a binary64 layout proof, so they cannot be applied to another
format in a `word64` carrier, such as binary32, where they computed `1 / 1 = 0` and
`1.5 * 1.5 = 1.25`.
-/
example (hw : FloatFormat.binary32.bitWidth ≤ 64)
    (x y : ExecFloat (Configured.Family FloatFormat.binary32
      (Configured.Code (.word64 hw)) (.word64 hw))) : x = x ∧ y = y := by
  fail_if_success have := Configured.Backend.binary64Div hw x y
  fail_if_success have := Configured.Backend.binary64Mul hw x y
  fail_if_success have := Configured.Backend.binary64Fma hw x y x
  fail_if_success have := Configured.Backend.binary64Div hw (by decide) x y
  exact ⟨rfl, rfl⟩

/-- On binary64 itself the direct kernels are the word operations they replace. -/
example (hw : FloatFormat.binary64.bitWidth ≤ 64)
    (x y : ExecFloat (Configured.Family FloatFormat.binary64
      (Configured.Code (.word64 hw)) (.word64 hw))) :
    Configured.Backend.binary64Div hw (by decide) x y = Configured.Backend.wordDiv x y :=
  Configured.Backend.binary64Div_eq hw (by decide) x y

/--
The direct binary64 addition and subtraction kernels use the conventional IEEE bias, and the
two-word kernels assume the `NativePair` layout and that bias. They take the matching proof, so
they cannot be applied to E4M3FNUZ (bias 8) in a `word64` carrier, or to the 70-bit unsigned-zero
format `finiteUnsignedZero 4 65` in a `pair` carrier, where both computed `1 + 1 = 4`.
-/
example (hw : FloatFormat.e4m3fnuz.bitWidth ≤ 64)
    (x y : ExecFloat (Configured.Family FloatFormat.e4m3fnuz
      (Configured.Code (.word64 hw)) (.word64 hw))) : x = x ∧ y = y := by
  fail_if_success have := Configured.Backend.binary64Add hw x y
  fail_if_success have := Configured.Backend.binary64Sub hw x y
  fail_if_success have := Configured.Backend.binary64Add hw (by decide) x y
  exact ⟨rfl, rfl⟩

example (hgt : 64 < (FloatFormat.finiteUnsignedZero 4 65).bitWidth)
    (hle : (FloatFormat.finiteUnsignedZero 4 65).bitWidth ≤ 128)
    (x y : ExecFloat (Configured.Family (FloatFormat.finiteUnsignedZero 4 65)
      (Configured.Code (.pair hgt hle)) (.pair hgt hle))) : x = x ∧ y = y := by
  fail_if_success have := Configured.Backend.pairAdd hgt hle x y
  fail_if_success have := Configured.Backend.pairSub hgt hle x y
  fail_if_success have := Configured.Backend.pairMul hgt hle x y
  fail_if_success have := Configured.Backend.pairDiv hgt hle x y
  fail_if_success have := Configured.Backend.pairSqrt hgt hle x
  fail_if_success have := Configured.Backend.pairFma hgt hle x y x
  fail_if_success have := Configured.Backend.pairAdd hgt hle (by decide) x y
  exact ⟨rfl, rfl⟩

/-- On binary64 and binary128 the direct addition kernels are word addition. -/
example (hw : FloatFormat.binary64.bitWidth ≤ 64)
    (x y : ExecFloat (Configured.Family FloatFormat.binary64
      (Configured.Code (.word64 hw)) (.word64 hw))) :
    Configured.Backend.binary64Add hw (by decide) x y = Configured.Backend.wordAdd x y :=
  Configured.Backend.binary64Add_eq hw (by decide) x y

example (hgt : 64 < FloatFormat.binary128.bitWidth) (hle : FloatFormat.binary128.bitWidth ≤ 128)
    (x y : ExecFloat (Configured.Family FloatFormat.binary128
      (Configured.Code (.pair hgt hle)) (.pair hgt hle))) :
    Configured.Backend.pairAdd hgt hle (by decide) x y = Configured.Backend.wordAdd x y :=
  Configured.Backend.pairAdd_eq hgt hle (by decide) x y

/-- Public configured binary32 uses certified fixed-format software for all six operations. -/
example :
    [ (ExecFloat.Add.selectedCandidate
        (F := Binary32Family)).kind
    , (ExecFloat.Sub.selectedCandidate
        (F := Binary32Family)).kind
    , (ExecFloat.Mul.selectedCandidate
        (F := Binary32Family)).kind
    , (ExecFloat.Div.selectedCandidate
        (F := Binary32Family)).kind
    , (ExecFloat.Sqrt.selectedCandidate
        (F := Binary32Family)).kind
    , (ExecFloat.Fma.selectedCandidate
        (F := Binary32Family)).kind
    ] =
      [ .fixedFormat, .fixedFormat, .fixedFormat
      , .fixedFormat, .fixedFormat, .fixedFormat
      ] := by
  rfl

/--
A 4,115-bit IEEE encoding with 4,096 significand bits is supported and, on its default
proof-model carrier, selects the generic exact baselines. The wide-limb kernels require the
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
finite encoding selects the exact generic implementation because the proved word kernels
require IEEE exceptional-value semantics. It is still planned automatically and needs no
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
    [ (ExecFloat.Add.selectedCandidate (F := Binary64Family)).kind
    , (ExecFloat.Sub.selectedCandidate (F := Binary64Family)).kind
    , (ExecFloat.Mul.selectedCandidate (F := Binary64Family)).kind
    , (ExecFloat.Div.selectedCandidate (F := Binary64Family)).kind
    , (ExecFloat.Sqrt.selectedCandidate (F := Binary64Family)).kind
    , (ExecFloat.Fma.selectedCandidate (F := Binary64Family)).kind
    ] =
      [ .fixedFormat, .fixedFormat, .fixedFormat
      , .fixedFormat, .fixedFormat, .fixedFormat
      ] := by
  rfl

/-- Binary128 is an ordinary fixed-limb input to the format-independent planner. -/
example :
    (ExecFloat.Add.selectedCandidate (F := Binary128Family)).kind = .fixedLimbs := by
  rfl

/--
Balanced OCP FP8 amortizes all admissible direct-byte tables and keeps FMA on the exact baseline.
-/
example :
    [ (ExecFloat.Add.selectedCandidate (F := E4M3.Family)).kind
    , (ExecFloat.Sub.selectedCandidate (F := E4M3.Family)).kind
    , (ExecFloat.Mul.selectedCandidate (F := E4M3.Family)).kind
    , (ExecFloat.Div.selectedCandidate (F := E4M3.Family)).kind
    , (ExecFloat.Sqrt.selectedCandidate (F := E4M3.Family)).kind
    , (ExecFloat.Fma.selectedCandidate (F := E4M3.Family)).kind
    ] =
      [ .exhaustiveTable, .exhaustiveTable, .exhaustiveTable
      , .exhaustiveTable, .exhaustiveTable, .generic
      ] := by
  rfl

/-!
The balanced priors below are deliberately tested at the measured crossover points as well as
at convenient named formats. Three isolated 100,000-call calibration trials compare first-use
plus warmed execution for every certified candidate. These examples make a future cost-model
change explain which structural selection changed.
-/

/--
At three bits of significand precision, complete FMA lookup still wins over the exact baseline.
The extra table dimension stops paying for itself at four bits, and the five-bit format stays on
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
allocation-free native-word alternatives, and FMA uses the lower-latency exact baseline.
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
    (ExecFloat.Add.selectedCandidate (F := E4M3.Family)).kind = .generic := by
  rfl

/-- A first-call OCP MX workload avoids setup for all six four-bit operation tables. -/
example :
    [ (ExecFloat.Add.selectedCandidate (F := E2M1.Family)).kind
    , (ExecFloat.Sub.selectedCandidate (F := E2M1.Family)).kind
    , (ExecFloat.Mul.selectedCandidate (F := E2M1.Family)).kind
    , (ExecFloat.Div.selectedCandidate (F := E2M1.Family)).kind
    , (ExecFloat.Sqrt.selectedCandidate (F := E2M1.Family)).kind
    , (ExecFloat.Fma.selectedCandidate (F := E2M1.Family)).kind
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
    (ExecFloat.Add.selectedCandidate (F := E4M3.Family)).kind = .exhaustiveTable := by
  rfl

/--
The sustained profile crosses the measured configured-binary FMA threshold at seven encoded
bits. The seven-bit table occupies two mebibytes and amortizes after roughly 3.5 million calls.
But the sixteen-mebibyte eight-bit table is still too expensive to build at the
five-million-call horizon.
-/
example :
    [ (ExecFloat.Fma.selectedCandidate (F := Binary7)).kind
    , (ExecFloat.Fma.selectedCandidate (F := Binary8)).kind
    ] = [ .exhaustiveTable, .generic ] := by
  rfl

/-- Sustained OCP MX arithmetic amortizes every complete four-bit operation table. -/
example :
    [ (ExecFloat.Add.selectedCandidate (F := E2M1.Family)).kind
    , (ExecFloat.Sub.selectedCandidate (F := E2M1.Family)).kind
    , (ExecFloat.Mul.selectedCandidate (F := E2M1.Family)).kind
    , (ExecFloat.Div.selectedCandidate (F := E2M1.Family)).kind
    , (ExecFloat.Sqrt.selectedCandidate (F := E2M1.Family)).kind
    , (ExecFloat.Fma.selectedCandidate (F := E2M1.Family)).kind
    ] =
      [ .exhaustiveTable, .exhaustiveTable, .exhaustiveTable
      , .exhaustiveTable, .exhaustiveTable, .exhaustiveTable
      ] := by
  rfl

/--
An eight-bit descriptor also receives the throughput policy structurally. It needs no nominal
standard-owned wrapper for the table planner to apply.
-/
example :
    (ExecFloat.Add.selectedCandidate
      (F := Descriptor FloatFormat.e4m3)).kind = .exhaustiveTable := by
  rfl

/--
The same throughput policy applies to a parameterized non-IEEE configured type. Binary and unary
tables are selected, while the sixteen-mebibyte eight-bit FMA table is still too costly to
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
