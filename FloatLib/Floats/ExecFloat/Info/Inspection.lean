/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Info.Profile
public meta import FloatLib.Floats.ExecFloat.Info.Profile
public meta import Lean.Meta.Eval
public import FloatLib.Floats.ExecFloat.Backends.Selection.Report
public import FloatLib.Floats.ExecFloat.Conversion.Core
public import FloatLib.Floats.ExecFloat.Core.Operations

/-!
# Inspecting proof-carrying capabilities and backend plans

Capability inspection reads the instances used by execution. It reports which universal
operations exist, the candidate selected by each capability, and the planner decisions behind
that selection. The selected candidate comes from the capability; diagnostic assessments rerun
the shared selector on that capability's candidate estimates and policy.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Inspection

open Lean
open Lean.Meta

/--
Synthesize a two-parameter capability whose second parameter is an output exact domain.

Both `ExactDecoder` and `Quantizer` use this shape. Returning the instantiated output parameter
lets the report show the actual mathematical domain selected by the execution instance instead
of repeating family-maintained prose.
-/
private meta def outputExactDomain?
    (className : Name) (valueType : Expr) : MetaM (Option Expr) := do
  let exactType ← mkFreshTypeMVar
  let capabilityClass ← mkConstWithFreshMVarLevels className
  let capabilityType := mkApp2 capabilityClass valueType exactType
  let some _ ← synthInstance? capabilityType
    | return none
  return some (← instantiateMVars exactType)

/-- Render a synthesized exact-domain type using the caller's normal pretty-printer options. -/
private meta def exactDomainDescription (exactType : Expr) : MetaM String :=
  return toString (← ppExpr exactType)

/-- Whether a destination quantizer has an installed default context. -/
private meta def hasDefaultQuantizer
    (destination exactType : Expr) : MetaM Bool := do
  let quantizerClass ←
    mkConstWithFreshMVarLevels ``FloatLib.Floats.ExecFloat.Quantizer
  let some quantizer ←
      synthInstance? (mkApp2 quantizerClass destination exactType)
    | return false
  let defaultClass ←
    mkConstWithFreshMVarLevels ``FloatLib.Floats.ExecFloat.DefaultQuantizer
  let capabilityType := mkApp3 defaultClass destination exactType quantizer
  return (← synthInstance? capabilityType).isSome

/-- Render the context type selected by a synthesized destination quantizer. -/
private meta def quantizerContextDescription
    (destination exactType : Expr) : MetaM String := do
  let quantizerClass ←
    mkConstWithFreshMVarLevels ``FloatLib.Floats.ExecFloat.Quantizer
  let some quantizer ←
      synthInstance? (mkApp2 quantizerClass destination exactType)
    | throwError "conversion inspection lost the synthesized destination quantizer"
  let contextProjection ←
    mkConstWithFreshMVarLevels ``FloatLib.Floats.ExecFloat.Quantizer.Context
  let contextType := mkApp3 contextProjection destination exactType quantizer
  let contextType ← withTransparency .all <| whnf contextType
  return toString (← ppExpr (← instantiateMVars contextType))

/--
Inspect the explicit conversion capabilities installed for one user-facing value type.

Source decoding, destination quantization, and a default context are inspected independently.
A source-only family can supply operands to casts or mixed arithmetic; a destination without
a default context requires an explicit context.
-/
meta def conversions (valueType : Expr) : MetaM (List InfoEntry) := do
  let sourceExact? ←
    outputExactDomain? ``FloatLib.Floats.ExecFloat.ExactDecoder valueType
  let destinationExact? ←
    outputExactDomain? ``FloatLib.Floats.ExecFloat.Quantizer valueType
  let sourceDescription ←
    match sourceExact? with
    | some exactType =>
        pure s!"installed; finite payload domain = {← exactDomainDescription exactType}"
    | none =>
        pure "not installed"
  let destinationDescription ←
    match destinationExact? with
    | some exactType => do
        let context ← quantizerContextDescription valueType exactType
        pure <|
          s!"installed and proof-backed; input domain = " ++
            s!"{← exactDomainDescription exactType}; context = {context}"
    | none =>
        pure <|
          if sourceExact?.isSome then
            "not installed; this type may still participate as an exact conversion source"
          else
            "not installed"
  let defaultDescription ←
    match destinationExact? with
    | some exactType =>
        if ← hasDefaultQuantizer valueType exactType then
          pure "installed; `cast` and destination-driven `*As` helpers may omit the context"
        else
          pure "none; callers must use `castWith` or `*AsWith` and supply the context"
    | none =>
        pure "not applicable because no destination quantizer is installed"
  let mixedDescription :=
    match sourceExact?, destinationExact? with
    | some _, some _ =>
        "available as source and destination: decode exactly, embed through `ExactMap`, operate in the destination exact domain, and round once"
    | none, some _ =>
        "available as an explicitly named result type when every operand supplies an exact decoder and an `ExactMap` preserving numerical value"
    | some _, none =>
        "available as an operand only when another explicitly named result type supplies the destination quantizer"
    | none, none =>
        "not installed for this carrier; use its family-specific operation and conversion policy"
  pure
    [ ⟨"source decoder", sourceDescription⟩
    , ⟨"destination quantizer", destinationDescription⟩
    , ⟨"default context", defaultDescription⟩
    , ⟨"mixed arithmetic", mixedDescription⟩
    , ⟨"implicit promotion",
        "none; ordinary same-type arithmetic stays in that type and cross-type results are named explicitly"⟩
    ]

/-- Attach synthesized conversion capabilities to a family-authored format profile. -/
meta def withConversions
    (profile : FormatProfile) (valueType : Expr) : MetaM FormatProfile := do
  if floatlib.floatInfo.errors.get (← getOptions) then
    return profile
  return { profile with conversions := ← conversions valueType }

/--
Recover the configured family encoded by an `ExecFloat` value type.

The check recognizes a `Subtype` predicate of the form `fun _ => ExecFloatTag family`.
It recovers the tag without checking that the underlying carrier is the code type of `family`.
-/
meta def execFamily? (valueType : Expr) : MetaM (Option Expr) := do
  let unfolded ← withTransparency .reducible <| whnf valueType
  unless unfolded.isAppOfArity ``Subtype 2 do
    return none
  let predicate := unfolded.getAppArgs[1]!
  unless predicate.isLambda do
    return none
  let tag := predicate.bindingBody!
  unless tag.isAppOfArity ``FloatLib.Floats.ExecFloatTag 1 do
    return none
  return some tag.getAppArgs[0]!

/--
Recover an `ExecFloat` family only when it is an application of the expected declaration and
arity. The returned argument array is safe to index below `arity`.
-/
meta def execFamilyApplication?
    (familyName : Name) (arity : Nat) (valueType : Expr) :
    MetaM (Option (Expr × Array Expr)) := do
  let some family ← execFamily? valueType
    | return none
  unless family.isAppOfArity familyName arity do
    return none
  return some (family, family.getAppArgs)

/-- Capability class corresponding to one universal operation. -/
private meta def capabilityClass : Backend.Operation → Name
  | .add => ``Add
  | .sub => ``Sub
  | .mul => ``Mul
  | .div => ``Div
  | .sqrt => ``Sqrt
  | .fma => ``Fma

/-- Candidate-set projection corresponding to one universal operation. -/
private meta def candidatesProjection : Backend.Operation → Name
  | .add => ``Add.candidates
  | .sub => ``Sub.candidates
  | .mul => ``Mul.candidates
  | .div => ``Div.candidates
  | .sqrt => ``Sqrt.candidates
  | .fma => ``Fma.candidates

/-- Selected-candidate projection corresponding to one universal operation. -/
private meta def selectedProjection : Backend.Operation → Name
  | .add => ``Add.selectedCandidate
  | .sub => ``Sub.selectedCandidate
  | .mul => ``Mul.selectedCandidate
  | .div => ``Div.selectedCandidate
  | .sqrt => ``Sqrt.selectedCandidate
  | .fma => ``Fma.selectedCandidate

/--
Synthesize the actual encoded-format, policy, and arithmetic capability dictionaries.

The result is proof-backed availability, not a declaration-name or storage-width heuristic.
-/
meta def hasCapability (className : Name) (family : Expr) : MetaM Bool := do
  let encodedFormatClass ←
    mkConstWithFreshMVarLevels ``FloatLib.Numerics.EncodedFormat
  let some encodedFormat ← synthInstance? (mkApp encodedFormatClass family)
    | return false
  let policyForClass ← mkConstWithFreshMVarLevels ``Backend.PolicyFor
  let some planning ← synthInstance? (mkApp policyForClass family)
    | return false
  let capabilityClass ← mkConstWithFreshMVarLevels className
  return (← synthInstance? (mkApp3 capabilityClass family encodedFormat planning)).isSome

/-- Inspect all six universal operation capabilities for one exact configured family. -/
meta def coreOperations (family : Expr) : MetaM CoreOperationCoverage := do
  if floatlib.floatInfo.errors.get (← getOptions) then
    return .none
  Backend.Operation.all.mapM fun operation => do
    pure (operation, ← hasCapability (capabilityClass operation) family)

/--
Reduce one projection from a closed expression.

Format-specific `#float_info` elaborators use this helper to inspect embedded descriptors without
duplicating projection construction or transparency policy.
-/
meta def reduceProjection (fieldName : Name) (object : Expr) : MetaM Expr := do
  let field ← mkConstWithFreshMVarLevels fieldName
  withTransparency .all <| whnf (mkApp field object)

/--
Read a closed two-constructor projection as a Boolean report field.

The caller supplies the constructors that mean `true` and `false`; inspection compares declaration
identities directly and never relies on printed names or constructor order.
-/
meta def readFlagProjection
    (description : String)
    (fieldName trueConstructor falseConstructor : Name)
    (object : Expr) : MetaM Bool := do
  let value ← reduceProjection fieldName object
  if value.isConstOf trueConstructor then
    return true
  if value.isConstOf falseConstructor then
    return false
  throwError "failed to inspect {description} field `{fieldName}`"

/--
Read a closed natural-number expression after reduction.

Family-specific `#float_info` elaborators use this helper for static widths, radix bases, and
scale parameters. Keeping the reduction and diagnostic policy here prevents each representation
family from maintaining a slightly different copy.
-/
meta def readNat (description : String) (value : Expr) : MetaM Nat := do
  let value ← withTransparency .all <| whnf value
  let some result ← getNatValue? value
    | throwError "failed to inspect {description}"
  pure result

/--
Read a natural-number-valued projection from a closed expression.

The description identifies the embedded descriptor or plan in diagnostics, while the projection
name identifies the exact field that failed to reduce.
-/
meta def readNatProjection
    (description : String) (fieldName : Name) (object : Expr) : MetaM Nat := do
  readNat s!"{description} field `{fieldName}`" (← reduceProjection fieldName object)

/-- Read one closed natural-number-valued candidate field. -/
private meta def readCandidateNat
    (fieldName : Name) (candidate : Expr) : MetaM Nat :=
  readNatProjection "selected-kernel" fieldName candidate

/-- Evaluate one closed string expression. -/
meta def readString (description : String) (value : Expr) : MetaM String := do
  let value ← withTransparency .all <| whnf value
  try
    unsafe evalExpr String (mkConst ``String) value
  catch _ =>
    throwError "failed to inspect {description}"

/-- Evaluate one closed string-valued candidate field. -/
private meta def readCandidateString
    (fieldName : Name) (candidate : Expr) : MetaM String := do
  readString s!"selected-kernel field `{fieldName}`"
    (← reduceProjection fieldName candidate)

/-- Render a reduced universal kernel class with the same label as `KernelClass.display`. -/
private meta def readCandidateKind (candidate : Expr) : MetaM String := do
  let value ← reduceProjection ``Backend.Candidate.kind candidate
  let builtin : List (Name × Backend.KernelClass) :=
    [(``Backend.KernelClass.exhaustiveTable, .exhaustiveTable),
      (``Backend.KernelClass.fixedFormat, .fixedFormat),
      (``Backend.KernelClass.nativeWord, .nativeWord),
      (``Backend.KernelClass.fixedLimbs, .fixedLimbs),
      (``Backend.KernelClass.wideLimbs, .wideLimbs),
      (``Backend.KernelClass.generic, .generic)]
  for (name, kind) in builtin do
    if value.isConstOf name then
      return kind.display
  if value.isAppOfArity ``Backend.KernelClass.custom 2 then
    let label := value.getAppArgs[0]!
    let some result := getStringValue? label
      | throwError "failed to inspect the selected custom kernel label"
    return result
  throwError "failed to inspect the selected universal kernel class"

/-- Read the persistent storage advertised by one closed candidate. -/
private meta def readCandidateStorage (candidate : Expr) : MetaM String := do
  let storage ← reduceProjection ``Backend.Candidate.storage candidate
  let display ← mkConstWithFreshMVarLevels ``Backend.StorageClass.display
  readString "selected-kernel storage class" (mkApp display storage)

/-- Render the concise identity of one reduced backend candidate. -/
private meta def selectedCandidateDescription (candidate : Expr) : MetaM String := do
  let kind ← readCandidateKind candidate
  let storage ← readCandidateStorage candidate
  pure s!"{kind} ({storage})"

/-- Render the complete engineering estimate of one candidate under a closed policy. -/
private meta def detailedCandidateDescription
    (policy candidate : Expr) : MetaM String := do
  let expectedCallsProjection ← mkConstWithFreshMVarLevels ``Backend.Policy.expectedCalls
  let profileName ← mkConstWithFreshMVarLevels ``Backend.Policy.profileName
  let warmCost ← mkConstWithFreshMVarLevels ``Backend.Candidate.warmCost
  let coldCost ← mkConstWithFreshMVarLevels ``Backend.Candidate.coldCost
  let score ← mkConstWithFreshMVarLevels ``Backend.Candidate.score
  let name ← readCandidateString ``Backend.Candidate.name candidate
  let kind ← readCandidateKind candidate
  let storage ← readCandidateStorage candidate
  let policyProfile ←
    readString "selection policy profile" (mkApp profileName policy)
  let steadyCost ← readCandidateNat ``Backend.Candidate.steadyCost candidate
  let marshallingCost ← readCandidateNat ``Backend.Candidate.marshallingCost candidate
  let warmCost ←
    readNat "selected-kernel warm cost" (mkApp2 warmCost policy candidate)
  let setupCost ← readCandidateNat ``Backend.Candidate.setupCost candidate
  let setupAllocations ← readCandidateNat ``Backend.Candidate.setupAllocations candidate
  let coldCost ←
    readNat "selected-kernel cold cost" (mkApp2 coldCost policy candidate)
  let residentBytes ← readCandidateNat ``Backend.Candidate.residentBytes candidate
  let temporaryBytes ← readCandidateNat ``Backend.Candidate.temporaryBytes candidate
  let allocations ← readCandidateNat ``Backend.Candidate.allocations candidate
  let expectedCalls ←
    readNat "selection policy's expected call count"
      (mkApp expectedCallsProjection policy)
  let score ←
    readNat "selected-kernel total score" (mkApp2 score policy candidate)
  let setup :=
    if setupCost = 0 then "" else s!"; raw setup {setupCost}"
  let setupAllocationText :=
    if setupAllocations = 0 then
      ""
    else
      s!"; {setupAllocations} setup allocation estimate"
  let memory :=
    if residentBytes = 0 then "" else s!"; resident {residentBytes} bytes"
  let allocationText :=
    if allocations = 0 then
      ""
    else
      s!"; {allocations} allocation estimate/call"
  let marshalling :=
    if marshallingCost = 0 then
      ""
    else
      s!"; carrier/model conversion {marshallingCost}"
  let temporary :=
    if temporaryBytes = 0 then
      ""
    else
      s!"; {temporaryBytes} temporary bytes/call"
  pure <|
    s!"{name} - {kind}; storage {storage} " ++
      s!"({policyProfile} policy; score {score} for " ++
      s!"{expectedCalls} expected calls = " ++
      s!"{expectedCalls} × warm {warmCost} + cold {coldCost}; " ++
      s!"raw operation {steadyCost}{marshalling}{allocationText}{temporary}" ++
      s!"{setup}{setupAllocationText}{memory})"

/--
Inspect the exact candidate selected by one synthesized proof-carrying capability.

The selected declaration is applied to the same dictionaries used by execution, so the report
cannot silently drift to a separate planning calculation.
-/
private meta def inspectSelectedCandidate
    (operation : Backend.Operation) (family : Expr) : MetaM (Option Expr) := do
  let encodedFormatClass ←
    mkConstWithFreshMVarLevels ``FloatLib.Numerics.EncodedFormat
  let some encodedFormat ← synthInstance? (mkApp encodedFormatClass family)
    | return none
  let policyForClass ← mkConstWithFreshMVarLevels ``Backend.PolicyFor
  let some planning ← synthInstance? (mkApp policyForClass family)
    | return none
  let capabilityType ← mkConstWithFreshMVarLevels (capabilityClass operation)
  let some capability ←
      synthInstance? (mkApp3 capabilityType family encodedFormat planning)
    | return none
  let selected ← mkConstWithFreshMVarLevels (selectedProjection operation)
  let candidate := mkAppN selected #[family, encodedFormat, planning, capability]
  return some candidate

/-- Reduce a closed Lean list to its elements. -/
private meta partial def readExprList (values : Expr) : MetaM (List Expr) := do
  let values ← withTransparency .all <| whnf values
  if values.isAppOfArity ``List.nil 1 then
    return []
  if values.isAppOfArity ``List.cons 3 then
    let arguments := values.getAppArgs
    return arguments[1]! :: (← readExprList arguments[2]!)
  throwError "failed to inspect a closed candidate list"

/--
Render the selector's decision recorded in one `Assessment.status`.

The report identifies the selected candidate by its position in the candidate list, so two
candidates with identical estimates are still reported as one selected and one not preferred.
-/
private meta def assessmentDescription (status : Expr) : MetaM String := do
  let status ← withTransparency .all <| whnf status
  if status.isAppOfArity ``Backend.AssessmentStatus.selected 0 then
    return "selected"
  if status.isAppOfArity ``Backend.AssessmentStatus.notPreferred 0 then
    return "not selected: higher workload-weighted cost or equal-score tie-break"
  if status.isAppOfArity ``Backend.AssessmentStatus.rejectedResidentMemory 2 then
    let arguments := status.getAppArgs
    let required ← readNat "rejected resident bytes" arguments[0]!
    let limit ← readNat "resident-byte limit" arguments[1]!
    return s!"rejected: {required} resident bytes exceeds {limit}"
  if status.isAppOfArity ``Backend.AssessmentStatus.rejectedTemporaryMemory 2 then
    let arguments := status.getAppArgs
    let required ← readNat "rejected temporary bytes" arguments[0]!
    let limit ← readNat "temporary-byte limit" arguments[1]!
    return s!"rejected: {required} temporary bytes exceeds {limit}"
  throwError "failed to inspect a selector assessment status"

/-- Inspect every candidate and resource decision for one synthesized capability. -/
private meta def inspectCandidatePlan
    (operation : Backend.Operation) (family : Expr) :
    MetaM (List (String × String)) := do
  let encodedFormatClass ←
    mkConstWithFreshMVarLevels ``FloatLib.Numerics.EncodedFormat
  let some encodedFormat ← synthInstance? (mkApp encodedFormatClass family)
    | return []
  let policyForClass ← mkConstWithFreshMVarLevels ``Backend.PolicyFor
  let some planning ← synthInstance? (mkApp policyForClass family)
    | return []
  let capabilityType ← mkConstWithFreshMVarLevels (capabilityClass operation)
  let some capability ←
      synthInstance? (mkApp3 capabilityType family encodedFormat planning)
    | return []
  let policy ← mkAppM ``Backend.PolicyFor.policy #[planning]
  let candidatesProjection ←
    mkConstWithFreshMVarLevels (candidatesProjection operation)
  let certifiedCandidates :=
    mkAppN candidatesProjection #[family, encodedFormat, planning, capability]
  let candidates ← mkAppM ``Backend.CandidateSet.estimates #[certifiedCandidates]
  let report ← mkAppM ``Backend.selectionReport #[policy, candidates]
  let assessments ← mkAppM ``Backend.SelectionReport.assessments #[report]
  let assessments ← readExprList assessments
  assessments.mapM fun assessment => do
    let candidate ← mkAppM ``Backend.Assessment.candidate #[assessment]
    let status ← assessmentDescription (← mkAppM ``Backend.Assessment.status #[assessment])
    pure (status, ← detailedCandidateDescription policy candidate)

/-- Compact multi-line rendering of every candidate considered for one operation. -/
private meta def candidatePlanDescription
    (candidates : List (String × String)) : String :=
  String.intercalate "\n    " <|
    candidates.map fun (status, description) => s!"{status}: {description}"

/--
Inspect selected backends and all alternatives for every synthesized universal capability.

Families append these entries to their own representation- and semantics-specific execution
profile. This keeps selection reporting uniform without imposing a common numerical model.
-/
meta def selectedBackends (family : Expr) : MetaM (List InfoEntry) := do
  if floatlib.floatInfo.errors.get (← getOptions) then
    return []
  let mut entries := []
  for operation in Backend.Operation.all do
    if let some candidate ← inspectSelectedCandidate operation family then
      let label := operation.label
      let description ← selectedCandidateDescription candidate
      entries := entries ++
        [⟨s!"selected {label}", description⟩]
      let plan ← inspectCandidatePlan operation family
      entries := entries ++
        [⟨s!"{label} decision", candidatePlanDescription plan⟩]
  pure entries

end FloatLib.Floats.ExecFloat.Inspection
