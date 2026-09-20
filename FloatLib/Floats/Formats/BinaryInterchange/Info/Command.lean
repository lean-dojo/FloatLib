/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Info.Profile
public meta import FloatLib.Floats.Formats.BinaryInterchange.Info.Profile
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Storage.Family.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Backends
public import FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Plan.Instances
public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte

/-!
# Binary-interchange inspection command

Resolve configured, descriptor, static-byte, and proof-model carriers for `#float_info`.
Their reports share the descriptor profile in `Info.Profile`, with storage and operation
availability taken from the elaborated type and its instances.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.FloatInfo.Command

open Lean Elab Command Meta

/--
Recover the descriptor from the lower-level `Model format` proof carrier.

The recursive abbreviation unfolding stops as soon as the exact model constructor is exposed,
so an expert-defined local alias remains inspectable without reducing the model to its fields.
-/
private meta def extractModelFormat? (type : Expr) : MetaM (Option Expr) := do
  let some model ←
      FloatLib.Floats.ExecFloat.unfoldUntilApp?
        ``FloatLib.Floats.Formats.BinaryInterchange.Model 1 type
    | return none
  return some model.getAppArgs[0]!

/-- Recover a descriptor-backed proof format, when the family is `Descriptor format`. -/
private meta def descriptorFormat? (family : Expr) : Option Expr :=
  if family.isAppOfArity ``Descriptor 1 then
    some family.getAppArgs[0]!
  else
    none

/-- Recover the descriptor and certified storage plan of a configured binary family. -/
private meta def configuredFormatPlan? (family : Expr) : Option (Expr × Expr) :=
  if family.isAppOfArity ``Configured.Family 3 then
    some (family.getAppArgs[0]!, family.getAppArgs[2]!)
  else
    none

/-- Recover the proof-model descriptor selected by a nominal static-byte family. -/
private meta def staticByteFormat? (family : Expr) : MetaM (Option Expr) := do
  let familyClass ← mkConstWithFreshMVarLevels ``StaticByte.Family
  let some familyInstance ← synthInstance? (mkApp familyClass family)
    | return none
  let formatProjection ← mkConstWithFreshMVarLevels ``StaticByte.Family.format
  return some (← withTransparency .all <| whnf (mkApp2 formatProjection family familyInstance))

/-- Runtime identity entries shared by the binary inspection profile. -/
private meta def executionIdentity
    (carrier dispatch : String) :
    List FloatLib.Floats.ExecFloat.InfoEntry :=
  [ ⟨"carrier", carrier⟩
  , ⟨"dispatch", dispatch⟩
  ]

/--
Certified operations exposed directly by the descriptor-indexed proof model.

They are listed as specialized operations because `Model format` intentionally does not install
the configured `ExecFloat` capability planner.
-/
private meta def modelOperations :
    List FloatLib.Floats.ExecFloat.InfoEntry :=
  [ ⟨"add",
      "`Model.add`; automatic tiny-table/native-word dispatch, with `Model.Proof.add_eq_spec`"⟩
  , ⟨"sub",
      "`Model.sub`; automatic tiny-table/native-word dispatch, with `Model.Proof.sub_eq_spec`"⟩
  , ⟨"mul",
      "`Model.mul`; automatic tiny-table/native-word dispatch, with `Model.Proof.mul_eq_spec`"⟩
  , ⟨"div",
      "`Model.div`; automatic tiny-table/native-word dispatch, with `Model.Proof.div_eq_spec`"⟩
  , ⟨"sqrt",
      "`Model.sqrt`; automatic tiny-table/word/generic dispatch, with `Model.Proof.sqrt_eq_spec`"⟩
  , ⟨"fma",
      "`Model.fma`; single-rounding automatic dispatch, with `Model.Proof.fma_eq_spec`"⟩
  , ⟨"directed arithmetic",
      "`*WithRounding`, `*Down`, and `*Up` expose explicit IEEE rounding directions"⟩
  , ⟨"status-bearing arithmetic",
      "`*WithStatus` returns the encoded result with invalid, divide-by-zero, overflow, underflow, and inexact flags"⟩
  ]

/-- Persistent storage specified by the configured family's selected plan. -/
private meta def configuredStorage (plan : Expr) (bitWidth : Nat) : MetaM String := do
  let plan ← withTransparency .all <| whnf plan
  let storage ←
    if plan.isAppOfArity ``Configured.StoragePlan.wide 1 then
      pure s!"BitVec {bitWidth} in Model"
    else do
      let storageClass ← mkAppM
        ``Configured.StoragePlan.storageClass #[plan]
      let storageDisplay ← mkAppM
        ``FloatLib.Floats.ExecFloat.Backend.StorageClass.display #[storageClass]
      FloatLib.Floats.ExecFloat.Inspection.readString
        "configured storage class" storageDisplay
  pure s!"{storage} specified by the configured storage plan"

/-- Read the standards identity supplied by a nominal static-byte family. -/
private meta def staticByteStandard (family : Expr) : MetaM String := do
  let infoClass ← mkConstWithFreshMVarLevels ``StaticByte.FamilyInfo
  let some info ← synthInstance? (mkApp infoClass family)
    | throwError
        "static-byte format is missing its `StaticByte.FamilyInfo` inspection instance"
  let standardProjection ←
    mkConstWithFreshMVarLevels ``StaticByte.FamilyInfo.standard
  FloatLib.Floats.ExecFloat.Inspection.readString
    "static-byte standards identity" (mkApp2 standardProjection family info)

open FloatLib.Floats.ExecFloat in
elab_rules : command
  | `(#float_info%$tk $type:term) =>
      FloatLib.Floats.ExecFloat.FloatInfo.Command.withElaboratedType
          type fun typeExpr => do
        match ← Inspection.execFamily? typeExpr with
        | some family => do
            let family ← withTransparency .reducible <| whnf family
            let (summary, standard, storage, execution) ←
              match configuredFormatPlan? family with
              | some (format, plan) => do
                  let summary ← FloatInfo.inspectSummary format
                  let storage ← configuredStorage plan summary.bitWidth
                  pure
                    ( summary
                    , FloatInfo.standardName summary
                    , storage
                    , executionIdentity
                        "packed persistent storage; the exact binary descriptor is retained as the proof model"
                        "representation-aware certified selection among direct tables, word, limb, and exact baseline kernels"
                    )
              | none =>
                  match descriptorFormat? family with
                  | some format => do
                      let summary ← FloatInfo.inspectSummary format
                      pure
                        ( summary
                        , FloatInfo.standardName summary
                        , s!"BitVec {summary.bitWidth}"
                        , executionIdentity
                            "the descriptor's exact-width encoded word; no host Float conversion"
                            "one-time proof-carrying selection among table, specialized, word, limb, and generic kernels"
                        )
                  | none =>
                      match ← staticByteFormat? family with
                      | some format => do
                          let summary ← FloatInfo.inspectSummary format
                          let standard ← staticByteStandard family
                          pure
                            ( summary
                            , standard
                            , "UInt8 with an erased valid-code-range proof"
                            , executionIdentity
                                "direct byte storage; the binary descriptor is used only as a proof model"
                                "proof-carrying automatic planner over byte tables and exact baseline kernels"
                            )
                      | none => throwUnsupportedSyntax
            let operations ← Inspection.coreOperations family
            let selectedBackends ← Inspection.selectedBackends family
            let profile := FloatInfo.profile summary standard storage execution
            let profile :=
              { profile with execution := profile.execution ++ selectedBackends }
            logInfoAt tk <| ← Inspection.renderProfile profile typeExpr operations
        | none => do
            let some format ← extractModelFormat? typeExpr
              | throwUnsupportedSyntax
            let summary ← FloatInfo.inspectSummary format
            let profile :=
              FloatInfo.profile summary (FloatInfo.standardName summary)
                s!"BitVec {summary.bitWidth} descriptor-indexed proof carrier"
                (executionIdentity
                  "the exact-width bit model; intended for specifications, conformance, and backend proofs"
                  "operation-local certified dispatch; no configured capability planner or packed persistent carrier")
            let profile :=
              { profile with
                rounding :=
                  [ ⟨"numeric literals",
                      "exact integer/rational input rounded once to nearest, ties to even"⟩
                  , ⟨"model arithmetic", "nearest, ties to even"⟩
                  , ⟨"directed APIs",
                      "explicit IEEE rounding modes and downward/upward convenience operations"⟩
                  , ⟨"status flags",
                      "invalid, divide-by-zero, overflow, underflow, and inexact are modeled explicitly"⟩
                  ]
                specializedOperations := modelOperations }
            logInfoAt tk <| ← Inspection.renderProfile profile typeExpr .none

end FloatLib.Floats.Formats.BinaryInterchange.FloatInfo.Command
