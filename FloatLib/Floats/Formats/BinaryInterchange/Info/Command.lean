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
Their reports share the descriptor profile in `Info.Profile`, which chooses rounding entries and
theorem groups by carrier. Storage, the planning policy, and the installed operations come from
the elaborated type and its instances.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.FloatInfo.Command

open Lean Elab Command Meta

/--
Recover the descriptor from the lower-level `Model format` proof carrier.

Abbreviation unfolding stops as soon as the model constructor is exposed, so a local alias stays
inspectable without reducing the model to its fields.
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

/--
Operations of the descriptor-indexed proof model, which has no planning policy or capability
dictionary: each operation dispatches to its kernels itself.
-/
private meta def modelOperations :
    List FloatLib.Floats.ExecFloat.InfoEntry :=
  [ ⟨"add",
      "`Model.add`; tiny-table or machine-word dispatch, with `Model.Proof.add_eq_spec`"⟩
  , ⟨"sub",
      "`Model.sub`; tiny-table or machine-word dispatch, with `Model.Proof.sub_eq_spec`"⟩
  , ⟨"mul",
      "`Model.mul`; tiny-table or machine-word dispatch, with `Model.Proof.mul_eq_spec`"⟩
  , ⟨"div",
      "`Model.div`; tiny-table or machine-word dispatch, with `Model.Proof.div_eq_spec`"⟩
  , ⟨"sqrt",
      "`Model.sqrt`; tiny-table, word, or generic dispatch, with `Model.Proof.sqrt_eq_spec`"⟩
  , ⟨"fma",
      "`Model.fma`; single-rounding dispatch, with `Model.Proof.fma_eq_spec`"⟩
  ]

/-- The storage a configured family's plan selects. -/
private meta def configuredStorage (plan : Expr) (bitWidth : Nat) : MetaM String := do
  let head := (← withTransparency .all <| whnf plan).getAppFn
  if head.isConstOf ``Configured.StoragePlan.byte then return "UInt8"
  if head.isConstOf ``Configured.StoragePlan.word16 then return "UInt16"
  if head.isConstOf ``Configured.StoragePlan.word32 then return "UInt32"
  if head.isConstOf ``Configured.StoragePlan.word64 then return "UInt64"
  if head.isConstOf ``Configured.StoragePlan.pair then return "two UInt64 words"
  if head.isConstOf ``Configured.StoragePlan.wide then
    return s!"BitVec {bitWidth} (the proof model itself)"
  if head.isConstOf ``Configured.StoragePlan.limbs then return "an array of 32-bit limbs"
  throwError "failed to inspect the configured storage plan"

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
            let (summary, standard, storage, carrier) ←
              match configuredFormatPlan? family with
              | some (format, plan) => do
                  let summary ← FloatInfo.inspectSummary format
                  pure
                    ( summary, FloatInfo.standardName summary
                    , ← configuredStorage plan summary.bitWidth, FloatInfo.Carrier.configured )
              | none =>
                  match descriptorFormat? family with
                  | some format => do
                      let summary ← FloatInfo.inspectSummary format
                      pure
                        ( summary, FloatInfo.standardName summary
                        , FloatInfo.carrierStorage summary .descriptor
                        , FloatInfo.Carrier.descriptor )
                  | none =>
                      match ← staticByteFormat? family with
                      | some format => do
                          let summary ← FloatInfo.inspectSummary format
                          pure
                            ( summary, ← staticByteStandard family
                            , FloatInfo.carrierStorage summary .staticByte
                            , FloatInfo.Carrier.staticByte )
                      | none => throwUnsupportedSyntax
            let profile :=
              FloatInfo.profile summary standard storage carrier
                (← Inspection.installedOperations family)
            let profile :=
              { profile with
                execution := profile.execution ++ (← Inspection.selectedBackends family) }
            logInfoAt tk <|
              ← Inspection.renderProfile profile typeExpr (← Inspection.coreOperations family)
        | none => do
            let some format ← extractModelFormat? typeExpr
              | throwUnsupportedSyntax
            let summary ← FloatInfo.inspectSummary format
            let profile :=
              { FloatInfo.profile summary (FloatInfo.standardName summary)
                  (FloatInfo.carrierStorage summary .model) with
                specializedOperations := modelOperations }
            logInfoAt tk <| ← Inspection.renderProfile profile typeExpr .none

end FloatLib.Floats.Formats.BinaryInterchange.FloatInfo.Command
