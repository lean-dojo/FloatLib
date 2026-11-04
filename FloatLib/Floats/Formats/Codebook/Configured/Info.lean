/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Codebook.Configured.Catalog
public import FloatLib.Floats.Formats.Codebook.Configured.Proof
public meta import Lean.Elab.Command
public import FloatLib.Floats.Formats.Codebook.Info

/-!
# Inspection for configured codebooks

This meta module adds `#float_info` for `ExecFloat.Codebook`, and it's optional. Generic execution
and storage import on their own, with no editor tooling and no proof-only dependencies.
-/

public meta section

namespace FloatLib.Floats.Formats.Codebook.Configured.FloatInfo.Command

open Lean Elab Command Meta
open FloatLib.Floats.ExecFloat

elab_rules : command
  | `(#float_info%$tk $type:term) =>
      FloatLib.Floats.ExecFloat.FloatInfo.Command.withExecFamilyApplication
          type ``FloatLib.Floats.ExecFloat.Codebook.Family 3
          fun typeExpr family arguments => do
        let widthExpr := arguments[0]!
        let book := arguments[2]!
        let width ← Inspection.readNat "codebook width" widthExpr
        let selected :=
          FloatLib.Floats.Formats.Codebook.FloatInfo.catalogIdentity book
        let base :=
          FloatLib.Floats.Formats.Codebook.FloatInfo.profile width selected
        let configuredCode : TheoremSurface :=
          { topic := "decoding to the code"
            declarations :=
              [ ``FloatLib.Floats.ExecFloat.Codebook.toCode_ofCode
              , ``FloatLib.Floats.ExecFloat.Codebook.ofCode_toCode
              , ``FloatLib.Floats.ExecFloat.Codebook.toNatBits_ofNatBits
              ]
            definitions :=
              [ ``FloatLib.Floats.ExecFloat.Codebook.toCode
              , ``FloatLib.Floats.ExecFloat.Codebook.ofCode
              , ``FloatLib.Floats.ExecFloat.Codebook.decode ]
            applicability := .verifiedForType
            scope :=
              "every stored word; the configured carrier decodes through the selected table, " ++
              "and `toCode` and `ofCode` are inverse, so the theorems about the code below " ++
              "apply through `toCode`" }
        let baseProfile : FormatProfile :=
          { base with
            execution :=
              [ ⟨"carrier", s!"ExecFloat over BitVec {width}"⟩
              , ⟨"dispatch", "only family-specific proved kernels are installed"⟩
              , ⟨"backend proof",
                  "a capability is reported only when its kernel carries a checked refinement"⟩
              ]
            specializedOperations :=
              FloatLib.Floats.Formats.Codebook.FloatInfo.configuredSpecializedOperations selected
            theoremSurfaces :=
              refinementEquations (← Inspection.installedOperations family) ++ [configuredCode]
            relatedTheorems :=
              [ { type := ``FloatLib.Floats.Formats.Codebook.Code
                  embedding := ``FloatLib.Floats.ExecFloat.Codebook.toCode
                  surfaces := base.theoremSurfaces } ] }
        logInfoAt tk <| ← Inspection.renderExecProfile baseProfile typeExpr family

end FloatLib.Floats.Formats.Codebook.Configured.FloatInfo.Command
