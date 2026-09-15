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

This optional meta module registers `#float_info` for `ExecFloat.Codebook`. Generic execution and
storage remain independently importable without editor tooling or proof-only dependencies.
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
        let configuredDenotation : TheoremSurface :=
          { topic := "configured complete denotation"
            declarations := []
            definitions := [``FloatLib.Floats.ExecFloat.Codebook.decode]
            applicability := .verifiedForType
            scope :=
              "every stored word; the configured carrier decodes through the selected table" }
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
            theoremSurfaces := configuredDenotation :: base.theoremSurfaces }
        logInfoAt tk <| ← Inspection.renderExecProfile baseProfile typeExpr family

end FloatLib.Floats.Formats.Codebook.Configured.FloatInfo.Command
