/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.MX.Configured.Proof
public import FloatLib.Tactic.FloatInfo.OCP.MX.E8M0

/-!
# Inspection report for the configured E8M0 scale

Import this meta module to get `#float_info` for the E8M0 scale family on the common carrier. The
executable wrappers don't need it, so they never depend on command elaboration or proof-report
rendering.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.OCP.MX.Configured.FloatInfo.Command

open Lean Elab Command Meta
open FloatLib.Floats.ExecFloat

/--
The report of the configured E8M0 scale: its round-trip theorems, then the raw scale's theorems,
which `toCode` reaches.
-/
private meta def scaleProfile : FormatProfile :=
  let raw := E8M0.FloatInfo.Command.profile
  { raw with
    theoremSurfaces :=
      [ { topic := "decoding to the raw scale"
          declarations :=
            [ ``FloatLib.Floats.ExecFloat.OCP.MX.E8M0.toCode_ofCode
            , ``FloatLib.Floats.ExecFloat.OCP.MX.E8M0.ofCode_toCode
            , ``FloatLib.Floats.ExecFloat.OCP.MX.E8M0.ofNatBits_toNatBits
            , ``FloatLib.Floats.ExecFloat.OCP.MX.E8M0.toNatBits_ofNatBits_of_lt
            ]
          definitions :=
            [ ``FloatLib.Floats.ExecFloat.OCP.MX.E8M0.toCode
            , ``FloatLib.Floats.ExecFloat.OCP.MX.E8M0.ofCode ]
          applicability := .verifiedForType
          scope :=
            "every scale and every byte; `toCode` and `ofCode` are inverse, so the theorems " ++
            "about the raw scale below apply through `toCode`" } ]
    relatedTheorems :=
      [ { type := ``FloatLib.Floats.Formats.OCP.MX.E8M0
          embedding := ``FloatLib.Floats.ExecFloat.OCP.MX.E8M0.toCode
          surfaces := raw.theoremSurfaces } ] }

elab_rules : command
  | `(#float_info%$tk $type:term) =>
      FloatLib.Floats.ExecFloat.FloatInfo.Command.withElaboratedType
          type fun typeExpr => do
        let some family ← Inspection.execFamily? typeExpr
          | throwUnsupportedSyntax
        unless family.isConstOf ``FloatLib.Floats.ExecFloat.OCP.MX.E8M0.Family do
          throwUnsupportedSyntax
        logInfoAt tk <| ← Inspection.renderProfile scaleProfile typeExpr .none

end FloatLib.Floats.Formats.OCP.MX.Configured.FloatInfo.Command
