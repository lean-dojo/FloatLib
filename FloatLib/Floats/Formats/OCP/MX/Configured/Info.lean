/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.MX.Configured.Proof
public import FloatLib.Floats.Formats.OCP.MX.E8M0.Info

/-!
# Inspection reports for configured OCP MX values

This optional meta module registers `#float_info` for the common-carrier E8M0 scale and MX block
families. The executable wrappers remain independent of command elaboration and proof-report
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

/--
The report of a configured MX block: its construction and round-trip theorems, then the joint
block theorems about the raw code, which `toCode` reaches. The raw block report also lists the
scale's element-scaling theorems, which are about the raw E8M0 scale rather than about blocks; the
`#float_info` report of `ExecFloat.OCP.MX.E8M0` lists them.
-/
private meta def blockProfile (elementIdentity : String) : FormatProfile :=
  let raw := E8M0.FloatInfo.Command.blockProfile elementIdentity
  { raw with
    theoremSurfaces :=
      [ { topic := "construction and decoding to the raw block"
          declarations :=
            [ ``FloatLib.Floats.ExecFloat.OCP.MX.Block.toCode_ofCode
            , ``FloatLib.Floats.ExecFloat.OCP.MX.Block.ofCode_toCode
            , ``FloatLib.Floats.ExecFloat.OCP.MX.Block.scale_ofComponents
            , ``FloatLib.Floats.ExecFloat.OCP.MX.Block.values_ofComponents
            , ``FloatLib.Floats.ExecFloat.OCP.MX.Block.values_ofElements
            ]
          definitions :=
            [ ``FloatLib.Floats.ExecFloat.OCP.MX.Block.toCode
            , ``FloatLib.Floats.ExecFloat.OCP.MX.Block.ofCode ]
          applicability := .verifiedForType
          scope :=
            "every block; the components and element words are stored as given, and `toCode` " ++
            "and `ofCode` are inverse, so the theorems about the raw block below apply through " ++
            "`toCode`" } ]
    relatedTheorems :=
      [ { type := ``FloatLib.Floats.Formats.OCP.MX.BlockCode
          embedding := ``FloatLib.Floats.ExecFloat.OCP.MX.Block.toCode
          surfaces := [E8M0.FloatInfo.Command.blockRepresentation] } ] }

elab_rules : command
  | `(#float_info%$tk $type:term) =>
      FloatLib.Floats.ExecFloat.FloatInfo.Command.withElaboratedType
          type fun typeExpr => do
        let some family ← Inspection.execFamily? typeExpr
          | throwUnsupportedSyntax
        let result ←
          if family.isConstOf
              ``FloatLib.Floats.ExecFloat.OCP.MX.E8M0.Family then
            pure scaleProfile
          else if family.isAppOfArity
              ``FloatLib.Floats.ExecFloat.OCP.MX.Block.Family 1 then
            let format := family.getAppArgs[0]!
            let identity ← E8M0.FloatInfo.Command.blockElementIdentity format
            pure (blockProfile identity)
          else
            throwUnsupportedSyntax
        logInfoAt tk <| ← Inspection.renderProfile result typeExpr .none

end FloatLib.Floats.Formats.OCP.MX.Configured.FloatInfo.Command
