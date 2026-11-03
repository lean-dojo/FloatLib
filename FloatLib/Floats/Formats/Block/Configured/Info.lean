/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Block.Configured.Proof
public meta import Lean.Elab.Command
public import FloatLib.Floats.Formats.Block.SharedScale.Info

/-!
# Inspection for configured shared-scale blocks

This optional meta module registers `#float_info` for `ExecFloat.SharedScale`. Runtime block
construction and quantization remain independently importable without editor elaborators.
-/

public meta section

namespace FloatLib.Floats.Formats.Block.Configured.FloatInfo.Command

open Lean Elab Command Meta
open FloatLib.Floats.ExecFloat

elab_rules : command
  | `(#float_info%$tk $type:term) =>
      FloatLib.Floats.ExecFloat.FloatInfo.Command.withExecFamilyApplication
          type ``FloatLib.Floats.Formats.Block.SharedScale 1
          fun typeExpr _family arguments => do
        let lanesExpr := arguments[0]!
        let lanes ← Inspection.readNat "shared-scale lane count" lanesExpr
        let coreProfile :=
          FloatLib.Floats.Formats.Block.FloatInfo.Command.profile lanes
        let configuredQuantization : TheoremSurface :=
          { topic := "contextual quantization"
            declarations :=
              [ ``FloatLib.Floats.ExecFloat.SharedScale.quantizesAt_quantizeAt
              , ``FloatLib.Floats.ExecFloat.SharedScale.decode_quantizeAt_get
              , ``FloatLib.Floats.ExecFloat.SharedScale.exponent_quantizeAt
              ]
            applicability := .verifiedForType
            scope := "all lanes at the caller-supplied exponent"
            numericalGuarantee? := some {
              kinds := [.rounding]
              statement :=
                "Each lane is nearest-even rounded to the grid selected by the explicit shared exponent." } }
        let configuredCode : TheoremSurface :=
          { topic := "decoding to the code"
            declarations :=
              [ ``FloatLib.Floats.ExecFloat.SharedScale.toCode_ofCode
              , ``FloatLib.Floats.ExecFloat.SharedScale.ofCode_toCode
              ]
            definitions :=
              [ ``FloatLib.Floats.ExecFloat.SharedScale.toCode
              , ``FloatLib.Floats.ExecFloat.SharedScale.ofCode ]
            applicability := .verifiedForType
            scope :=
              "every block; `toCode` and `ofCode` are inverse, so the theorems about the code " ++
              "below apply through `toCode`" }
        let baseProfile : FormatProfile :=
          { coreProfile with
            execution :=
              [ ⟨"carrier", "ExecFloat over one whole SharedScaleCode"⟩
              , ⟨"dispatch", "direct vector quantization kernel"⟩
              ]
            theoremSurfaces := [configuredQuantization, configuredCode]
            relatedTheorems :=
              [ { type := ``FloatLib.Floats.Formats.Block.SharedScaleCode
                  embedding := ``FloatLib.Floats.ExecFloat.SharedScale.toCode
                  surfaces := coreProfile.theoremSurfaces } ]
            nonclaims :=
              [ "a scale-selection policy is hidden in construction"
              , "the scalar six-operation interface applies to this vector-valued block"
              , "bounded MX lane encodings or accelerator instructions are implied" ] }
        logInfoAt tk <| ← Inspection.renderProfile baseProfile typeExpr .none

end FloatLib.Floats.Formats.Block.Configured.FloatInfo.Command
