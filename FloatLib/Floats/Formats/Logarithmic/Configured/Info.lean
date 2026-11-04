/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Proof.Arithmetic
public meta import Lean.Elab.Command
public import FloatLib.Floats.Formats.Logarithmic.Configured.Proof
public import FloatLib.Floats.Formats.Logarithmic.Exact.Info

/-!
# Inspection for configured logarithmic numbers

`#float_info` for `ExecFloat.Logarithmic` is registered here, in an optional meta module. You can
import the configured format without it.
-/

public meta section

namespace FloatLib.Floats.Formats.Logarithmic.Configured.FloatInfo.Command

open Lean Elab Command Meta
open FloatLib.Numerics
open FloatLib.Floats.ExecFloat

elab_rules : command
  | `(#float_info%$tk $type:term) =>
      FloatLib.Floats.ExecFloat.FloatInfo.Command.withExecFamilyApplication
          type ``FloatLib.Floats.ExecFloat.Logarithmic.Family 1
          fun typeExpr family arguments => do
        let radix := arguments[0]!
        let base ←
          Inspection.readNatProjection "logarithmic radix" ``Radix.base radix
        let coreProfile :=
          FloatLib.Floats.Formats.Logarithmic.FloatInfo.Command.profile base
        let ownSurfaces : List TheoremSurface :=
          refinementEquations (← Inspection.installedOperations family) ++
          [ { topic := "exact multiplication"
              declarations :=
                [ ``FloatLib.Floats.ExecFloat.Logarithmic.toReal_mul
                , ``FloatLib.Floats.ExecFloat.Logarithmic.toReal_zero
                , ``FloatLib.Floats.ExecFloat.Logarithmic.toRat_mul
                , ``FloatLib.Floats.ExecFloat.Logarithmic.toRat_zero
                , ``FloatLib.Floats.ExecFloat.Logarithmic.cast_toRat
                ]
              definitions := [``FloatLib.Floats.ExecFloat.Logarithmic.toRat]
              applicability := .verifiedForType
              scope := "all values; `toRat` reads a value exactly, and its cast to ℝ is `toReal`"
              numericalGuarantee? := some {
                kinds := [.exactness]
                statement :=
                  "Multiplication has zero real error because signs and unbounded exponents combine exactly." } }
          , { topic := "decoding to the code"
              declarations :=
                [ ``FloatLib.Floats.ExecFloat.Logarithmic.toCode_ofCode
                , ``FloatLib.Floats.ExecFloat.Logarithmic.ofCode_toCode
                ]
              definitions :=
                [ ``FloatLib.Floats.ExecFloat.Logarithmic.toCode
                , ``FloatLib.Floats.ExecFloat.Logarithmic.ofCode ]
              applicability := .verifiedForType
              scope :=
                "every value; `toCode` and `ofCode` are inverse, so the theorems about the code " ++
                "below apply through `toCode`" } ]
        let baseProfile : FormatProfile :=
          { coreProfile with
            execution :=
              [ ⟨"carrier", "ExecFloat over the exact logarithmic code"⟩
              , ⟨"dispatch", "direct certified multiplication kernel"⟩
              ]
            theoremSurfaces := ownSurfaces
            relatedTheorems :=
              [ { type := ``FloatLib.Floats.Formats.Logarithmic.Code
                  embedding := ``FloatLib.Floats.ExecFloat.Logarithmic.toCode
                  surfaces := coreProfile.theoremSurfaces } ]
            nonclaims :=
              [ "addition, division, square root, fused multiply-add, or transcendental functions are provided"
              , "a bounded hardware encoding or fractional logarithm field is implied" ] }
        logInfoAt tk <| ← Inspection.renderExecProfile baseProfile typeExpr family

end FloatLib.Floats.Formats.Logarithmic.Configured.FloatInfo.Command
