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

This optional meta module registers `#float_info` for `ExecFloat.Logarithmic`. The configured
format can be imported independently of this command registration.
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
        let configuredMultiplication : TheoremSurface :=
          { topic := "configured exact multiplication"
            declarations :=
              [ ``FloatLib.Floats.ExecFloat.Logarithmic.toReal_mul
              , ``FloatLib.Floats.ExecFloat.Proof.mul_eq_spec
              ]
            applicability := .verifiedForType
            scope := "all configured logarithmic values"
            numericalGuarantee? := some {
              kinds := [.exactness]
              statement :=
                "Configured multiplication has zero real error because signs and unbounded exponents combine exactly." } }
        let baseProfile : FormatProfile :=
          { coreProfile with
            declarationPrefix := "FloatLib.Floats.ExecFloat.Logarithmic."
            execution :=
              [ ⟨"carrier", "ExecFloat over the exact logarithmic code"⟩
              , ⟨"dispatch", "direct certified multiplication kernel"⟩
              ]
            theoremSurfaces :=
              configuredMultiplication :: coreProfile.theoremSurfaces
            nonclaims :=
              [ "addition, division, square root, fused multiply-add, or transcendental functions are provided"
              , "a bounded hardware encoding or fractional logarithm field is implied" ] }
        logInfoAt tk <| ← Inspection.renderExecProfile baseProfile typeExpr family

end FloatLib.Floats.Formats.Logarithmic.Configured.FloatInfo.Command
