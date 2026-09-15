/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Proof.Arithmetic
public meta import Lean.Elab.Command
public import FloatLib.Floats.Formats.FixedPoint.Configured.Proof
public import FloatLib.Floats.Formats.FixedPoint.Exact.Info

/-!
# Inspection for configured exact fixed point

This optional meta module registers `#float_info` for `ExecFloat.FixedPoint`. The executable
configured type remains independently importable without editor elaborators or the public proof
module.
-/

public meta section

namespace FloatLib.Floats.Formats.FixedPoint.Configured.FloatInfo.Command

open Lean Elab Command Meta
open FloatLib.Numerics
open FloatLib.Floats.ExecFloat

elab_rules : command
  | `(#float_info%$tk $type:term) =>
      FloatLib.Floats.ExecFloat.FloatInfo.Command.withExecFamilyApplication
          type ``FloatLib.Floats.ExecFloat.FixedPoint.Family 2
          fun typeExpr family arguments => do
        let radix := arguments[0]!
        let fractionalDigitsExpr := arguments[1]!
        let base ←
          Inspection.readNatProjection "fixed-point radix" ``Radix.base radix
        let fractionalDigits ←
          Inspection.readNat "fixed-point fractional-digit count" fractionalDigitsExpr
        let coreProfile :=
          FloatLib.Floats.Formats.FixedPoint.FloatInfo.Command.profile base fractionalDigits
        let configuredArithmetic : TheoremSurface :=
          { topic := "configured exact arithmetic"
            declarations :=
              [ ``FloatLib.Floats.ExecFloat.FixedPoint.toRat_add
              , ``FloatLib.Floats.ExecFloat.FixedPoint.toRat_sub
              , ``FloatLib.Floats.ExecFloat.FixedPoint.toRat_mul
              , ``FloatLib.Floats.ExecFloat.Proof.add_eq_spec
              , ``FloatLib.Floats.ExecFloat.Proof.sub_eq_spec
              ]
            applicability := .verifiedForType
            scope := "all coefficients; multiplication composes operand scales"
            numericalGuarantee? := some {
              kinds := [.exactness]
              statement :=
                "Configured addition, subtraction, and heterogeneous multiplication have zero rational error." } }
        let baseProfile : FormatProfile :=
          { coreProfile with
            declarationPrefix := "FloatLib.Floats.ExecFloat.FixedPoint."
            rounding :=
              ⟨"numeric literals", "exact rational input rounded once to nearest, ties to even"⟩ ::
                coreProfile.rounding
            execution :=
              [ ⟨"carrier", "ExecFloat over an unbounded Int coefficient"⟩
              , ⟨"dispatch", "direct certified integer addition and subtraction"⟩
              ]
            specializedOperations :=
              [ ⟨"mul",
                  "exact heterogeneous multiplication returning the statically composed output scale"⟩
              ]
            theoremSurfaces :=
              configuredArithmetic :: coreProfile.theoremSurfaces
            nonclaims :=
              [ "homogeneous multiplication silently rounds back to the input scale"
              , "division, square root, fused multiply-add, or transcendental functions are provided"
              , "a fixed-width overflow policy is implied" ] }
        logInfoAt tk <| ← Inspection.renderExecProfile baseProfile typeExpr family

end FloatLib.Floats.Formats.FixedPoint.Configured.FloatInfo.Command
