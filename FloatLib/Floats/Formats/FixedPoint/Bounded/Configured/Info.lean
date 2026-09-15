/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Bounded.Configured.Proof
public meta import Lean.Elab.Command
public import FloatLib.Floats.Formats.FixedPoint.Bounded.Info

/-!
# Inspection for configured bounded fixed point

This optional meta module registers `#float_info` for the promoted
`ExecFloat.BoundedFixedPoint` wrapper. It reports the selected coefficient width and radix scale,
then exposes only theorem-backed wrapping, checked, and saturating guarantees.

Keeping inspection optional prevents elaborator support from entering ordinary runtime imports.
The profile mirrors the raw family while naming the configured public operations users actually
call.
-/

public meta section

namespace FloatLib.Floats.Formats.FixedPoint.Bounded.Configured.FloatInfo.Command

open Lean Elab Command Meta
open FloatLib.Numerics
open FloatLib.Floats.ExecFloat

elab_rules : command
  | `(#float_info%$tk $type:term) =>
      FloatLib.Floats.ExecFloat.FloatInfo.Command.withExecFamilyApplication
          type ``FloatLib.Floats.ExecFloat.BoundedFixedPoint.Family 3
          fun typeExpr _family arguments => do
        let radix := arguments[0]!
        let fractionalDigitsExpr := arguments[1]!
        let widthExpr := arguments[2]!
        let base ←
          Inspection.readNatProjection "bounded fixed-point radix" ``Radix.base radix
        let fractionalDigits ←
          Inspection.readNat
            "bounded fixed-point fractional-digit count" fractionalDigitsExpr
        let width ←
          Inspection.readNat "bounded fixed-point coefficient width" widthExpr
        let coreProfile :=
          FloatLib.Floats.Formats.FixedPoint.Bounded.FloatInfo.Command.profile
            base fractionalDigits width
        let configuredWrapping : TheoremSurface :=
          { topic := "configured wrapping arithmetic"
            declarations :=
              [ ``FloatLib.Floats.ExecFloat.BoundedFixedPoint.toRat_wrapAdd
              , ``FloatLib.Floats.ExecFloat.BoundedFixedPoint.toRat_wrapSub
              , ``FloatLib.Floats.ExecFloat.BoundedFixedPoint.toRat_wrapMul
              ]
            applicability := .verifiedForType
            scope := "all stored coefficients and destination widths"
            numericalGuarantee? := some {
              kinds := [.range]
              statement :=
                "Wrapping always returns a represented coefficient and exactly follows centered modular reduction." } }
        let configuredChecked : TheoremSurface :=
          { topic := "configured checked and saturating arithmetic"
            declarations :=
              [ ``FloatLib.Floats.ExecFloat.BoundedFixedPoint.checkedAdd_eq_some
              , ``FloatLib.Floats.ExecFloat.BoundedFixedPoint.checkedSub_eq_some
              , ``FloatLib.Floats.ExecFloat.BoundedFixedPoint.checkedMul_eq_some
              , ``FloatLib.Floats.ExecFloat.BoundedFixedPoint.toRat_of_checkedAdd_eq_some
              , ``FloatLib.Floats.ExecFloat.BoundedFixedPoint.toRat_of_checkedSub_eq_some
              , ``FloatLib.Floats.ExecFloat.BoundedFixedPoint.toRat_of_checkedMul_eq_some
              , ``FloatLib.Floats.ExecFloat.BoundedFixedPoint.toRat_saturatingAdd
              , ``FloatLib.Floats.ExecFloat.BoundedFixedPoint.toRat_saturatingSub
              , ``FloatLib.Floats.ExecFloat.BoundedFixedPoint.toRat_saturatingMul
              ]
            applicability :=
              if width > 0 then .verifiedForType else .unavailable "signed width must be positive"
            scope :=
              "positive destination widths; checked exactness holds whenever a value is returned"
            numericalGuarantee? := some {
              kinds := [.range, .exactness]
              statement :=
                "Checked operations succeed when the exact coefficient fits and every returned value decodes to the exact rational result; saturating operations decode to the exact coefficient clamped to the signed range." } }
        let baseProfile : FormatProfile :=
          { coreProfile with
            declarationPrefix := "FloatLib.Floats.ExecFloat.BoundedFixedPoint."
            rounding :=
              ⟨"numeric conversion",
                "nearest-even coefficient with an explicit overflow policy"⟩ ::
                coreProfile.rounding
            execution :=
              [ ⟨"carrier", s!"ExecFloat over FixedInt {width}"⟩
              , ⟨"dispatch", "direct fixed-width kernels selected by explicit operation names"⟩
              , ⟨"backend proof",
                  "wrapping, checked, and saturating operations each lift a rational decoding "
                    ++ "theorem from the raw code layer"⟩
              ]
            theoremSurfaces :=
              configuredWrapping :: configuredChecked :: coreProfile.theoremSurfaces
            nonclaims :=
              [ "one overflow policy is silently selected by ordinary arithmetic notation"
              , "division, square root, fused multiply-add, or transcendental functions are "
                  ++ "provided"
              , "IEEE exceptional values or flags apply to this integer-backed family" ] }
        logInfoAt tk <| ← Inspection.renderProfile baseProfile typeExpr .none

end FloatLib.Floats.Formats.FixedPoint.Bounded.Configured.FloatInfo.Command
