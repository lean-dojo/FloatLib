/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Info
public import FloatLib.Floats.Formats.FixedPoint.Bounded.Core
public import FloatLib.Floats.Formats.FixedPoint.Bounded.Semantics.Proof
public meta import Lean.Elab.Command

/-!
# Bounded fixed-point format inspection

Inspection for a bounded fixed-point code reports its radix, scale, signed coefficient range, and
the three distinct overflow policies. It links refinement theorems for modular, checked, and
saturating arithmetic.

No external wire standard is claimed for this mathematical family. The public entry point is
`FloatLib.Floats.Formats.FixedPoint.Bounded`; this module contains only the optional meta-level
inspection support.
-/

public meta section

namespace FloatLib.Floats.Formats.FixedPoint.Bounded.FloatInfo.Command

open Lean Elab Command Meta
open FloatLib.Numerics
open FloatLib.Floats.ExecFloat

/--
Build the fixed-width description shared by raw codes and the configured `ExecFloat` wrapper.
Carrier-specific reports replace the execution entries and may add wrapper theorems, but the
represented range and overflow policies are defined here once.
-/
meta def profile (base fractionalDigits width : Nat) : FormatProfile where
  family := "bounded radix-parametric fixed point"
  standard := "mathematical fixed-point format; no external encoding standard claimed"
  declarationPrefix := "FloatLib.Floats.Formats.FixedPoint.Bounded."
  representation :=
    [ ⟨"storage", s!"signed {width}-bit two's-complement coefficient"⟩
    , ⟨"radix", toString base⟩
    , ⟨"fractional digits", toString fractionalDigits⟩
    , ⟨"scale denominator", s!"{base}^{fractionalDigits}"⟩
    ]
  values :=
    [ ⟨"finite rational values", "yes; signed coefficient / radix^fractionalDigits"⟩
    , ⟨"signed zero", "no; the coefficient has one zero"⟩
    , ⟨"infinity", "no"⟩
    , ⟨"NaN", "no"⟩
    ]
  rounding :=
    [ ⟨"wrapping policy", "centered reduction modulo 2^width for the destination width"⟩
    , ⟨"checked policy", "returns none exactly when the exact coefficient does not fit"⟩
    , ⟨"saturating policy", "clamps the exact coefficient to the signed bounds"⟩
    , ⟨"multiplication scale", "output fractional digits are the sum of input scales"⟩
    ]
  execution :=
    [ ⟨"carrier", s!"FixedInt {width} backed by BitVec {width}"⟩
    , ⟨"dispatch", "direct fixed-width kernels; overflow policy is explicit in the function name"⟩
    , ⟨"backend proof",
        "the wrapping, checked, and saturating kernels each have a rational refinement theorem "
          ++ "in `Bounded.Semantics.Proof`"⟩
    ]
  specializedOperations :=
    [ ⟨"wrapAdd / wrapSub",
        "modular coefficient arithmetic with exact centered-reduction refinement"⟩
    , ⟨"wrapMul",
        "modular multiplication with an explicit destination width and summed input scales"⟩
    , ⟨"checkedAdd / checkedSub / checkedMul",
        "return `none` exactly when the mathematically exact coefficient does not fit"⟩
    , ⟨"saturatingAdd / saturatingSub / saturatingMul",
        "clamp to the signed destination bounds with rational refinement theorems"⟩
    ]
  theoremSurfaces :=
    [ { topic := "representation and coefficient recovery"
        declarations :=
          [ ``FloatLib.Floats.Formats.FixedPoint.Bounded.numericalSystem_represents_iff
          , ``FloatLib.Floats.Formats.FixedPoint.Bounded.coefficientOf_toRat
          , ``FloatLib.Floats.Formats.FixedPoint.Bounded.toUnbounded_toRat
          ]
        applicability := .verifiedForType
        scope := "every stored coefficient" }
    , { topic := "wrapping arithmetic"
        declarations :=
          [ ``FloatLib.Floats.Formats.FixedPoint.Bounded.wrapAdd_refines
          , ``FloatLib.Floats.Formats.FixedPoint.Bounded.wrapSub_refines
          , ``FloatLib.Floats.Formats.FixedPoint.Bounded.wrapMul_refines
          ]
        applicability := .verifiedForType
        scope := "all widths; multiplication may choose a separate destination width"
        numericalGuarantee? := some {
          kinds := [.range]
          statement :=
            "Wrapping always returns a represented coefficient and exactly follows centered modular reduction; it is not advertised as a small real-error bound." } }
    , { topic := "checked and saturating arithmetic"
        declarations :=
          [ ``FloatLib.Floats.Formats.FixedPoint.Bounded.checkedAdd_refines
          , ``FloatLib.Floats.Formats.FixedPoint.Bounded.checkedSub_refines
          , ``FloatLib.Floats.Formats.FixedPoint.Bounded.checkedMul_refines
          , ``FloatLib.Floats.Formats.FixedPoint.Bounded.saturatingAdd_refines
          , ``FloatLib.Floats.Formats.FixedPoint.Bounded.saturatingSub_refines
          , ``FloatLib.Floats.Formats.FixedPoint.Bounded.saturatingMul_refines
          ]
        applicability :=
          if width > 0 then .verifiedForType else .unavailable "signed width must be positive"
        scope := "positive destination widths; checked exactness also assumes the result fits"
        numericalGuarantee? := some {
          kinds := [.range, .exactness]
          statement :=
            "Checked arithmetic is exact when it succeeds; saturating arithmetic clamps the exact coefficient to the represented signed range." } }
    ]
  nonclaims :=
    [ "one overflow policy is silently selected as the default"
    , "division, square root, fused multiply-add, or transcendental functions are implemented"
    , "IEEE exceptional values or status flags apply to this integer-backed family"
    ]

elab_rules : command
  | `(#float_info%$tk $type:term) =>
      FloatLib.Floats.ExecFloat.FloatInfo.Command.withElaboratedType
          type fun typeExpr => do
        let some arguments ←
            unfoldUntilAppArgs?
              ``FloatLib.Floats.Formats.FixedPoint.Bounded.Code 3 typeExpr
          | throwUnsupportedSyntax
        let base ←
          Inspection.readNatProjection
            "bounded fixed-point radix" ``Radix.base arguments[0]!
        let fractionalDigits ←
          Inspection.readNat
            "bounded fixed-point fractional-digit count" arguments[1]!
        let width ←
          Inspection.readNat "bounded fixed-point coefficient width" arguments[2]!
        logInfoAt tk <| ←
          Inspection.renderProfile (profile base fractionalDigits width) typeExpr .none

end FloatLib.Floats.Formats.FixedPoint.Bounded.FloatInfo.Command
