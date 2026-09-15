/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Exact.Proof
public meta import Lean.Elab.Command
public import FloatLib.Floats.ExecFloat.Info

/-!
# Inspection for exact fixed-point codes

The unbounded fixed-point core has exact integer-coefficient arithmetic and no overflow policy.
Its inspection profile therefore emphasizes rational denotation, common-scale addition and
subtraction, and heterogeneous multiplication with a composed scale.

This optional meta module registers `#float_info` without adding elaborator dependencies to the
runtime family. It also states the missing operations plainly so exactness is not mistaken for a
complete floating-point API.
-/

public meta section

namespace FloatLib.Floats.Formats.FixedPoint.FloatInfo.Command

open Lean Elab Command Meta
open FloatLib.Numerics
open FloatLib.Floats.ExecFloat

/--
Build the proof-aware description shared by the exact code and its configured `ExecFloat`
wrapper. The wrapper replaces carrier-specific execution and theorem entries while retaining this
single account of the value set, scale, and exact arithmetic.
-/
meta def profile (base fractionalDigits : Nat) : FormatProfile where
  family := "radix-parametric fixed point"
  standard := "mathematical fixed-point format; no external encoding standard claimed"
  declarationPrefix := "FloatLib.Floats.Formats.FixedPoint."
  representation :=
    [ ⟨"storage", "Int coefficient"⟩
    , ⟨"radix", toString base⟩
    , ⟨"fractional digits", toString fractionalDigits⟩
    , ⟨"scale denominator", s!"{base}^{fractionalDigits}"⟩
    , ⟨"coefficient width", "unbounded"⟩
    ]
  values :=
    [ ⟨"finite rational values", "yes; coefficient / radix^fractionalDigits"⟩
    , ⟨"signed zero", "no; the integer coefficient has one zero"⟩
    , ⟨"infinity", "no"⟩
    , ⟨"NaN", "no"⟩
    ]
  rounding :=
    [ ⟨"addition/subtraction", "exact at a common scale"⟩
    , ⟨"multiplication", "exact; output fractional digits are the sum of input scales"⟩
    , ⟨"overflow", "none; the coefficient is unbounded"⟩
    ]
  execution :=
    [ ⟨"carrier", "Lean Int coefficient"⟩
    , ⟨"dispatch", "direct integer arithmetic in the family API"⟩
    , ⟨"backend proof", "operation refinement is stated against exact rational arithmetic"⟩
    ]
  specializedOperations :=
    [ ⟨"neg / add / sub", "exact integer-coefficient arithmetic at one common scale"⟩
    , ⟨"mul",
        "exact heterogeneous multiplication whose result scale is the sum of operand scales"⟩
    ]
  theoremSurfaces :=
    [ { topic := "exact rational interpretation"
        declarations := [``Code.toRat_add, ``Code.toRat_neg, ``Code.toRat_sub, ``Code.toRat_mul]
        applicability := .verifiedForType
        scope := "all coefficients and every validated radix" }
    , { topic := "family-operation refinement"
        declarations := [``add_refines, ``neg_refines, ``sub_refines, ``mul_refines]
        applicability := .verifiedForType
        scope :=
          "addition and subtraction use a common scale; multiplication returns the composed scale"
        numericalGuarantee? := some {
          kinds := [.exactness]
          statement :=
            "Negation, addition, subtraction, and heterogeneous multiplication have zero rational error." } }
    ]
  nonclaims :=
    [ "the universal six-operation `ExecFloat` API is implemented for this unbounded carrier"
    , "division, square root, fused multiply-add, or transcendental rounding is provided"
    , "a fixed-width overflow or saturation policy is implied"
    ]

elab_rules : command
  | `(#float_info%$tk $type:term) =>
      FloatLib.Floats.ExecFloat.FloatInfo.Command.withElaboratedType
          type fun typeExpr => do
        let some arguments ← unfoldUntilAppArgs? ``Code 2 typeExpr
          | throwUnsupportedSyntax
        let base ←
          Inspection.readNatProjection "fixed-point radix" ``Radix.base arguments[0]!
        let fractionalDigits ←
          Inspection.readNat "fixed-point fractional-digit count" arguments[1]!
        logInfoAt tk <| ←
          Inspection.renderProfile (profile base fractionalDigits) typeExpr .none

end FloatLib.Floats.Formats.FixedPoint.FloatInfo.Command
