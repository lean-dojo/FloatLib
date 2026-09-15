/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Logarithmic.Exact.Proof
public meta import Lean.Elab.Command
public import FloatLib.Floats.ExecFloat.Info

/-!
# Inspection for exact logarithmic codes

The exact logarithmic core represents zero or a signed integral power of a chosen radix.
Multiplication is the only arithmetic operation supplied and is exact exponent addition.
General addition and conversion into this value set require rounding. Nonzero division could
subtract exponents exactly, but division and its zero-divisor policy are not implemented.

This optional meta module reports the real denotation and multiplication refinement through
`#float_info`, together with the limits of the implemented operation set.
-/

public meta section

namespace FloatLib.Floats.Formats.Logarithmic.FloatInfo.Command

open Lean Elab Command Meta
open FloatLib.Numerics
open FloatLib.Floats.ExecFloat

/--
Build the logarithmic description shared by the exact code and its configured `ExecFloat`
wrapper. Both carriers use the same value set and exact multiplication law; only execution and
wrapper-level theorem entries differ.
-/
meta def profile (base : Nat) : FormatProfile where
  family := "radix-parametric logarithmic number system"
  standard := "mathematical logarithmic format; no external encoding standard claimed"
  declarationPrefix := "FloatLib.Floats.Formats.Logarithmic."
  representation :=
    [ ⟨"storage", "zero, or a sign bit and an unbounded Int exponent"⟩
    , ⟨"radix", toString base⟩
    , ⟨"nonzero value", s!"±{base}^exponent"⟩
    , ⟨"mantissa", "none"⟩
    , ⟨"exponent width", "unbounded"⟩
    ]
  values :=
    [ ⟨"zero", "one unsigned zero code"⟩
    , ⟨"nonzero finite values", s!"signed integral powers of {base}"⟩
    , ⟨"infinity", "no"⟩
    , ⟨"NaN", "no"⟩
    ]
  rounding :=
    [ ⟨"multiplication", "exact; signs xor and exponents add"⟩
    , ⟨"overflow/underflow", "none; the exponent is unbounded"⟩
    , ⟨"addition and division",
        "not supplied; the sum of two integral powers of the radix is in general not one"⟩
    , ⟨"conversion", "not supplied by this exact core"⟩
    ]
  execution :=
    [ ⟨"carrier", "inductive zero/value code with Bool sign and Int exponent"⟩
    , ⟨"dispatch", "direct constructor matching and integer exponent addition"⟩
    , ⟨"backend proof", "multiplication refinement is checked against real multiplication"⟩
    ]
  specializedOperations :=
    [ ⟨"mul", "the only arithmetic operation: exact sign xor and unbounded exponent addition"⟩ ]
  theoremSurfaces :=
    [ { topic := "exact real interpretation"
        declarations :=
          [ ``FloatLib.Floats.Formats.Logarithmic.Code.toReal_zero
          , ``FloatLib.Floats.Formats.Logarithmic.Code.toReal_mul
          ]
        applicability := .verifiedForType
        scope := "every code and every validated radix" }
    , { topic := "representation and multiplication refinement"
        declarations :=
          [ ``FloatLib.Floats.Formats.Logarithmic.numericalSystem_represents_iff
          , ``FloatLib.Floats.Formats.Logarithmic.mul_refines
          ]
        applicability := .verifiedForType
        scope := "all logarithmic codes; multiplication is exact over their real denotations"
        numericalGuarantee? := some {
          kinds := [.exactness]
          statement :=
            "Multiplication has zero real error because signs combine and unbounded exponents add exactly." } }
    ]
  nonclaims :=
    [ "the universal six-operation `ExecFloat` API is implemented for this carrier"
    , "addition, subtraction, division, square root, fused multiply-add, or transcendental functions are provided"
    , "a bounded hardware encoding or a fractional logarithm field is implied"
    ]

elab_rules : command
  | `(#float_info%$tk $type:term) =>
      FloatLib.Floats.ExecFloat.FloatInfo.Command.withElaboratedType
          type fun typeExpr => do
        let some arguments ←
            unfoldUntilAppArgs? ``FloatLib.Floats.Formats.Logarithmic.Code 1 typeExpr
          | throwUnsupportedSyntax
        let base ←
          Inspection.readNatProjection
            "logarithmic-format radix" ``Radix.base arguments[0]!
        logInfoAt tk <| ← Inspection.renderProfile (profile base) typeExpr .none

end FloatLib.Floats.Formats.Logarithmic.FloatInfo.Command
