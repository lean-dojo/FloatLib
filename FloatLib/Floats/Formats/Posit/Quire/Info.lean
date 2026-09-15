/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import Lean.Elab.Command
public import FloatLib.Floats.ExecFloat.Info
public import FloatLib.Floats.Formats.Posit.Quire.Accumulation
public import FloatLib.Floats.Formats.Posit.Quire.Capacity
public import FloatLib.Floats.Formats.Posit.Quire.Configured.Conversion.Proof
public import FloatLib.Floats.Formats.Posit.Quire.Configured.Conversion.Runtime
public import FloatLib.Floats.Formats.Posit.Quire.Configured.Proof
public import FloatLib.Floats.Formats.Posit.Quire.Semantics.Projective

/-!
# Posit quire inspection

`#float_info` shows the quire width, fixed-point scale, capacity, and exact accumulation
operations. The quire has an exact source decoder and an explicit exit to its associated posit
type. Its profile lists those operations separately from scalar `ExecFloat` arithmetic.
-/

public meta section

namespace FloatLib.Floats.Formats.Posit.Quire.FloatInfo

open FloatLib.Floats.ExecFloat

/-- Quire conversion, capacity, and accumulation theorems shown by both posit reports. -/
meta def executionDeclarations : List Lean.Name :=
  [ ``Model.pToQ_zero
  , ``Model.pToQ_nar
  , ``Model.toRat?_qNegate_of_ordinary
  , ``Model.toRat?_qAddQ_of_ordinary
  , ``Model.toRat?_qSubQ_of_ordinary
  , ``Model.toRat?_addDyadic_of_ordinary
  , ``Model.addDyadic_eq_nar_of_exponent_lt
  , ``Model.addDyadic_eq_nar_of_not_ordinary
  , ``Model.toRat?_qAddP_of_ordinary
  , ``Model.qAddP_eq_nar_of_not_ordinary
  , ``Model.toRat?_qSubP_of_ordinary
  , ``Model.toRat?_qMulAdd_of_ordinary
  , ``Model.qMulAdd_eq_nar_of_not_ordinary
  , ``Model.toRat?_qMulSub_of_ordinary
  , ``Model.scaleExponent_le_exponent_of_toDyadic?_eq_some
  , ``Model.scaleExponent_le_mul_exponent_of_toDyadic?_eq_some
  , ``Model.coefficientOfDyadic_ordinary
  , ``Model.natAbs_coefficientOfDyadic_le_positCoefficientBound
  , ``Model.natAbs_coefficientOfDyadic_mul_le_productCoefficientBound
  , ``Model.ordinaryCoefficient_sum_of_length_lt_positSumTermLimit
  , ``Model.ordinaryCoefficient_sum_of_length_lt_productSumTermLimit
  , ``Model.toRat?_foldAddP_zero
  , ``Model.toRat?_foldMulAdd_zero
  , ``Model.isNaR_foldMulAdd_zero
  , ``Model.toRat?_pToQ
  , ``Model.qToP_eq_roundRat
  ]

/-- Describe a Posit Standard (2022) quire and its operation contracts. -/
meta def profile (bits : Nat) : FormatProfile where
  family := "posit quire exact accumulator"
  standard := "Standard for Posit Arithmetic (2022)"
  declarationPrefix := "FloatLib.Floats.Formats.Posit.Quire."
  representation :=
    [ ⟨"storage", s!"FixedInt {16 * bits} backed by an exact-width BitVec"⟩
    , ⟨"associated posit width", toString bits⟩
    , ⟨"quire width", s!"16 × {bits} = {16 * bits} bits"⟩
    , ⟨"least-significant-bit scale", s!"2^({16 - 8 * Int.ofNat bits})"⟩
    , ⟨"ordinary encoding",
        "signed two's-complement coefficient multiplied by the fixed scale"⟩
    , ⟨"reserved encoding", "the most-negative coefficient is quire NaR"⟩
    ]
  values :=
    [ ⟨"ordinary values",
        "exact rational grid points throughout the signed fixed-point range except the reserved word"⟩
    , ⟨"zero", "one all-zero word"⟩
    , ⟨"Not-a-Real", "one reserved quire NaR word"⟩
    , ⟨"infinities", "none"⟩
    , ⟨"IEEE NaNs", "none; quire NaR is a distinct exceptional value"⟩
    ]
  rounding :=
    [ ⟨"posit to quire",
        "exact and unconditional; every ordinary associated posit fits the quire grid"⟩
    , ⟨"accumulation",
        "integer/dyadic operations introduce no rounding while their exact result remains ordinary"⟩
    , ⟨"quire overflow",
        "an out-of-range result or collision with the reserved coefficient produces quire NaR"⟩
    , ⟨"proved capacity",
        s!"folding qAddP over fewer than 2^(23 + 4×{bits}) ordinary posits, or qMulAdd over fewer than 2^31 exact posit products, from the zero quire is exact and never reaches NaR"⟩
    , ⟨"quire to posit",
        "one final current-standard posit rounding, nearest with ties to even"⟩
    ]
  execution :=
    [ ⟨"carrier", s!"one persistent {16 * bits}-bit fixed integer word"⟩
    , ⟨"exact decoder",
        "direct signed coefficient and power-of-two scale; Rat is the public semantic coordinate"⟩
    , ⟨"quire operations",
        "pToQ, qNegate, qAbs, qAddP, qSubP, qAddQ, qSubQ, qMulAdd, qMulSub, and qToP"⟩
    , ⟨"hot-path intermediates",
        "integer and dyadic; rational semantics appears in refinement theorems, not as required runtime storage"⟩
    , ⟨"dispatch",
        "explicit quire API tied by type to its associated posit descriptor; no universal float backend is selected"⟩
    ]
  specializedOperations :=
    [ ⟨"pToQ / qToP",
        "exact posit entry and one nearest-even posit rounding on exit"⟩
    , ⟨"qNegate / qAbs",
        "sign operations on the quire coefficient with explicit NaR behavior"⟩
    , ⟨"qAddP / qSubP / qAddQ / qSubQ",
        "exact fixed-grid accumulation whenever the result remains an ordinary quire value"⟩
    , ⟨"qMulAdd / qMulSub",
        "exact posit-product accumulation before the single final qToP rounding"⟩
    ]
  theoremSurfaces :=
    [ { topic := "exact representation and exceptional semantics"
        declarations :=
          [ ``Model.zero_ne_nar
          , ``Model.eq_nar_iff_coefficient_eq_min
          , ``Model.ordinaryCoefficient_iff_isNaR_eq_false
          , ``Model.toRat?_eq_toDyadic?_map
          , ``Model.toRat?_eq_none_iff
          , ``Model.toReal?_eq_none_iff
          ]
        definitions := [``width, ``scaleExponent]
        applicability := .verifiedForType
        scope :=
          "every word at every valid static posit width; only the reserved minimum word denotes NaR" }
    , { topic := "mathlib projective interoperability"
        declarations :=
          [ ``Model.toProjectiveRat_eq_infty_iff
          , ``Model.toProjectiveRat_eq_coe_iff
          , ``Model.toProjectiveRatLine_eq_nar_iff
          , ``Model.toProjectiveReal_eq_infty_iff
          , ``Model.toProjectiveRealLine_eq_nar_iff
          ]
        applicability := .verifiedForType
        scope :=
          "optional projective views map finite quire values to their exact coordinates and NaR to the added point; primary NumericalValue semantics keeps NaR exceptional" }
    , { topic := "exact quire execution and one-rounding exit"
        declarations := executionDeclarations
        applicability := .verifiedForType
        scope :=
          "pToQ and qToP are global; the fold theorems discharge the ordinary-result condition for every qAddP or qMulAdd loop from zero below the ordinary-addend or exact-product limit, and the overflow theorems show NaR is the only other outcome"
        numericalGuarantee? := some {
          kinds := [.range, .rounding, .exactness]
          statement :=
            "Entry and in-capacity accumulation preserve exact rational meaning; the standard term limits prevent NaR, and qToP rounds once." } }
    , { topic := "configured quire interface"
        declarations :=
          [ ``FloatLib.Floats.ExecFloat.Posit.Quire.ofNatBits_toNatBits
          , ``FloatLib.Floats.ExecFloat.Posit.Quire.pToQ_zero
          , ``FloatLib.Floats.ExecFloat.Posit.Quire.pToQ_nar
          , ``FloatLib.Floats.ExecFloat.Posit.Quire.toRat?_pToQ
          , ``FloatLib.Floats.ExecFloat.Posit.Quire.qToP_zero
          , ``FloatLib.Floats.ExecFloat.Posit.Quire.qToP_nar
          , ``FloatLib.Floats.ExecFloat.Posit.Quire.Conversion.exactDecoder_run
          ]
        applicability := .verifiedForType
        scope :=
          "the public configured API preserves the shared posit descriptor and exposes the same complete exact semantics" }
    ]
  nonclaims :=
    [ "a general rational-to-quire destination quantizer exists; grid rounding and overflow policy must be chosen explicitly"
    , "ordinary `+`, `*`, or the six-operation ExecFloat capability interface denotes quire accumulation"
    , "quire NaR is an ordered or signed infinity"
    , "arbitrarily long accumulation cannot overflow; the proved guarantees use the Posit Standard's explicit exclusive term limits"
    , "the optional projective view changes the primary exceptional semantics"
    ]

end FloatLib.Floats.Formats.Posit.Quire.FloatInfo

namespace FloatLib.Floats.Formats.Posit.Quire.FloatInfo.Command

open Lean Elab Command Meta
open FloatLib.Floats.ExecFloat

elab_rules : command
  | `(#float_info%$tk $type:term) =>
      FloatLib.Floats.ExecFloat.FloatInfo.Command.withElaboratedType
          type fun typeExpr => do
        let some arguments ←
            unfoldUntilAppArgs?
              ``FloatLib.Floats.Formats.Posit.Quire.Model 1 typeExpr
          | throwUnsupportedSyntax
        let bits ←
          Inspection.readNatProjection
            "posit quire descriptor"
            ``FloatLib.Floats.Formats.Posit.Format.bits
            arguments[0]!
        logInfoAt tk <| ←
          Inspection.renderProfile (FloatInfo.profile bits) typeExpr .none

end FloatLib.Floats.Formats.Posit.Quire.FloatInfo.Command
