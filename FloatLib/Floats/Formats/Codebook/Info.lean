/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Info
public import FloatLib.Floats.Formats.Codebook.Arithmetic.Proof
public import FloatLib.Floats.Formats.Codebook.Catalog.Proof
public import FloatLib.Floats.Formats.Codebook.Core.Nearest
public import FloatLib.Floats.Formats.Codebook.Core.Proof
public meta import Lean.Elab.Command

/-!
# Codebook format inspection

Codebook formats assign a meaning to every stored word by an explicit finite table. Their
inspection output therefore reports the table-defined denotation and only the operations whose
refinement theorems are actually available; it does not infer arithmetic from bit width.

Catalog entries additionally report their word denotations and finite-input arithmetic theorems.
Custom tables receive the generic representation and nearest-codeword guarantees. The public
family entry point is `FloatLib.Floats.Formats.Codebook`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Codebook.FloatInfo

open FloatLib.Floats.ExecFloat

/-- The known catalog identity, when the inspected codebook is one supplied by FloatLib. -/
meta inductive CatalogIdentity where
  | bipolar1
  | ternary2
  | custom

/-- Recognize public catalog entries without guessing from the storage width. -/
meta def catalogIdentity (book : Lean.Expr) : CatalogIdentity :=
  if book.isConstOf ``FloatLib.Floats.Formats.Codebook.Catalog.bipolar1 then
    .bipolar1
  else if book.isConstOf ``FloatLib.Floats.Formats.Codebook.Catalog.ternary2 then
    .ternary2
  else
    .custom

/-- Checked theorem surfaces for the selected codebook. -/
meta def theoremSurfaces (identity : CatalogIdentity) : List TheoremSurface :=
  let representation : TheoremSurface :=
    { topic := "complete lookup denotation"
      declarations := [``FloatLib.Floats.Formats.Codebook.numericalSystem_denote]
      applicability := .verifiedForType
      scope := "every stored word; the user-supplied codebook defines every denotation"
      numericalGuarantee? := some {
        kinds := [.exactness]
        statement :=
          "Every stored word has exactly the denotation supplied by the complete codebook." } }
  let nearest : TheoremSurface :=
    { topic := "nearest-codeword quantizer"
      declarations :=
        [ ``FloatLib.Floats.Formats.Codebook.nearestCode_spec
        , ``FloatLib.Floats.Formats.Codebook.nearestCode_isSome_of_denote_finite
        ]
      applicability := .verifiedForType
      scope :=
        "scalar types with subtraction and a linear order; ties resolve to the lower word"
      numericalGuarantee? := some {
        kinds := [.exactness]
        statement :=
          "The selected finite codeword minimizes |x - c| over every finite codeword c of the table." } }
  match identity with
  | .bipolar1 =>
      representation :: nearest ::
        [ { topic := "one-bit bipolar catalog semantics"
            declarations :=
              [ ``FloatLib.Floats.Formats.Codebook.Catalog.bipolar1_denote_zero
              , ``FloatLib.Floats.Formats.Codebook.Catalog.bipolar1_denote_one
              , ``FloatLib.Floats.Formats.Codebook.Catalog.bipolar1.neg_refines
              , ``FloatLib.Floats.Formats.Codebook.Catalog.bipolar1.mul_refines
              ]
            applicability := .verifiedForType
            scope := "both bit patterns; negation and multiplication are total and exact"
            numericalGuarantee? := some {
              kinds := [.exactness]
              statement :=
                "Negation and multiplication have zero denotational error on both bipolar words." } } ]
  | .ternary2 =>
      representation :: nearest ::
        [ { topic := "two-bit ternary catalog semantics"
            declarations :=
              [ ``FloatLib.Floats.Formats.Codebook.Catalog.ternary2_denote_zero
              , ``FloatLib.Floats.Formats.Codebook.Catalog.ternary2_denote_positive
              , ``FloatLib.Floats.Formats.Codebook.Catalog.ternary2_denote_negative
              , ``FloatLib.Floats.Formats.Codebook.Catalog.ternary2_denote_reserved
              , ``FloatLib.Floats.Formats.Codebook.Catalog.ternary2.neg_refines
              , ``FloatLib.Floats.Formats.Codebook.Catalog.ternary2.mul_refines
              ]
            applicability := .verifiedForType
            scope := "all four words; checked operations reject the reserved word"
            numericalGuarantee? := some {
              kinds := [.exactness]
              statement :=
                "Checked negation and multiplication are exact whenever no reserved word is supplied." } } ]
  | .custom => [representation, nearest]

/-- Operations implemented by the raw catalog code, without implying universal scalar dispatch. -/
meta def rawSpecializedOperations (identity : CatalogIdentity) : List InfoEntry :=
  match identity with
  | .bipolar1 =>
      [ ⟨"neg", "total exact negation on both one-bit words"⟩
      , ⟨"mul", "total exact multiplication on both one-bit words"⟩
      ]
  | .ternary2 =>
      [ ⟨"neg?", "checked exact negation; returns none for the reserved word"⟩
      , ⟨"mul?", "checked exact multiplication; returns none for a reserved operand"⟩
      ]
  | .custom => []

/--
Operations outside universal configured dispatch.

Bipolar multiplication is omitted here because the configured family installs it as the ordinary
proof-linked `ExecFloat.Mul` capability. Its exact negation remains a family-specific operation.
The ternary operations remain checked `Option` APIs, so both are specialized.
-/
meta def configuredSpecializedOperations (identity : CatalogIdentity) : List InfoEntry :=
  match identity with
  | .bipolar1 =>
      [ ⟨"neg", "total exact negation exposed through the configured `Neg` instance"⟩ ]
  | .ternary2 =>
      [ ⟨"neg?", "checked exact negation; returns none for the reserved word"⟩
      , ⟨"mul?", "checked exact multiplication; returns none for a reserved operand"⟩
      ]
  | .custom => []

/-- Build the proof-aware profile for an exact-width lookup encoding. -/
meta def profile (width : Nat) (identity : CatalogIdentity) : FormatProfile :=
  let (standard, valueDescription, exceptionDescription, arithmetic, nonclaims) :=
    match identity with
    | .bipolar1 =>
        ( "FloatLib catalog encoding; not an external standard"
        , "{-1, +1}"
        , "none"
        , "total exact negation and multiplication"
        , [ "addition, division, square root, fused multiply-add, or transcendental functions "
              ++ "are supplied" ] )
    | .ternary2 =>
        ( "FloatLib catalog encoding; not an external standard"
        , "{0, +1, -1}"
        , "one reserved word"
        , "checked exact negation and multiplication"
        , ["the reserved word is interpreted as NaN or infinity"] )
    | .custom =>
        ( "user-defined complete lookup encoding"
        , "defined by the selected codebook denotation"
        , "defined by the selected codebook denotation"
        , "no generic arithmetic is inferred from a lookup table"
        , ["any operation or algebraic law beyond complete lookup denotation is verified"] )
  { family := "exact-width lookup codebook"
    standard := standard
    declarationPrefix := "FloatLib.Floats.Formats.Codebook."
    representation :=
      [ ⟨"storage", s!"BitVec {width}"⟩
      , ⟨"encoding", "a complete denotation table indexed by every stored word"⟩
      , ⟨"catalog identity",
          match identity with
          | .bipolar1 => "bipolar1"
          | .ternary2 => "ternary2"
          | .custom => "custom codebook"⟩
      ]
    values :=
      [ ⟨"finite values", valueDescription⟩
      , ⟨"exceptional values", exceptionDescription⟩
      , ⟨"unassigned bit patterns", "none; every word has a denotation"⟩
      ]
    rounding :=
      [ ⟨"lookup", "exact"⟩
      , ⟨"nearest codeword", "first finite word minimizing |x - c|; ties to the lower word"⟩
      , ⟨"arithmetic", arithmetic⟩
      ]
    execution :=
      [ ⟨"carrier", s!"BitVec {width}"⟩
      , ⟨"dispatch", "direct lookup and any family-defined bit kernel"⟩
      , ⟨"backend proof", "catalog arithmetic is reported only when a checked refinement exists"⟩
      ]
    specializedOperations := rawSpecializedOperations identity
    theoremSurfaces := theoremSurfaces identity
    nonclaims :=
      "the six-operation `ExecFloat` API applies automatically to arbitrary lookup tables" ::
        nonclaims }

namespace Command

open Lean Elab Command Meta

elab_rules : command
  | `(#float_info%$tk $type:term) =>
      FloatLib.Floats.ExecFloat.FloatInfo.Command.withElaboratedType
          type fun typeExpr => do
        let some arguments ←
            unfoldUntilAppArgs? ``FloatLib.Floats.Formats.Codebook.Code 3 typeExpr
          | throwUnsupportedSyntax
        let width ← Inspection.readNat "codebook width" arguments[0]!
        logInfoAt tk <| ←
          Inspection.renderProfile
            (profile width (catalogIdentity arguments[2]!)) typeExpr .none

end Command

end FloatLib.Floats.Formats.Codebook.FloatInfo
