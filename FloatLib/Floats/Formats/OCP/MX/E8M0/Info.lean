/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Info
public import FloatLib.Floats.Formats.OCP.MX.E8M0.Block
public meta import Lean.Elab.Command
public import FloatLib.Floats.Formats.BinaryInterchange.Format.Catalog
public import FloatLib.Floats.Formats.OCP.MX.E8M0.Semantics

/-!
# Inspection reports for OCP E8M0 and raw MX blocks

This optional meta module registers `#float_info` for the raw E8M0 scale and `BlockCode` types.
Executable decoding remains in `Core`, `Semantics`, and `Block`, so runtime-only clients do not
depend on command elaboration or report rendering.

Reports distinguish scale decoding from joint block decoding and list their refinement theorems.
The raw block type admits arbitrary lengths and element descriptors.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.OCP.MX.E8M0.FloatInfo.Command

open Lean Elab Command Meta
open FloatLib.Floats.ExecFloat

/--
Build the E8M0 inspection profile shared by the raw code and configured `ExecFloat` wrapper.
-/
meta def profile : FormatProfile where
  family := "exponent-only microscaling scale"
  standard := "Open Compute Project MX E8M0"
  declarationPrefix := "FloatLib.Floats.Formats.OCP.MX.E8M0."
  representation :=
    [ ⟨"storage", "8-bit word"⟩
    , ⟨"finite codes", "0x00 through 0xfe"⟩
    , ⟨"exponent bias", "127"⟩
    , ⟨"finite value", "2^(code - 127)"⟩
    , ⟨"NaN code", "0xff"⟩
    ]
  values :=
    [ ⟨"positive finite scales", "2^-127 through 2^127"⟩
    , ⟨"zero", "not representable"⟩
    , ⟨"negative values", "not representable"⟩
    , ⟨"infinity", "not representable"⟩
    , ⟨"NaN", "one encoding: 0xff"⟩
    ]
  rounding :=
    [ ⟨"scale decoding", "exact power-of-two dyadic"⟩
    , ⟨"element scaling", "exact dyadic exponent addition"⟩
    , ⟨"exponent construction", "checked or explicitly saturating"⟩
    ]
  execution :=
    [ ⟨"carrier", "E8M0 transparent over BitVec 8"⟩
    , ⟨"dispatch", "direct byte decoding and dyadic exponent arithmetic"⟩
    , ⟨"backend proof", "successful scale and block-element decoding refine exact dyadic scaling"⟩
    ]
  specializedOperations :=
    [ ⟨"exponent? / toDyadic?", "checked exact decoding; the sole NaN code returns none"⟩
    , ⟨"ofExponent? / ofExponentSaturating",
        "explicit checked or clamped construction from an unbiased exponent"⟩
    , ⟨"scaleDyadic? / decodeElement?",
        "checked exact power-of-two scaling by dyadic exponent addition"⟩
    ]
  theoremSurfaces :=
    [ { topic := "E8M0 value-class invariants"
        declarations :=
          [ ``FloatLib.Floats.Formats.OCP.MX.E8M0.toDyadic?_significand_eq_one
          , ``FloatLib.Floats.Formats.OCP.MX.E8M0.toDyadic?_negative_eq_false
          , ``FloatLib.Floats.Formats.OCP.MX.E8M0.numericalSystem_represents_iff
          ]
        applicability := .verifiedForType
        scope := "every successfully decoded finite scale" }
    , { topic := "exact scale and element refinement"
        declarations :=
          [ ``FloatLib.Floats.Formats.OCP.MX.E8M0.scaleDyadic_refines
          , ``FloatLib.Floats.Formats.OCP.MX.E8M0.decodeElement_refines
          ]
        applicability := .verifiedForType
        scope := "finite E8M0 scale and finite binary-interchange element inputs"
        numericalGuarantee? := some {
          kinds := [.exactness]
          statement :=
            "Applying a finite E8M0 scale is exact dyadic exponent addition with zero scaling error." } }
    ]
  nonclaims :=
    [ "E8M0 is an ordinary sign/exponent/fraction floating-point format"
    , "E8M0 represents zero or infinity"
    , "a block scale-selection policy or accelerator instruction equivalence is proved"
    ]

/-- Human-readable identity for a binary element descriptor used in an E8M0-scaled block. -/
meta def blockElementIdentity (format : Expr) : MetaM String := do
  if format.isConstOf
      ``FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.e2m1 then
    return "OCP MX E2M1"
  if format.isConstOf
      ``FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.e2m3 then
    return "OCP MX E2M3"
  if format.isConstOf
      ``FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.e3m2 then
    return "OCP MX E3M2"
  let normalized ← withTransparency .all <| whnf format
  if normalized.isConstOf
      ``FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.e2m1 then
    return "OCP MX E2M1"
  if normalized.isConstOf
      ``FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.e2m3 then
    return "OCP MX E2M3"
  if normalized.isConstOf
      ``FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.e3m2 then
    return "OCP MX E3M2"
  return toString (← Meta.ppExpr format)

/-- Build the report for the joint shared-scale-and-elements block carrier. -/
meta def blockProfile (elementIdentity : String) : FormatProfile where
  family := "E8M0-scaled binary block"
  standard := "OCP MX representation when the chosen element descriptor and block size satisfy MX"
  declarationPrefix := "FloatLib.Floats.Formats.OCP.MX."
  representation :=
    [ ⟨"scale storage", "one E8M0 byte"⟩
    , ⟨"element format", elementIdentity⟩
    , ⟨"element storage", "runtime-sized Array of exact binary-interchange words"⟩
    , ⟨"joint code", "BlockCode stores the scale and element words together"⟩
    ]
  values :=
    [ ⟨"finite block", "an exact dyadic array when the scale and every element decode"⟩
    , ⟨"NaN block", "yes; any failed joint decoding denotes a NaN exception"⟩
    , ⟨"infinity", "not produced by the exact block decoder"⟩
    , ⟨"block length", "dynamic; the Array length is not a type parameter"⟩
    ]
  rounding :=
    [ ⟨"scale application", "exact dyadic exponent addition"⟩
    , ⟨"element conversion", "exact decoding; no rounding occurs in BlockCode.decode?"⟩
    , ⟨"scale selection", "not hidden in the carrier; callers choose the stored scale"⟩
    ]
  execution :=
    [ ⟨"carrier", "structure containing one E8M0 and an Array of Model element words"⟩
    , ⟨"dispatch", "linear array traversal with exact per-lane dyadic scaling"⟩
    , ⟨"backend proof", "successful joint decoding refines the exact dyadic-array system"⟩
    ]
  specializedOperations :=
    [ ⟨"decode?", "checked exact joint decoding of the stored scale and every element word"⟩ ]
  theoremSurfaces :=
    [ { topic := "joint block representation"
        declarations :=
          [ ``FloatLib.Floats.Formats.OCP.MX.blockSystem_represents_iff
          , ``FloatLib.Floats.Formats.OCP.MX.BlockCode.decode_refines
          ]
        applicability := .verifiedForType
        scope := "every runtime block length and every selected binary element descriptor"
        numericalGuarantee? := some {
          kinds := [.exactness]
          statement :=
            "Successful joint decoding returns exactly the dyadic array denoted by the stored scale and element words." } }
    , { topic := "exact E8M0 element scaling"
        declarations :=
          [ ``FloatLib.Floats.Formats.OCP.MX.E8M0.scaleDyadic_refines
          , ``FloatLib.Floats.Formats.OCP.MX.E8M0.decodeElement_refines
          ]
        applicability := .verifiedForType
        scope := "finite E8M0 scale and successfully decoded finite element words"
        numericalGuarantee? := some {
          kinds := [.exactness]
          statement :=
            "Every successfully decoded element is scaled exactly by power-of-two exponent addition." } }
    ]
  nonclaims :=
    [ "the Array length satisfies a particular MX block-size requirement"
    , "a scale-selection, saturation, or quantization policy is implemented by BlockCode.decode?"
    , "accelerator instructions or packed-memory layouts are equivalent to this structure"
    ]

elab_rules : command
  | `(#float_info%$tk $type:term) =>
      FloatLib.Floats.ExecFloat.FloatInfo.Command.withElaboratedType
          type fun typeExpr => do
        match ←
            unfoldUntilApp? ``FloatLib.Floats.Formats.OCP.MX.BlockCode 1 typeExpr with
        | some family =>
            let elementIdentity ← blockElementIdentity family.getAppArgs[0]!
            logInfoAt tk <| ←
              Inspection.renderProfile (blockProfile elementIdentity) typeExpr .none
        | none =>
            let some _ ←
                unfoldUntilApp? ``FloatLib.Floats.Formats.OCP.MX.E8M0 0 typeExpr
              | throwUnsupportedSyntax
            logInfoAt tk <| ← Inspection.renderProfile profile typeExpr .none

end FloatLib.Floats.Formats.OCP.MX.E8M0.FloatInfo.Command
