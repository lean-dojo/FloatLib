/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import Lean.Elab.Command
public import FloatLib.Floats.Formats.BinaryInterchange.Format.Catalog
public import FloatLib.Floats.Formats.OCP.MX.E8M0.Semantics
public import FloatLib.Tactic.FloatInfo

/-!
# Inspection report for OCP E8M0

`#float_info` for the raw E8M0 scale is registered here, in an optional meta module. Executable
decoding lives in `Core` and `Semantics`, so a client that only runs scales never loads the report
renderer.
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
    , ⟨"backend proof", "successful scale decoding refines exact dyadic scaling"⟩
    ]
  specializedOperations :=
    [ ⟨"exponent? / toDyadic?", "checked exact decoding; the sole NaN code returns none"⟩
    , ⟨"ofExponent? / ofExponentSaturating",
        "explicit checked or clamped construction from an unbiased exponent"⟩
    , ⟨"scaleDyadic?", "checked exact power-of-two scaling by dyadic exponent addition"⟩
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
          , ``FloatLib.Floats.Formats.OCP.MX.E8M0.map_toRat_scaleDyadic?
          , ``FloatLib.Floats.Formats.OCP.MX.E8M0.toRat_scaledValue_of_toDyadic?_eq_some
          , ``FloatLib.Floats.Formats.OCP.MX.E8M0.toRat_of_toDyadic?_eq_some
          ]
        applicability := .verifiedForType
        scope := "finite E8M0 scale and exact dyadic inputs"
        numericalGuarantee? := some {
          kinds := [.exactness]
          statement :=
            "Applying a finite E8M0 scale is exact dyadic exponent addition with zero scaling \
              error." } }
    ]
  nonclaims :=
    [ "E8M0 is an ordinary sign/exponent/fraction floating-point format"
    , "E8M0 represents zero or infinity"
    , "a block scale-selection policy or accelerator instruction equivalence is proved"
    ]

elab_rules : command
  | `(#float_info%$tk $type:term) =>
      FloatLib.Floats.ExecFloat.FloatInfo.Command.withElaboratedType
          type fun typeExpr => do
        let some _ ←
            unfoldUntilApp? ``FloatLib.Floats.Formats.OCP.MX.E8M0 0 typeExpr
          | throwUnsupportedSyntax
        logInfoAt tk <| ← Inspection.renderProfile profile typeExpr .none

end FloatLib.Floats.Formats.OCP.MX.E8M0.FloatInfo.Command
