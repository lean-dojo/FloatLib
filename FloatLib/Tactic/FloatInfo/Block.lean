/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import Lean.Elab.Command
public import FloatLib.Floats.Formats.Block.CodedDot
public import FloatLib.Floats.Formats.Block.Configured
public import FloatLib.Numerics.Quantization.Block.Transpose
public import FloatLib.Tactic.FloatInfo

/-!
# Inspection for block-scaled tensors

On a stored tensor `Block.Tensor F` and on its configured carrier `ExecFloat.Block F`,
`#float_info` reports the storage, the exact decoding rule, the quantizer and the theorems of the
general block theory that apply to every coded format `F`. For `sharedScale`, the report also
describes its integer storage and the nearest-even theorems for a supplied exponent.

The module is meta-only, so tensor runtime code never imports command elaboration.
-/

public meta section

namespace FloatLib.Floats.Formats.Block.FloatInfo.Command

open Lean Elab Command Meta
open FloatLib.Floats.ExecFloat

/-- The report shared by the stored tensor and its configured carrier. -/
meta def profile : FormatProfile where
  family := "block-scaled tensor"
  standard :=
    "general block-scaled format; OCP MX 1.0, NVFP4 and shared-scale blocks are instances"
  representation :=
    [ ⟨"storage", "one element code per position and, for each scale level, one code per group"⟩
    , ⟨"position value", "element value times the scales of its groups"⟩
    , ⟨"levels", "zero or more, outermost first; the last is the block scale"⟩
    , ⟨"formats", "any element codec and any scale codec per level"⟩
    ]
  values :=
    [ ⟨"finite position", "exact signed rational: element times scales, with no rounding"⟩
    , ⟨"scale with no finite value", "the position is NaN, whatever its element"⟩
    , ⟨"element infinity or NaN", "kept under finite scales"⟩
    ]
  rounding :=
    [ ⟨"elements", "one rounding of the exact scaled input by the element codec"⟩
    , ⟨"scales", "each level's rule selects an ideal scale, stored rounded by its codec"⟩
    , ⟨"overflow", "the element codec's saturation or overflow policy"⟩
    ]
  execution :=
    [ ⟨"carrier", "Tensor with one function of codes per level and one for the elements"⟩
    , ⟨"dispatch", "exact rational scale selection and element encoding"⟩
    , ⟨"backend proof", "stored values equal the values of the block theory without codes"⟩
    ]
  specializedOperations :=
    [ ⟨"CodedFormat.quantize", "scale selection and one element rounding per position"⟩
    , ⟨"Tensor.decode", "exact decoding that keeps the class of every position"⟩
    , ⟨"OCP.MX.Dot", "exact accumulation and one rounding into a binary descriptor"⟩
    ]
  theoremSurfaces :=
    [ { topic := "quantization"
        declarations :=
          [ ``FloatLib.Floats.Formats.Block.CodedFormat.value_quantize
          , ``FloatLib.Floats.Formats.Block.CodedFormat.scale_quantize
          , ``FloatLib.Floats.Formats.Block.CodedFormat.elements_quantize
          , ``FloatLib.Floats.Formats.Block.Format.reconstruct_eq
          , ``FloatLib.Floats.Formats.Block.Format.abs_reconstruct_sub_le
          ]
        applicability := .verifiedForType
        scope := "every element codec, scale codec, level structure and selection rule"
        numericalGuarantee? := some {
          kinds := [.rounding]
          statement :=
            "Each stored value is one rounding of the input in the element format scaled by " ++
              "the position's total scale." } }
    , { topic := "exact decoding"
        declarations :=
          [ ``FloatLib.Floats.Formats.Block.Tensor.decode_finite
          , ``FloatLib.Floats.Formats.Block.Tensor.decode_of_not_isFinite
          , ``FloatLib.Floats.Formats.Block.Tensor.decode_infinity
          , ``FloatLib.Floats.Formats.Block.Tensor.decode_exceptional
          , ``FloatLib.Floats.Formats.Block.Tensor.value_of_decode
          , ``FloatLib.Floats.Formats.Block.blockScaled_tensor
          ]
        applicability := .verifiedForType
        scope := "every stored tensor"
        numericalGuarantee? := some {
          kinds := [.exactness]
          statement :=
            "A finite position decodes to its element value times its scales, with no rounding." } }
    , { topic := "flush to zero, transposition and dot products"
        declarations :=
          [ ``FloatLib.Floats.Formats.Block.Format.reconstruct_eq_zero_iff_abs_le
          , ``FloatLib.Floats.Formats.Block.Format.reconstruct_relabel
          , ``FloatLib.Floats.Formats.Block.Tensor.dotExact_finite
          , ``FloatLib.Floats.Formats.Block.Tensor.abs_toReal_Dot_sub_le
          , ``FloatLib.Floats.Formats.Block.Tensor.sum_value_mul_value
          ]
        applicability :=
          .conditional "the stated premises on the element format, the levels and the result"
        scope := "every coded format that meets the premises" }
    ]
  nonclaims :=
    [ "the scalar six-operation `ExecFloat` API applies to tensors"
    , "a packed memory layout or an accelerator instruction is modelled"
    , "scale arithmetic in a finite working precision is modelled; scales and scaled inputs " ++
        "are exact rationals"
    ]

/-- Storage and contextual quantization for integer significands with one binary exponent. -/
meta def sharedScaleProfile (positions : String) : FormatProfile :=
  { profile with
    family := "contextual shared-scale block"
    standard := "unbounded mathematical shared-scale format; no bounded MX encoding claimed"
    representation :=
      [ ⟨"storage", "one Int exponent and one Int significand per position"⟩
      , ⟨"positions", positions⟩
      , ⟨"shared radix", "2"⟩
      , ⟨"position value", "significand × 2^sharedExponent"⟩
      , ⟨"field widths", "unbounded in this mathematical core"⟩ ]
    values :=
      [ ⟨"finite position", "exact rational value"⟩
      , ⟨"signed zero", "no; integer significands have one zero"⟩
      , ⟨"infinity", "no"⟩
      , ⟨"NaN", "no"⟩ ]
    rounding :=
      [ ⟨"elements", "nearest-even integer rounding after exact division by the scale"⟩
      , ⟨"sharedExponent policy", "the caller supplies the stored binary exponent explicitly"⟩
      , ⟨"overflow", "none; exponent and significands are unbounded"⟩ ]
    execution :=
      [ ⟨"carrier", "Tensor with one integer exponent and an integer function on positions"⟩
      , ⟨"dispatch", "exact rational nearest-even rounding at each position"⟩
      , ⟨"backend proof", "stored exponent, significands and exact values meet their formulas"⟩ ]
    specializedOperations :=
      [ ⟨"CodedFormat.quantize with sharedExponent",
          "nearest-even quantization at the caller-supplied binary exponent"⟩
      , ⟨"Tensor.decode", "exact finite rational decoding at every position"⟩ ]
    theoremSurfaces := profile.theoremSurfaces ++
      [ { topic := "contextual nearest-even quantization"
          declarations :=
            [ ``FloatLib.Floats.Formats.Block.sharedScale_code
            , ``FloatLib.Floats.Formats.Block.sharedScale_elements
            , ``FloatLib.Floats.Formats.Block.sharedScale_value ]
          applicability := .conditional "the scale-selection policy is sharedExponent"
          scope := "every supplied exponent, input and position"
          numericalGuarantee? := some {
            kinds := [.rounding]
            statement :=
              "Each position is nearest-even rounded to the integer grid selected by the " ++
                "caller's shared exponent." } } ]
    nonclaims :=
      [ "a bounded MX element code, reserved scale encoding, or accelerator layout is implemented"
      , "an arbitrary scale-selection policy equals the explicit sharedExponent policy"
      , "the scalar six-operation ExecFloat API applies to tensors"
      , "NaN, infinity, saturation, or per-position status flags are stored" ] }

/-- Select the storage facts visible in the coded format, for either tensor carrier. -/
private meta def profileFor (format : Expr) : MetaM FormatProfile := do
  let some arguments ← unfoldUntilAppArgs?
      ``FloatLib.Floats.Formats.Block.sharedScale 1 format
    | return profile
  return sharedScaleProfile (toString (← ppExpr arguments[0]!))

elab_rules : command
  | `(#float_info%$tk $type:term) =>
      FloatLib.Floats.ExecFloat.FloatInfo.Command.withElaboratedType
          type fun typeExpr => do
        let some arguments ←
            unfoldUntilAppArgs? ``FloatLib.Floats.Formats.Block.Tensor 3 typeExpr
          | throwUnsupportedSyntax
        logInfoAt tk <| ← Inspection.renderProfile (← profileFor arguments[2]!) typeExpr .none

elab_rules : command
  | `(#float_info%$tk $type:term) =>
      FloatLib.Floats.ExecFloat.FloatInfo.Command.withExecFamilyApplication
          type ``FloatLib.Floats.Formats.Block.Family 3
          fun typeExpr _family arguments => do
        let selected ← profileFor arguments[2]!
        let configured : TheoremSurface :=
          { topic := "configured conversion"
            declarations :=
              [ ``FloatLib.Floats.ExecFloat.Block.value_quantize
              , ``FloatLib.Floats.ExecFloat.Block.Conversion.implements_run
              , ``FloatLib.Floats.ExecFloat.Block.toCode_ofCode
              , ``FloatLib.Floats.ExecFloat.Block.ofCode_toCode
              ]
            definitions :=
              [ ``FloatLib.Floats.ExecFloat.Block.toCode
              , ``FloatLib.Floats.ExecFloat.Block.ofCode ]
            applicability := .verifiedForType
            scope :=
              "every tensor; `toCode` and `ofCode` are inverse, so the theorems about the " ++
              "stored tensor apply through `toCode`" }
        let baseProfile : FormatProfile :=
          { selected with
            execution :=
              [ ⟨"carrier", "ExecFloat over one whole stored tensor"⟩
              , ⟨"dispatch", "exact rational scale selection and element encoding"⟩ ]
            theoremSurfaces := [configured]
            relatedTheorems :=
              [ { type := ``FloatLib.Floats.Formats.Block.Tensor
                  embedding := ``FloatLib.Floats.ExecFloat.Block.toCode
                  surfaces := selected.theoremSurfaces } ] }
        logInfoAt tk <| ← Inspection.renderProfile baseProfile typeExpr .none

end FloatLib.Floats.Formats.Block.FloatInfo.Command
