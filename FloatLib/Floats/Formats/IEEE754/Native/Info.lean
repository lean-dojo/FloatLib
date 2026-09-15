/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.IEEE754.Native
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Core.Proof
import FloatLib.Floats.Formats.BinaryInterchange.Configured.NativeFPU.Proof
public import FloatLib.Floats.ExecFloat.Info

/-!
# Inspection of Lean's native runtime floats

`#float_info` reports native storage, arithmetic, and conversions for Lean's `Float32` and
binary64 `Float`. It lists conversion equations and certified software refinements for their
configured software counterparts. Correctness of Lean's native arithmetic, including explicit
calls through `Configured.NativeFPU.Unchecked`, depends on Lean's compiler, runtime, and host
hardware.
-/

public meta section

namespace FloatLib.Floats.Formats.IEEE754.Native.FloatInfo

open FloatLib.Floats.ExecFloat
open FloatLib.Floats.Formats.BinaryInterchange.Configured

/-- Conversion and arithmetic declarations for Lean's two native float types. -/
private meta def theoremSurfaces (bits : Nat) : List TheoremSurface :=
  let (name, conversions, arithmetic) : String × List Lean.Name × List Lean.Name :=
    if bits = 32 then
      ( "Float32"
      , [ ``Binary.toBits32_ofFloat32
        , ``Binary.toModel_toFloat32
        , ``Binary.ofFloat32_toFloat32
        , ``Binary.nativeFloat32ExactDecoder_run ]
      , [ ``Backend.wordAdd_eq_spec
        , ``Backend.wordSub_eq_spec
        , ``Backend.wordMul_eq_spec
        , ``Backend.wordDiv_eq_spec
        , ``Backend.wordSqrt_eq_spec
        , ``NativeFPU.softwareFma32_eq_spec ] )
    else
      ( "Float"
      , [ ``Binary.toBits64_ofFloat
        , ``Binary.toModel_toFloat
        , ``Binary.ofFloat_toFloat
        , ``Binary.nativeFloatExactDecoder_run ]
      , [ ``Backend.wordAdd_eq_spec
        , ``Backend.wordSub_eq_spec
        , ``Backend.wordMul_eq_spec
        , ``Backend.wordDiv_eq_spec
        , ``Backend.wordSqrt_eq_spec
        , ``NativeFPU.softwareFma64_eq_spec ] )
  let width := if bits = 32 then 32 else 64
  [ { topic := s!"native binary{width} conversion boundary"
      declarations := conversions
      applicability := .verifiedForType
      scope :=
        s!"every Lean {name} value; direct configured-to-native round trips follow Lean's logical canonical-NaN model" }
  , { topic := s!"configured binary{width} certified software arithmetic"
      declarations := arithmetic
      applicability := .verifiedForType
      scope :=
        s!"all configured binary{width} values; compiled host equivalence is not asserted" }
  ]

/-- Storage, operations, and conversion theorems for a Lean native float type. -/
meta def profile (bits exponentBits fractionBits : Nat) (name storage : String) :
    FormatProfile where
  family := s!"Lean native {name}"
  standard := s!"IEEE 754 binary{bits} runtime format through Lean's native float API"
  declarationPrefix := "FloatLib.Floats.ExecFloat.Binary."
  representation :=
    [ ⟨"Lean type", name⟩
    , ⟨"runtime storage", storage⟩
    , ⟨"total bits", toString bits⟩
    , ⟨"sign bits", "1"⟩
    , ⟨"exponent bits", toString exponentBits⟩
    , ⟨"stored fraction bits", toString fractionBits⟩
    ]
  values :=
    [ ⟨"finite numbers", "IEEE binary finite values, including subnormals"⟩
    , ⟨"signed zero", "positive and negative zero"⟩
    , ⟨"infinities", "positive and negative infinity"⟩
    , ⟨"NaNs", "IEEE NaN values; Lean's logical model canonicalizes payloads at model boundaries"⟩
    ]
  rounding :=
    [ ⟨"native arithmetic",
        "runtime/compiler implementation of the fixed IEEE width; not a FloatLib refinement theorem"⟩
    , ⟨"conversion into ExecFloat",
        "exact interchange decoding followed by explicit destination rounding only when another type is requested"⟩
    ]
  execution :=
    [ ⟨"carrier", storage⟩
    , ⟨"compiled operations",
        "Lean native primitives lowered through the compiler and platform floating-point runtime"⟩
    , ⟨"interchange boundary",
        s!"public {name}.toBits and {name}.ofBits operations"⟩
    , ⟨"proof boundary",
        "FloatLib proves its conversion-side model equations; native arithmetic correctness is trusted externally"⟩
    ]
  theoremSurfaces := theoremSurfaces bits
  nonclaims :=
    [ "native arithmetic is linked to ExecFloat.Spec by a Lean theorem"
    , "NaN payloads are preserved through native-value conversion"
    , "this runtime type is a FloatLib destination quantizer or participates in implicit promotion"
    , "platform rounding-mode state, exception flags, or compiler lowering are verified by this report"
    ]

end FloatLib.Floats.Formats.IEEE754.Native.FloatInfo

namespace FloatLib.Floats.Formats.IEEE754.Native.FloatInfo.Command

open Lean Elab Command Meta
open FloatLib.Floats.ExecFloat

elab_rules : command
  | `(#float_info%$tk $type:term) =>
      FloatLib.Floats.ExecFloat.FloatInfo.Command.withElaboratedType
          type fun typeExpr => do
        let typeExpr ← withTransparency .reducible <| whnf typeExpr
        let profile ←
          if typeExpr.isConstOf ``Float32 then
            pure <| FloatInfo.profile 32 8 23 "Float32" "native 32-bit floating-point word"
          else if typeExpr.isConstOf ``Float then
            pure <| FloatInfo.profile 64 11 52 "Float" "native 64-bit floating-point word"
          else
            throwUnsupportedSyntax
        logInfoAt tk <| ← Inspection.renderProfile profile typeExpr .none

end FloatLib.Floats.Formats.IEEE754.Native.FloatInfo.Command
