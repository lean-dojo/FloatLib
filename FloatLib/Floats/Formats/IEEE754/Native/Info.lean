/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.IEEE754.Native.AddSub
public import FloatLib.Floats.Formats.IEEE754.Native.Integer
public import FloatLib.Floats.Formats.IEEE754.Native.Sqrt
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Core.Proof
import FloatLib.Floats.Formats.BinaryInterchange.Configured.NativeFPU.Proof
public import FloatLib.Floats.ExecFloat.Info

/-!
# Inspection of Lean's native runtime floats

`#float_info` reports native storage, arithmetic, and conversions for Lean's `Float32` and
binary64 `Float`. It lists the Lean 4.34 logical-model bridges with their input conditions and
the certified software refinements for their configured counterparts. Execution of native
arithmetic, including explicit calls through `Configured.NativeFPU.Unchecked`, also depends on
Lean's compiler, runtime, and host hardware.
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
        , ``Binary.toFloat32_ofFloat32
        , ``Binary.toModel_ofFloat32_nan
        , ``Binary.toModel_ofFloat32_inf
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
        , ``Binary.toFloat_ofFloat
        , ``Binary.toModel_ofFloat_nan
        , ``Binary.toModel_ofFloat_inf
        , ``Binary.nativeFloatExactDecoder_run ]
      , [ ``Backend.wordAdd_eq_spec
        , ``Backend.wordSub_eq_spec
        , ``Backend.wordMul_eq_spec
        , ``Backend.wordDiv_eq_spec
        , ``Backend.wordSqrt_eq_spec
        , ``NativeFPU.softwareFma64_eq_spec ] )
  let width := if bits = 32 then 32 else 64
  let integerConversions := if bits = 32 then
    [ ``Binary.toModel_ofFloat32_ofNat
    , ``Binary.toModel_ofFloat32_intToFloat32
    , ``Binary.toModel_ofFloat32_int64ToFloat32
    , ``Binary.float32ToInt8_eq_floatToIntSaturating ]
    else
    [ ``Binary.toModel_ofFloat_ofNat
    , ``Binary.toModel_ofFloat_intToFloat
    , ``Binary.toModel_ofFloat_int64ToFloat
    , ``Binary.floatToInt8_eq_floatToIntSaturating ]
  let addSub := if bits = 32 then
    [``Binary.ofFloat32_add_of_isFinite, ``Binary.ofFloat32_sub_of_isFinite]
    else [``Binary.ofFloat_add_of_isFinite, ``Binary.ofFloat_sub_of_isFinite]
  let sqrt := if bits = 32 then [``Binary.toFloat32_sqrt] else [``Binary.toFloat_sqrt]
  [ { topic := s!"native binary{width} conversion boundary"
      declarations := conversions
      applicability := .verifiedForType
      scope :=
        s!"every Lean {name} value; direct configured-to-native round trips follow Lean's logical canonical-NaN model" }
  , { topic := s!"native binary{width} integer conversion models"
      declarations := integerConversions
      applicability := .verifiedForType
      scope :=
        "unbounded constructors and representative signed casts: integers round to nearest-even; float-to-integer casts truncate, saturate, and map NaN to zero" }
  , { topic := s!"native binary{width} addition and subtraction models"
      declarations := addSub
      applicability := .verifiedForType
      scope :=
        "both operands finite, including signed zeros; the complete result word agrees, including overflow" }
  , { topic := s!"native binary{width} square-root model"
      declarations := sqrt
      applicability := .verifiedForType
      scope :=
        "every input word; export canonicalizes NaNs and preserves all other result bits" }
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
        "nearest-even in Lean's logical model; compiled calls use the platform runtime"⟩
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
        "conversion and selected arithmetic model equations are proved; native compilation and hardware remain external"⟩
    ]
  theoremSurfaces := theoremSurfaces bits
  nonclaims :=
    [ "every native arithmetic operation has an unconditional FloatLib model bridge"
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
