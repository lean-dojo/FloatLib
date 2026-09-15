/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Storage.Family.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Model.NumericalSystem

/-!
# Configured binary-family conversion proofs

The configured runtime/model conversions are mutual inverses. Their injectivity and
`FormatSemantics` instance are consequences of the codec laws, independent of the chosen carrier.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Configured

open FloatLib.Numerics
namespace Family

variable {format : FloatFormat} {plan : StoragePlan format} {code : Type}
    [codec : FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]
/-- Decoding immediately after packing through a configured codec is lossless. -/
@[simp, grind =] theorem toModel_ofModel (value : Model format) :
    toModel (plan := plan) (code := code)
      (ofModel (plan := plan) (code := code) value) = value :=
  FloatLib.Floats.ExecFloat.ModelCodec.decode_encode
    (F := Family format code plan) (plan := plan) value

/-- Packing immediately after decoding a configured value is lossless. -/
@[simp, grind =] theorem ofModel_toModel
    (value : FloatLib.Floats.ExecFloat (Family format code plan)) :
    ofModel (code := code) (toModel (code := code) value) = value :=
  FloatLib.Floats.ExecFloat.ModelCodec.encode_decode
    (plan := plan) value

/-- Model decoding is injective because packing is its inverse. -/
theorem toModel_injective
    {left right : FloatLib.Floats.ExecFloat (Family format code plan)}
    (equality : toModel (code := code) left = toModel (code := code) right) :
    left = right :=
  FloatLib.Floats.ExecFloat.ModelCodec.decode_injective
    (plan := plan) equality

noncomputable instance :
    FormatSemantics (Family format code plan) where
  denote bits := Model.toNumericalValue (codec.toModel bits)

end Family

end FloatLib.Floats.Formats.BinaryInterchange.Configured
