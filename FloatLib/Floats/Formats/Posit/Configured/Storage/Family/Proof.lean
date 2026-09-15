/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.Storage.Family.Runtime
public import FloatLib.Floats.Formats.Posit.Semantics.Exact.Runtime
public import FloatLib.Floats.Formats.Posit.Configured.Storage.Codecs

/-!
# Configured posit-family conversion proofs

The configured runtime/model conversions are mutual inverses. The same codec laws yield
injectivity, ordinary numerical semantics, and format-indexed exact decoding.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured

open FloatLib.Numerics

namespace Family

variable {format : Format} {plan : StoragePlan format} {code : Type}
    [codec : FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

/--
For the built-in storage family, codec decoding is exactly the constructor-indexed
`Code.toModel` function.
-/
@[simp, grind =] theorem decode_eq_codeToModel
    (value : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    FloatLib.Floats.ExecFloat.ModelCodec.decode
        (F := Family format (Code plan) plan)
        (Model := Model format) (plan := plan)
        (codec := codecForPlan format plan) value =
      Code.toModel value.raw := by
  cases plan <;> rfl

/-- Decoding immediately after packing through a configured posit codec is lossless. -/
@[simp, grind =] theorem toModel_ofModel (value : Model format) :
    toModel (plan := plan) (code := code)
      (ofModel (plan := plan) (code := code) value) = value :=
  FloatLib.Floats.ExecFloat.ModelCodec.decode_encode
    (F := Family format code plan) (plan := plan) value

/-- Packing immediately after decoding a configured posit is lossless. -/
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

instance : FormatSemantics (Family format code plan) where
  denote bits := Model.decode (codec.toModel bits)

instance : HasExactSemantics (Family format code plan) where
  exactSemantics :=
    { Exact := Model.ExactValue format
      decode := fun bits => Model.decodeExact (codec.toModel bits)
      forget := Model.ExactValue.forget
      forget_decode := by
        intro bits
        change
          Model.ExactValue.forget (Model.decodeExact (codec.toModel bits)) =
            Model.decode (codec.toModel bits)
        rfl }

end Family

end FloatLib.Floats.Formats.Posit.Configured
