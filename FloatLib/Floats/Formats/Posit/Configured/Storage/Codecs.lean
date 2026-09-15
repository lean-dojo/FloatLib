/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.Storage.Code.Proof
public import FloatLib.Floats.ExecFloat.Carrier

/-!
# Storage codecs for configured posits

Every storage plan uses the same canonical `Code` conversion pair. The plan remains reducible, so
a closed configured posit still specializes to its selected primitive, pair, or wide carrier.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured

/--
The canonical lossless codec for one statically known storage plan.

Keeping the record construction in one place avoids duplicating conversion code and inverse
proofs across the primitive, pair, and wide carriers.
-/
abbrev canonicalCodec (format : Format) (plan : StoragePlan format) :
    FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) (Code plan) where
  toModel := Code.toModel (plan := plan)
  ofModel := Code.ofModel (plan := plan)
  toModel_ofModel := Code.toModel_ofModel (plan := plan)
  ofModel_toModel := Code.ofModel_toModel (plan := plan)

/--
The lossless codec selected by an arbitrary static storage plan.

The match precedes codec-record construction so native code generation sees the selected unboxed
carrier before compiling record projections. Every branch still uses the same generic codec.
-/
abbrev codecForPlan (format : Format) (plan : StoragePlan format) :
    FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) (Code plan) :=
  match plan with
  | .byte width_le => canonicalCodec format (.byte width_le)
  | .word16 width_le => canonicalCodec format (.word16 width_le)
  | .word32 width_le => canonicalCodec format (.word32 width_le)
  | .word64 width_le => canonicalCodec format (.word64 width_le)
  | .pair width_le => canonicalCodec format (.pair width_le)
  | .wide => canonicalCodec format .wide

attribute [instance] codecForPlan

end FloatLib.Floats.Formats.Posit.Configured
