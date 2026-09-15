/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Storage.Code.Proof

/-!
# Storage codecs for configured binary formats

Every storage plan uses the same canonical `Code` conversion pair. The plan remains reducible, so
a closed executable format still specializes to its ordinary unboxed carrier.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Configured

/--
The canonical lossless codec for one statically known storage plan.

Keeping the record construction in one place avoids duplicating conversion code and inverse
proofs across the primitive carriers.
-/
abbrev canonicalCodec (format : FloatFormat) (plan : StoragePlan format) :
    FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) (Code plan) where
  toModel := Code.toModel (plan := plan)
  ofModel := Code.ofModel (plan := plan)
  toModel_ofModel := Code.toModel_ofModel (plan := plan)
  ofModel_toModel := Code.ofModel_toModel (plan := plan)

/--
The lossless codec selected by an arbitrary static storage plan.

The match deliberately precedes codec-record construction. Lean's native compiler must see the
selected primitive carrier before compiling the record projections; otherwise a dependent
`UInt8`, `UInt16`, `UInt32`, or `UInt64` result can be assigned the boxed calling convention.
All branches still use the same generic codec definition.
-/
abbrev codecForPlan (format : FloatFormat) (plan : StoragePlan format) :
    FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) (Code plan) :=
  match plan with
  | .byte width_le => canonicalCodec format (.byte width_le)
  | .word16 width_le => canonicalCodec format (.word16 width_le)
  | .word32 width_le => canonicalCodec format (.word32 width_le)
  | .word64 width_le => canonicalCodec format (.word64 width_le)
  | .wide => canonicalCodec format .wide
  | .limbs width_gt => canonicalCodec format (.limbs width_gt)

attribute [instance] codecForPlan

end FloatLib.Floats.Formats.BinaryInterchange.Configured
