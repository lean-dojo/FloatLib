/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Conversion.Proof

/-!
# Configured binary-interchange conversion instances

Configured binary-interchange destinations support signed-rational quantization with finite,
infinity, and exceptional policies, and conversions into them accept all six rounding directions
as `(mode := ...)`.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics
open FloatLib.Floats.Formats.BinaryInterchange

universe u v

namespace ExecFloat.Binary
namespace Conversion

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

/-- Every configured binary destination supports policy-aware signed-rational quantization. -/
instance quantizer :
    FloatLib.Floats.ExecFloat.Quantizer
      (FloatLib.Floats.ExecFloat (Configured.Family format code plan)) SignedRat where
  Context := Context
  run := run
  spec := spec
  correct := implements_run
  addExact := addExact
  subExact := subExact

/-- Context-free conversion uses `Context.default`. -/
instance defaultQuantizer :
    FloatLib.Floats.ExecFloat.DefaultQuantizer
      (FloatLib.Floats.ExecFloat (Configured.Family format code plan)) SignedRat where
  defaultContext := Context.default

/-- Conversions into a binary destination take an `IEEERoundingMode`, nearest-even by default. -/
instance roundingModes :
    FloatLib.Floats.ExecFloat.RoundingModes
      (FloatLib.Floats.ExecFloat (Configured.Family format code plan)) Model.IEEERoundingMode where
  default := .nearest

/--
A conversion's `(mode := m)` selects `Context.withRounding m`, and `.nearest` the canonical
`Context.default` that it equals.
-/
@[inline] instance modeContext (mode : Model.IEEERoundingMode) :
    FloatLib.Floats.ExecFloat.ModeContext
      (FloatLib.Floats.ExecFloat (Configured.Family format code plan)) SignedRat mode where
  context :=
    match mode with
    | .nearest => Context.default
    | mode => Context.withRounding mode

/-- The context a binary conversion's `(mode := m)` selects is `Context.withRounding m`. -/
@[simp] theorem context_modeContext (mode : Model.IEEERoundingMode) :
    (FloatLib.Floats.ExecFloat.ModeContext.context :
        FloatLib.Floats.ExecFloat.ContextFor
          (FloatLib.Floats.ExecFloat (Configured.Family format code plan)) mode) =
      Context.withRounding mode := by
  cases mode <;> rfl

/--
A cast whose source decodes to a finite exact value is the canonical nearest-even rounding of
that value in the destination format.

The hypothesis names the decoded value, so the theorem applies to any source with an exact decoder
and an embedding into `SignedRat`. For conventional IEEE destinations and finite results,
`Model.toReal_roundRatScaled_eq_roundAt` supplies the corresponding real-number meaning.
-/
theorem cast_eq_roundRat_of_decodeTo_eq_finite {F : Type u} [EncodedFormat F]
    {SourceExact : Type v}
    [FloatLib.Floats.ExecFloat.ExactDecoder (FloatLib.Floats.ExecFloat F) SourceExact]
    [FloatLib.Floats.ExecFloat.ExactMap SourceExact SignedRat]
    (value : FloatLib.Floats.ExecFloat F) (exact : SignedRat)
    (hdecode :
      FloatLib.Floats.ExecFloat.ExactDecoder.decodeTo (TargetExact := SignedRat) value =
        .finite exact) :
    FloatLib.Floats.ExecFloat.cast
        (target := FloatLib.Floats.ExecFloat (Configured.Family format code plan)) value =
      .success
        (ofModel (Model.roundRat format exact.negative exact.value.num.natAbs exact.value.den))
        (finiteStatus Context.default exact.value
          (Model.roundRat format exact.negative exact.value.num.natAbs exact.value.den)) := by
  change run Context.default (FloatLib.Floats.ExecFloat.ExactDecoder.decodeTo value) = _
  rw [hdecode]
  exact run_default_finite exact

end Conversion
end ExecFloat.Binary
end FloatLib.Floats
