/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.Core

/-!
# Configured binary-interchange conversion runtime

This adapter supplies the configured carrier's `ofModel` bridge to the representation-independent
binary conversion policy. Exact rounding happens before packing, so storage and backend selection
cannot change conversion semantics. The exact domain is `SignedRat`, which carries the sign of
zero to the quantizer; the destination's encoding policy determines whether that sign is retained.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics
open FloatLib.Floats.Formats.BinaryInterchange

namespace ExecFloat.Binary
namespace Conversion

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

/-- Pack a rounded binary model through the configured destination codec. -/
@[always_inline, inline] def configuredPack (value : Model format) :
    FloatLib.Floats.ExecFloat (Configured.Family format code plan) :=
  ExecFloat.Binary.ofModel value

/-- Quantize one finite signed rational into the configured binary destination. -/
@[inline] def quantizeFinite (context : Context) (exact : SignedRat) :
    FloatLib.Floats.ExecFloat.ConversionOutcome
      (FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :=
  quantizeFiniteWith configuredPack context exact

/-- Apply the explicit exceptional-value policy to a configured binary destination. -/
@[inline] def quantizeExceptional (context : Context) (exceptional : ExceptionalValue) :
    FloatLib.Floats.ExecFloat.ConversionOutcome
      (FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :=
  quantizeExceptionalWith configuredPack context exceptional

/-- Apply the explicit infinity policy to a configured binary destination. -/
@[inline] def quantizeInfinity (context : Context) (negative : Bool) :
    FloatLib.Floats.ExecFloat.ConversionOutcome
      (FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :=
  quantizeInfinityWith configuredPack context negative

/-- Reference conversion for every complete exact observation. -/
@[inline] def run (context : Context) :
    NumericalValue SignedRat →
      FloatLib.Floats.ExecFloat.ConversionOutcome
        (FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :=
  runWith configuredPack context

/--
Complete configured outcome with the default IEEE nearest-value contract.

`Binary.Conversion.specWith` supplies the independent finite-denotation clause and retains the
complete word, status, and explicit policy behavior.
-/
def spec :
    Quantization.Spec Context (NumericalValue SignedRat)
      (FloatLib.Floats.ExecFloat.ConversionOutcome
        (FloatLib.Floats.ExecFloat (Configured.Family format code plan))) :=
  specWith configuredPack

/-- Configured binary decoding selects the signed-rational exact domain, keeping signed zero. -/
instance exactDecoder :
    FloatLib.Floats.ExecFloat.ExactDecoder
      (FloatLib.Floats.ExecFloat (Configured.Family format code plan)) SignedRat where
  decode := ExecFloat.Binary.decode

end Conversion
end ExecFloat.Binary
end FloatLib.Floats
