/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Model.ExactNumericalSystem
public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.Core.Runtime

/-!
# Static-byte exact conversion runtime

Nominal families backed by `StaticByte.Family` decode through `SignedRat` and use the shared binary
conversion policy and numerical contract.

The adapter uses the family descriptor and byte codec, independently of its arithmetic kernels.
Typeclass installation lives in `Conversion.Instances`; correctness equations live in
`Conversion.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.StaticByte
namespace Conversion

open FloatLib.Numerics

universe u

variable {F : Type u} [Family F]

/-- Decode a static-byte value into the signed-rational domain, keeping the sign of zero. -/
@[inline] def decode (value : FloatLib.Floats.ExecFloat F) : NumericalValue SignedRat :=
  ((Model.exactNumericalSystem (Family.format (F := F))).denote (toModel value)).map
    SignedRat.ofDyadic

/-- Pack a rounded binary model into the nominal family's direct byte carrier. -/
@[always_inline, inline] def pack
    (value : ModelValue (Family.format (F := F))) :
    FloatLib.Floats.ExecFloat F :=
  ofModel value

/-- Quantize one finite signed rational into the nominal static-byte destination. -/
@[inline] def quantizeFinite
    (context : FloatLib.Floats.ExecFloat.Binary.Conversion.Context) (exact : SignedRat) :
    FloatLib.Floats.ExecFloat.ConversionOutcome (FloatLib.Floats.ExecFloat F) :=
  FloatLib.Floats.ExecFloat.Binary.Conversion.quantizeFiniteWith pack context exact

/-- Apply the explicit infinity policy to a nominal static-byte destination. -/
@[inline] def quantizeInfinity
    (context : FloatLib.Floats.ExecFloat.Binary.Conversion.Context) (negative : Bool) :
    FloatLib.Floats.ExecFloat.ConversionOutcome (FloatLib.Floats.ExecFloat F) :=
  FloatLib.Floats.ExecFloat.Binary.Conversion.quantizeInfinityWith pack context negative

/-- Apply the explicit exceptional-value policy to a nominal static-byte destination. -/
@[inline] def quantizeExceptional
    (context : FloatLib.Floats.ExecFloat.Binary.Conversion.Context)
    (exceptional : ExceptionalValue) :
    FloatLib.Floats.ExecFloat.ConversionOutcome (FloatLib.Floats.ExecFloat F) :=
  FloatLib.Floats.ExecFloat.Binary.Conversion.quantizeExceptionalWith
    pack context exceptional

/-- Reference conversion for every complete exact observation. -/
@[inline] def run
    (context : FloatLib.Floats.ExecFloat.Binary.Conversion.Context) :
    NumericalValue SignedRat →
      FloatLib.Floats.ExecFloat.ConversionOutcome (FloatLib.Floats.ExecFloat F) :=
  FloatLib.Floats.ExecFloat.Binary.Conversion.runWith pack context

/-- Shared binary outcome and nearest-value contract, transported through the static-byte codec. -/
def spec :
    Quantization.Spec FloatLib.Floats.ExecFloat.Binary.Conversion.Context
      (NumericalValue SignedRat)
      (FloatLib.Floats.ExecFloat.ConversionOutcome (FloatLib.Floats.ExecFloat F)) :=
  FloatLib.Floats.ExecFloat.Binary.Conversion.specWith pack

/-- Every nominal static-byte binary source decodes exactly through `SignedRat`. -/
instance exactDecoder :
    FloatLib.Floats.ExecFloat.ExactDecoder (FloatLib.Floats.ExecFloat F) SignedRat where
  decode := decode

end Conversion
end FloatLib.Floats.Formats.BinaryInterchange.StaticByte
