/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Storage.Family.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Model.ExactNumericalSystem
public import FloatLib.Floats.Formats.BinaryInterchange.Model.ExactValue
public import FloatLib.Numerics.Exact.SignedRat

/-!
# Representation interface for configured binary values

A configured binary format chooses its storage plan statically, but numerical programs should not
need separate APIs for byte, word, fixed-limb, and wide carriers. This module exposes one
storage-independent boundary for packing, exact decoding, classification, and special values.

Conversions through the logical `Model` are explicit and exact. The module does not register
arithmetic backends, so representation and conversion code can use configured values without
importing the operation planner or native-width dispatch instances.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.BinaryInterchange

namespace ExecFloat.Binary

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

/--
Decode the statically selected runtime carrier into the exact-width binary proof model.

This boundary does not expose whether the carrier is a byte, machine word, or wide model.
-/
@[always_inline, inline] def toModel
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    Model format :=
  Configured.Family.toModel value

/-- Pack an exact-width binary model into the statically selected runtime carrier. -/
@[always_inline, inline] def ofModel
    (value : Model format) :
    FloatLib.Floats.ExecFloat (Configured.Family format code plan) :=
  Configured.Family.ofModel value

/--
Construct a configured binary value from its complete unsigned interchange word.

Inputs outside the configured width are reduced modulo `2 ^ format.bitWidth`, matching
`Model.ofNatBits`.
-/
@[inline] def ofNatBits (bits : Nat) :
    FloatLib.Floats.ExecFloat (Configured.Family format code plan) :=
  ofModel (Model.ofNatBits bits)

/-- Read the complete configured binary interchange word as an unsigned natural number. -/
@[inline] def toNatBits
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) : Nat :=
  (toModel value).toNatBits

/-- Decode the complete mathematical value, retaining signed zero and NaN metadata. -/
@[inline] def exactValue
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    Model.ExactValue :=
  Model.exactValue (toModel value)

/--
Decode into the exact signed-rational semantic domain used by binary conversion.

Finite values become exact rationals together with their sign bit, so a negative zero decodes to
`SignedRat.negZero` rather than to `0`. Infinities retain their sign, and NaNs carry their
complete encoded word as payload. Use `exactValue` when signaling-NaN metadata is required, or
`toRat?` when only the rational value of a finite number matters.
-/
@[inline] def decode
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    FloatLib.Numerics.NumericalValue FloatLib.Numerics.SignedRat :=
  ((Model.exactNumericalSystem format).denote (toModel value)).map
    FloatLib.Numerics.SignedRat.ofDyadic

/-- Exact rational value of a finite configured binary number, or `none` for NaN and infinity. -/
@[inline] def toRat?
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) : Option Rat :=
  Model.toRat? (toModel value)

/-- Whether the stored sign bit is set. -/
@[inline] def signBit
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) : Bool :=
  Model.signBit (toModel value)

/-- Whether the value is a NaN under its configured encoding policy. -/
@[inline] def isNaN
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) : Bool :=
  Model.isNaN (toModel value)

/-- Whether the value is a quiet NaN under its configured encoding policy. -/
@[inline] def isQuietNaN
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) : Bool :=
  Model.isQNaN (toModel value)

/-- Whether the value is a signaling NaN under its configured encoding policy. -/
@[inline] def isSignalingNaN
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) : Bool :=
  Model.isSNaN (toModel value)

/-- Whether the value is an infinity; finite encodings always return `false`. -/
@[inline] def isInfinite
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) : Bool :=
  Model.isInf (toModel value)

/-- Whether the value denotes a finite number under its configured encoding policy. -/
@[inline] def isFinite
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) : Bool :=
  Model.isFinite (toModel value)

/-- Whether the value is zero under its configured encoding policy. -/
@[inline] def isZero
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) : Bool :=
  Model.isZero (toModel value)

/-- Whether the value is a finite subnormal. -/
@[inline] def isSubnormal
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) : Bool :=
  Model.isSubnormal (toModel value)

/--
Construct zero with the requested sign.

Encodings with one unsigned zero canonicalize a requested negative zero to positive zero.
-/
@[inline] def zero (sign : Bool) :
    FloatLib.Floats.ExecFloat (Configured.Family format code plan) :=
  ofModel (Model.zero format sign)

/--
Construct signed infinity when the configured encoding represents it.

IEEE encodings return `some`; finite-only, maximum-NaN, and FNUZ encodings return `none`.
-/
@[inline] def infinity? (sign : Bool) :
    Option (FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :=
  (Model.infinity? format sign).map ofModel

/--
Construct signed infinity when the configured encoding is statically known to support it.

Calling this constructor for a finite encoding fails during elaboration.
-/
@[inline] def infinity (sign : Bool)
    (_supportsInfinity : format.supportsInfinity = true := by decide) :
    FloatLib.Floats.ExecFloat (Configured.Family format code plan) :=
  ofModel (if sign then Model.negInf format else Model.posInf format)

/--
Construct the encoding's canonical quiet NaN when it has a NaN representation.

IEEE, maximum-NaN, and FNUZ encodings return `some`; fully finite encodings return `none`.
-/
@[inline] def canonicalNaN? :
    Option (FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :=
  (Model.canonicalNaN? format).map ofModel

/--
Construct the canonical quiet NaN when support is statically known.

Fully finite encodings reject this constructor during elaboration.
-/
@[inline] def canonicalNaN
    (_supportsNaN : format.supportsNaN = true := by decide) :
    FloatLib.Floats.ExecFloat (Configured.Family format code plan) :=
  ofModel (Model.invalidResult format)

/-- Construct the finite value of greatest magnitude with the requested sign. -/
@[inline] def maxFinite (sign : Bool) :
    FloatLib.Floats.ExecFloat (Configured.Family format code plan) :=
  ofModel (Model.maxFinite format sign)

end ExecFloat.Binary
end FloatLib.Floats
