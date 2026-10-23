/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Type
public import FloatLib.Floats.Formats.BinaryInterchange.Model.ExactNumericalSystem
public import FloatLib.Floats.Formats.BinaryInterchange.Model.ExactValue
public import FloatLib.Numerics.Exact.SignedRat

/-!
# Representation interface for configured binary values

A configured binary format chooses its storage plan statically, but numerical programs should not
need separate APIs for byte, word, fixed-limb, and wide carriers. This module exposes one
storage-independent boundary for packing, exact decoding, classification, and special values.

`toModel` and `ofModel` convert through the logical `Model` without loss. The module does not
register arithmetic backends, so representation and conversion code can use configured values
without importing the operation planner or native-width dispatch instances.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.BinaryInterchange

namespace ExecFloat.Binary

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  ExecFloat.Binary format.expWidth format.fracWidth format.encoding format.exponentBias
    format.expWidth_ge_two format.fracWidth_pos format.exponentBias_pos
    format.exponentBias_le_maxFinite plan code

/--
Decode the statically selected runtime carrier into the exact-width binary proof model.

This boundary does not expose whether the carrier is a byte, machine word, or wide model.
-/
@[always_inline, inline] def toModel
    (value : Value) :
    Model format :=
  Configured.Family.toModel value

/-- Pack an exact-width binary model into the statically selected runtime carrier. -/
@[always_inline, inline] def ofModel
    (value : Model format) :
    Value :=
  Configured.Family.ofModel value

/--
Construct a configured binary value from its complete unsigned interchange word.

Inputs outside the configured width are reduced modulo `2 ^ format.bitWidth`, matching
`Model.ofNatBits`.
-/
@[inline] def ofNatBits (bits : Nat) :
    Value :=
  ofModel (Model.ofNatBits bits)

/-- Read the complete configured binary interchange word as an unsigned natural number. -/
@[inline] def toNatBits
    (value : Value) : Nat :=
  (toModel value).toNatBits

/-- Decode the complete mathematical value, retaining signed zero and NaN metadata. -/
@[inline] def exactValue
    (value : Value) :
    Model.ExactValue :=
  Model.exactValue (toModel value)

/--
Decode into the exact signed-rational semantic domain used by binary conversion.

Finite values become exact rationals together with their sign bit, so a negative zero decodes to
`SignedRat.negZero` rather than to `0`. Infinities retain their sign, and a NaN carries its
diagnostic payload without the quiet bit, together with its sign bit and signaling class.
Use `toRat?` when only the rational value of a finite number matters.
-/
@[inline] def decode
    (value : Value) :
    FloatLib.Numerics.NumericalValue FloatLib.Numerics.SignedRat :=
  ((Model.exactNumericalSystem format).denote (toModel value)).map
    FloatLib.Numerics.SignedRat.ofDyadic

/-- Exact rational value of a finite configured binary number, or `none` for NaN and infinity. -/
@[inline] def toRat?
    (value : Value) : Option Rat :=
  Model.toRat? (toModel value)

/-- Whether the stored sign bit is set. -/
@[inline] def signBit
    (value : Value) : Bool :=
  Model.signBit (toModel value)

/-- Whether the value is a NaN under its configured encoding policy. -/
@[inline] def isNaN
    (value : Value) : Bool :=
  Model.isNaN (toModel value)

/-- Whether the value is a quiet NaN under its configured encoding policy. -/
@[inline] def isQuietNaN
    (value : Value) : Bool :=
  Model.isQNaN (toModel value)

/-- Whether the value is a signaling NaN under its configured encoding policy. -/
@[inline] def isSignalingNaN
    (value : Value) : Bool :=
  Model.isSNaN (toModel value)

/-- Whether the value is an infinity. Finite encodings always return `false`. -/
@[inline] def isInfinite
    (value : Value) : Bool :=
  Model.isInf (toModel value)

/-- Whether the value denotes a finite number under its configured encoding policy. -/
@[inline] def isFinite
    (value : Value) : Bool :=
  Model.isFinite (toModel value)

/-- Whether the value is zero under its configured encoding policy. -/
@[inline] def isZero
    (value : Value) : Bool :=
  Model.isZero (toModel value)

/-- Whether the value is a finite subnormal. -/
@[inline] def isSubnormal
    (value : Value) : Bool :=
  Model.isSubnormal (toModel value)

/--
Construct zero, positive by default. `(sign := true)` requests negative zero.

Encodings with one unsigned zero canonicalize a requested negative zero to positive zero.
-/
@[inline] def zero (sign : Bool := false) :
    Value :=
  ofModel (Model.zero format sign)

/--
Construct infinity, positive by default, when the configured encoding represents it.

IEEE encodings return `some`, while finite-only, maximum-NaN, and FNUZ encodings return `none`.
-/
@[inline] def infinity? (sign : Bool := false) :
    Option (Value) :=
  (Model.infinity? format sign).map ofModel

/--
Construct infinity, positive by default, when the configured encoding is statically known to
support it.

Calling this constructor for a finite encoding fails during elaboration.
-/
@[inline] def infinity (sign : Bool := false)
    (_supportsInfinity : format.supportsInfinity = true := by decide) :
    Value :=
  ofModel (if sign then Model.negInf format else Model.posInf format)

/--
Construct the encoding's canonical quiet NaN when it has a NaN representation.

IEEE, maximum-NaN, and FNUZ encodings return `some`, while fully finite encodings return `none`.
-/
@[inline] def canonicalNaN? :
    Option (Value) :=
  (Model.canonicalNaN? format).map ofModel

/--
Construct the canonical quiet NaN when support is statically known.

Fully finite encodings reject this constructor during elaboration.
-/
@[inline] def canonicalNaN
    (_supportsNaN : format.supportsNaN = true := by decide) :
    Value :=
  ofModel (Model.invalidResult format)

/-- The finite value of greatest magnitude, positive by default. -/
@[inline] def maxFinite (sign : Bool := false) :
    Value :=
  ofModel (Model.maxFinite format sign)

/-- The normal value of least magnitude, `2 ^ minNormalExponent`, positive by default. -/
@[inline] def minNormal (sign : Bool := false) :
    Value :=
  ofModel (Model.ofFields format sign 1 0)

/--
The subnormal value of least magnitude, `2 ^ minSubnormalExponent`, positive by default.

Every binary encoding has gradual underflow, so this is the least nonzero magnitude.
-/
@[inline] def minSubnormal (sign : Bool := false) :
    Value :=
  ofModel (Model.ofFields format sign 0 1)

/--
Unit in the last place: the spacing of the representable values in the binade of `value`, as
Java's `Math.ulp`. A finite value with exponent `e` gives `2 ^ (e - fractionBits)`. Subnormals and
zeros use the least normal exponent, so `ulp 0` is `minSubnormal`. Infinity gives positive
infinity and a NaN the format's invalid result.
-/
@[inline] def ulp (value : Value) :
    Value :=
  let x := toModel value
  if Model.isNaN x then ofModel (Model.invalidResult format)
  else if Model.isInf x then ofModel (Model.posInf format)
  else
    let field := max (Model.expField x) 1
    ofModel <|
      if format.fracWidth < field then Model.ofFields format false (field - format.fracWidth) 0
      else Model.ofFields format false 0 (1 <<< (field - 1))

/--
Machine epsilon `2 ^ -fractionBits`, the gap between one and the next larger value: `ulp 1`, as
C's `DBL_EPSILON` and PyTorch's `finfo.eps`. It is twice `Model.epsilonAt format 1`, the half-ulp
rounding bound of the error theorems.
-/
@[inline] def epsilon :
    Value :=
  ulp (ofModel (Model.posOne format))

end ExecFloat.Binary
end FloatLib.Floats
