/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.BinaryInterchange.Model.Carrier
public import FloatLib.Numerics.IEEEClass

/-!
# Binary classification and canonicality queries

The non-signaling queries of IEEE 754-2019 §5.7.2 inspect the complete descriptor.
They also apply to custom biases and finite encodings: an all-ones exponent can
be normal, and the FNUZ negative-zero word is a quiet NaN.

Every word in these implicit-leading-bit layouts is a canonical interchange
encoding. This includes every NaN payload; canonicality does not mean choosing
the library's preferred NaN or repacking through Lean's logical model.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

/-- A normal value is finite and has a nonzero biased exponent field. -/
@[inline] def isNormal {fmt : FloatFormat} (x : Model fmt) : Bool :=
  isFinite x && expField x != 0

/-- Classify without quieting NaNs or raising exceptions, using the complete descriptor. -/
@[inline] def classify {fmt : FloatFormat} (x : Model fmt) : Numerics.IEEEClass :=
  if isNaN x then
    if isSNaN x then .signalingNaN else .quietNaN
  else if isInf x then
    if signBit x then .negativeInfinity else .positiveInfinity
  else if isZero x then
    if signBit x then .negativeZero else .positiveZero
  else if isSubnormal x then
    if signBit x then .negativeSubnormal else .positiveSubnormal
  else
    if signBit x then .negativeNormal else .positiveNormal

/-- Every exact-width word of an implicit-leading-bit binary layout is canonical. -/
@[inline] def isCanonical {fmt : FloatFormat} (_ : Model fmt) : Bool := true

end FloatLib.Floats.Formats.BinaryInterchange.Model
