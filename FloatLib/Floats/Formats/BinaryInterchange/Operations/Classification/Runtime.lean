/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.BinaryInterchange.Model.Carrier
public import FloatLib.Numerics.IEEEClass

/-!
# Binary classification and canonicality queries

These are the non-signaling queries of IEEE 754-2019 §5.7.2, and because each one inspects the
complete descriptor they work for custom biases and finite encodings too, where an all-ones
exponent can be normal and the FNUZ negative-zero word is a quiet NaN.

In these implicit-leading-bit layouts every word is a canonical interchange encoding, whatever its
NaN payload. Canonical here does not mean the library's preferred NaN, and it does not mean
repacking through Lean's logical model.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

/-- A normal value is finite and has a nonzero biased exponent field. -/
@[inline] def isNormal {fmt : FloatFormat} (x : Model fmt) : Bool :=
  isFinite x && expField x != 0

/-- Classify without quieting NaNs or raising exceptions, using the complete descriptor. -/
@[inline] def classify {fmt : FloatFormat} (x : Model fmt) : Numerics.IEEEClass :=
  if isNaN x then
    if isSignaling x then .signalingNaN else .quietNaN
  else if isInfinite x then
    if signBit x then .negativeInfinity else .positiveInfinity
  else if isZero x then
    if signBit x then .negativeZero else .positiveZero
  else if isSubnormal x then
    if signBit x then .negativeSubnormal else .positiveSubnormal
  else
    if signBit x then .negativeNormal else .positiveNormal

/-- Every exact-width word of an implicit-leading-bit binary layout is canonical. -/
@[inline] def isCanonical {fmt : FloatFormat} (_ : Model fmt) : Bool := true

/--
IEEE 754-2019 §5.7.2 `radix` (C23 `FLT_RADIX`, N3220 Table F.2): the radix of the format of the
operand, two for every binary format. No flag is raised, also for a signaling NaN.
-/
@[inline] def radix {fmt : FloatFormat} (_ : Model fmt) : Nat := 2

/--
IEEE 754-2019 §5.5.1 `copy`: the operand unchanged, with its sign bit and, for a NaN, its
signaling state and payload. No flag is raised, also for a signaling NaN.
-/
@[inline] def copy {fmt : FloatFormat} (x : Model fmt) : Model fmt := x

end FloatLib.Floats.Formats.BinaryInterchange.Model
