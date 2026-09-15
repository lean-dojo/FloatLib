/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Decode

/-!
# Exponent-only scaling formats

OCP microscaling uses E8M0 for a scale shared by a block of narrow elements. E8M0 is not a member
of the sign/exponent/fraction family: it has no sign bit, no zero, and no explicit fraction. Codes
`0` through `254` denote powers of two from `2^-127` through `2^127`; code `255` is NaN.

Keeping this scale type beside, rather than inside, `FloatFormat` prevents artificial optional
fields and invalid combinations in the ordinary float API.

References:

* Open Compute Project, *Microscaling Formats (MX) Specification, Version 1.0*, Section 5.4,
  <https://www.opencompute.org/documents/ocp-microscaling-formats-mx-v1-0-spec-final-pdf>.
* ONNX, *Float stored in 8 bits: E8M0*,
  <https://onnx.ai/onnx/technical/float8.html#e8m0>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.OCP.MX

open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.Model

/--
Exact E8M0 storage word.

The transparent definition has the same compiled representation as `BitVec 8`, while retaining
the exponent-only format identity for proof-aware type inspection.
-/
def E8M0 := BitVec 8

deriving instance DecidableEq, BEq, Repr for E8M0

namespace E8M0

/-- E8M0 exponent bias. -/
def bias : Int := 127

/-- Construct an E8M0 word from its raw code. -/
@[inline] def ofNatBits (bits : Nat) : E8M0 :=
  BitVec.ofNat 8 bits

/-- Raw code as a natural number. -/
@[inline] def toNatBits (x : E8M0) : Nat :=
  x.toNat

/-- Re-encoding an E8M0 word's complete byte pattern preserves it. -/
@[simp] theorem ofNatBits_toNatBits (value : E8M0) :
    ofNatBits value.toNatBits = value := by
  change BitVec 8 at value
  apply BitVec.eq_of_toNat_eq
  simp [ofNatBits, toNatBits]

/-- An in-range byte pattern is unchanged by E8M0 encoding. -/
@[simp] theorem toNatBits_ofNatBits_of_lt (bits : Nat) (bits_lt : bits < 2 ^ 8) :
    (ofNatBits bits).toNatBits = bits := by
  change (BitVec.ofNat 8 bits).toNat = bits
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt bits_lt

/-- The sole NaN encoding (`0xff`). -/
@[inline] def isNaN (x : E8M0) : Bool :=
  x.toNat == 255

/-- Unbiased power-of-two exponent, or `none` for NaN. -/
@[inline] def exponent? (x : E8M0) : Option Int :=
  if isNaN x then none else some (Int.ofNat x.toNat - bias)

/-- Exact positive dyadic scale, or `none` for NaN. -/
@[inline] def toDyadic? (x : E8M0) : Option FloatLib.Numerics.Dyadic :=
  (exponent? x).map fun exponent =>
    { negative := false, significand := 1, exponent }

/-- Apply an E8M0 scale to an exact dyadic by adding its power-of-two exponent. -/
@[inline] def scaleDyadic? (scale : E8M0) (value : FloatLib.Numerics.Dyadic) :
    Option FloatLib.Numerics.Dyadic :=
  (exponent? scale).map fun exponent =>
    { value with exponent := value.exponent + exponent }

/--
Decode and scale one element of a microscaling block.

`none` records either the E8M0 NaN code or a non-finite element. The operation is exact: scaling by
a power of two changes only the dyadic exponent.
-/
@[inline] def decodeElement? {fmt : FloatFormat} (scale : E8M0) (x : Model fmt) :
    Option FloatLib.Numerics.Dyadic := do
  let value ← Model.toDyadic? x
  scaleDyadic? scale value

/--
Exact mathematical decoding of a microscaling block with one shared E8M0 scale.

This function decodes an already encoded block; it does not choose the shared scale. An empty
array succeeds without inspecting the scale. On a nonempty array, a NaN scale or any non-finite
element causes decoding to fail.
-/
def decodeBlock? {fmt : FloatFormat} (scale : E8M0) (values : Array (Model fmt)) :
    Option (Array FloatLib.Numerics.Dyadic) :=
  values.mapM (decodeElement? scale)

/-- Encode an in-range exponent; return `none` outside `[-127, 127]`. -/
def ofExponent? (exponent : Int) : Option E8M0 :=
  if -127 ≤ exponent && exponent ≤ 127 then
    some (ofNatBits (Int.toNat (exponent + bias)))
  else
    none

/-- Encode an exponent after clamping it to the finite E8M0 range. -/
def ofExponentSaturating (exponent : Int) : E8M0 :=
  ofNatBits (Int.toNat (max (-127) (min 127 exponent) + bias))

/-- Every successfully decoded E8M0 scale has significand one. -/
theorem toDyadic?_significand_eq_one {x : E8M0} {value : FloatLib.Numerics.Dyadic}
    (hx : toDyadic? x = some value) : value.significand = 1 := by
  unfold toDyadic? at hx
  cases hexponent : exponent? x with
  | none => simp [hexponent] at hx
  | some exponent =>
      simp [hexponent] at hx
      subst value
      rfl

/-- Every successfully decoded E8M0 scale has its sign bit clear. -/
theorem toDyadic?_negative_eq_false {x : E8M0} {value : FloatLib.Numerics.Dyadic}
    (hx : toDyadic? x = some value) : value.negative = false := by
  unfold toDyadic? at hx
  cases hexponent : exponent? x with
  | none => simp [hexponent] at hx
  | some exponent =>
      simp [hexponent] at hx
      subst value
      rfl

end E8M0

end FloatLib.Floats.Formats.OCP.MX
