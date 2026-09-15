/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Saturating
public import Mathlib.Data.BitVec

/-!
# Fixed-width signed integers

`FixedInt width` stores a two's-complement integer in exactly `width` bits.  The policy is explicit
in every arithmetic name:

* `wrapAdd`, `wrapSub`, and `wrapMul` compute modulo `2^width`;
* checked operations return `none` on signed overflow;
* saturating operations clamp to the signed range.

The wrapping kernels operate directly on `BitVec`. Checked operations use Lean's signed-overflow
tests. Saturating operations compute the exact `Int` result, clamp it to the signed range, and
encode it.
-/

@[expose] public section

namespace FloatLib.Numerics.Representations

/-- A two's-complement integer stored in exactly `width` bits. -/
structure FixedInt (width : Nat) where
  /-- Complete two's-complement bit pattern. -/
  bits : BitVec width
  deriving DecidableEq, Repr

namespace FixedInt

/-- Construct a fixed-width integer from the low `width` bits of a natural number. -/
@[inline] def ofNatBits {width : Nat} (value : Nat) : FixedInt width :=
  ⟨BitVec.ofNat width value⟩

/-- Extract the unsigned bit pattern. -/
@[inline] def toNatBits {width : Nat} (value : FixedInt width) : Nat :=
  value.bits.toNat

/-- Every exact-width word lies below its unsigned modulus. -/
theorem toNatBits_lt_modulus {width : Nat} (value : FixedInt width) :
    value.toNatBits < 2 ^ width :=
  BitVec.toNat_lt_twoPow_of_le (Nat.le_refl width)

/-- Re-encoding a fixed integer's complete bit pattern preserves it. -/
@[simp, grind =] theorem ofNatBits_toNatBits {width : Nat} (value : FixedInt width) :
    ofNatBits value.toNatBits = value := by
  cases value with
  | mk bits =>
      simp [ofNatBits, toNatBits]

/-- An in-range unsigned bit pattern is unchanged by exact-width encoding. -/
@[simp, grind =] theorem toNatBits_ofNatBits_of_lt {width : Nat} (bits : Nat)
    (bits_lt : bits < 2 ^ width) :
    (ofNatBits (width := width) bits).toNatBits = bits := by
  change (BitVec.ofNat width bits).toNat = bits
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt bits_lt

/-- Interpret a word as a signed two's-complement integer. -/
@[inline] def toInt {width : Nat} (value : FixedInt width) : Int :=
  value.bits.toInt

/-- Encode an integer modulo `2^width`. -/
@[inline] def ofInt {width : Nat} (value : Int) : FixedInt width :=
  ⟨BitVec.ofInt width value⟩

/-- Least signed integer representable at `width`. -/
@[inline] def minValue (width : Nat) : Int :=
  (BitVec.intMin width).toInt

/-- Greatest signed integer representable at `width`. -/
@[inline] def maxValue (width : Nat) : Int :=
  (BitVec.intMax width).toInt

/-- Whether an integer lies in the signed range of `width` bits. -/
def InRange (width : Nat) (value : Int) : Prop :=
  minValue width ≤ value ∧ value ≤ maxValue width

instance (width : Nat) (value : Int) : Decidable (InRange width value) :=
  inferInstanceAs (Decidable (minValue width ≤ value ∧ value ≤ maxValue width))

/-- Clamp an integer to the signed range of `width` bits, the shared `Saturating.clamp` applied to
the range endpoints. -/
@[inline] def clamp (width : Nat) (value : Int) : Int :=
  Quantization.Saturating.clamp (minValue width) (maxValue width) value

/-- The least representable word, denoting `minValue width`. -/
@[inline] def minCode (width : Nat) : FixedInt width :=
  ⟨BitVec.intMin width⟩

/-- The greatest representable word, denoting `maxValue width`. -/
@[inline] def maxCode (width : Nat) : FixedInt width :=
  ⟨BitVec.intMax width⟩

/-- Two's-complement addition modulo `2^width`. -/
@[inline] def wrapAdd {width : Nat} (left right : FixedInt width) : FixedInt width :=
  ⟨left.bits + right.bits⟩

/-- Two's-complement subtraction modulo `2^width`. -/
@[inline] def wrapSub {width : Nat} (left right : FixedInt width) : FixedInt width :=
  ⟨left.bits - right.bits⟩

/-- Two's-complement multiplication modulo `2^width`. -/
@[inline] def wrapMul {width : Nat} (left right : FixedInt width) : FixedInt width :=
  ⟨left.bits * right.bits⟩

/-- Return the exact sum when it fits in `width` signed bits. -/
@[inline] def checkedAdd {width : Nat}
    (left right : FixedInt width) : Option (FixedInt width) :=
  if left.bits.saddOverflow right.bits then none else some (wrapAdd left right)

/-- Return the exact difference when it fits in `width` signed bits. -/
@[inline] def checkedSub {width : Nat}
    (left right : FixedInt width) : Option (FixedInt width) :=
  if left.bits.ssubOverflow right.bits then none else some (wrapSub left right)

/-- Return the exact product when it fits in `width` signed bits. -/
@[inline] def checkedMul {width : Nat}
    (left right : FixedInt width) : Option (FixedInt width) :=
  if left.bits.smulOverflow right.bits then none else some (wrapMul left right)

/-- Encode an exact integer, clamping it to the signed range when necessary. -/
@[inline] def ofIntSaturating {width : Nat} (value : Int) : FixedInt width :=
  ofInt (clamp width value)

/-- Signed addition with saturation at the destination bounds. -/
@[inline] def saturatingAdd {width : Nat}
    (left right : FixedInt width) : FixedInt width :=
  ofIntSaturating (left.toInt + right.toInt)

/-- Signed subtraction with saturation at the destination bounds. -/
@[inline] def saturatingSub {width : Nat}
    (left right : FixedInt width) : FixedInt width :=
  ofIntSaturating (left.toInt - right.toInt)

/-- Signed multiplication with saturation at the destination bounds. -/
@[inline] def saturatingMul {width : Nat}
    (left right : FixedInt width) : FixedInt width :=
  ofIntSaturating (left.toInt * right.toInt)

end FixedInt
end FloatLib.Numerics.Representations
