/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Format.Properties

/-!
# Exact-width binary format storage

Exact-width `BitVec` representations of layout masks derived from a validated `FloatFormat`.

The definitions centralize sign, exponent, significand, and payload masks so packing code does not
reconstruct them with ad hoc shifts. They describe logical layout only; selection of `UInt8`,
`UInt16`, `UInt32`, `UInt64`, or arbitrary-width storage belongs to the configured execution layer.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace FloatFormat

/-- Pack a `Nat` pattern into the format's exact-width storage word. -/
@[inline] def ofWordNat (fmt : FloatFormat) (n : Nat) : ExecWord fmt :=
  BitVec.ofNat fmt.bitWidth n

/-- Exponent all-ones as storage word. -/
@[inline] def expAllOnes (fmt : FloatFormat) : ExecWord fmt :=
  ofWordNat fmt (expAllOnesNat fmt)

/-- Fraction mask as storage word. -/
@[inline] def fracMask (fmt : FloatFormat) : ExecWord fmt :=
  ofWordNat fmt (fracMaskNat fmt)

/-- Shifted exponent mask as storage word. -/
@[inline] def expMask (fmt : FloatFormat) : ExecWord fmt :=
  ofWordNat fmt (expMaskNat fmt)

/-- Sign-bit mask as storage word. -/
@[inline] def signMask (fmt : FloatFormat) : ExecWord fmt :=
  ofWordNat fmt (signMaskNat fmt)

/-- The exact-width sign mask decodes to its unique top-bit power of two. -/
@[simp] theorem signMask_toNat (fmt : FloatFormat) :
    (signMask fmt).toNat = 2 ^ (bitWidth fmt - 1) := by
  unfold signMask ofWordNat signMaskNat signBitIndex
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  exact Nat.pow_lt_pow_right (by decide) (Nat.sub_one_lt (by
    unfold bitWidth
    omega))

/-- The sign-bit mask is nonzero for every valid format descriptor. -/
@[simp] theorem signMask_ne_zero (fmt : FloatFormat) :
    signMask fmt ≠ 0#fmt.bitWidth := by
  intro hzero
  have hnat := congrArg BitVec.toNat hzero
  rw [signMask_toNat] at hnat
  simp at hnat

/-- Quiet-NaN bit as storage word. -/
@[inline] def quietBit (fmt : FloatFormat) : ExecWord fmt :=
  ofWordNat fmt (quietBitNat fmt)

end FloatFormat
end FloatLib.Floats.Formats.BinaryInterchange
