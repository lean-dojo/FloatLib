/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Codec.Runtime

/-!
# Exact-width decimal sign and payload extraction

Both codecs keep the sign in the top bit and everything else below it. These lemmas show that the
split is clean: pack a sign with a payload below `f.signBase` and you read both fields back
unchanged, and for every word of the format's bit width the extracted payload stays below that
bound.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Bits

/-- Packing two bounded fields stays below the product of their exclusive bounds. -/
theorem mul_add_lt_mul {high highBound low radix : Nat}
    (hh : high < highBound) (hl : low < radix) :
    high * radix + low < highBound * radix := by
  calc
    high * radix + low < high * radix + radix := Nat.add_lt_add_left hl _
    _ = (high + 1) * radix := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ highBound * radix := Nat.mul_le_mul_right radix hh

/-- Unpacking `high * radix + low` with `low < radix` recovers the high field. -/
theorem mul_add_div_of_lt {high low radix : Nat} (hl : low < radix) :
    (high * radix + low) / radix = high := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hl, Nat.zero_add]

/-- For a payload below the sign bit, packing adds the sign's place value to the payload, without
overlap or wraparound. -/
theorem pack_toNat (f : Format) (s : Bool) (n : Nat) (h : n < f.signBase) :
    (pack f s n).toNat = (if s then f.signBase else 0) + n := by
  simp only [pack, BitVec.toNat_ofNat, ← f.twice_signBase]
  apply Nat.mod_eq_of_lt
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- The sign bit of a packed word is the packed sign, for any payload below the sign bit. -/
@[simp] theorem negative_pack (f : Format) (s : Bool) (n : Nat) (h : n < f.signBase) :
    negative f (pack f s n) = s := by
  rw [negative, pack_toNat f s n h]
  cases s <;> simp <;> omega

/-- The bits below the sign of a packed word are the packed payload, for any payload below the sign
bit. -/
@[simp] theorem payload_pack (f : Format) (s : Bool) (n : Nat) (h : n < f.signBase) :
    payload f (pack f s n) = n := by
  rw [payload, pack_toNat f s n h]
  cases s <;> simp [Nat.mod_eq_of_lt h]

/-- The bits below the sign of any word are below the sign bit's place value. -/
theorem payload_lt (f : Format) (word : BitVec f.bitWidth) :
    payload f word < f.signBase := Nat.mod_lt _ f.signBase_pos

end FloatLib.Floats.Formats.DecimalInterchange.Bits
