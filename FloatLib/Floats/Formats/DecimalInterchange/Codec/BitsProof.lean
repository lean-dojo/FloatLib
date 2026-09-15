/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Codec.Runtime

/-!
# Exact-width decimal sign and payload extraction

Packing a sign with a payload below `f.signBase` recovers both fields exactly. Payload
extraction stays below that bound for every word of the format's bit width.
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

theorem pack_toNat (f : Format) (s : Bool) (n : Nat) (h : n < f.signBase) :
    (pack f s n).toNat = (if s then f.signBase else 0) + n := by
  simp only [pack, BitVec.toNat_ofNat, ← f.twice_signBase]
  apply Nat.mod_eq_of_lt
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

@[simp] theorem negative_pack (f : Format) (s : Bool) (n : Nat) (h : n < f.signBase) :
    negative f (pack f s n) = s := by
  rw [negative, pack_toNat f s n h]
  cases s <;> simp <;> omega

@[simp] theorem payload_pack (f : Format) (s : Bool) (n : Nat) (h : n < f.signBase) :
    payload f (pack f s n) = n := by
  rw [payload, pack_toNat f s n h]
  cases s <;> simp [Nat.mod_eq_of_lt h]

theorem payload_lt (f : Format) (word : BitVec f.bitWidth) :
    payload f word < f.signBase := Nat.mod_lt _ f.signBase_pos

end FloatLib.Floats.Formats.DecimalInterchange.Bits
