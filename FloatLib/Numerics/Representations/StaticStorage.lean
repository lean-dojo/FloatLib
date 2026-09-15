/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.Nat.Basic

/-!
# Bounded static storage

Bounded `UInt8`, `UInt16`, `UInt32`, and `UInt64` carriers store exact natural-number encodings.
Callers choose a carrier and prove that the encoding fits both the format bound and the word's
capacity.

The bounds are propositions erased from the runtime carrier. The packing functions and their
round-trip laws are independent of the numerical format using them.
-/

@[expose] public section

universe u

namespace FloatLib.Numerics.StaticStorage

/-- A primitive carrier whose natural-number view lies below a format-specific bound. -/
abbrev BoundedCode (α : Type u) (toNat : α → Nat) (bound : Nat) :=
  { value : α // toNat value < bound }

/-- An in-range encoding stored directly in `UInt8`. -/
abbrev ByteCode (bound : Nat) := BoundedCode UInt8 UInt8.toNat bound

/-- An in-range encoding stored directly in `UInt16`. -/
abbrev Word16Code (bound : Nat) := BoundedCode UInt16 UInt16.toNat bound

/-- An in-range encoding stored directly in `UInt32`. -/
abbrev Word32Code (bound : Nat) := BoundedCode UInt32 UInt32.toNat bound

/-- An in-range encoding stored directly in `UInt64`. -/
abbrev Word64Code (bound : Nat) := BoundedCode UInt64 UInt64.toNat bound

/-- An encoding below its format bound fits any storage width containing that bound. -/
theorem lt_capacity {bits bound width : Nat}
    (hbits : bits < bound) (bound_le : bound ≤ 2 ^ width) :
    bits < 2 ^ width :=
  lt_of_lt_of_le hbits bound_le

namespace ByteCode

/-- Narrow an in-range encoding to a direct byte carrier. -/
@[always_inline, inline] def ofNat {bound : Nat} (bits : Nat)
    (hbound : bits < bound) (hcapacity : bits < 2 ^ 8) : ByteCode bound :=
  ⟨UInt8.ofNat bits, by
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt hcapacity]
    exact hbound⟩

/-- Reading a byte immediately after packing returns the supplied encoding. -/
@[simp, grind =] theorem toNat_ofNat {bound bits : Nat}
    (hbound : bits < bound) (hcapacity : bits < 2 ^ 8) :
    (ofNat bits hbound hcapacity).1.toNat = bits := by
  simp only [ofNat, UInt8.toNat_ofNat', Nat.mod_eq_of_lt hcapacity]

end ByteCode

namespace Word16Code

/-- Narrow an in-range encoding to a direct 16-bit carrier. -/
@[always_inline, inline] def ofNat {bound : Nat} (bits : Nat)
    (hbound : bits < bound) (hcapacity : bits < 2 ^ 16) : Word16Code bound :=
  ⟨UInt16.ofNat bits, by
    rw [UInt16.toNat_ofNat', Nat.mod_eq_of_lt hcapacity]
    exact hbound⟩

/-- Reading a 16-bit word immediately after packing returns the supplied encoding. -/
@[simp, grind =] theorem toNat_ofNat {bound bits : Nat}
    (hbound : bits < bound) (hcapacity : bits < 2 ^ 16) :
    (ofNat bits hbound hcapacity).1.toNat = bits := by
  simp only [ofNat, UInt16.toNat_ofNat', Nat.mod_eq_of_lt hcapacity]

end Word16Code

namespace Word32Code

/-- Narrow an in-range encoding to a direct 32-bit carrier. -/
@[always_inline, inline] def ofNat {bound : Nat} (bits : Nat)
    (hbound : bits < bound) (hcapacity : bits < 2 ^ 32) : Word32Code bound :=
  ⟨UInt32.ofNat bits, by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hcapacity]
    exact hbound⟩

/-- Reading a 32-bit word immediately after packing returns the supplied encoding. -/
@[simp, grind =] theorem toNat_ofNat {bound bits : Nat}
    (hbound : bits < bound) (hcapacity : bits < 2 ^ 32) :
    (ofNat bits hbound hcapacity).1.toNat = bits := by
  simp only [ofNat, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hcapacity]

end Word32Code

namespace Word64Code

/-- Narrow an in-range encoding to a direct 64-bit carrier. -/
@[always_inline, inline] def ofNat {bound : Nat} (bits : Nat)
    (hbound : bits < bound) (hcapacity : bits < 2 ^ 64) : Word64Code bound :=
  ⟨UInt64.ofNat bits, by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hcapacity]
    exact hbound⟩

/-- Reading a 64-bit word immediately after packing returns the supplied encoding. -/
@[simp, grind =] theorem toNat_ofNat {bound bits : Nat}
    (hbound : bits < bound) (hcapacity : bits < 2 ^ 64) :
    (ofNat bits hbound hcapacity).1.toNat = bits := by
  simp only [ofNat, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hcapacity]

end Word64Code

end FloatLib.Numerics.StaticStorage
