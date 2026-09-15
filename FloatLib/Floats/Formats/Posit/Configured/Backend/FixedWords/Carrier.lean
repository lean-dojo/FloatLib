/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.Nat.Basic

/-!
# Primitive carriers for fixed-word posit kernels

The four built-in posit carriers differ only in how they widen to and narrow from `UInt64`.
`Carrier` records that relationship once. It is passed only to always-inlined helpers; the public
raw kernels remain monomorphic so their native calling conventions are unchanged.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured.Backend.FixedWords

/-- Arithmetic view of one primitive unsigned carrier. -/
structure Carrier (α : Type) (capacity : Nat) where
  /-- Observe the encoded natural number. -/
  toNat : α → Nat
  /-- Zero-extend the carrier to the packed arithmetic word. -/
  toUInt64 : α → UInt64
  /-- Narrow a packed arithmetic result back to the carrier. -/
  narrow : UInt64 → α
  /-- Construct the carrier from a natural number. -/
  ofNat : Nat → α
  /-- Natural-number observation determines the primitive carrier. -/
  toNat_injective : Function.Injective toNat
  /-- Widening preserves the represented natural number. -/
  toNat_toUInt64 : ∀ value, (toUInt64 value).toNat = toNat value
  /-- Narrowing is reduction modulo the carrier capacity. -/
  toNat_narrow : ∀ word, toNat (narrow word) = word.toNat % 2 ^ capacity
  /-- Natural construction is reduction modulo the carrier capacity. -/
  toNat_ofNat : ∀ value, toNat (ofNat value) = value % 2 ^ capacity
  /-- Fixed-word carriers fit in the packed `UInt64` arithmetic word. -/
  capacity_le : capacity ≤ 64

/--
`UInt8` as a packed posit carrier.

This is an abbreviation so monomorphic raw kernels reduce its projections at compile time
instead of loading conversion closures from a runtime record.
-/
abbrev uint8Carrier : Carrier UInt8 8 where
  toNat := UInt8.toNat
  toUInt64 := UInt8.toUInt64
  narrow := UInt64.toUInt8
  ofNat := UInt8.ofNat
  toNat_injective _ _ h := UInt8.toNat_inj.mp h
  toNat_toUInt64 value := by simp
  toNat_narrow word := UInt64.toNat_toUInt8 word
  toNat_ofNat _ := UInt8.toNat_ofNat'
  capacity_le := by decide

/--
`UInt16` as a packed posit carrier.

Keeping the carrier transparent preserves the native `UInt16` calling convention after the
generic fixed-word kernel specializes.
-/
abbrev uint16Carrier : Carrier UInt16 16 where
  toNat := UInt16.toNat
  toUInt64 := UInt16.toUInt64
  narrow := UInt64.toUInt16
  ofNat := UInt16.ofNat
  toNat_injective _ _ h := UInt16.toNat_inj.mp h
  toNat_toUInt64 value := by simp
  toNat_narrow word := UInt64.toNat_toUInt16 word
  toNat_ofNat _ := UInt16.toNat_ofNat'
  capacity_le := by decide

/--
`UInt32` as a packed posit carrier.

Keeping the carrier transparent lets widening and narrowing compile to primitive operations.
-/
abbrev uint32Carrier : Carrier UInt32 32 where
  toNat := UInt32.toNat
  toUInt64 := UInt32.toUInt64
  narrow := UInt64.toUInt32
  ofNat := UInt32.ofNat
  toNat_injective _ _ h := UInt32.toNat_inj.mp h
  toNat_toUInt64 value := by simp
  toNat_narrow word := UInt64.toNat_toUInt32 word
  toNat_ofNat _ := UInt32.toNat_ofNat'
  capacity_le := by decide

/--
`UInt64` as the full packed arithmetic carrier.

Keeping the carrier transparent reduces both conversion projections to `id`.
-/
abbrev uint64Carrier : Carrier UInt64 64 where
  toNat := UInt64.toNat
  toUInt64 := id
  narrow := id
  ofNat := UInt64.ofNat
  toNat_injective _ _ h := UInt64.toNat_inj.mp h
  toNat_toUInt64 _ := rfl
  toNat_narrow word := by
    exact (Nat.mod_eq_of_lt word.toNat_lt).symm
  toNat_ofNat _ := UInt64.toNat_ofNat'
  capacity_le := le_rfl

end FloatLib.Floats.Formats.Posit.Configured.Backend.FixedWords
