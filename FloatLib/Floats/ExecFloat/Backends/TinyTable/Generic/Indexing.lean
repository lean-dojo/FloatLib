/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Batteries.Data.Nat.Lemmas
public import FloatLib.Floats.ExecFloat.Backends.TinyTable.Generic.Construction

/-!
# Native indexing for exhaustive byte tables

The index proof shows that row-major `USize` arithmetic neither wraps nor leaves a generated table.
The only size bound is `encoding.radix ≤ 256`, and the radix doesn't have to be a power of two or
come from a floating-point layout.

The executable formulas stay plain native arithmetic, and all bounds are erased after compilation.
So table lookup has no runtime certificate check, while generation and dispatch can rely on the
proved index envelope.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Backend.TinyTable

universe u

variable {Model : Type u}

/-- Native row-major index for two byte-backed operands. -/
@[always_inline, inline] def binaryByteIndex
    (radix : USize) (left right : UInt8) : USize :=
  left.toUSize * radix + right.toUSize

/-- Native index for a unary byte table, which is the byte value itself. -/
@[always_inline, inline] def unaryByteIndex (value : UInt8) : USize :=
  value.toUSize

/-- Native row-major index for three byte-backed operands. -/
@[always_inline, inline] def ternaryByteIndex
    (radix : USize) (left right addend : UInt8) : USize :=
  (left.toUSize * radix + right.toUSize) * radix + addend.toUSize

/-- A row-major step `index * radix + byte` that does not wrap agrees with its natural value. -/
private theorem mulAdd_toNat (index radix : USize) (byte : UInt8)
    (hstep : index.toNat * radix.toNat + byte.toNat < 2 ^ System.Platform.numBits) :
    (index * radix + byte.toUSize).toNat = index.toNat * radix.toNat + byte.toNat := by
  have hmul : index.toNat * radix.toNat < 2 ^ System.Platform.numBits :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hstep
  rw [USize.toNat_add, USize.toNat_mul, UInt8.toNat_toUSize, Nat.mod_eq_of_lt hmul,
    Nat.mod_eq_of_lt hstep]

/-- A non-wrapping native binary index agrees with its natural-number expression. -/
theorem binaryByteIndex_toNat (radix : USize) (left right : UInt8)
    (hindex :
      left.toNat * radix.toNat + right.toNat <
        2 ^ System.Platform.numBits) :
    (binaryByteIndex radix left right).toNat =
      left.toNat * radix.toNat + right.toNat := by
  have hstep := mulAdd_toNat left.toUSize radix right (by rwa [UInt8.toNat_toUSize])
  rwa [UInt8.toNat_toUSize] at hstep

/-- The native unary-table index preserves the byte's natural value. -/
@[simp] theorem unaryByteIndex_toNat (value : UInt8) :
    (unaryByteIndex value).toNat = value.toNat := by
  exact UInt8.toNat_toUSize value

/--
A non-wrapping native ternary index agrees with its natural-number expression.

The final bound covers every intermediate: each partial index is at most the next one, and a zero
radix leaves only a byte.
-/
theorem ternaryByteIndex_toNat
    (radix : USize) (left right addend : UInt8)
    (hindex :
      (left.toNat * radix.toNat + right.toNat) * radix.toNat + addend.toNat <
        2 ^ System.Platform.numBits) :
    (ternaryByteIndex radix left right addend).toNat =
      (left.toNat * radix.toNat + right.toNat) * radix.toNat + addend.toNat := by
  have hpairMul :
      (left.toNat * radix.toNat + right.toNat) * radix.toNat <
        2 ^ System.Platform.numBits :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hindex
  have hpair :
      left.toNat * radix.toNat + right.toNat < 2 ^ System.Platform.numBits := by
    rcases Nat.eq_zero_or_pos radix.toNat with hzero | hpos
    · rw [hzero, Nat.mul_zero, Nat.zero_add]
      calc
        right.toNat < 2 ^ 8 := UInt8.toNat_lt right
        _ ≤ 2 ^ System.Platform.numBits :=
          Nat.pow_le_pow_right (by decide) (by rcases System.Platform.numBits_eq with h | h <;> omega)
    · exact Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hpos) hpairMul
  have hbinary := binaryByteIndex_toNat radix left right hpair
  have hstep := mulAdd_toNat (binaryByteIndex radix left right) radix addend
    (by rwa [hbinary])
  rwa [hbinary] at hstep

/-- Every intermediate of a three-input byte-table index fits a platform word. -/
theorem ternaryIndex_noOverflow
    (encoding : Encoding Model) (radixWord : USize)
    (hradixWord : radixWord.toNat = encoding.radix)
    (left right addend : Code encoding) :
    left.1.toNat * radixWord.toNat < 2 ^ System.Platform.numBits ∧
    left.1.toNat * radixWord.toNat + right.1.toNat <
      2 ^ System.Platform.numBits ∧
    (left.1.toNat * radixWord.toNat + right.1.toNat) * radixWord.toNat <
      2 ^ System.Platform.numBits ∧
    (left.1.toNat * radixWord.toNat + right.1.toNat) * radixWord.toNat +
        addend.1.toNat <
      2 ^ System.Platform.numBits := by
  have hleft : left.1.toNat ≤ 255 := Nat.le_pred_of_lt (UInt8.toNat_lt left.1)
  have hright : right.1.toNat ≤ 255 := Nat.le_pred_of_lt (UInt8.toNat_lt right.1)
  have haddend : addend.1.toNat ≤ 255 :=
    Nat.le_pred_of_lt (UInt8.toNat_lt addend.1)
  have hleftMul :
      left.1.toNat * encoding.radix ≤ 255 * 256 :=
    Nat.mul_le_mul hleft encoding.radix_le_byte
  have hpair :
      left.1.toNat * encoding.radix + right.1.toNat ≤ 255 * 256 + 255 :=
    Nat.add_le_add hleftMul hright
  have hpairMul :
      (left.1.toNat * encoding.radix + right.1.toNat) * encoding.radix ≤
        (255 * 256 + 255) * 256 :=
    Nat.mul_le_mul hpair encoding.radix_le_byte
  have hall :
      (left.1.toNat * encoding.radix + right.1.toNat) * encoding.radix +
          addend.1.toNat ≤
        (255 * 256 + 255) * 256 + 255 :=
    Nat.add_le_add hpairMul haddend
  rcases System.Platform.numBits_eq with hbits | hbits <;>
    simp only [hradixWord, hbits] <;> omega

/-- Every two-input byte-table index fits both supported platform word widths. -/
theorem binaryIndex_noOverflow
    (encoding : Encoding Model) (radixWord : USize)
    (hradixWord : radixWord.toNat = encoding.radix)
    (left right : Code encoding) :
    left.1.toNat * radixWord.toNat + right.1.toNat <
      2 ^ System.Platform.numBits :=
  (ternaryIndex_noOverflow encoding radixWord hradixWord left right left).2.1

/-- Native-word representation of an at-most-256-code encoding's radix. -/
@[always_inline, inline] def radixWord (encoding : Encoding Model) : USize :=
  USize.ofNat encoding.radix

/-- The native radix constant denotes the mathematical encoding radix. -/
@[simp] theorem radixWord_toNat (encoding : Encoding Model) :
    (radixWord encoding).toNat = encoding.radix := by
  apply USize.toNat_ofNat_of_lt
  rcases System.Platform.numBits_eq with hbits | hbits <;>
    simp only [USize.size, hbits]
  all_goals
    exact Nat.lt_of_le_of_lt encoding.radix_le_byte (by decide)

/-- Valid input bytes select an in-bounds binary table entry. -/
theorem binaryIndex_lt
    (encoding : Encoding Model)
    (op : Model → Model → Model) (left right : Code encoding) :
    (binaryByteIndex (radixWord encoding) left.1 right.1).toNat <
      (binaryTotal encoding op).size := by
  rw [binaryByteIndex_toNat (radixWord encoding) left.1 right.1
    (binaryIndex_noOverflow encoding (radixWord encoding)
      (radixWord_toNat encoding) left right)]
  simpa only [binaryTotal, ByteArray.size_ofFn, radixWord_toNat, Nat.mul_comm] using
    Nat.mul_add_lt_mul_of_lt_of_lt left.2 right.2

/-- Valid input bytes select an in-bounds unary table entry. -/
theorem unaryIndex_lt
    (encoding : Encoding Model) (op : Model → Model) (value : Code encoding) :
    (unaryByteIndex value.1).toNat < (unaryTotal encoding op).size := by
  simpa only [unaryByteIndex_toNat, unaryTotal, ByteArray.size_ofFn] using value.2

/-- Valid input bytes select an in-bounds ternary table entry. -/
theorem ternaryIndex_lt
    (encoding : Encoding Model)
    (op : Model → Model → Model → Model)
    (left right addend : Code encoding) :
    (ternaryByteIndex (radixWord encoding) left.1 right.1 addend.1).toNat <
      (ternaryTotal encoding op).size := by
  rw [ternaryByteIndex_toNat (radixWord encoding) left.1 right.1 addend.1
    (ternaryIndex_noOverflow encoding (radixWord encoding)
      (radixWord_toNat encoding) left right addend).2.2.2]
  simpa only [ternaryTotal, ByteArray.size_ofFn, radixWord_toNat, Nat.mul_comm] using
    Nat.mul_add_lt_mul_of_lt_of_lt
      (Nat.mul_add_lt_mul_of_lt_of_lt left.2 right.2) addend.2

end FloatLib.Floats.ExecFloat.Backend.TinyTable
