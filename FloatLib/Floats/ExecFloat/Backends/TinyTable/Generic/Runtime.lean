/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.TinyTable.Generic.Certificates

/-!
# Direct byte-table execution

This is the warm execution path. Each function forces a memoized table, computes a native row-major
index, and does one byte load. The proofs attached to `Code` and array bounds are erased, and once
the table exists, lookup never evaluates the model operation again.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Backend.TinyTable

universe u

variable {Model : Type u}

/-- Read the encoded result from an arbitrary certified binary-table thunk. -/
@[always_inline, inline] def runBinaryCode
    (encoding : Encoding Model)
    (op : Model → Model → Model) (table : Thunk ByteArray)
    (table_eq : table.get = binaryTotal encoding op)
    (left right : Code encoding) : UInt8 :=
  table.get.uget
    (binaryByteIndex (radixWord encoding) left.1 right.1)
    (by
      simpa only [table_eq] using
        binaryIndex_lt encoding op left right)

/-- Execute one generated binary table on byte codes, with a single byte load. -/
@[always_inline, inline] def runBinary
    (encoding : Encoding Model)
    (op : Model → Model → Model) (table : Thunk ByteArray)
    (table_eq : table.get = binaryTotal encoding op)
    (left right : Code encoding) : Code encoding :=
  ⟨runBinaryCode encoding op table table_eq left right, by
    unfold runBinaryCode
    simp only [table_eq]
    rw [lookupBinary encoding op left right]
    rw [UInt8.toNat_ofNat']
    have hcode :
        (encoding.encode
          (op (encoding.decodeCode left) (encoding.decodeCode right))).val < 256 :=
      Nat.lt_of_lt_of_le
        (encoding.encode
          (op (encoding.decodeCode left) (encoding.decodeCode right))).isLt
        encoding.radix_le_byte
    rw [Nat.mod_eq_of_lt hcode]
    exact
      (encoding.encode
        (op (encoding.decodeCode left) (encoding.decodeCode right))).isLt⟩

/-- Read the encoded result from an arbitrary certified unary-table thunk. -/
@[always_inline, inline] def runUnaryCode
    (encoding : Encoding Model) (op : Model → Model)
    (table : Thunk ByteArray) (table_eq : table.get = unaryTotal encoding op)
    (value : Code encoding) : UInt8 :=
  table.get.uget (unaryByteIndex value.1)
    (by simpa only [table_eq] using unaryIndex_lt encoding op value)

/-- Execute one generated unary table on a byte code, with a single byte load. -/
@[always_inline, inline] def runUnary
    (encoding : Encoding Model) (op : Model → Model)
    (table : Thunk ByteArray) (table_eq : table.get = unaryTotal encoding op)
    (value : Code encoding) : Code encoding :=
  ⟨runUnaryCode encoding op table table_eq value, by
    unfold runUnaryCode
    simp only [table_eq]
    rw [lookupUnary encoding op value]
    rw [UInt8.toNat_ofNat']
    have hcode :
        (encoding.encode (op (encoding.decodeCode value))).val < 256 :=
      Nat.lt_of_lt_of_le
        (encoding.encode (op (encoding.decodeCode value))).isLt
        encoding.radix_le_byte
    rw [Nat.mod_eq_of_lt hcode]
    exact (encoding.encode (op (encoding.decodeCode value))).isLt⟩

/-- Read the encoded result from an arbitrary certified ternary-table thunk. -/
@[always_inline, inline] def runTernaryCode
    (encoding : Encoding Model)
    (op : Model → Model → Model → Model)
    (table : Thunk ByteArray) (table_eq : table.get = ternaryTotal encoding op)
    (left right addend : Code encoding) : UInt8 :=
  table.get.uget
    (ternaryByteIndex (radixWord encoding) left.1 right.1 addend.1)
    (by
      simpa only [table_eq] using
        ternaryIndex_lt encoding op left right addend)

/-- Execute one generated ternary table on byte codes, with a single byte load. -/
@[always_inline, inline] def runTernary
    (encoding : Encoding Model)
    (op : Model → Model → Model → Model)
    (table : Thunk ByteArray) (table_eq : table.get = ternaryTotal encoding op)
    (left right addend : Code encoding) : Code encoding :=
  ⟨runTernaryCode encoding op table table_eq left right addend, by
    unfold runTernaryCode
    simp only [table_eq]
    rw [lookupTernary encoding op left right addend]
    rw [UInt8.toNat_ofNat']
    have hcode :
        (encoding.encode <|
          op (encoding.decodeCode left) (encoding.decodeCode right)
            (encoding.decodeCode addend)).val < 256 :=
      Nat.lt_of_lt_of_le
        (encoding.encode <|
          op (encoding.decodeCode left) (encoding.decodeCode right)
            (encoding.decodeCode addend)).isLt
        encoding.radix_le_byte
    rw [Nat.mod_eq_of_lt hcode]
    exact
      (encoding.encode <|
        op (encoding.decodeCode left) (encoding.decodeCode right)
          (encoding.decodeCode addend)).isLt⟩

end FloatLib.Floats.ExecFloat.Backend.TinyTable
