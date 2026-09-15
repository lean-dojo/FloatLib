/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.TinyTable.Generic.Indexing

/-!
# Byte-table lookup certificates

These theorems identify each native array read with the encoded result used to generate that
entry. Runtime definitions use the equations to prove that the returned byte is a valid code;
`Generic.Proof` then establishes equality of the decoded result with the model operation.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Backend.TinyTable

universe u

variable {Model : Type u}

/-- A native binary table read returns the encoded model-operation result. -/
theorem lookupBinary
    (encoding : Encoding Model)
    (op : Model → Model → Model) (left right : Code encoding)
    (hindex :
      (binaryByteIndex (radixWord encoding) left.1 right.1).toNat <
        (binaryTotal encoding op).size) :
    (binaryTotal encoding op).uget
        (binaryByteIndex (radixWord encoding) left.1 right.1)
        hindex =
      UInt8.ofNat
        (encoding.encode
          (op (encoding.decodeCode left) (encoding.decodeCode right))).val := by
  have hidx :
      (binaryByteIndex (radixWord encoding) left.1 right.1).toNat =
        left.1.toNat * encoding.radix + right.1.toNat := by
    simpa only [radixWord_toNat] using
      binaryByteIndex_toNat (radixWord encoding) left.1 right.1
        (binaryIndex_noOverflow encoding (radixWord encoding)
          (radixWord_toNat encoding) left right)
  rw [uget_eq_get]
  simpa only [binaryTotal, hidx, Encoding.decodeCode] using
    Tabulation.getElem_binary encoding.radix
      (fun x y => UInt8.ofNat (encoding.encode (op (encoding.decode x) (encoding.decode y))).val)
      ⟨left.1.toNat, left.2⟩ ⟨right.1.toNat, right.2⟩
      (by simpa only [binaryTotal, hidx] using hindex)

/-- A native unary table read returns the encoded model-operation result. -/
theorem lookupUnary
    (encoding : Encoding Model) (op : Model → Model) (value : Code encoding)
    (hindex :
      (unaryByteIndex value.1).toNat <
        (unaryTotal encoding op).size) :
    (unaryTotal encoding op).uget
        (unaryByteIndex value.1) hindex =
      UInt8.ofNat
        (encoding.encode (op (encoding.decodeCode value))).val := by
  rw [uget_eq_get]
  unfold unaryTotal at hindex ⊢
  rw [ByteArray.getElem_ofFn]
  simp only [unaryByteIndex_toNat, Encoding.decodeCode]

/-- A native ternary table read returns the encoded model-operation result. -/
theorem lookupTernary
    (encoding : Encoding Model)
    (op : Model → Model → Model → Model)
    (left right addend : Code encoding)
    (hindex :
      (ternaryByteIndex (radixWord encoding) left.1 right.1 addend.1).toNat <
        (ternaryTotal encoding op).size) :
    (ternaryTotal encoding op).uget
        (ternaryByteIndex (radixWord encoding) left.1 right.1 addend.1)
        hindex =
      UInt8.ofNat
        (encoding.encode <|
          op (encoding.decodeCode left) (encoding.decodeCode right)
            (encoding.decodeCode addend)).val := by
  obtain ⟨hleftMul, hpair, hpairMul, hword⟩ :=
    ternaryIndex_noOverflow encoding (radixWord encoding)
      (radixWord_toNat encoding) left right addend
  have hidx :
      (ternaryByteIndex (radixWord encoding) left.1 right.1 addend.1).toNat =
        (left.1.toNat * encoding.radix + right.1.toNat) * encoding.radix +
          addend.1.toNat := by
    simpa only [radixWord_toNat] using
      ternaryByteIndex_toNat (radixWord encoding) left.1 right.1 addend.1
        hleftMul hpair hpairMul hword
  rw [uget_eq_get]
  simpa only [ternaryTotal, hidx, Encoding.decodeCode] using
    Tabulation.getElem_ternary encoding.radix
      (fun x y z => UInt8.ofNat
        (encoding.encode (op (encoding.decode x) (encoding.decode y) (encoding.decode z))).val)
      ⟨left.1.toNat, left.2⟩ ⟨right.1.toNat, right.2⟩ ⟨addend.1.toNat, addend.2⟩
      (by simpa only [ternaryTotal, hidx] using hindex)

end FloatLib.Floats.ExecFloat.Backend.TinyTable
