/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Batteries.Data.ByteArray

/-!
# Finite byte encodings

The generic byte-table backend represents a format through a finite encoding bijection. A format
contributes only a proved bijection between its exact model and a nonempty set of at most 256
ordinals. No IEEE, Posit, rounding, or exceptional-value policy is built into this layer.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Backend.TinyTable

universe u

/-- `ByteArray.uget` and proof-indexed natural lookup select the same byte. -/
theorem uget_eq_get (array : ByteArray) (index : USize)
    (hindex : index.toNat < array.size) :
    array.uget index hindex = array[index.toNat] := by
  cases array with
  | mk data => rfl

/--
A proved finite encoding of an exact model.

`radix_le_byte` is the only storage-specific assumption. The inverse laws make table generation
and lookup representation-preserving; no numerical property is required.
-/
structure Encoding (Model : Type u) where
  /-- Number of valid code words. -/
  radix : Nat
  /-- The encoding is nonempty. -/
  radix_pos : 0 < radix
  /-- Every code word fits in one byte. -/
  radix_le_byte : radix ≤ 256
  /-- Decode one valid ordinal into the exact model. -/
  decode : Fin radix → Model
  /-- Encode one exact model as its unique ordinal. -/
  encode : Model → Fin radix
  /-- Decoding after encoding preserves the model. -/
  decode_encode : ∀ value, decode (encode value) = value
  /-- Encoding after decoding preserves the ordinal. -/
  encode_decode : ∀ code, encode (decode code) = code

variable {Model : Type u}

/-- Direct byte carrier for one finite encoding. Its range proof is erased. -/
abbrev Code (encoding : Encoding Model) :=
  { bits : UInt8 // bits.toNat < encoding.radix }

namespace Encoding

variable {Model : Type u} (encoding : Encoding Model)

/-- Convert a direct byte code into the exact model. -/
@[always_inline, inline] def decodeCode (code : Code encoding) : Model :=
  encoding.decode ⟨code.1.toNat, code.2⟩

/-- Pack an exact model into the direct byte carrier. -/
@[always_inline, inline] def encodeCode (value : Model) : Code encoding :=
  ⟨UInt8.ofNat (encoding.encode value).val, by
    rw [UInt8.toNat_ofNat']
    have hbyte : (encoding.encode value).val < 256 :=
      Nat.lt_of_lt_of_le (encoding.encode value).isLt encoding.radix_le_byte
    rw [Nat.mod_eq_of_lt hbyte]
    exact (encoding.encode value).isLt⟩

/-- Decoding a directly encoded model value recovers that value. -/
@[simp] theorem decodeCode_encodeCode (value : Model) :
    encoding.decodeCode (encoding.encodeCode value) = value := by
  let code := encoding.encode value
  have hbyte : (encoding.encode value).val < 256 :=
    Nat.lt_of_lt_of_le (encoding.encode value).isLt encoding.radix_le_byte
  have hnat :
      (UInt8.ofNat (encoding.encode value).val).toNat =
        (encoding.encode value).val := by
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt hbyte]
  have hcode :
      (⟨(UInt8.ofNat (encoding.encode value).val).toNat,
          by
            simpa only [hnat] using (encoding.encode value).isLt⟩ :
        Fin encoding.radix) =
        code := by
    apply Fin.ext
    exact hnat
  change encoding.decode
      ⟨(UInt8.ofNat (encoding.encode value).val).toNat, _⟩ = value
  rw [hcode]
  exact encoding.decode_encode value

/-- Encoding a decoded direct byte code recovers that code. -/
@[simp] theorem encodeCode_decodeCode (code : Code encoding) :
    encoding.encodeCode (encoding.decodeCode code) = code := by
  let ordinal : Fin encoding.radix := ⟨code.1.toNat, code.2⟩
  have hordinal :
      encoding.encode (encoding.decode ordinal) = ordinal :=
    encoding.encode_decode ordinal
  have hval :
      (encoding.encode (encoding.decode ordinal)).val = code.1.toNat := by
    exact congrArg Fin.val hordinal
  apply Subtype.ext
  apply UInt8.toNat_inj.mp
  change
    (UInt8.ofNat (encoding.encode (encoding.decode ordinal)).val).toNat =
      code.1.toNat
  rw [hval, UInt8.toNat_ofNat', Nat.mod_eq_of_lt (UInt8.toNat_lt code.1)]

end Encoding

end FloatLib.Floats.ExecFloat.Backend.TinyTable
