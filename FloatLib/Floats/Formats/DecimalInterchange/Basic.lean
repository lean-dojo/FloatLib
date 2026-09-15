/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.BID.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.DPD.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.DatumProof
public import FloatLib.Floats.Formats.DecimalInterchange.Runtime

/-!
# Decimal interchange codecs and proofs

The executable BID and DPD implementations satisfy exact datum round trips for
every `Format` descriptor, including decimal32, decimal64, and decimal128.
Every word decodes to a representable datum.
Canonicalization and conversion between encodings preserve that datum, including
cohort exponent, signed zero, infinity sign, and NaN sign, signaling bit, and payload.

The specifications are IEEE 754-2019 §§3.3, 3.5 and 5.5.2, Tables 3.3–3.4 and 3.6, and
Mike Cowlishaw's *Densely Packed Decimal Encoding*:
<https://speleotrove.com/decimal/DPDecimal.html>.
The IEEE standard is identified by DOI `10.1109/IEEESTD.2019.8766229`.

These are representation guarantees. Import `Arithmetic.Basic` for decimal
arithmetic and its rounding, preferred-exponent, and exception theorems.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

namespace Encoding

/-- Both supported encodings satisfy the shared laws through their actual field codecs. -/
theorem lawful (encoding : Encoding) : encoding.codec.Lawful := by
  cases encoding
  · exact BID.lawful
  · exact DPD.lawful

theorem decode_valid (encoding : Encoding) (f : Format) (word : BitVec f.bitWidth) :
    (encoding.decode f word).Valid f :=
  encoding.codec.decode_valid encoding.lawful f word

/-- Successful checked encoding retains every component of the input datum. -/
theorem decode_of_encode?_eq_some (encoding : Encoding) (f : Format)
    (datum : Datum) (word : BitVec f.bitWidth)
    (h : encoding.encode? f datum = some word) :
    encoding.decode f word = datum :=
  encoding.codec.decode_of_encode?_eq_some encoding.lawful f datum word h

/-- Re-encoding any decoded word succeeds and produces its canonical representative. -/
theorem encode?_decode (encoding : Encoding) (f : Format) (word : BitVec f.bitWidth) :
    encoding.encode? f (encoding.decode f word) = some (encoding.canonicalize f word) := by
  change (if (encoding.decode f word).Valid f then
    some (encoding.codec.encode f (encoding.decode f word)) else none) = _
  rw [if_pos (encoding.decode_valid f word)]
  rfl

theorem decode_canonicalize (encoding : Encoding) (f : Format) (word : BitVec f.bitWidth) :
    encoding.decode f (encoding.canonicalize f word) = encoding.decode f word :=
  encoding.codec.decode_canonicalize encoding.lawful f word

theorem canonicalize_idempotent (encoding : Encoding) (f : Format)
    (word : BitVec f.bitWidth) :
    encoding.canonicalize f (encoding.canonicalize f word) =
      encoding.canonicalize f word :=
  encoding.codec.canonicalize_idempotent encoding.lawful f word

end Encoding

/-- Re-encoding to the same encoding is a bit-for-bit copy, including noncanonical words. -/
@[simp] theorem transcode_self (encoding : Encoding) (f : Format)
    (word : BitVec f.bitWidth) : transcode encoding encoding f word = word := by
  simp [transcode]

/-- Conversion preserves the complete datum, including special values. -/
theorem decode_transcode (source target : Encoding) (f : Format)
    (word : BitVec f.bitWidth) :
    target.decode f (transcode source target f word) = source.decode f word := by
  unfold transcode
  split
  · rename_i h
    subst target
    rfl
  · exact target.codec.decode_encode target.lawful f _ (source.decode_valid f word)

/-- Conversion to the other encoding and back recovers the canonical source word.
An originally redundant encoding need not be recovered bit for bit. -/
theorem transcode_transcode (source target : Encoding) (f : Format)
    (word : BitVec f.bitWidth) :
    transcode target source f (transcode source target f word) =
      if source = target then word else source.canonicalize f word := by
  by_cases h : source = target
  · subst target
    simp
  · rw [transcode, if_neg (Ne.symm h), decode_transcode, if_neg h]
    rfl

end FloatLib.Floats.Formats.DecimalInterchange
