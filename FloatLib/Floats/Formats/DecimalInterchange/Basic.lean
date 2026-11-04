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

This module proves that the BID and DPD codecs lose nothing. For every `Format` descriptor,
decimal32, decimal64, and decimal128 included, encoding a datum and decoding the word gives the
datum back, and every word decodes to a representable datum. Canonicalizing a word or converting it
to the other encoding keeps that datum whole: the cohort exponent, the sign of a zero or an
infinity, and a NaN's sign, signaling bit, and payload.

Both codecs follow IEEE 754-2019 §§3.3, 3.5 and 5.5.2, Tables 3.3, 3.4 and 3.6, and
Mike Cowlishaw's *Densely Packed Decimal Encoding*:
<https://speleotrove.com/decimal/DPDecimal.html>.
The IEEE standard is identified by DOI `10.1109/IEEESTD.2019.8766229`.

Everything here is about representation. For decimal arithmetic, with its rounding,
preferred-exponent, and exception theorems, import `Arithmetic.Basic`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

namespace Encoding

/-- Both supported encodings satisfy the shared laws through their actual field codecs. -/
theorem lawful (encoding : Encoding) : encoding.codec.Lawful := by
  cases encoding
  · exact BID.lawful
  · exact DPD.lawful

/-- In both BID and DPD, every word of the format's width, noncanonical encodings included, decodes
to a valid datum. -/
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
  rw [ite_eq_left (encoding.decode_valid f word)]
  rfl

/-- In both encodings, canonicalizing a word does not change the datum it decodes to. -/
theorem decode_canonicalize (encoding : Encoding) (f : Format) (word : BitVec f.bitWidth) :
    encoding.decode f (encoding.canonicalize f word) = encoding.decode f word :=
  encoding.codec.decode_canonicalize encoding.lawful f word

/-- In both encodings, canonicalizing an already canonical word changes no bit. -/
theorem canonicalize_idempotent (encoding : Encoding) (f : Format)
    (word : BitVec f.bitWidth) :
    encoding.canonicalize f (encoding.canonicalize f word) =
      encoding.canonicalize f word :=
  encoding.codec.canonicalize_idempotent encoding.lawful f word

/-- In both encodings, two words have the same canonical word if and only if they decode to the
same datum. -/
theorem canonicalize_eq_canonicalize_iff (encoding : Encoding) (f : Format)
    (left right : BitVec f.bitWidth) :
    encoding.canonicalize f left = encoding.canonicalize f right ↔
      encoding.decode f left = encoding.decode f right :=
  encoding.codec.canonicalize_eq_canonicalize_iff encoding.lawful f left right

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

/-- Converting to a different encoding and back yields the canonical source word, so an originally
redundant encoding need not be recovered bit for bit. When the two encodings are equal, both
conversions copy the word and the original word is returned unchanged. -/
theorem transcode_transcode (source target : Encoding) (f : Format)
    (word : BitVec f.bitWidth) :
    transcode target source f (transcode source target f word) =
      if source = target then word else source.canonicalize f word := by
  by_cases h : source = target
  · subst target
    simp
  · rw [transcode, ite_eq_right (Ne.symm h), decode_transcode, ite_eq_right h]
    rfl

end FloatLib.Floats.Formats.DecimalInterchange
