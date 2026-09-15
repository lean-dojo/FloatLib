/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.DPD.FieldsProof
public import FloatLib.Floats.Formats.DecimalInterchange.DPD.TrailingProof
public import FloatLib.Floats.Formats.DecimalInterchange.Codec.Proof

/-!
# DPD coefficient correctness and complete datum round trips

DPD coefficient and exponent packing recovers every valid datum after encoding. Decoding always
produces a valid datum, and canonicalization preserves that datum while removing redundant
encodings idempotently.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.DPD

theorem encodeFinite_lt (f : Format) (c e : Nat)
    (hc : c < f.coefficientBound) (he : e < f.exponentBound) :
    encodeFinite f c e < 30 * (f.exponentBase * f.trailingBase) := by
  apply encodeFields_lt
  · exact (Nat.div_lt_iff_lt_mul f.payloadBound_pos).mpr hc
  · exact he
  · exact encodeTrailing_lt _ _

theorem decodeFinite_valid (f : Format) (n : Nat)
    (hn : n < 30 * (f.exponentBase * f.trailingBase)) :
    (decodeFinite f n).1 < f.coefficientBound ∧
      (decodeFinite f n).2 < f.exponentBound := by
  have hf := (Nat.div_lt_iff_lt_mul
    (Nat.mul_pos f.exponentBase_pos f.trailingBase_pos)).mpr hn
  have hl := leadingDigit_lt (n / (f.exponentBase * f.trailingBase))
  have he := highExponent_lt _ hf
  have ht := decodeTrailing_lt f.declets (n % f.trailingBase)
  exact ⟨Bits.mul_add_lt_mul hl ht,
    Bits.mul_add_lt_mul he (Nat.mod_lt _ f.exponentBase_pos)⟩

/-- DPD decoding recovers the coefficient and biased exponent of every finite datum. -/
theorem decodeFinite_encodeFinite (f : Format) (c e : Nat)
    (hc : c < f.coefficientBound) (he : e < f.exponentBound) :
    decodeFinite f (encodeFinite f c e) = (c, e) := by
  have hl : c / f.payloadBound < 10 :=
    (Nat.div_lt_iff_lt_mul f.payloadBound_pos).mpr hc
  have hh : e / f.exponentBase < 3 :=
    (Nat.div_lt_iff_lt_mul f.exponentBase_pos).mpr he
  obtain ⟨hfield, hexponent, htrailing⟩ :=
    encodeFields_extract f (c / f.payloadBound) e _
      (encodeTrailing_lt f.declets (c % f.payloadBound))
  dsimp only [decodeFinite, encodeFinite]
  rw [hfield, hexponent, htrailing, leadingDigit_combination _ _ hl hh,
    highExponent_combination _ _ hl hh,
    decodeTrailing_encodeTrailing f.declets (c % f.payloadBound)
      (Nat.mod_lt c f.payloadBound_pos)]
  apply Prod.ext <;> dsimp
  · simpa only [Nat.mul_comm] using Nat.div_add_mod c f.payloadBound
  · simpa only [Nat.mul_comm] using Nat.div_add_mod e f.exponentBase

/-- The executable DPD fields satisfy the shared codec laws. -/
theorem lawful : codec.Lawful where
  encodeFinite_lt := encodeFinite_lt
  decodeFinite_valid := decodeFinite_valid
  decodeFinite_encodeFinite := decodeFinite_encodeFinite
  encodePayload_lt f p _ := encodeTrailing_lt f.declets p
  decodePayload_lt f n _ := decodeTrailing_lt f.declets n
  decodePayload_encodePayload f p hp := decodeTrailing_encodeTrailing f.declets p hp

/-- DPD encoding and decoding preserve the complete datum, including its cohort. -/
theorem decode_encode (f : Format) (d : Datum) (h : d.Valid f) :
    decode f (codec.encode f d) = d :=
  codec.decode_encode lawful f d h

theorem decode_valid (f : Format) (word : BitVec f.bitWidth) : (decode f word).Valid f :=
  codec.decode_valid lawful f word

/-- Replacing redundant declets does not alter the represented datum. -/
theorem decode_canonicalize (f : Format) (word : BitVec f.bitWidth) :
    decode f (canonicalize f word) = decode f word :=
  codec.decode_canonicalize lawful f word

theorem canonicalize_idempotent (f : Format) (word : BitVec f.bitWidth) :
    canonicalize f (canonicalize f word) = canonicalize f word :=
  codec.canonicalize_idempotent lawful f word

end FloatLib.Floats.Formats.DecimalInterchange.DPD
