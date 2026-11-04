/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.BID.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Codec.Proof

/-!
# BID coefficient correctness and complete datum round trips

Here BID meets the shared codec laws of `Codec.Proof`. Packing a coefficient and an exponent stays
within the field bounds, and decoding gives back every valid datum after encoding. Every decoded
word is valid. Canonicalization keeps the complete datum, applying it twice changes nothing, and
two words get the same canonical word if and only if they decode to the same datum.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.BID

/-- A biased exponent above a coefficient field `k` trailing fields wide packs below `3 * k`
exponent-continuation blocks. The two steering branches use `k = 8` and `k = 2`. -/
private theorem exponent_field_lt (f : Format) (k c e : Nat)
    (hc : c < k * f.trailingBase) (he : e < f.exponentBound) :
    e * (k * f.trailingBase) + c < 3 * k * (f.exponentBase * f.trailingBase) := by
  have h := Bits.mul_add_lt_mul he hc
  simp only [Format.exponentBound, Nat.mul_assoc, Nat.mul_left_comm] at h ⊢
  exact h

/-- Conversely, a field below `3 * k` exponent-continuation blocks has a valid biased exponent
above its `k`-wide coefficient field. -/
private theorem exponent_field_div_lt (f : Format) (k n : Nat) (hk : 0 < k)
    (hn : n < 3 * k * (f.exponentBase * f.trailingBase)) :
    n / (k * f.trailingBase) < f.exponentBound := by
  apply (Nat.div_lt_iff_lt_mul (Nat.mul_pos hk f.trailingBase_pos)).mpr
  simp only [Format.exponentBound, Nat.mul_assoc, Nat.mul_left_comm] at hn ⊢
  exact hn

private theorem small_fields_lt (f : Format) (c e : Nat)
    (hc : c < 8 * f.trailingBase) (he : e < f.exponentBound) :
    e * (8 * f.trailingBase) + c < 24 * (f.exponentBase * f.trailingBase) :=
  exponent_field_lt f 8 c e hc he

private theorem coefficient_remainder_lt (f : Format) (c : Nat)
    (hc : c < f.coefficientBound) (hs : ¬c < 8 * f.trailingBase) :
    c - 8 * f.trailingBase < 2 * f.trailingBase := by
  have h := hc.trans_le (Nat.mul_le_mul_left 10 f.payloadBound_le)
  omega

/-- A representable coefficient and biased exponent encode in BID below the combination patterns
reserved for infinities and NaNs, in both steering branches. -/
theorem encodeFinite_lt (f : Format) (c e : Nat)
    (hc : c < f.coefficientBound) (he : e < f.exponentBound) :
    encodeFinite f c e < 30 * (f.exponentBase * f.trailingBase) := by
  unfold encodeFinite
  split
  · have h := small_fields_lt f c e ‹_› he
    omega
  · have h := exponent_field_lt f 2 _ e (coefficient_remainder_lt f c hc ‹_›) he
    omega

/-- Every finite BID field pattern decodes to a coefficient and biased exponent within the format
bounds. An oversized significand decodes as zero. -/
theorem decodeFinite_valid (f : Format) (n : Nat)
    (hn : n < 30 * (f.exponentBase * f.trailingBase)) :
    (decodeFinite f n).1 < f.coefficientBound ∧
      (decodeFinite f n).2 < f.exponentBound := by
  constructor
  · dsimp only [decodeFinite]
    split
    · assumption
    · exact f.coefficientBound_pos
  · dsimp only [decodeFinite, biasedExponent]
    split
    · exact exponent_field_div_lt f 8 n (by decide) (by omega)
    · exact exponent_field_div_lt f 2 _ (by decide) (by omega)

private theorem finite_fields (f : Format) (c e : Nat)
    (hc : c < f.coefficientBound) (he : e < f.exponentBound) :
    rawCoefficient f (encodeFinite f c e) = c ∧
      biasedExponent f (encodeFinite f c e) = e := by
  unfold encodeFinite
  split
  · rename_i hs
    have hn := small_fields_lt f c e hs he
    simp only [rawCoefficient, biasedExponent, ite_eq_left hn]
    constructor
    · exact Nat.mul_add_mod_of_lt hs
    · exact Bits.mul_add_div_of_lt hs
  · rename_i hs
    have hn : ¬24 * (f.exponentBase * f.trailingBase) + e * (2 * f.trailingBase) +
        (c - 8 * f.trailingBase) < 24 * (f.exponentBase * f.trailingBase) := by omega
    simp only [rawCoefficient, biasedExponent, ite_eq_right hn]
    have hsub : 24 * (f.exponentBase * f.trailingBase) + e * (2 * f.trailingBase) +
        (c - 8 * f.trailingBase) - 24 * (f.exponentBase * f.trailingBase) =
        e * (2 * f.trailingBase) + (c - 8 * f.trailingBase) := by omega
    rw [hsub]
    have hr := coefficient_remainder_lt f c hc hs
    constructor
    · rw [Nat.mul_add_mod_of_lt hr]
      omega
    · exact Bits.mul_add_div_of_lt hr

/-- Recover both the coefficient and the biased exponent from either steering branch. -/
theorem decodeFinite_encodeFinite (f : Format) (c e : Nat)
    (hc : c < f.coefficientBound) (he : e < f.exponentBound) :
    decodeFinite f (encodeFinite f c e) = (c, e) := by
  obtain ⟨hc', he'⟩ := finite_fields f c e hc he
  simp [decodeFinite, hc', he', hc]

/-- Oversized BID significands denote zero while retaining the encoded exponent. -/
theorem decodeFinite_oversized (f : Format) (n : Nat)
    (h : f.coefficientBound ≤ rawCoefficient f n) :
    decodeFinite f n = (0, biasedExponent f n) := by
  simp [decodeFinite, Nat.not_lt.mpr h]

/-- An excessive BID NaN payload denotes zero rather than a decimal remainder. -/
theorem decodePayload_oversized (f : Format) (n : Nat) (h : f.payloadBound ≤ n) :
    decodePayload f n = 0 := by
  simp [decodePayload, Nat.not_lt.mpr h]

/-- The executable BID fields satisfy the shared codec laws. -/
theorem lawful : codec.Lawful where
  encodeFinite_lt := encodeFinite_lt
  decodeFinite_valid := decodeFinite_valid
  decodeFinite_encodeFinite := decodeFinite_encodeFinite
  encodePayload_lt f p hp := Nat.lt_of_lt_of_le hp f.payloadBound_le
  decodePayload_lt f n _ := by
    dsimp [codec, decodePayload]
    split
    · assumption
    · exact f.payloadBound_pos
  decodePayload_encodePayload f p hp := by
    simp [codec, decodePayload, hp]

/-- Encoding a representable datum and decoding the word gives the datum back unchanged. -/
theorem decode_encode (f : Format) (d : Datum) (h : d.Valid f) :
    decode f (codec.encode f d) = d :=
  codec.decode_encode lawful f d h

/-- Every BID word of the format's width, noncanonical encodings included, decodes to a valid datum.
-/
theorem decode_valid (f : Format) (word : BitVec f.bitWidth) : (decode f word).Valid f :=
  codec.decode_valid lawful f word

/-- Canonicalizing a BID word preserves its sign, quantum exponent, and special metadata. -/
theorem decode_canonicalize (f : Format) (word : BitVec f.bitWidth) :
    decode f (canonicalize f word) = decode f word :=
  codec.decode_canonicalize lawful f word

/-- Canonicalizing an already canonical BID word changes no bit. -/
theorem canonicalize_idempotent (f : Format) (word : BitVec f.bitWidth) :
    canonicalize f (canonicalize f word) = canonicalize f word :=
  codec.canonicalize_idempotent lawful f word

/-- Two BID words have the same canonical word if and only if they decode to the same datum, so
noncanonical significands and unused special-value bits are collapsed onto one word. -/
theorem canonicalize_eq_canonicalize_iff (f : Format) (left right : BitVec f.bitWidth) :
    canonicalize f left = canonicalize f right ↔ decode f left = decode f right :=
  codec.canonicalize_eq_canonicalize_iff lawful f left right

end FloatLib.Floats.Formats.DecimalInterchange.BID
