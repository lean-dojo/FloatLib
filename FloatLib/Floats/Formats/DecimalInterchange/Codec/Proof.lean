/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Codec.BitsProof

/-!
# Decimal codec correctness

The coefficient laws imply a round trip for every representable datum and
semantic preservation and idempotence of word canonicalization. Equality here
preserves each datum's quantum exponent, signed zero, and NaN metadata, not only
the rational value of ordinary numbers.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Codec

/-- The obligations for an actual coefficient encoding. BID and DPD each prove
these laws for their executable field manipulations. -/
structure Lawful (codec : Codec) : Prop where
  encodeFinite_lt : ∀ (f : Format) (c e : Nat),
    c < f.coefficientBound → e < f.exponentBound →
    codec.encodeFinite f c e < 30 * (f.exponentBase * f.trailingBase)
  decodeFinite_valid : ∀ (f : Format) (n : Nat),
    n < 30 * (f.exponentBase * f.trailingBase) →
    (codec.decodeFinite f n).1 < f.coefficientBound ∧
      (codec.decodeFinite f n).2 < f.exponentBound
  decodeFinite_encodeFinite : ∀ (f : Format) (c e : Nat),
    c < f.coefficientBound → e < f.exponentBound →
    codec.decodeFinite f (codec.encodeFinite f c e) = (c, e)
  encodePayload_lt : ∀ (f : Format) (p : Nat),
    p < f.payloadBound → codec.encodePayload f p < f.trailingBase
  decodePayload_lt : ∀ (f : Format) (n : Nat),
    n < f.trailingBase → codec.decodePayload f n < f.payloadBound
  decodePayload_encodePayload : ∀ (f : Format) (p : Nat),
    p < f.payloadBound → codec.decodePayload f (codec.encodePayload f p) = p

private theorem finite_lt_signBase (f : Format) (n : Nat)
    (h : n < 30 * (f.exponentBase * f.trailingBase)) : n < f.signBase := by
  simp only [Format.signBase, Nat.mul_assoc]
  omega

private theorem nan_fields (f : Format) (signaling : Bool) (p : Nat)
    (h : p < f.trailingBase) :
    let n := 31 * (f.exponentBase * f.trailingBase) +
      (if signaling then f.exponentBase * f.trailingBase / 2 else 0) + p
    n < f.signBase ∧ n / (f.exponentBase * f.trailingBase) = 31 ∧
      (n / (f.exponentBase * f.trailingBase / 2) % 2 == 1) = signaling ∧
      n % f.trailingBase = p := by
  let half := 2 ^ (f.exponentBits - 1) * f.trailingBase
  let bit : Nat := if signaling then 1 else 0
  have ht : f.trailingBase ≤ half :=
    Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide))
  have hp : p < half := h.trans_le ht
  have hh : 0 < half := f.trailingBase_pos.trans_le ht
  have hg : f.exponentBase * f.trailingBase = 2 * half := by
    rw [f.exponentBase_eq_two_mul, Nat.mul_assoc]
  have hb : bit < 2 := by cases signaling <;> decide
  have hs : (if signaling then half else 0) = bit * half := by
    cases signaling <;> simp [bit]
  have hr : bit * half + p < 2 * half := Bits.mul_add_lt_mul hb hp
  dsimp only
  simp only [Format.signBase, Nat.mul_assoc, hg,
    Nat.mul_div_cancel_left half (by decide : 0 < 2), hs]
  refine ⟨?_, ?_, ?_, ?_⟩
  · omega
  · rw [Nat.add_assoc, Nat.add_comm (31 * (2 * half)),
      Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hr]
  · have hn : 31 * (2 * half) + bit * half + p = (62 + bit) * half + p := by
      rw [Nat.add_mul]
      omega
    rw [hn, Nat.add_comm, Nat.add_mul_div_right _ _ hh, Nat.div_eq_of_lt hp]
    cases signaling <;> simp [bit]
  · simp [half, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt h]

/-- Every bit pattern decodes to a representable datum, including noncanonical words. -/
theorem decode_valid (codec : Codec) (laws : codec.Lawful)
    (f : Format) (word : BitVec f.bitWidth) : (codec.decode f word).Valid f := by
  have hg : 0 < f.exponentBase * f.trailingBase :=
    Nat.mul_pos f.exponentBase_pos f.trailingBase_pos
  dsimp [decode]
  split
  · rename_i h
    apply (Datum.ofBiased_valid f _ _ _).mpr
    exact laws.decodeFinite_valid f _ ((Nat.div_lt_iff_lt_mul hg).mp h)
  · split
    · trivial
    · exact laws.decodePayload_lt f _ (Nat.mod_lt _ f.trailingBase_pos)

/-- Every representable datum survives encoding and decoding exactly. -/
theorem decode_encode (codec : Codec) (laws : codec.Lawful)
    (f : Format) (d : Datum) (h : d.Valid f) :
    codec.decode f (codec.encode f d) = d := by
  cases d with
  | finite s c q =>
    obtain ⟨hc, hq, he⟩ := h
    have hn := laws.encodeFinite_lt f c _ hc he
    have hb := finite_lt_signBase f _ hn
    have hg : 0 < f.exponentBase * f.trailingBase :=
      Nat.mul_pos f.exponentBase_pos f.trailingBase_pos
    have hf := (Nat.div_lt_iff_lt_mul hg).mpr hn
    simp only [encode, decode, Bits.negative_pack f s _ hb, Bits.payload_pack f s _ hb,
      hf, ↓reduceIte, laws.decodeFinite_encodeFinite f c _ hc he, Datum.ofBiased]
    congr
    omega
  | infinity s =>
    have hg : 0 < f.exponentBase * f.trailingBase :=
      Nat.mul_pos f.exponentBase_pos f.trailingBase_pos
    have hb : 30 * (f.exponentBase * f.trailingBase) < f.signBase := by
      simp only [Format.signBase, Nat.mul_assoc]
      omega
    have he : 30 * (f.exponentBase * f.trailingBase) /
        (f.exponentBase * f.trailingBase) = 30 := by
      exact Nat.mul_div_left 30 hg
    simp [encode, decode, Bits.negative_pack f s _ hb, Bits.payload_pack f s _ hb, he]
  | nan s signaling p =>
    obtain ⟨hb, he, hs, hp⟩ := nan_fields f signaling _
      (laws.encodePayload_lt f p h)
    simp only [encode, decode, Bits.negative_pack f s _ hb, Bits.payload_pack f s _ hb,
      he, show ¬(31 : Nat) < 30 by decide, show ¬(31 : Nat) = 30 by decide, ↓reduceIte,
      hs, hp, laws.decodePayload_encodePayload f p h]

/-- Canonicalization preserves all decoded information, including quantum and NaN payload. -/
theorem decode_canonicalize (codec : Codec) (laws : codec.Lawful)
    (f : Format) (word : BitVec f.bitWidth) :
    codec.decode f (codec.canonicalize f word) = codec.decode f word :=
  codec.decode_encode laws f _ (codec.decode_valid laws f word)

/-- Applying canonicalization twice has the same result as applying it once. -/
theorem canonicalize_idempotent (codec : Codec) (laws : codec.Lawful)
    (f : Format) (word : BitVec f.bitWidth) :
    codec.canonicalize f (codec.canonicalize f word) = codec.canonicalize f word := by
  simp only [canonicalize, codec.decode_encode laws f _ (codec.decode_valid laws f word)]

/-- An accepted checked encoding always decodes to the original datum. -/
theorem decode_of_encode?_eq_some (codec : Codec) (laws : codec.Lawful)
    (f : Format) (d : Datum) (word : BitVec f.bitWidth)
    (h : codec.encode? f d = some word) : codec.decode f word = d := by
  unfold encode? at h
  split at h
  · cases Option.some.inj h
    exact codec.decode_encode laws f d ‹d.Valid f›
  · simp at h

end FloatLib.Floats.Formats.DecimalInterchange.Codec
