/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Model.Lean

/-!
# Canonical representations in Lean's floating-point model

The bridge uses the conventional IEEE interpretation of the exponent and fraction widths.
Packing an unpacked value need not preserve an arbitrary mantissa and exponent, but unpacking
packed bits always gives a representable value. Repacking those values preserves every bit
except the sign and payload of a noncanonical NaN.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open Float.Model (Format UnpackedFloat)
open Float.Model.UnpackedFloat

/--
Repacking a bit pattern changes only NaN encodings. This statement is independent of any
fixed exponent or fraction width.
-/
theorem pack_unpack_eq (spec : Format) (bits : BitVec spec.numBits) :
    pack spec (unpack spec bits) =
      if unpackExponent bits = -1#_ ∧ unpackMantissa bits ≠ 0#_ then
        packedNaN spec
      else bits := by
  have hcomponents := packComponents_unpackComponents spec bits
  by_cases he : unpackExponent bits = -1#_
  · by_cases hm : unpackMantissa bits = 0#_
    · simpa [unpack, he, hm, pack, packedInfinity] using hcomponents
    · simp [unpack, he, hm, pack]
  · have hbound : (unpackExponent bits).toNat + 1 < 2 ^ spec.exponentBits := by
      have hlt := (unpackExponent bits).isLt
      have hne : (unpackExponent bits).toNat ≠ 2 ^ spec.exponentBits - 1 := by
        simpa [← BitVec.toNat_inj, BitVec.neg_one_eq_allOnes] using he
      omega
    by_cases hezero : unpackExponent bits = 0#_
    · by_cases hm : unpackMantissa bits = 0#_
      · simpa [unpack, he, hezero, hm, pack, packedZero, Nat.ne_zero_of_lt spec.he]
          using hcomponents
      · have hmpos : (unpackMantissa bits).toNat ≠ 0 := by
          simpa [← BitVec.toNat_inj] using hm
        have hlog : (unpackMantissa bits).toNat.log2 <
            spec.mantissaBitsWithoutImplicit :=
          (Nat.log2_lt hmpos).2 (unpackMantissa bits).isLt
        have hbiased : ((0 : Int) - (spec.exponentBias + spec.mantissaBitsWithoutImplicit) +
            1 + spec.exponentBias + spec.mantissaBitsWithoutImplicit).toNat = 1 := by
          omega
        have hexp : 2 < 2 ^ spec.exponentBits := by
          simpa using Nat.pow_lt_pow_right (by decide : 1 < (2 : Nat))
            (show 1 < spec.exponentBits by have := spec.he; omega)
        have hshort : (unpackMantissa bits).toNat.log2 + 1 ≠ spec.mantissaBits := by
          unfold Format.mantissaBits
          omega
        simp only [unpack, he, false_and, ite_false]
        simp only [hezero, ite_true, hm, dite_false, BitVec.toNat_ofNat, Nat.zero_mod,
          Int.natCast_zero, pack, hbiased, not_le.mpr hexp, ite_false, hshort,
          BitVec.ofNat_toNat, BitVec.setWidth_eq]
        simpa only [hezero] using hcomponents
    · have hmantissa : (1#1 ++ unpackMantissa bits).toNat =
          2 ^ spec.mantissaBitsWithoutImplicit + (unpackMantissa bits).toNat := by
        rw [BitVec.toNat_append,
          ← Nat.shiftLeft_add_eq_or_of_lt (unpackMantissa bits).isLt]
        simp [Nat.shiftLeft_eq]
      have hmpos : (1#1 ++ unpackMantissa bits).toNat ≠ 0 := by simp
      have hlog : (1#1 ++ unpackMantissa bits).toNat.log2 =
          spec.mantissaBitsWithoutImplicit := by
        apply (Nat.log2_eq_iff hmpos).2
        rw [hmantissa, Nat.pow_succ]
        have := (unpackMantissa bits).isLt
        omega
      have hbiased : (((unpackExponent bits).toNat : Int) -
            (spec.exponentBias + spec.mantissaBitsWithoutImplicit) +
            spec.exponentBias + spec.mantissaBitsWithoutImplicit).toNat =
          (unpackExponent bits).toNat := by
        rw [show ((unpackExponent bits).toNat : Int) -
            (spec.exponentBias + spec.mantissaBitsWithoutImplicit) +
            spec.exponentBias + spec.mantissaBitsWithoutImplicit =
            (unpackExponent bits).toNat by omega, Int.toNat_natCast]
      have hfraction : BitVec.ofNat spec.mantissaBitsWithoutImplicit
          (1#1 ++ unpackMantissa bits).toNat = unpackMantissa bits := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, hmantissa, Nat.add_mod]
        simp
      have hnormal : (1#1 ++ unpackMantissa bits).toNat.log2 + 1 = spec.mantissaBits := by
        simp only [hlog, Format.mantissaBits, Nat.add_comm]
      simpa only [unpack, he, hezero, ite_false, false_and, pack, hbiased,
        not_le.mpr hbound, hnormal, ite_true, BitVec.ofNat_toNat, BitVec.setWidth_eq, hfraction]
        using hcomponents

/-- A valid packed value is recovered exactly after unpacking and repacking. -/
theorem pack_unpack_of_valid (spec : Format) (bits : BitVec spec.numBits)
    (hvalid : spec.Valid bits) :
    pack spec (unpack spec bits) = bits := by
  rw [pack_unpack_eq]
  split
  · rename_i h
    exact (hvalid.eq_packedNaN h.1 h.2).symm
  · rfl

/-- The canonical NaN payload unpacks to the model's single NaN value. -/
@[simp] theorem unpack_pack_notANumber (spec : Format) :
    unpack spec (pack spec .notANumber) = .notANumber := by
  have hquiet : (1#spec.mantissaBitsWithoutImplicit <<<
      (spec.mantissaBitsWithoutImplicit - 1)) ≠ 0#_ := by
    intro h
    have hbit := congrArg
      (fun bits : BitVec spec.mantissaBitsWithoutImplicit =>
        bits.getLsbD (spec.mantissaBitsWithoutImplicit - 1)) h
    have hindex : spec.mantissaBitsWithoutImplicit - 1 <
        spec.mantissaBitsWithoutImplicit := Nat.sub_lt spec.hm (by decide)
    simp [hindex] at hbit
  simp [pack, packedNaN, unpack, hquiet]

/-- Unpacking forgets precisely the information discarded by NaN canonicalization. -/
theorem unpack_pack_unpack (spec : Format) (bits : BitVec spec.numBits) :
    unpack spec (pack spec (unpack spec bits)) = unpack spec bits := by
  rw [pack_unpack_eq]
  split
  · rename_i h
    have hnan : unpack spec (packedNaN spec) = .notANumber :=
      unpack_pack_notANumber spec
    rw [hnan]
    simp only [unpack, h.1, h.2, ite_true, ite_false]
  · rfl

/-- Canonicalization fixes precisely the bit patterns admitted by Lean's packed model. -/
theorem canonicalizeModel_eq_self_iff {fmt : FloatFormat} (value : Model fmt) :
    canonicalizeModel value = value ↔ IsModelCanonical value := by
  constructor
  · intro h
    rw [← h]
    exact isModelCanonical_canonicalizeModel value
  · intro h
    unfold canonicalizeModel ofModel toModel
    rw [pack_unpack_of_valid _ _ h, ofModelBits_toModelBits]

/-- Canonical packed words round-trip exactly through the unpacked model. -/
@[simp] theorem canonicalizeModel_eq_self {fmt : FloatFormat} (value : Model fmt)
    (h : IsModelCanonical value) : canonicalizeModel value = value :=
  (canonicalizeModel_eq_self_iff value).2 h

/-- A second canonicalization leaves the result unchanged. -/
@[simp] theorem canonicalizeModel_idempotent {fmt : FloatFormat} (value : Model fmt) :
    canonicalizeModel (canonicalizeModel value) = canonicalizeModel value :=
  canonicalizeModel_eq_self _ (isModelCanonical_canonicalizeModel value)

/-- Values packed from the unpacked model are already canonical. -/
@[simp] theorem canonicalizeModel_ofModel (fmt : FloatFormat) (value : UnpackedFloat) :
    canonicalizeModel (ofModel fmt value) = ofModel fmt value :=
  canonicalizeModel_eq_self _ (isModelCanonical_ofModel fmt value)

/-- Canonicalization preserves the entire unpacked value, including the sign of zero. -/
@[simp] theorem toModel_canonicalizeModel {fmt : FloatFormat} (value : Model fmt) :
    toModel (canonicalizeModel value) = toModel value :=
  unpack_pack_unpack _ _

/--
Equality after unpacking is exactly equality of canonical packed representations.
Operation refinement proofs may therefore use either form of the representation relation.
-/
theorem toModel_eq_iff_canonicalizeModel_eq {fmt : FloatFormat} (left right : Model fmt) :
    toModel left = toModel right ↔ canonicalizeModel left = canonicalizeModel right := by
  constructor
  · exact congrArg (ofModel fmt)
  · intro h
    simpa only [toModel_canonicalizeModel] using congrArg toModel h

/-- The unpacked interpretation is injective on canonical packed representations. -/
theorem eq_of_toModel_eq {fmt : FloatFormat} {left right : Model fmt}
    (hleft : IsModelCanonical left) (hright : IsModelCanonical right)
    (h : toModel left = toModel right) : left = right := by
  simpa only [canonicalizeModel_eq_self left hleft, canonicalizeModel_eq_self right hright]
    using (toModel_eq_iff_canonicalizeModel_eq left right).1 h

end FloatLib.Floats.Formats.BinaryInterchange.Model
