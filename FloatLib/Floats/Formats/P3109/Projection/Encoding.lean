/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Proof
public import FloatLib.Floats.Formats.P3109.Projection.Runtime
public import FloatLib.Numerics.Exact.Dyadic.Order

/-!
# Direct encoding for P3109 projection

The direct encoder and decoder satisfy the inverse laws needed by P3109 projection. Further
contracts relate executable datum comparison to the mathematical `SameDatum` relation and
specify the checked encoder. Precision rounding and saturation correctness live in later
modules.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109

namespace Format

/--
The encoder on a record whose exponent row is already selected.

When the leading exponent `max (log2 s + e) minNormal` equals `e + (P - 1)`, no shift is needed
and the encoder reads the trailing field and biased exponent straight from the record.
-/
private theorem encodePositiveFinite_mk_of_max_eq
    (format : Format) (significand : Nat) (exponent : Int)
    (hzero : significand ≠ 0)
    (hmax : max (Int.ofNat significand.log2 + exponent) format.minimumNormalExponent =
      exponent + Int.ofNat format.trailingBits) :
    Internal.encodePositiveFinite format ⟨false, significand, exponent⟩ =
      if significand < 2 ^ format.trailingBits then
        significand % 2 ^ format.trailingBits
      else
        significand % 2 ^ format.trailingBits +
          Int.toNat (exponent + Int.ofNat format.trailingBits + Int.ofNat format.exponentBias) *
            2 ^ format.trailingBits := by
  unfold Internal.encodePositiveFinite
  simp only [hzero, beq_iff_eq, if_false, hmax]
  rw [show exponent - (exponent + Int.ofNat format.trailingBits) + Int.ofNat format.trailingBits =
    Int.ofNat 0 by simp only [Int.ofNat_eq_natCast]; omega]
  simp

/--
Encoding a decoded positive finite row recovers its natural-number code.

The result is width-independent: it follows from the descriptor's precision and exponent bias,
including `P = 1`, rather than from an enumerated codebook.
-/
private theorem encodePositiveFinite_decodePositiveFinite
    (format : Format) (bits : Nat) :
    Internal.encodePositiveFinite format
        (format.decodePositiveFinite bits) = bits := by
  by_cases hzero : bits = 0
  · simp [hzero, Internal.encodePositiveFinite]
  have hunit : 0 < 2 ^ format.trailingBits := Nat.two_pow_pos _
  have hTi := format.trailingBits_int
  simp only [Int.ofNat_eq_natCast] at hTi
  by_cases hrow : bits / 2 ^ format.trailingBits = 0
  · have hlt : bits < 2 ^ format.trailingBits :=
      (Nat.div_eq_zero_iff.mp hrow).resolve_left hunit.ne'
    have hlog : bits.log2 < format.trailingBits := (Nat.log2_lt hzero).2 hlt
    rw [format.decodePositiveFinite_of_biasedExponent_eq_zero bits hzero hrow,
      Nat.mod_eq_of_lt hlt, encodePositiveFinite_mk_of_max_eq _ _ _ hzero, if_pos hlt,
      Nat.mod_eq_of_lt hlt]
    rw [max_eq_right] <;>
      unfold minimumQuantumExponent minimumNormalExponent <;>
      simp only [Int.ofNat_eq_natCast] <;>
      omega
  · have hmod := Nat.mod_lt bits hunit
    have hrow_pos := Nat.pos_of_ne_zero hrow
    have hlog : (2 ^ format.trailingBits + bits % 2 ^ format.trailingBits).log2 =
        format.trailingBits :=
      (Nat.log2_eq_iff (by omega)).2 ⟨Nat.le_add_right _ _, by rw [Nat.pow_succ]; omega⟩
    rw [format.decodePositiveFinite_of_biasedExponent_ne_zero bits hzero hrow,
      encodePositiveFinite_mk_of_max_eq _ _ _ (by omega), if_neg (by omega),
      Nat.add_mod_left, Nat.mod_eq_of_lt hmod,
      show Int.ofNat (bits / 2 ^ format.trailingBits) - Int.ofNat format.exponentBias + 1 -
          Int.ofNat format.precision + Int.ofNat format.trailingBits +
          Int.ofNat format.exponentBias = Int.ofNat (bits / 2 ^ format.trailingBits) by
        simp only [Int.ofNat_eq_natCast]
        omega,
      Int.ofNat_eq_natCast, Int.toNat_natCast, Nat.mul_comm]
    · exact Nat.mod_add_div bits _
    · rw [hlog, max_eq_left] <;>
        simp only [minimumNormalExponent, Int.ofNat_eq_natCast] <;>
        omega

/-- Encoding a positive finite decoded row through the full datum encoder recovers that row. -/
private theorem encodeDatumNat_finite_decodePositiveFinite
    (format : Format) (bits : Nat) :
    Internal.encodeDatumNat format
        (.finite (format.decodePositiveFinite bits)) = bits := by
  by_cases bits_eq_zero : bits = 0
  · simp [bits_eq_zero, Internal.encodeDatumNat]
  have hne := (format.decodePositiveFinite_significand_eq_zero_iff bits).not.mpr bits_eq_zero
  simp only [Internal.encodeDatumNat, beq_iff_eq, hne, if_false, decodePositiveFinite_negative,
    Bool.false_eq_true]
  exact format.encodePositiveFinite_decodePositiveFinite bits

/-- Encoding the negation of a decoded positive row lands in the mirrored half of the codes. -/
private theorem encodeDatumNat_finite_neg_decodePositiveFinite
    (format : Format) (bits : Nat)
    (bits_ne_zero : bits ≠ 0) :
    Internal.encodeDatumNat format
        (.finite (format.decodePositiveFinite bits).neg) =
      format.signBoundary + bits := by
  have hne := (format.decodePositiveFinite_significand_eq_zero_iff bits).not.mpr bits_ne_zero
  have hrecord :
      (⟨false, (format.decodePositiveFinite bits).significand,
        (format.decodePositiveFinite bits).exponent⟩ : Numerics.Dyadic) =
        format.decodePositiveFinite bits :=
    Numerics.Dyadic.ext (format.decodePositiveFinite_negative bits).symm rfl rfl
  simp only [Internal.encodeDatumNat, Numerics.Dyadic.neg_significand, beq_iff_eq, hne, if_false,
    Numerics.Dyadic.neg_negative, Numerics.Dyadic.neg_exponent, decodePositiveFinite_negative,
    Bool.not_false, if_true]
  rw [hrecord, format.encodePositiveFinite_decodePositiveFinite]

/--
Encoding any decoded natural-number code recovers that code.

The statement is intentionally independent of a bit-width bound. Width reduction belongs to
`BitVec`; the P3109 row formulas themselves are inverse for every natural row number.
-/
private theorem encodeDatumNat_decodeNat
    (format : Format) (bits : Nat) :
    Internal.encodeDatumNat format (format.decodeNat bits) = bits := by
  have hfinite := format.encodeDatumNat_finite_decodePositiveFinite
  have hneg : format.signBoundary < bits →
      Internal.encodeDatumNat format
          (.finite (format.decodePositiveFinite (bits - format.signBoundary)).neg) =
        format.signBoundary + (bits - format.signBoundary) :=
    fun h => format.encodeDatumNat_finite_neg_decodePositiveFinite _ (Nat.sub_ne_zero_of_lt h)
  have hsigned := format.positiveInfinityBits_ne_signBoundary_of_signed
  have hsigned' := format.negativeInfinityBits_ne_signBoundary_of_signed
  have hsigned'' := format.negativeInfinityBits_ne_positiveInfinityBits_of_signed
  have hunsigned := format.positiveInfinityBits_ne_nanBits_of_unsigned
  have hnan : ∀ e, Internal.encodeDatumNat format (.exceptional e) = format.nanBits :=
    fun _ => rfl
  have hpinf : Internal.encodeDatumNat format (.infinity false) = format.positiveInfinityBits :=
    rfl
  have hninf : Internal.encodeDatumNat format (.infinity true) = format.negativeInfinityBits :=
    rfl
  unfold decodeNat
  split <;> rename_i hs hd <;> split_ifs <;> simp_all [nanBits, -Numerics.Dyadic.neg_eq] <;> omega

/-- Every P3109 code decodes to a datum for which `SameDatum` is reflexive. -/
private theorem sameDatum_decode_self
    (format : Format) (code : BitVec format.bitWidth) :
    SameDatum (format.decode code) (format.decode code) := by
  unfold decode decodeNat
  split <;> split_ifs <;> simp [SameDatum]

/-- The direct natural-number encoder is a left inverse of exact-width decoding. -/
@[simp] theorem encodeDatumNat_decode
    (format : Format) (code : BitVec format.bitWidth) :
    Internal.encodeDatumNat format (format.decode code) =
      code.toNat := by
  unfold decode
  exact format.encodeDatumNat_decodeNat code.toNat

private theorem directCode_decode
    (format : Format) (code : BitVec format.bitWidth) :
    BitVec.ofNat format.bitWidth
        (Internal.encodeDatumNat format (format.decode code)) =
      code := by
  rw [format.encodeDatumNat_decode]
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- Executable datum equality holds exactly for the same mathematical P3109 datum. -/
theorem datumEqual_eq_true_iff
    (left right : NumericalValue Numerics.Dyadic) :
    datumEqual left right = true ↔ SameDatum left right := by
  cases left with
  | finite left =>
      cases right with
      | finite right =>
          simp [datumEqual, SameDatum,
            Numerics.Dyadic.Internal.compareScalable_eq_compare,
            Numerics.Dyadic.compare_eq_eq_iff]
      | infinity _ => simp [datumEqual, SameDatum]
      | exceptional _ => simp [datumEqual, SameDatum]
  | infinity left =>
      cases right with
      | finite _ => simp [datumEqual, SameDatum]
      | infinity right => simp [datumEqual, SameDatum]
      | exceptional _ => simp [datumEqual, SameDatum]
  | exceptional left =>
      cases right with
      | finite _ => simp [datumEqual, SameDatum]
      | infinity _ => simp [datumEqual, SameDatum]
      | exceptional right =>
          cases left <;> cases right <;> simp [datumEqual, SameDatum]

/-- Checked encoding is a left inverse of P3109 decoding. -/
@[simp] theorem encode?_decode
    (format : Format) (code : BitVec format.bitWidth) :
    format.encode? (format.decode code) = some code := by
  unfold encode?
  rw [format.directCode_decode]
  have same := format.sameDatum_decode_self code
  have equal :
      datumEqual (format.decode code) (format.decode code) = true :=
    (datumEqual_eq_true_iff _ _).2 same
  simp [equal]

/--
A successful checked encoding decodes to the same P3109 datum as its input.

No rounding occurs in `encode?`; success is exactly the representability certificate.
-/
theorem sameDatum_decode_of_encode?_eq_some
    (format : Format)
    (value : NumericalValue Numerics.Dyadic)
    (code : BitVec format.bitWidth)
    (success : format.encode? value = some code) :
    SameDatum (format.decode code) value := by
  unfold encode? at success
  dsimp only at success
  split at success
  next hsame =>
    simp only [Option.some.injEq] at success
    subst code
    exact (datumEqual_eq_true_iff _ _).1 hsame
  next _ =>
    contradiction

end Format
end FloatLib.Floats.Formats.P3109
