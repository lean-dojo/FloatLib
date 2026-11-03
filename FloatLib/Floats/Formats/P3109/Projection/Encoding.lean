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
specify the checked encoder: it returns a code exactly when that code decodes to the same datum
as its input. The direct encoder depends only on the datum, so differently normalized dyadics with
one rational value encode alike. Precision rounding and saturation correctness live in later
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
  simp only [hzero, beq_iff_eq, ite_false, hmax]
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
      Nat.mod_eq_of_lt hlt, encodePositiveFinite_mk_of_max_eq _ _ _ hzero, ite_eq_left hlt,
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
    rw [format.decodePositiveFinite_of_biasedExponent_ne_zero bits hrow,
      encodePositiveFinite_mk_of_max_eq _ _ _ (by omega), ite_eq_right (by omega),
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
  simp only [Internal.encodeDatumNat, beq_iff_eq, hne, ite_false, decodePositiveFinite_negative,
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
  simp only [Internal.encodeDatumNat, Numerics.Dyadic.neg_significand, beq_iff_eq, hne, ite_false,
    Numerics.Dyadic.neg_negative, Numerics.Dyadic.neg_exponent, decodePositiveFinite_negative,
    Bool.not_false, ite_true]
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
  have hsigned := format.positiveInfinityBits_ne_signBoundary
  have hsigned' := format.negativeInfinityBits_ne_signBoundary
  have hsigned'' := format.negativeInfinityBits_ne_positiveInfinityBits
  have hunsigned := format.positiveInfinityBits_ne_nanBits
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

No rounding occurs in `encode?`. The converse, that `encode?` accepts every value some code denotes,
is `encode?_eq_some_iff`.
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

/-- Doubling the significand and lowering the exponent by one does not change the encoding. -/
private theorem encodePositiveFinite_double (format : Format) (value : Numerics.Dyadic)
    (hzero : value.significand ≠ 0) :
    Internal.encodePositiveFinite format ⟨value.negative, 2 * value.significand, value.exponent - 1⟩ =
      Internal.encodePositiveFinite format value := by
  have hlog := Nat.log2_two_mul hzero
  have htwo : 2 * value.significand ≠ 0 := by omega
  unfold Internal.encodePositiveFinite
  simp only [beq_iff_eq, htwo, hzero, ite_false, hlog]
  have hE : Int.ofNat (value.significand.log2 + 1) + (value.exponent - 1) =
      Int.ofNat value.significand.log2 + value.exponent := by
    simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one]
    omega
  rw [hE]
  generalize max (Int.ofNat value.significand.log2 + value.exponent)
    format.minimumNormalExponent = E
  generalize hz : value.exponent - E + Int.ofNat format.trailingBits = z
  have hw : value.exponent - 1 - E + Int.ofNat format.trailingBits = z - 1 := by omega
  rw [hw]
  generalize hw' : z - 1 = w
  have hdouble (shift : Nat) :
      Nat.shiftLeft (2 * value.significand) shift = Nat.shiftLeft value.significand (shift + 1) := by
    simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq]
    rw [Nat.pow_succ, Nat.mul_comm 2 value.significand, Nat.mul_assoc, Nat.mul_comm 2]
  have hhalve (shift : Nat) :
      Nat.shiftRight (2 * value.significand) (shift + 1 + 1) =
        Nat.shiftRight value.significand (shift + 1) := by
    simp only [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
    rw [Nat.pow_succ, Nat.mul_comm _ 2, Nat.mul_div_mul_left _ _ (by decide)]
  rcases w with a | a <;> rcases z with b | b <;>
    simp only [Int.ofNat_eq_natCast, Int.negSucc_eq] at hw' <;> dsimp only
  · obtain rfl : b = a + 1 := by omega
    simp only [hdouble]
  · omega
  · obtain rfl : b = 0 := by omega
    obtain rfl : a = 0 := by omega
    have hone : Nat.shiftRight (2 * value.significand) (0 + 1) = Nat.shiftLeft value.significand 0 := by
      simp only [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq', Nat.shiftLeft_eq]
      simp
    simp only [hone]
  · obtain rfl : a = b + 1 := by omega
    simp only [hhalve]

/-- Scaling the significand by `2 ^ k` and lowering the exponent by `k` does not change the
encoding. -/
private theorem encodePositiveFinite_scale (format : Format) (value : Numerics.Dyadic)
    (hzero : value.significand ≠ 0) (k : Nat) :
    Internal.encodePositiveFinite format
        ⟨value.negative, value.significand * 2 ^ k, value.exponent - k⟩ =
      Internal.encodePositiveFinite format value := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk : value.significand * 2 ^ k ≠ 0 :=
        Nat.mul_ne_zero hzero (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k))
      have h := encodePositiveFinite_double format
        ⟨value.negative, value.significand * 2 ^ k, value.exponent - k⟩ hk
      rw [← ih, ← h]
      congr 2
      · rw [Nat.pow_succ, Nat.mul_comm 2, Nat.mul_assoc]
      · push_cast
        omega

/-- Dyadics with equal rational values are zero together. -/
private theorem significand_eq_zero_iff_of_toRat_eq {left right : Numerics.Dyadic}
    (h : left.toRat = right.toRat) : left.significand = 0 ↔ right.significand = 0 := by
  rw [← Numerics.Dyadic.toRat_eq_zero_iff, ← Numerics.Dyadic.toRat_eq_zero_iff, h]

/-- The encoder of a nonnegative dyadic depends only on its rational value. -/
private theorem encodePositiveFinite_eq_of_toRat_eq (format : Format)
    {left right : Numerics.Dyadic}
    (hleft : left.negative = false) (hright : right.negative = false)
    (h : left.toRat = right.toRat) :
    Internal.encodePositiveFinite format left = Internal.encodePositiveFinite format right := by
  have hz := significand_eq_zero_iff_of_toRat_eq h
  by_cases hl0 : left.significand = 0
  · simp [Internal.encodePositiveFinite, hl0, hz.1 hl0]
  have hr0 : right.significand ≠ 0 := mt hz.2 hl0
  wlog hle : left.exponent ≤ right.exponent generalizing left right
  · exact (this hright hleft h.symm hz.symm hr0 hl0 (le_of_not_ge hle)).symm
  obtain ⟨k, hk⟩ : ∃ k : Nat, right.exponent = left.exponent + k :=
    ⟨(right.exponent - left.exponent).toNat, by omega⟩
  have hsig : left.significand = right.significand * 2 ^ k := by
    have hvalue := h
    simp only [Numerics.Dyadic.toRat, Numerics.Dyadic.signedSignificand, hleft, hright,
      Bool.false_eq_true, ite_false, hk, zpow_add₀ (two_ne_zero (α := ℚ)), zpow_natCast,
      Rat.ofInt_eq_cast, Int.ofNat_eq_natCast, Int.cast_natCast] at hvalue
    have hpow : (2 : ℚ) ^ left.exponent ≠ 0 := zpow_ne_zero _ two_ne_zero
    have : (left.significand : ℚ) = right.significand * 2 ^ k := by
      apply mul_right_cancel₀ hpow
      rw [hvalue, mul_assoc, mul_comm (2 ^ left.exponent)]
    exact_mod_cast this
  rw [← encodePositiveFinite_scale format right hr0 k]
  congr 1
  apply Numerics.Dyadic.ext
  · simp [hleft, hright]
  · exact hsig
  · simp only
    omega

/-- The direct encoder respects `SameDatum`: equal finite values, equal infinities and any two NaNs
encode to the same code. -/
private theorem encodeDatumNat_eq_of_sameDatum (format : Format)
    {left right : NumericalValue Numerics.Dyadic} (h : SameDatum left right) :
    Internal.encodeDatumNat format left = Internal.encodeDatumNat format right := by
  cases left with
  | finite a =>
      cases right with
      | finite b =>
          have hab : a.toRat = b.toRat := h
          have hz := significand_eq_zero_iff_of_toRat_eq hab
          by_cases ha : a.significand = 0
          · simp [Internal.encodeDatumNat, ha, hz.1 ha]
          have hb : b.significand ≠ 0 := mt hz.2 ha
          have hpos (d : Numerics.Dyadic) (hd : d.significand ≠ 0) :
              (d.negative = false → 0 < d.toRat) ∧ (d.negative = true → d.toRat < 0) := by
            refine ⟨Numerics.Dyadic.toRat_pos_of_significand_ne_zero d hd, fun hneg => ?_⟩
            have := Numerics.Dyadic.toRat_pos_of_significand_ne_zero d.neg hd (by simp [hneg])
            rw [Numerics.Dyadic.neg_toRat] at this
            exact neg_pos.mp this
          have hsign : a.negative = b.negative := by
            cases hna : a.negative <;> cases hnb : b.negative
            · rfl
            · exact absurd (hab ▸ (hpos a ha).1 hna) (not_lt.2 ((hpos b hb).2 hnb).le)
            · exact absurd (hab ▸ (hpos a ha).2 hna) (not_lt.2 ((hpos b hb).1 hnb).le)
            · rfl
          have hmagnitude (d : Numerics.Dyadic) :
              ({ d with negative := false } : Numerics.Dyadic).toRat =
                if d.negative then -d.toRat else d.toRat := by
            cases hd : d.negative
            · simp only [Bool.false_eq_true, ite_false]
              congr 1
              exact Numerics.Dyadic.ext (by simp [hd]) rfl rfl
            · simp only [ite_true]
              rw [← Numerics.Dyadic.neg_toRat]
              congr 1
              exact Numerics.Dyadic.ext (by simp [hd]) rfl rfl
          have hmag := encodePositiveFinite_eq_of_toRat_eq format
            (left := { a with negative := false }) (right := { b with negative := false })
            rfl rfl (by rw [hmagnitude, hmagnitude, hsign, hab])
          simp only [Internal.encodeDatumNat, beq_iff_eq, ha, hb, ite_false, hsign, hmag]
      | infinity _ => exact absurd h (by simp [SameDatum])
      | exceptional _ => exact absurd h (by simp [SameDatum])
  | infinity s =>
      cases right with
      | infinity t =>
          have hst : s = t := h
          subst hst
          rfl
      | finite _ => exact absurd h (by simp [SameDatum])
      | exceptional _ => exact absurd h (by simp [SameDatum])
  | exceptional e =>
      cases right with
      | exceptional _ => rfl
      | finite _ => exact absurd h (by cases e <;> simp [SameDatum])
      | infinity _ => exact absurd h (by cases e <;> simp [SameDatum])

/-- Checked encoding succeeds exactly on the P3109 datums: it returns `code` precisely when `code`
decodes to the same datum as the input. -/
theorem encode?_eq_some_iff (format : Format) (value : NumericalValue Numerics.Dyadic)
    (code : BitVec format.bitWidth) :
    format.encode? value = some code ↔ SameDatum (format.decode code) value := by
  constructor
  · exact format.sameDatum_decode_of_encode?_eq_some value code
  · intro hsame
    have hencode : Internal.encodeDatumNat format value = code.toNat := by
      rw [← format.encodeDatumNat_eq_of_sameDatum hsame, format.encodeDatumNat_decode]
    unfold encode?
    rw [hencode, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp [(datumEqual_eq_true_iff _ _).2 hsame]

end Format
end FloatLib.Floats.Formats.P3109
