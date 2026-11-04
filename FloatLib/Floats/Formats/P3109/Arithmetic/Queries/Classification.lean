/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Arithmetic.Queries.Neighbors

/-!
# Exact meanings of P3109 value queries

Each executable value query is tied to the exact decoder, with no approximate host conversion in
between. The statements hold for every valid descriptor, precision one included.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.ExecFloat.P3109

open Formats.P3109

variable {format : Format}

/-- The raw natural-number decoder and the public decoder have the same exact observation. -/
theorem decode_eq_decodeNat (value : ExecFloat.P3109 format) :
    value.decode = format.decodeNat value.toNatBits := by
  rw [decode_eq_format_decode]
  rfl

/-- `isInf` is true iff exact decoding produces a signed infinity. -/
theorem isInf_iff_decode (value : ExecFloat.P3109 format) :
    value.isInf = true ↔ ∃ negative, value.decode = .infinity negative := by
  rw [decode_eq_decodeNat]
  have hmodulus := format.modulus_eq_two_mul_signBoundary
  have hboundary := format.one_lt_signBoundary
  cases hs : format.signedness <;> cases hd : format.domain <;>
    (by_cases hn : value.toNatBits = format.nanBits) <;>
    (by_cases hp : value.toNatBits = format.positiveInfinityBits) <;>
    (by_cases hm : value.toNatBits = format.negativeInfinityBits) <;>
    (by_cases hsign : format.signBoundary < value.toNatBits) <;>
    simp_all [isInf, Format.decodeNat, Format.nanBits,
      Format.positiveInfinityBits, Format.negativeInfinityBits] <;>
    (try split_ifs) <;> (try simp_all) <;> omega

/-- The NaN code is the only code that decodes to an exceptional value. -/
private theorem isNaN_of_decode_eq_exceptional (value : ExecFloat.P3109 format)
    (exception : ExceptionalValue) (hdecode : value.decode = .exceptional exception) :
    value.isNaN = true := by
  rw [decode_eq_decodeNat] at hdecode
  simp only [isNaN, beq_iff_eq]
  cases hs : format.signedness <;> cases hd : format.domain <;>
    simp only [Format.decodeNat, Format.nanBits, hs, hd] at hdecode ⊢ <;>
    split_ifs at hdecode <;> assumption

/-- `isFinite` is true iff exact decoding produces a finite dyadic. -/
theorem isFinite_iff_decode (value : ExecFloat.P3109 format) :
    value.isFinite = true ↔ ∃ exact, value.decode = .finite exact := by
  have hnan := isNaN_iff_decode value
  have hinfinite := isInf_iff_decode value
  simp only [isFinite, Bool.not_eq_true', Bool.or_eq_false_iff]
  cases hdecode : value.decode with
  | finite exact => simp_all
  | infinity negative => simp_all
  | exceptional exception =>
      simp [isNaN_of_decode_eq_exceptional value exception hdecode]

/-- Testing for one agrees with equality of the exact rational observation to one. -/
theorem isOne_iff_toClosedRat (value : ExecFloat.P3109 format) :
    value.isOne = true ↔ value.toClosedRat = .finite 1 := by
  unfold isOne toClosedRat
  cases hdecode : value.decode with
  | finite exact =>
      simp only [Arithmetic.toRat, NumericalValue.finite.injEq]
      rw [Dyadic.Internal.compareScalable_eq_compare]
      simp only [beq_iff_eq, Dyadic.compare_eq_eq_iff]
      simp
  | infinity negative => simp [Arithmetic.toRat]
  | exceptional exception => simp [Arithmetic.toRat, Arithmetic.nan]

/-- Removing the sign partition gives the exact absolute value of every finite datum. -/
theorem abs_toRat_of_decode_finite (value : ExecFloat.P3109 format) (exact : Numerics.Dyadic)
    (hdecode : value.decode = .finite exact) :
    |exact.toRat| = (format.decodePositiveFinite value.magnitudeBits).toRat := by
  have hnonneg (bits : Nat) : 0 ≤ (format.decodePositiveFinite bits).toRat := by
    simpa using format.decodePositiveFinite_strictMono.monotone (Nat.zero_le bits)
  rw [decode_eq_decodeNat] at hdecode
  cases hs : format.signedness <;> cases hd : format.domain <;>
    simp only [Format.decodeNat, hs, hd] at hdecode <;>
    split_ifs at hdecode <;> cases hdecode <;>
    (try simp only [Dyadic.neg_toRat, abs_neg]) <;>
    rw [abs_of_nonneg (hnonneg _)] <;>
    simp [magnitudeBits, hs, Format.nanBits] at * <;>
    (try split_ifs) <;> first | rfl | omega

/-- A finite datum whose magnitude code satisfies `P` is a datum decoding to a finite value whose
absolute value satisfies `Q`, for any `P` and `Q` that agree through the decoding of magnitude
codes. -/
private theorem isFinite_and_iff_decode (value : ExecFloat.P3109 format) (P : Nat → Prop)
    (Q : Rat → Prop) (h : ∀ bits, P bits ↔ Q (format.decodePositiveFinite bits).toRat) :
    (value.isFinite = true ∧ P value.magnitudeBits) ↔
      ∃ exact, value.decode = .finite exact ∧ Q |exact.toRat| := by
  constructor
  · rintro ⟨hfinite, hp⟩
    obtain ⟨exact, hdecode⟩ := (isFinite_iff_decode value).mp hfinite
    exact ⟨exact, hdecode, by rw [abs_toRat_of_decode_finite value exact hdecode]; exact (h _).mp hp⟩
  · rintro ⟨exact, hdecode, hq⟩
    rw [abs_toRat_of_decode_finite value exact hdecode] at hq
    exact ⟨(isFinite_iff_decode value).mpr ⟨exact, hdecode⟩, (h _).mpr hq⟩

/-- Normality is an exact absolute-value bound at the first normal magnitude code. -/
theorem isNormal_iff_decode (value : ExecFloat.P3109 format) :
    value.isNormal = true ↔ ∃ exact, value.decode = .finite exact ∧
      (format.decodePositiveFinite (2 ^ format.trailingBits)).toRat ≤ |exact.toRat| := by
  simp only [isNormal, Bool.and_eq_true, decide_eq_true_eq]
  exact isFinite_and_iff_decode value (2 ^ format.trailingBits ≤ ·)
    ((format.decodePositiveFinite (2 ^ format.trailingBits)).toRat ≤ ·)
    fun _ => format.decodePositiveFinite_strictMono.le_iff_le.symm

/-- Subnormality is an exact nonzero absolute-value bound below the first normal value. -/
theorem isSubnormal_iff_decode (value : ExecFloat.P3109 format) :
    value.isSubnormal = true ↔ ∃ exact, value.decode = .finite exact ∧
      0 < |exact.toRat| ∧
      |exact.toRat| < (format.decodePositiveFinite (2 ^ format.trailingBits)).toRat := by
  simp only [isSubnormal, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  exact isFinite_and_iff_decode value (fun bits => 0 < bits ∧ bits < 2 ^ format.trailingBits)
    (fun x => 0 < x ∧ x < (format.decodePositiveFinite (2 ^ format.trailingBits)).toRat)
    fun bits => and_congr
      (by simpa using (format.decodePositiveFinite_strictMono.lt_iff_lt (a := 0) (b := bits)).symm)
      format.decodePositiveFinite_strictMono.lt_iff_lt.symm

/-- The zero code is the only datum whose exact rational observation is zero. -/
theorem isZero_iff_toClosedRat (value : ExecFloat.P3109 format) :
    value.isZero = true ↔ value.toClosedRat = .finite 0 := by
  simp only [isZero, beq_iff_eq]
  constructor
  · intro hzero
    rw [toClosedRat, decode_eq_decodeNat]
    rw [hzero]
    have hdecode : format.decodeNat 0 = .finite .zero := by
      simpa only [Format.decode, BitVec.toNat_ofNat, Nat.zero_mod] using format.decode_zero
    rw [hdecode]
    simp [Arithmetic.toRat]
  · intro hzero
    unfold toClosedRat at hzero
    cases hdecode : value.decode with
    | finite exact =>
        simp only [hdecode, Arithmetic.toRat, NumericalValue.finite.injEq] at hzero
        have habs := abs_toRat_of_decode_finite value exact hdecode
        have hmagnitude : value.magnitudeBits = 0 :=
          format.decodePositiveFinite_strictMono.injective (by simpa [hzero] using habs.symm)
        have hnan : value.toNatBits ≠ format.nanBits := by
          intro hbits
          have hquery : value.isNaN = true := by simpa [isNaN] using hbits
          have := (isNaN_iff_decode value).mp hquery
          rw [hdecode] at this
          cases this
        cases hs : format.signedness <;>
          simp [magnitudeBits, Format.nanBits, hs] at hmagnitude hnan <;>
          (try split_ifs at hmagnitude) <;> omega
    | infinity negative => simp only [hdecode, Arithmetic.toRat, reduceCtorEq] at hzero
    | exceptional exception =>
        simp only [hdecode, Arithmetic.toRat, Arithmetic.nan, reduceCtorEq] at hzero

/-- `isSignMinus` agrees with strict comparison against zero, under which NaN is unordered. -/
theorem isSignMinus_iff_less_zero (value : ExecFloat.P3109 format) :
    value.isSignMinus = true ↔ value.less zero = true := by
  rw [less_iff_orderIndex]
  have hmodulus := format.modulus_eq_two_mul_signBoundary
  have hboundary := format.one_lt_signBoundary
  cases hs : format.signedness <;>
    (by_cases hsign : format.signBoundary < value.toNatBits) <;>
    simp [isSignMinus, isNaN, orderIndex, Format.orderIndex, Format.nanBits, hs, hsign]
  omega

end FloatLib.Floats.ExecFloat.P3109
