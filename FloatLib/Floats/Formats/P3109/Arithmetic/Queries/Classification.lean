/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Arithmetic.Queries.Neighbors

/-!
# Exact meanings of P3109 value queries

The executable predicates are connected to the exact decoder rather than to an approximate
host conversion. The statements apply to every valid descriptor, including precision one.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.ExecFloat.P3109

open Formats.P3109

variable {format : Format}

/-- The raw natural-number decoder and the public decoder have the same exact observation. -/
theorem decode_eq_decodeNat (value : ExecFloat.P3109 format) :
    value.decode = format.decodeNat value.toNatBits :=
  rfl

/-- The finite query is true precisely when exact decoding produces a finite dyadic. -/
theorem isFinite_iff_decode (value : ExecFloat.P3109 format) :
    value.isFinite = true ↔ ∃ exact, value.decode = .finite exact := by
  rw [decode_eq_decodeNat]
  have hmodulus := format.modulus_eq_two_mul_signBoundary
  have hboundary := format.one_lt_signBoundary
  cases hs : format.signedness <;> cases hd : format.domain <;>
    (by_cases hn : value.toNatBits = format.nanBits) <;>
    (by_cases hp : value.toNatBits = format.positiveInfinityBits) <;>
    (by_cases hm : value.toNatBits = format.negativeInfinityBits) <;>
    (by_cases hsign : format.signBoundary < value.toNatBits) <;>
    simp_all [isFinite, isNaN, isInfinite, Format.decodeNat, Format.nanBits,
      Format.positiveInfinityBits, Format.negativeInfinityBits] <;>
    (try split_ifs) <;> (try simp_all)

/-- The infinity query is true precisely when exact decoding produces either signed infinity. -/
theorem isInfinite_iff_decode (value : ExecFloat.P3109 format) :
    value.isInfinite = true ↔ ∃ negative, value.decode = .infinity negative := by
  rw [decode_eq_decodeNat]
  have hmodulus := format.modulus_eq_two_mul_signBoundary
  have hboundary := format.one_lt_signBoundary
  cases hs : format.signedness <;> cases hd : format.domain <;>
    (by_cases hn : value.toNatBits = format.nanBits) <;>
    (by_cases hp : value.toNatBits = format.positiveInfinityBits) <;>
    (by_cases hm : value.toNatBits = format.negativeInfinityBits) <;>
    (by_cases hsign : format.signBoundary < value.toNatBits) <;>
    simp_all [isInfinite, Format.decodeNat, Format.nanBits,
      Format.positiveInfinityBits, Format.negativeInfinityBits] <;>
    (try split_ifs) <;> (try simp_all) <;> omega

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

/-- Normality is an exact absolute-value bound at the first normal magnitude code. -/
theorem isNormal_iff_decode (value : ExecFloat.P3109 format) :
    value.isNormal = true ↔ ∃ exact, value.decode = .finite exact ∧
      (format.decodePositiveFinite (2 ^ format.trailingBits)).toRat ≤ |exact.toRat| := by
  simp only [isNormal, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hfinite, hnormal⟩
    obtain ⟨exact, hdecode⟩ := (isFinite_iff_decode value).mp hfinite
    refine ⟨exact, hdecode, ?_⟩
    rw [abs_toRat_of_decode_finite value exact hdecode]
    exact format.decodePositiveFinite_strictMono.monotone hnormal
  · rintro ⟨exact, hdecode, hnormal⟩
    refine ⟨(isFinite_iff_decode value).mpr ⟨exact, hdecode⟩, ?_⟩
    rw [abs_toRat_of_decode_finite value exact hdecode] at hnormal
    exact format.decodePositiveFinite_strictMono.le_iff_le.mp hnormal

/-- Subnormality is an exact nonzero absolute-value bound below the first normal value. -/
theorem isSubnormal_iff_decode (value : ExecFloat.P3109 format) :
    value.isSubnormal = true ↔ ∃ exact, value.decode = .finite exact ∧
      0 < |exact.toRat| ∧
      |exact.toRat| < (format.decodePositiveFinite (2 ^ format.trailingBits)).toRat := by
  simp only [isSubnormal, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hfinite, hpositive⟩, hsubnormal⟩
    obtain ⟨exact, hdecode⟩ := (isFinite_iff_decode value).mp hfinite
    refine ⟨exact, hdecode, ?_, ?_⟩
    · rw [abs_toRat_of_decode_finite value exact hdecode]
      simpa using format.decodePositiveFinite_strictMono hpositive
    · rw [abs_toRat_of_decode_finite value exact hdecode]
      exact format.decodePositiveFinite_strictMono hsubnormal
  · rintro ⟨exact, hdecode, hpositive, hsubnormal⟩
    rw [abs_toRat_of_decode_finite value exact hdecode] at hpositive hsubnormal
    refine ⟨⟨(isFinite_iff_decode value).mpr ⟨exact, hdecode⟩, ?_⟩,
      format.decodePositiveFinite_strictMono.lt_iff_lt.mp hsubnormal⟩
    exact format.decodePositiveFinite_strictMono.lt_iff_lt.mp (by simpa using hpositive)

/-- The unique zero code is precisely the datum with exact rational observation zero. -/
theorem isZero_iff_toClosedRat (value : ExecFloat.P3109 format) :
    value.isZero = true ↔ value.toClosedRat = .finite 0 := by
  simp only [isZero, beq_iff_eq]
  constructor
  · intro hzero
    change Arithmetic.toRat (format.decodeNat value.toNatBits) = .finite 0
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

/-- The sign query is precisely strict numerical comparison with zero; NaN is unordered. -/
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
