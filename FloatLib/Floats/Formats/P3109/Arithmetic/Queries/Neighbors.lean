/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Arithmetic.Queries.Order

/-!
# Correctness of P3109 neighboring values

The exact numerical ordering of non-NaN values is a consecutive integer interval. The upper
and lower neighbor operations move by one in that interval, returning NaN precisely when the
requested neighbor does not exist. Infinite endpoints obey the same order as finite values.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109.Format

/-- Index of the least numerical datum; unsigned formats begin at zero. -/
def firstOrderIndex (format : Format) : Int :=
  if format.signedness = .signed then 1 - (format.signBoundary : Int) else 0

/-- Index of the greatest numerical datum, whether finite or infinite. -/
def lastOrderIndex (format : Format) : Int :=
  if format.signedness = .signed then (format.signBoundary : Int) - 1
  else (format.modulus : Int) - 2

/-- Every non-NaN code lies in the numerical index interval. -/
theorem orderIndex_bounds (format : Format) (bits : Nat)
    (hbits : bits < format.modulus) (hnan : bits ≠ format.nanBits) :
    format.firstOrderIndex ≤ format.orderIndex bits ∧
      format.orderIndex bits ≤ format.lastOrderIndex := by
  have hmodulus := format.modulus_eq_two_mul_signBoundary
  cases hs : format.signedness <;>
    simp [orderIndex, firstOrderIndex, lastOrderIndex, nanBits, hs] at * <;>
    (try split_ifs) <;> omega

end FloatLib.Floats.Formats.P3109.Format

namespace FloatLib.Floats.ExecFloat.P3109

open Formats.P3109

variable {format : Format}

/-- Every executable code fits the declared descriptor width. -/
theorem toNatBits_lt_modulus (value : ExecFloat.P3109 format) :
    value.toNatBits < format.modulus :=
  (ExecFloat.Codebook.toCode value).isLt

/-- Numerical-order index of an executable value, used only after excluding NaN. -/
def orderIndex (value : ExecFloat.P3109 format) : Int :=
  format.orderIndex value.toNatBits

/-- The executable NaN predicate agrees with exact decoding. -/
theorem isNaN_iff_decode (value : ExecFloat.P3109 format) :
    value.isNaN = true ↔ value.decode = .exceptional (.nan) := by
  change (value.toNatBits == format.nanBits) = true ↔
    format.decodeNat value.toNatBits = .exceptional (.nan)
  cases hs : format.signedness <;> cases hd : format.domain <;>
    simp only [Format.decodeNat, Format.nanBits, hs, hd, beq_iff_eq] <;>
    split_ifs <;> simp_all

/-- A NaN left operand is unordered under the public strict comparison. -/
theorem less_of_isNaN_left (left right : ExecFloat.P3109 format)
    (hleft : left.isNaN = true) : left.less right = false := by
  simp only [less, toClosedRat, (isNaN_iff_decode left).mp hleft,
    Arithmetic.toRat, Arithmetic.nan, Arithmetic.less]

/-- A NaN right operand is unordered under the public strict comparison. -/
theorem less_of_isNaN_right (left right : ExecFloat.P3109 format)
    (hright : right.isNaN = true) : left.less right = false := by
  have hdecode := (isNaN_iff_decode right).mp hright
  unfold less toClosedRat
  rw [hdecode]
  cases Arithmetic.toRat left.decode <;> rfl

/-- Public strict comparison agrees with integer-index order, with NaN excluded explicitly. -/
theorem less_iff_orderIndex (left right : ExecFloat.P3109 format) :
    left.less right = true ↔ left.isNaN = false ∧ right.isNaN = false ∧
      left.orderIndex < right.orderIndex := by
  by_cases hl : left.isNaN = false
  · by_cases hr : right.isNaN = false
    · have hln : left.toNatBits ≠ format.nanBits := by simpa [isNaN] using hl
      have hrn : right.toNatBits ≠ format.nanBits := by simpa [isNaN] using hr
      simp only [hl, hr, true_and]
      change Arithmetic.less (Arithmetic.toRat (format.decodeNat left.toNatBits))
        (Arithmetic.toRat (format.decodeNat right.toNatBits)) = true ↔
          format.orderIndex left.toNatBits < format.orderIndex right.toNatBits
      exact
        format.less_decodeNat_iff_orderIndex left.toNatBits right.toNatBits
          left.toNatBits_lt_modulus right.toNatBits_lt_modulus hln hrn
    · have hrt : right.isNaN = true := Bool.ne_false_iff.mp hr
      simp [less_of_isNaN_right left right hrt, hr]
  · have hlt : left.isNaN = true := Bool.ne_false_iff.mp hl
    simp [less_of_isNaN_left left right hlt, hl]

/-- Non-NaN executable values lie between the numerical index endpoints. -/
theorem orderIndex_bounds (value : ExecFloat.P3109 format) (hnan : value.isNaN = false) :
    format.firstOrderIndex ≤ value.orderIndex ∧ value.orderIndex ≤ format.lastOrderIndex := by
  exact format.orderIndex_bounds value.toNatBits value.toNatBits_lt_modulus
    (by simpa [isNaN] using hnan)

/-- The public zero constructor has code zero. -/
@[simp] theorem toNatBits_zero : (zero (format := format)).toNatBits = 0 := by
  change 0 % 2 ^ format.bitWidth = 0
  exact Nat.zero_mod _

/-- The public NaN constructor has the descriptor's unique NaN code. -/
@[simp] theorem toNatBits_nan : (nan (format := format)).toNatBits = format.nanBits := by
  change format.nanBits % format.modulus = format.nanBits
  exact Nat.mod_eq_of_lt format.nanBits_lt_modulus

/-- Below the greatest datum, the upper neighbor exists and advances the order index by one. -/
theorem nextGreaterThan_orderIndex (value : ExecFloat.P3109 format)
    (hnan : value.isNaN = false) (hindex : value.orderIndex < format.lastOrderIndex) :
    value.nextGreaterThan.isNaN = false ∧
      value.nextGreaterThan.orderIndex = value.orderIndex + 1 := by
  have hbits := value.toNatBits_lt_modulus
  have hmodulus := format.modulus_eq_two_mul_signBoundary
  have hpow : 2 ^ format.bitWidth = format.modulus := rfl
  have hboundary := format.one_lt_signBoundary
  have hnanBits : value.toNatBits ≠ format.nanBits := by simpa [isNaN] using hnan
  simp only [nextGreaterThan, hnan, Bool.false_eq_true, ite_false]
  cases hs : format.signedness <;>
    (by_cases hn : format.signBoundary < value.toNatBits) <;>
    (by_cases hunit : value.toNatBits = format.signBoundary + 1) <;>
    (by_cases hend : value.toNatBits = format.positiveInfinityBits) <;>
    simp [orderIndex, Format.orderIndex, Format.lastOrderIndex, Format.positiveInfinityBits,
      Format.nanBits, hs, hn] at hindex hnanBits hend <;>
    simp (disch := omega) [isSignMinus, hs, hn, hunit, hend,
      isNaN, orderIndex, Format.orderIndex, Format.nanBits, Format.positiveInfinityBits,
      Nat.mod_eq_of_lt] <;>
    (try split_ifs) <;>
    (try simp (disch := omega) only [toNatBits_ofNatBits, Nat.mod_eq_of_lt]) <;> omega

/-- Above the least datum, the lower neighbor exists and retreats by one in numerical order. -/
theorem nextLessThan_orderIndex (value : ExecFloat.P3109 format)
    (hnan : value.isNaN = false) (hindex : format.firstOrderIndex < value.orderIndex) :
    value.nextLessThan.isNaN = false ∧
      value.nextLessThan.orderIndex = value.orderIndex - 1 := by
  have hbits := value.toNatBits_lt_modulus
  have hmodulus := format.modulus_eq_two_mul_signBoundary
  have hpow : 2 ^ format.bitWidth = format.modulus := rfl
  have hboundary := format.one_lt_signBoundary
  have hnanBits : value.toNatBits ≠ format.nanBits := by simpa [isNaN] using hnan
  simp only [nextLessThan, hnan, Bool.false_eq_true, ite_false]
  cases hs : format.signedness <;>
    (by_cases hn : format.signBoundary < value.toNatBits) <;>
    (by_cases hz : value.toNatBits = 0) <;>
    (by_cases hend : value.toNatBits = format.negativeInfinityBits) <;>
    simp [orderIndex, Format.orderIndex, Format.firstOrderIndex, Format.negativeInfinityBits,
      Format.nanBits, hs, hn] at hindex hnanBits hend <;>
    simp (disch := omega) [isZero, isSignMinus, hs, hn, hz, hend,
      isNaN, orderIndex, Format.orderIndex, Format.nanBits, Format.negativeInfinityBits,
      Nat.mod_eq_of_lt] <;>
    (try split_ifs) <;> omega

/-- The greatest numerical datum has no upper neighbor, in either finite or extended formats. -/
theorem nextGreaterThan_eq_nan_of_last (value : ExecFloat.P3109 format)
    (hindex : value.orderIndex = format.lastOrderIndex) : value.nextGreaterThan = nan := by
  have hbits := value.toNatBits_lt_modulus
  have hmodulus := format.modulus_eq_two_mul_signBoundary
  have hboundary := format.one_lt_signBoundary
  cases hs : format.signedness <;>
    (by_cases hn : format.signBoundary < value.toNatBits) <;>
    simp [orderIndex, Format.orderIndex, Format.lastOrderIndex, hs, hn] at hindex <;>
    simp (disch := omega) [nextGreaterThan, isNaN, isSignMinus, hs, hn,
      Format.positiveInfinityBits, Format.nanBits] <;>
    (try split_ifs) <;> omega

/-- The least numerical datum has no lower neighbor, in either finite or extended formats. -/
theorem nextLessThan_eq_nan_of_first (value : ExecFloat.P3109 format)
    (hindex : value.orderIndex = format.firstOrderIndex) : value.nextLessThan = nan := by
  have hbits := value.toNatBits_lt_modulus
  have hmodulus := format.modulus_eq_two_mul_signBoundary
  have hboundary := format.one_lt_signBoundary
  cases hs : format.signedness <;>
    (by_cases hn : format.signBoundary < value.toNatBits) <;>
    simp [orderIndex, Format.orderIndex, Format.firstOrderIndex, hs, hn] at hindex <;>
    simp (disch := omega) [nextLessThan, isNaN, isZero, isSignMinus, hs, hn,
      Format.negativeInfinityBits, Format.nanBits] <;>
    (try split_ifs) <;> (try simp) <;> omega

/-- Whenever a greater value exists, the upper neighbor is strictly greater than the input. -/
theorem less_nextGreaterThan (value candidate : ExecFloat.P3109 format)
    (h : value.less candidate = true) : value.less value.nextGreaterThan = true := by
  obtain ⟨hv, hc, horder⟩ := (less_iff_orderIndex value candidate).mp h
  have hcBound := (orderIndex_bounds candidate hc).2
  obtain ⟨hn, hstep⟩ := nextGreaterThan_orderIndex value hv (by omega)
  exact (less_iff_orderIndex value value.nextGreaterThan).mpr ⟨hv, hn, by omega⟩

/-- No value greater than the input is smaller than its upper neighbor. -/
theorem not_less_nextGreaterThan (value candidate : ExecFloat.P3109 format)
    (h : value.less candidate = true) : candidate.less value.nextGreaterThan = false := by
  obtain ⟨hv, hc, horder⟩ := (less_iff_orderIndex value candidate).mp h
  have hcBound := (orderIndex_bounds candidate hc).2
  obtain ⟨hn, hstep⟩ := nextGreaterThan_orderIndex value hv (by omega)
  apply Bool.eq_false_iff.mpr
  intro hless
  have := (less_iff_orderIndex candidate value.nextGreaterThan).mp hless
  omega

/-- Whenever a lesser value exists, the lower neighbor is strictly smaller than the input. -/
theorem nextLessThan_less (value candidate : ExecFloat.P3109 format)
    (h : candidate.less value = true) : value.nextLessThan.less value = true := by
  obtain ⟨hc, hv, horder⟩ := (less_iff_orderIndex candidate value).mp h
  have hcBound := (orderIndex_bounds candidate hc).1
  obtain ⟨hn, hstep⟩ := nextLessThan_orderIndex value hv (by omega)
  exact (less_iff_orderIndex value.nextLessThan value).mpr ⟨hn, hv, by omega⟩

/-- No value smaller than the input is greater than its lower neighbor. -/
theorem not_nextLessThan_less (value candidate : ExecFloat.P3109 format)
    (h : candidate.less value = true) : value.nextLessThan.less candidate = false := by
  obtain ⟨hc, hv, horder⟩ := (less_iff_orderIndex candidate value).mp h
  have hcBound := (orderIndex_bounds candidate hc).1
  obtain ⟨hn, hstep⟩ := nextLessThan_orderIndex value hv (by omega)
  apply Bool.eq_false_iff.mpr
  intro hless
  have := (less_iff_orderIndex value.nextLessThan candidate).mp hless
  omega

/-- The upper-neighbor result is NaN exactly when the numerical order has no greater datum. -/
theorem nextGreaterThan_isNaN_iff (value : ExecFloat.P3109 format) :
    value.nextGreaterThan.isNaN = true ↔
      ¬ ∃ candidate : ExecFloat.P3109 format, value.less candidate = true := by
  constructor
  · rintro hnan ⟨candidate, hcandidate⟩
    have hnext := less_nextGreaterThan value candidate hcandidate
    have := (less_iff_orderIndex value value.nextGreaterThan).mp hnext
    simp_all
  · intro hnone
    by_cases hnan : value.isNaN = true
    · simp only [nextGreaterThan, hnan, ite_true]
      simp [isNaN]
    · have hfinite : value.isNaN = false := Bool.eq_false_iff.mpr hnan
      have hbound := (orderIndex_bounds value hfinite).2
      by_cases hend : value.orderIndex = format.lastOrderIndex
      · rw [nextGreaterThan_eq_nan_of_last value hend]
        simp [isNaN]
      · obtain ⟨hn, hstep⟩ := nextGreaterThan_orderIndex value hfinite (by omega)
        exact False.elim (hnone ⟨value.nextGreaterThan,
          (less_iff_orderIndex value value.nextGreaterThan).mpr ⟨hfinite, hn, by omega⟩⟩)

/-- The lower-neighbor result is NaN exactly when the numerical order has no lesser datum. -/
theorem nextLessThan_isNaN_iff (value : ExecFloat.P3109 format) :
    value.nextLessThan.isNaN = true ↔
      ¬ ∃ candidate : ExecFloat.P3109 format, candidate.less value = true := by
  constructor
  · rintro hnan ⟨candidate, hcandidate⟩
    have hnext := nextLessThan_less value candidate hcandidate
    have := (less_iff_orderIndex value.nextLessThan value).mp hnext
    simp_all
  · intro hnone
    by_cases hnan : value.isNaN = true
    · simp only [nextLessThan, hnan, ite_true]
      simp [isNaN]
    · have hfinite : value.isNaN = false := Bool.eq_false_iff.mpr hnan
      have hbound := (orderIndex_bounds value hfinite).1
      by_cases hend : value.orderIndex = format.firstOrderIndex
      · rw [nextLessThan_eq_nan_of_first value hend]
        simp [isNaN]
      · obtain ⟨hn, hstep⟩ := nextLessThan_orderIndex value hfinite (by omega)
        exact False.elim (hnone ⟨value.nextLessThan,
          (less_iff_orderIndex value.nextLessThan value).mpr ⟨hn, hfinite, by omega⟩⟩)

end FloatLib.Floats.ExecFloat.P3109
