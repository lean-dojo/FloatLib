/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Arithmetic.Queries.Order

/-!
# Correctness of P3109 neighboring values

Leave out NaN, and the values of a P3109 format, in numerical order, line up with a consecutive
interval of integers. The upper and lower neighbor operations move one step in that interval, and
they return NaN if and only if the requested neighbor doesn't exist. Infinite endpoints follow the
same order as finite values.

Reference: P3109 Interim Report v4.1 (unapproved draft), §§3.1 and 4.16.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109.Format

/-- Index of the least numerical datum, which is zero for unsigned formats. -/
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
    simp only [nanBits, hs, ne_eq, firstOrderIndex, ↓reduceIte, orderIndex, true_and,
      tsub_le_iff_right, lastOrderIndex, Order.le_sub_one_iff, reduceCtorEq, false_and,
      Nat.cast_nonneg, ge_iff_le] at * <;>
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
    value.IsNaN = true ↔ value.decode = .exceptional (.nan) := by
  rw [decode_eq_format_decode]
  change (value.toNatBits == format.nanBits) = true ↔
    format.decodeNat value.toNatBits = .exceptional (.nan)
  cases hs : format.signedness <;> cases hd : format.domain <;>
    simp only [Format.decodeNat, Format.nanBits, hs, hd, beq_iff_eq] <;>
    split_ifs <;> simp_all

/-- A NaN left operand is unordered under the public strict comparison. -/
theorem less_of_isNaN_left (left right : ExecFloat.P3109 format)
    (hleft : left.IsNaN = true) : left.CompareLess right = false := by
  simp only [CompareLess, toClosedRat, (isNaN_iff_decode left).mp hleft,
    Arithmetic.toRat, Arithmetic.nan, Arithmetic.CompareLess]

/-- A NaN right operand is unordered under the public strict comparison. -/
theorem less_of_isNaN_right (left right : ExecFloat.P3109 format)
    (hright : right.IsNaN = true) : left.CompareLess right = false := by
  have hdecode := (isNaN_iff_decode right).mp hright
  unfold CompareLess toClosedRat
  rw [hdecode]
  cases Arithmetic.toRat left.decode <;> rfl

/-- Strict comparison holds iff both operands are non-NaN and their order indices increase. -/
theorem less_iff_orderIndex (left right : ExecFloat.P3109 format) :
    left.CompareLess right = true ↔ left.IsNaN = false ∧ right.IsNaN = false ∧
      left.orderIndex < right.orderIndex := by
  by_cases hl : left.IsNaN = false
  · by_cases hr : right.IsNaN = false
    · have hln : left.toNatBits ≠ format.nanBits := by simpa [IsNaN] using hl
      have hrn : right.toNatBits ≠ format.nanBits := by simpa [IsNaN] using hr
      simp only [hl, hr, true_and]
      unfold CompareLess toClosedRat
      rw [decode_eq_format_decode, decode_eq_format_decode]
      change Arithmetic.CompareLess (Arithmetic.toRat (format.decodeNat left.toNatBits))
        (Arithmetic.toRat (format.decodeNat right.toNatBits)) = true ↔
          format.orderIndex left.toNatBits < format.orderIndex right.toNatBits
      exact
        format.less_decodeNat_iff_orderIndex left.toNatBits right.toNatBits
          left.toNatBits_lt_modulus right.toNatBits_lt_modulus hln hrn
    · have hrt : right.IsNaN = true := Bool.ne_false_iff.mp hr
      simp [less_of_isNaN_right left right hrt, hr]
  · have hlt : left.IsNaN = true := Bool.ne_false_iff.mp hl
    simp [less_of_isNaN_left left right hlt, hl]

/-- Non-NaN executable values lie between the numerical index endpoints. -/
theorem orderIndex_bounds (value : ExecFloat.P3109 format) (hnan : value.IsNaN = false) :
    format.firstOrderIndex ≤ value.orderIndex ∧ value.orderIndex ≤ format.lastOrderIndex := by
  exact format.orderIndex_bounds value.toNatBits value.toNatBits_lt_modulus
    (by simpa [IsNaN] using hnan)

/-- The public zero constructor has code zero. -/
@[simp] theorem toNatBits_zero : (zero (format := format)).toNatBits = 0 := by
  change 0 % 2 ^ format.bitWidth = 0
  exact Nat.zero_mod _

/-- The public NaN constructor has the descriptor's unique NaN code. -/
@[simp] theorem toNatBits_nan : (nan (format := format)).toNatBits = format.nanBits := by
  change format.nanBits % format.modulus = format.nanBits
  exact Nat.mod_eq_of_lt format.nanBits_lt_modulus

/-- Below the greatest datum, the upper neighbor exists and advances the order index by one. The NaN
code has an order index at or above the greatest one, so the input is not NaN. -/
theorem nextGreaterThan_orderIndex (value : ExecFloat.P3109 format)
    (hindex : value.orderIndex < format.lastOrderIndex) :
    value.NextGreaterThan.IsNaN = false ∧
      value.NextGreaterThan.orderIndex = value.orderIndex + 1 := by
  have hbits := value.toNatBits_lt_modulus
  have hmodulus := format.modulus_eq_two_mul_signBoundary
  have hpow : 2 ^ format.bitWidth = format.modulus := rfl
  have hboundary := format.one_lt_signBoundary
  have hnan : value.IsNaN = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have hb : value.toNatBits = format.nanBits := by simpa [IsNaN] using h
    simp only [orderIndex, Format.orderIndex, Format.lastOrderIndex, hb, Format.nanBits] at hindex
    cases hs : format.signedness <;>
      simp only [hs, lt_self_iff_false, and_false, ↓reduceIte, reduceCtorEq,
        false_and] at hindex <;> omega
  have hnanBits : value.toNatBits ≠ format.nanBits := by simpa [IsNaN] using hnan
  simp only [NextGreaterThan, hnan, Bool.false_eq_true, ite_false]
  cases hs : format.signedness <;>
    (by_cases hn : format.signBoundary < value.toNatBits) <;>
    (by_cases hunit : value.toNatBits = format.signBoundary + 1) <;>
    (by_cases hend : value.toNatBits = format.positiveInfinityBits) <;>
    simp only [orderIndex, Format.orderIndex, hs, hn, and_self,
      ↓reduceIte, Format.lastOrderIndex, sub_lt_sub_iff_left,
      Nat.one_lt_cast, Format.nanBits, ne_eq,
      Format.positiveInfinityBits, and_false, reduceCtorEq, and_true] at hindex hnanBits hend <;>
    simp (disch := omega) only [IsNaN, IsSignMinus, hs, BEq.rfl, hunit, lt_add_iff_pos_right,
      not_lt_one, decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
      Format.positiveInfinityBits, Nat.sub_eq_zero_of_le, Nat.reduceBeqDiff, toNatBits_ofNatBits,
      Nat.mod_eq_of_lt, Format.nanBits, beq_eq_false_iff_ne, ne_eq, orderIndex, Format.orderIndex,
      Order.lt_add_one_iff, le_of_subsingleton, and_self, CharP.cast_eq_zero, sub_self, and_false,
      zero_add, OfNat.ofNat_eq_ofNat, OfNat.ofNat_ne_one, Order.lt_one_iff, decide_true,
      Bool.and_self, toNatBits_zero, not_lt_zero, Nat.cast_add, Nat.cast_one, sub_add_cancel_left,
      Int.reduceNeg, neg_add_cancel, and_true, hend, toNatBits_nan, Bool.true_eq_false,
      lt_self_iff_false, hn, beq_iff_eq, true_and, Nat.cast_sub,
      ite_eq_right_iff, reduceCtorEq, Bool.and_true, false_and] <;>
    (try split_ifs) <;>
    (try simp (disch := omega) only [toNatBits_ofNatBits, Nat.mod_eq_of_lt]) <;> omega

/-- Above the least datum, the lower neighbor exists and retreats by one in numerical order. -/
theorem nextLessThan_orderIndex (value : ExecFloat.P3109 format)
    (hnan : value.IsNaN = false) (hindex : format.firstOrderIndex < value.orderIndex) :
    value.NextLessThan.IsNaN = false ∧
      value.NextLessThan.orderIndex = value.orderIndex - 1 := by
  have hbits := value.toNatBits_lt_modulus
  have hmodulus := format.modulus_eq_two_mul_signBoundary
  have hpow : 2 ^ format.bitWidth = format.modulus := rfl
  have hboundary := format.one_lt_signBoundary
  have hnanBits : value.toNatBits ≠ format.nanBits := by simpa [IsNaN] using hnan
  simp only [NextLessThan, hnan, Bool.false_eq_true, ite_false]
  cases hs : format.signedness <;>
    (by_cases hn : format.signBoundary < value.toNatBits) <;>
    (by_cases hz : value.toNatBits = 0) <;>
    (by_cases hend : value.toNatBits = format.negativeInfinityBits) <;>
    simp only [Format.firstOrderIndex, hs, ↓reduceIte, orderIndex,
      Format.orderIndex, hn, and_self, Format.nanBits, ne_eq,
      Format.negativeInfinityBits, and_false, reduceCtorEq, and_true,
      Int.natCast_pos] at hindex hnanBits hend <;>
    simp (disch := omega) only [IsNaN, IsZero, hz, BEq.rfl, ↓reduceIte, toNatBits_ofNatBits,
      Nat.mod_eq_of_lt, Format.nanBits, hs, beq_eq_false_iff_ne, ne_eq, Nat.add_eq_left,
      OfNat.ofNat_ne_zero, not_false_eq_true, orderIndex, Format.orderIndex, lt_add_iff_pos_right,
      not_lt_one, and_false, CharP.cast_eq_zero, not_lt_zero, zero_sub,
      Int.reduceNeg, zero_eq_neg, OfNat.ofNat_eq_ofNat, hend, Nat.sub_eq_zero_of_le, beq_iff_eq,
      IsSignMinus, hn, decide_true, Bool.and_self, Format.negativeInfinityBits,
      Order.lt_add_one_iff, true_and, Nat.cast_add, Nat.cast_one, and_self, one_ne_zero,
      Order.lt_one_iff, sub_add_cancel_left, decide_false, Bool.and_false, Bool.false_eq_true,
      sub_self, Nat.cast_sub, ite_eq_right_iff, reduceCtorEq, toNatBits_nan, Bool.true_eq_false,
      Bool.and_true, false_and, and_true] <;>
    (try split_ifs) <;> omega

/-- The greatest numerical datum has no upper neighbor, in either finite or extended formats. -/
theorem nextGreaterThan_eq_nan_of_last (value : ExecFloat.P3109 format)
    (hindex : value.orderIndex = format.lastOrderIndex) : value.NextGreaterThan = nan := by
  have hmodulus := format.modulus_eq_two_mul_signBoundary
  have hboundary := format.one_lt_signBoundary
  cases hs : format.signedness <;>
    (by_cases hn : format.signBoundary < value.toNatBits) <;>
    simp only [orderIndex, Format.orderIndex, hs, hn, and_self, ↓reduceIte, Format.lastOrderIndex,
      sub_right_inj, Nat.cast_eq_one, and_false, reduceCtorEq, and_true] at hindex <;>
    simp (disch := omega) only [NextGreaterThan, IsNaN, Format.nanBits, hs, beq_iff_eq,
      IsSignMinus, BEq.rfl, hn, decide_true, Bool.and_self, ↓reduceIte, Nat.sub_eq_zero_of_le,
      ite_eq_left_iff, forall_const, decide_false, Bool.and_false, Bool.false_eq_true,
      Format.positiveInfinityBits, Bool.and_true, reduceCtorEq] <;>
    (try split_ifs) <;> omega

/-- The least numerical datum has no lower neighbor, in either finite or extended formats. -/
theorem nextLessThan_eq_nan_of_first (value : ExecFloat.P3109 format)
    (hindex : value.orderIndex = format.firstOrderIndex) : value.NextLessThan = nan := by
  have hmodulus := format.modulus_eq_two_mul_signBoundary
  have hboundary := format.one_lt_signBoundary
  cases hs : format.signedness <;>
    (by_cases hn : format.signBoundary < value.toNatBits) <;>
    simp only [orderIndex, Format.orderIndex, hs, hn, and_self, ↓reduceIte,
      Format.firstOrderIndex, and_false, reduceCtorEq, and_true, Int.natCast_eq_zero] at hindex <;>
    simp (disch := omega) only [NextLessThan, IsNaN, Format.nanBits, hs, beq_iff_eq, IsZero,
      BEq.rfl, ↓reduceIte, IsSignMinus, hn, decide_true, Bool.and_self,
      Format.negativeInfinityBits, ite_eq_left_iff, decide_false, Bool.and_false,
      Bool.false_eq_true, Nat.sub_eq_zero_of_le, forall_const, reduceCtorEq, Bool.and_true] <;>
    (try split_ifs) <;> (try simp only [implies_true]) <;> omega

/-- Whenever a greater value exists, the upper neighbor is strictly greater than the input. -/
theorem less_nextGreaterThan (value candidate : ExecFloat.P3109 format)
    (h : value.CompareLess candidate = true) : value.CompareLess value.NextGreaterThan = true := by
  obtain ⟨hv, hc, horder⟩ := (less_iff_orderIndex value candidate).mp h
  have hcBound := (orderIndex_bounds candidate hc).2
  obtain ⟨hn, hstep⟩ := nextGreaterThan_orderIndex value (by omega)
  exact (less_iff_orderIndex value value.NextGreaterThan).mpr ⟨hv, hn, by omega⟩

/-- No value greater than the input is smaller than its upper neighbor. -/
theorem not_less_nextGreaterThan (value candidate : ExecFloat.P3109 format)
    (h : value.CompareLess candidate = true) : candidate.CompareLess value.NextGreaterThan =
      false := by
  obtain ⟨_, hc, horder⟩ := (less_iff_orderIndex value candidate).mp h
  have hcBound := (orderIndex_bounds candidate hc).2
  obtain ⟨_, hstep⟩ := nextGreaterThan_orderIndex value (by omega)
  apply Bool.eq_false_iff.mpr
  intro hless
  have := (less_iff_orderIndex candidate value.NextGreaterThan).mp hless
  omega

/-- Whenever a lesser value exists, the lower neighbor is strictly smaller than the input. -/
theorem nextLessThan_less (value candidate : ExecFloat.P3109 format)
    (h : candidate.CompareLess value = true) : value.NextLessThan.CompareLess value = true := by
  obtain ⟨hc, hv, horder⟩ := (less_iff_orderIndex candidate value).mp h
  have hcBound := (orderIndex_bounds candidate hc).1
  obtain ⟨hn, hstep⟩ := nextLessThan_orderIndex value hv (by omega)
  exact (less_iff_orderIndex value.NextLessThan value).mpr ⟨hn, hv, by omega⟩

/-- No value smaller than the input is greater than its lower neighbor. -/
theorem not_nextLessThan_less (value candidate : ExecFloat.P3109 format)
    (h : candidate.CompareLess value = true) : value.NextLessThan.CompareLess candidate = false
      := by
  obtain ⟨hc, hv, horder⟩ := (less_iff_orderIndex candidate value).mp h
  have hcBound := (orderIndex_bounds candidate hc).1
  obtain ⟨_, hstep⟩ := nextLessThan_orderIndex value hv (by omega)
  apply Bool.eq_false_iff.mpr
  intro hless
  have := (less_iff_orderIndex value.NextLessThan candidate).mp hless
  omega

/-- The upper-neighbor result is NaN if and only if the numerical order has no greater datum. -/
theorem nextGreaterThan_isNaN_iff (value : ExecFloat.P3109 format) :
    value.NextGreaterThan.IsNaN = true ↔
      ¬ ∃ candidate : ExecFloat.P3109 format, value.CompareLess candidate = true := by
  constructor
  · rintro hnan ⟨candidate, hcandidate⟩
    have hnext := less_nextGreaterThan value candidate hcandidate
    have := (less_iff_orderIndex value value.NextGreaterThan).mp hnext
    simp_all
  · intro hnone
    by_cases hnan : value.IsNaN = true
    · simp only [NextGreaterThan, hnan, ite_true]
      simp [IsNaN]
    · have hfinite : value.IsNaN = false := Bool.eq_false_iff.mpr hnan
      have hbound := (orderIndex_bounds value hfinite).2
      by_cases hend : value.orderIndex = format.lastOrderIndex
      · rw [nextGreaterThan_eq_nan_of_last value hend]
        simp [IsNaN]
      · obtain ⟨hn, hstep⟩ := nextGreaterThan_orderIndex value (by omega)
        exact False.elim (hnone ⟨value.NextGreaterThan,
          (less_iff_orderIndex value value.NextGreaterThan).mpr ⟨hfinite, hn, by omega⟩⟩)

/-- The lower-neighbor result is NaN if and only if the numerical order has no lesser datum. -/
theorem nextLessThan_isNaN_iff (value : ExecFloat.P3109 format) :
    value.NextLessThan.IsNaN = true ↔
      ¬ ∃ candidate : ExecFloat.P3109 format, candidate.CompareLess value = true := by
  constructor
  · rintro hnan ⟨candidate, hcandidate⟩
    have hnext := nextLessThan_less value candidate hcandidate
    have := (less_iff_orderIndex value.NextLessThan value).mp hnext
    simp_all
  · intro hnone
    by_cases hnan : value.IsNaN = true
    · simp only [NextLessThan, hnan, ite_true]
      simp [IsNaN]
    · have hfinite : value.IsNaN = false := Bool.eq_false_iff.mpr hnan
      have hbound := (orderIndex_bounds value hfinite).1
      by_cases hend : value.orderIndex = format.firstOrderIndex
      · rw [nextLessThan_eq_nan_of_first value hend]
        simp [IsNaN]
      · obtain ⟨hn, hstep⟩ := nextLessThan_orderIndex value hfinite (by omega)
        exact False.elim (hnone ⟨value.NextLessThan,
          (less_iff_orderIndex value.NextLessThan value).mpr ⟨hn, hfinite, by omega⟩⟩)

end FloatLib.Floats.ExecFloat.P3109
