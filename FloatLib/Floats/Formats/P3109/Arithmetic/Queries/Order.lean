/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Arithmetic.Extrema.Proof
public import FloatLib.Floats.Formats.P3109.Arithmetic.Queries.Runtime
public import FloatLib.Floats.Formats.P3109.Order
import Mathlib.Tactic.Linarith

/-!
# Integer indices for P3109 numerical order

Excluding NaN, the encoded datum set is a consecutive interval of integers: negative magnitude
codes receive negative indices, zero receives zero, and nonnegative codes keep their indices.
The exact decoder preserves this order, including the infinite endpoints in extended formats.
These indices allow adjacency arguments without enumerating a descriptor's code space.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109.Format

/-- An integer index in numerical order; its value at the NaN code is not used. -/
def orderIndex (format : Format) (bits : Nat) : Int :=
  if format.signedness = .signed ∧ format.signBoundary < bits then
    (format.signBoundary : Int) - bits
  else bits

private theorem positiveFinite_nonneg (format : Format) (bits : Nat) :
    0 ≤ (format.decodePositiveFinite bits).toRat := by
  simpa using format.decodePositiveFinite_strictMono.monotone (Nat.zero_le bits)

private theorem positiveFinite_pos (format : Format) (bits : Nat) (hbits : 0 < bits) :
    0 < (format.decodePositiveFinite bits).toRat := by
  simpa using format.decodePositiveFinite_strictMono hbits

private theorem positiveFinite_lt_negative (format : Format) (left right : Nat) :
    ¬ ((format.decodePositiveFinite left).toRat <
      -(format.decodePositiveFinite right).toRat) := by
  have hl := positiveFinite_nonneg format left
  have hr := positiveFinite_nonneg format right
  linarith

private theorem negative_lt_positiveFinite (format : Format) (left right : Nat)
    (hleft : 0 < left) :
    -(format.decodePositiveFinite left).toRat <
      (format.decodePositiveFinite right).toRat := by
  have hl := positiveFinite_pos format left hleft
  have hr := positiveFinite_nonneg format right
  linarith

/-- Exact decoded strict order is the integer-index order on every pair of non-NaN codes. -/
theorem less_decodeNat_iff_orderIndex (format : Format) (left right : Nat)
    (hleft : left < format.modulus) (hright : right < format.modulus)
    (hleftNan : left ≠ format.nanBits) (hrightNan : right ≠ format.nanBits) :
    Arithmetic.less (Arithmetic.toRat (format.decodeNat left))
      (Arithmetic.toRat (format.decodeNat right)) = true ↔
        format.orderIndex left < format.orderIndex right := by
  have hmodulus := format.modulus_eq_two_mul_signBoundary
  have hboundary := format.one_lt_signBoundary
  cases hs : format.signedness <;> cases hd : format.domain <;>
    (by_cases hls : format.signBoundary < left) <;>
    (by_cases hrs : format.signBoundary < right) <;>
    (by_cases hlp : left = format.positiveInfinityBits) <;>
    (by_cases hrp : right = format.positiveInfinityBits) <;>
    (by_cases hln : left = format.negativeInfinityBits) <;>
    (by_cases hrn : right = format.negativeInfinityBits) <;>
    simp_all only [decodeNat, orderIndex, nanBits, positiveInfinityBits, negativeInfinityBits,
      reduceCtorEq, true_and, false_and, ite_true, ite_false,
      Arithmetic.toRat, Arithmetic.less, Dyadic.neg_toRat,
      decide_eq_true_eq, Bool.false_eq_true, neg_lt_neg_iff,
      format.decodePositiveFinite_strictMono.lt_iff_lt, positiveFinite_lt_negative,
      true_iff, false_iff] <;>
    first
    | omega
    | constructor
      · intro; omega
      · intro
        apply negative_lt_positiveFinite
        omega

end FloatLib.Floats.Formats.P3109.Format
