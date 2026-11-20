/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Arithmetic.Extrema.Proof
public import FloatLib.Floats.Formats.P3109.Arithmetic.Queries.Runtime

/-!
# Integer indices for P3109 numerical order

Give each non-NaN code an integer index and the encoded datum set becomes a consecutive interval.
Negative magnitude codes get negative indices, zero gets zero, and nonnegative codes keep their own
numbers, so in a signed 8-bit format code `0x81` gets index `-1`. The exact decoder preserves this
order, the infinite endpoints of extended formats included. With these indices, adjacency
arguments never have to enumerate a descriptor's code space.

Reference: P3109 Interim Report v4.1 (unapproved draft), §§3.1 and 4.16.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109.Format

/-- An integer index in numerical order. Its value at the NaN code is never used. -/
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

/--
Closes one case of `less_decodeNat_iff_orderIndex`: the decoder and the index are unfolded at
the facts of the case, and the comparison of two finite values is that of their codes.
-/
local macro "order_case" : tactic =>
  `(tactic| (
    simp_all only [decodeNat, orderIndex, nanBits, positiveInfinityBits, negativeInfinityBits,
      reduceCtorEq, true_and, false_and, ite_true, ite_false,
      Arithmetic.toRat, Arithmetic.CompareLess, Dyadic.neg_toRat,
      decide_eq_true_eq, Bool.false_eq_true, neg_lt_neg_iff,
      (decodePositiveFinite_strictMono _).lt_iff_lt, positiveFinite_lt_negative,
      true_iff, false_iff] <;>
    first
    | omega
    | constructor
      · intro; omega
      · intro
        apply negative_lt_positiveFinite
        omega))

/-- Exact decoded strict order is the integer-index order on every pair of non-NaN codes. -/
theorem less_decodeNat_iff_orderIndex (format : Format) (left right : Nat)
    (hleft : left < format.modulus) (hright : right < format.modulus)
    (hleftNan : left ≠ format.nanBits) (hrightNan : right ≠ format.nanBits) :
    Arithmetic.CompareLess (Arithmetic.toRat (format.decodeNat left))
      (Arithmetic.toRat (format.decodeNat right)) = true ↔
        format.orderIndex left < format.orderIndex right := by
  have hmodulus := format.modulus_eq_two_mul_signBoundary
  have hboundary := format.one_lt_signBoundary
  -- A code of a signed extended format is positive infinity, negative infinity, another code of
  -- the negative half, or a code of the nonnegative half.
  have classes (bits : Nat) (hs : format.signedness = .signed) :
      (bits = format.positiveInfinityBits ∧ bits ≠ format.negativeInfinityBits ∧
          ¬format.signBoundary < bits) ∨
        (bits ≠ format.positiveInfinityBits ∧ bits = format.negativeInfinityBits ∧
          format.signBoundary < bits) ∨
        (bits ≠ format.positiveInfinityBits ∧ bits ≠ format.negativeInfinityBits ∧
          format.signBoundary < bits) ∨
        (bits ≠ format.positiveInfinityBits ∧ bits ≠ format.negativeInfinityBits ∧
          ¬format.signBoundary < bits) := by
    simp only [positiveInfinityBits, negativeInfinityBits, hs]
    omega
  cases hs : format.signedness
  · cases hd : format.domain
    · by_cases hls : format.signBoundary < left <;>
        by_cases hrs : format.signBoundary < right <;> order_case
    · rcases classes left hs with ⟨hlp, hln, hls⟩ | ⟨hlp, hln, hls⟩ | ⟨hlp, hln, hls⟩ |
          ⟨hlp, hln, hls⟩ <;>
        rcases classes right hs with ⟨hrp, hrn, hrs⟩ | ⟨hrp, hrn, hrs⟩ | ⟨hrp, hrn, hrs⟩ |
          ⟨hrp, hrn, hrs⟩ <;> order_case
  · cases hd : format.domain
    · order_case
    · by_cases hlp : left = format.positiveInfinityBits <;>
        by_cases hrp : right = format.positiveInfinityBits <;> order_case

end FloatLib.Floats.Formats.P3109.Format
