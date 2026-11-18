/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.State.Proof

/-!
# Correctness and signed zeros of binary sums

A finite sum accumulates exact dyadics and rounds once. Its zero sign follows the input signs and
rounding direction: the empty sum is positive zero, a nonempty sum of zeros of one sign keeps that
sign, and other cancellation is negative only when rounding downward. Real-valued nearest-rounding
statements require a finite output. A singleton infinity agrees with the destination cast,
including status.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace Reduction

/--
The executable sum accumulator has the same exact rational value after any permutation.

It concerns the finite accumulator field and says nothing about the complete exceptional result,
because NaN selection depends on traversal order.
-/
theorem sumAccumulator_toRat_eq_of_perm
    {destination source : FloatFormat}
    {left right : List (Model source)} (hperm : left.Perm right) :
    (left.foldl Internal.State.pushValue
      ({} : Internal.State destination)).exact.toRat =
    (right.foldl Internal.State.pushValue
      ({} : Internal.State destination)).exact.toRat := by
  rw [Internal.foldl_pushValue_exact_toRat,
    Internal.foldl_pushValue_exact_toRat]
  simp only [Numerics.Dyadic.zero_toRat, zero_add]
  exact Semantics.finiteSum_eq_of_perm hperm

/--
A mathematically nonzero finite sum gives a nonzero exact accumulator.

Callers can stay in the rational specification without seeing the dyadic accumulator's internal
representation.
-/
theorem sumAccumulator_significand_ne_zero_of_finiteSum_ne_zero
    (destination : FloatFormat) {source : FloatFormat}
    (values : Array (Model source))
    (hnonzero : Semantics.finiteSum values.toList ≠ 0) :
    (values.foldl Internal.State.pushValue
      ({} : Internal.State destination)).exact.significand ≠ 0 := by
  intro hzero
  apply hnonzero
  have hrat :
      (values.foldl Internal.State.pushValue
        ({} : Internal.State destination)).exact.toRat = 0 :=
    (Numerics.Dyadic.toRat_eq_zero_iff _).2 hzero
  rw [Internal.array_foldl_pushValue_exact_toRat] at hrat
  exact hrat

/--
A nonzero sum of finite inputs performs one final dyadic rounding and reports that rounding's
status and ternary value.
-/
theorem sum_status_eq_round_of_finite_nonzero
    (destination : FloatFormat) {source : FloatFormat}
    (values : Array (Model source)) (mode : IEEERoundingMode)
    (hfinite : ∀ value ∈ values.toList, isFinite value = true)
    (hnonzero : Semantics.finiteSum values.toList ≠ 0) :
    sum destination values mode (status := true) =
      {
        value := Internal.Directed.roundDyadic destination mode
          (values.foldl Internal.State.pushValue
            ({} : Internal.State destination)).exact
        status := dyadicRoundingStatus destination mode
          (values.foldl Internal.State.pushValue
            ({} : Internal.State destination)).exact
          (Internal.Directed.roundDyadic destination mode
            (values.foldl Internal.State.pushValue
              ({} : Internal.State destination)).exact)
        ternary := dyadicTernary
          (values.foldl Internal.State.pushValue
            ({} : Internal.State destination)).exact
          (Internal.Directed.roundDyadic destination mode
            (values.foldl Internal.State.pushValue
              ({} : Internal.State destination)).exact)
      } :=
  Internal.State.finish_of_hasOnlyFiniteTerms_of_ne_zero _ mode
    (Internal.array_foldl_pushValue_hasOnlyFiniteTerms values hfinite)
    (sumAccumulator_significand_ne_zero_of_finiteSum_ne_zero destination values hnonzero)

/--
A finite sum whose exact accumulator is zero returns a zero and raises no status indicator.

Its sign follows the accumulator's signed-zero rule. If at least one term was accumulated, the zero
is negative when every term was a negative zero, or when the terms were not all positive zeros and
the direction is downward. The empty sum accumulates no term and gives a positive zero. A
destination without signed zero returns its single zero. `sum_status_empty`,
`sum_status_eq_zero_of_same_sign_zeros` and `sum_status_eq_zero_of_finiteSum_eq_zero` state the
sign from the inputs.
-/
theorem sum_status_eq_zero_of_finite
    (destination : FloatFormat) {source : FloatFormat}
    (values : Array (Model source)) (mode : IEEERoundingMode)
    (hfinite : ∀ value ∈ values.toList, isFinite value = true)
    (hzero :
      (values.foldl Internal.State.pushValue
        ({} : Internal.State destination)).exact.significand = 0) :
    sum destination values mode (status := true) =
      {
        value := zero destination <|
          (values.foldl Internal.State.pushValue
            ({} : Internal.State destination)).sawFiniteTerm &&
          ((values.foldl Internal.State.pushValue
              ({} : Internal.State destination)).allTermsNegativeZero ||
            (!(values.foldl Internal.State.pushValue
                ({} : Internal.State destination)).allTermsPositiveZero &&
              mode == .down))
        status := .clear
        ternary := .eq
      } :=
  Internal.State.finish_of_hasOnlyFiniteTerms_of_eq_zero _ mode
    (Internal.array_foldl_pushValue_hasOnlyFiniteTerms values hfinite) hzero

/--
Every finite-input nearest-even sum with a finite result is one real rounding of the exact sum.
Zero totals include empty input, signed zeros, and cancellation. Their stored signs are specified
by `sum_status_eq_zero_of_finite` and disappear only in the real-valued conclusion.
-/
theorem sum_status_value_toReal_eq_roundAt_of_finite
    (destination : FloatFormat) {source : FloatFormat}
    (values : Array (Model source))
    (hfmt : destination.isIEEE = true)
    (hfinite : ∀ value ∈ values.toList, isFinite value = true)
    (hresult : isFinite (sum destination values .nearest (status := true)).value = true) :
    toReal (sum destination values .nearest (status := true)).value =
      roundAt destination (Semantics.finiteSum values.toList : ℝ) := by
  have hround := Internal.State.toReal_finish_nearest_eq_roundAt
    (values.foldl Internal.State.pushValue ({} : Internal.State destination)) hfmt
    (Internal.array_foldl_pushValue_hasOnlyFiniteTerms values hfinite) hresult
  rwa [Internal.array_foldl_pushValue_exact_toRat] at hround

/--
A nonempty sum of zeros with one common sign preserves that sign in every rounding mode.

The destination's zero constructor accounts for formats without a negative zero. The hypotheses
refer only to the input values, independently of the accumulator's signed-zero flags.
-/
theorem sum_status_eq_zero_of_same_sign_zeros
    (destination : FloatFormat) {source : FloatFormat}
    (values : Array (Model source)) (mode : IEEERoundingMode) (negative : Bool)
    (hnonempty : values ≠ #[])
    (hzero : ∀ value ∈ values.toList, isZero value = true)
    (hsign : ∀ value ∈ values.toList, signBit value = negative) :
    sum destination values mode (status := true) =
      { value := zero destination negative, status := .clear, ternary := .eq } := by
  let state : Internal.State destination :=
    { sawFiniteTerm := true
      allTermsNegativeZero := negative
      allTermsPositiveZero := !negative }
  have hstep (value : Model source) (hmem : value ∈ values.toList)
      (accumulator : Internal.State destination) :
      accumulator.pushValue value =
        accumulator.pushExact { negative, significand := 0, exponent := 0 } := by
    have hfinite := isFinite_eq_true_of_isZero_eq_true value (hzero value hmem)
    rw [Internal.State.pushValue_eq_pushExact _ _ hfinite,
      finiteDyadic_eq_of_toDyadic hfinite
        (toDyadic?_eq_zero_of_isZero_eq_true value (hzero value hmem)), hsign value hmem]
  unfold sum Internal.Status.sum
  rw [← Array.foldl_toList]
  cases hlist : values.toList with
  | nil => exact (hnonempty (Array.toList_eq_nil_iff.mp hlist)).elim
  | cons value rest =>
      have hfirst : ({} : Internal.State destination).pushValue value = state := by
        rw [hstep value (by simp [hlist])]
        cases negative <;> simp [state, Internal.State.pushExact, Numerics.Dyadic.zero]
      have hrest : rest.foldl Internal.State.pushValue state = state := by
        refine List.foldlRecOn (motive := fun accumulator => accumulator = state)
          rest Internal.State.pushValue rfl ?_
        intro accumulator haccumulator term hmem
        rw [haccumulator, hstep term (by simp [hlist, hmem])]
        cases negative <;> simp [state, Internal.State.pushExact, Numerics.Dyadic.zero]
      rw [List.foldl_cons, hfirst, hrest]
      cases negative <;> simp [state, Internal.State.finish, outcomeWithInvalid]

/--
A nonempty finite sum whose exact value is zero, but whose terms are not all zeros of one sign,
returns the zero C23 draft N3220 Annex F.9.3 assigns to an exact cancellation or to mixed-sign
zeros: negative when
rounding toward negative infinity and positive otherwise, with clear status. A destination without
signed zero returns its single zero. The hypotheses refer only to the input values. The two sign
premises fail for the empty sum, which gives a positive zero in every mode (`sum_status_empty`).
-/
theorem sum_status_eq_zero_of_finiteSum_eq_zero
    (destination : FloatFormat) {source : FloatFormat}
    (values : Array (Model source)) (mode : IEEERoundingMode)
    (hfinite : ∀ value ∈ values.toList, isFinite value = true)
    (hzero : Semantics.finiteSum values.toList = 0)
    (hnegative : ¬∀ value ∈ values.toList, isZero value = true ∧ signBit value = true)
    (hpositive : ¬∀ value ∈ values.toList, isZero value = true ∧ signBit value = false) :
    sum destination values mode (status := true) =
      { value := zero destination (mode == .down), status := .clear, ternary := .eq } := by
  have hsig : (values.foldl Internal.State.pushValue
      ({} : Internal.State destination)).exact.significand = 0 := by
    apply (Numerics.Dyadic.toRat_eq_zero_iff _).mp
    rw [Internal.array_foldl_pushValue_exact_toRat, hzero]
  rw [sum_status_eq_zero_of_finite destination values mode hfinite hsig, ← Array.foldl_toList]
  obtain ⟨hsaw, hallNegative, hallPositive⟩ :=
    Internal.foldl_pushValue_flags ({} : Internal.State destination) values.toList hfinite
  have hnonempty : values.toList.isEmpty = false := by
    cases hlist : values.toList with
    | nil => exact absurd (by simp [hlist]) hnegative
    | cons _ _ => rfl
  have hnotNegative : (values.toList.all fun value => isZero value && signBit value) = false := by
    rw [Bool.eq_false_iff]
    intro hall
    exact hnegative fun value hmem => by simpa using List.all_eq_true.mp hall value hmem
  have hnotPositive :
      (values.toList.all fun value => isZero value && !signBit value) = false := by
    rw [Bool.eq_false_iff]
    intro hall
    exact hpositive fun value hmem => by simpa using List.all_eq_true.mp hall value hmem
  rw [hsaw, hallNegative, hallPositive, hnonempty, hnotNegative, hnotPositive]
  simp

/-- A singleton infinity has the value and exception indicators of a destination cast. -/
theorem sum_status_singleton_eq_cast_status_of_isInfinite
    (destination : FloatFormat) {source : FloatFormat}
    (value : Model source) (mode : IEEERoundingMode)
    (hinf : isInfinite value = true) :
    sum destination #[value] mode (status := true) =
      cast source destination value mode (status := true) := by
  have hnan := isNaN_eq_false_of_isInfinite_eq_true value hinf
  cases mode <;> cases hsign : signBit value <;>
    simp only [sum, Internal.Status.sum, Internal.State.finish, List.size_toArray,
      List.length_cons, List.length_nil, zero_add, List.foldl_toArray', List.foldl_cons,
      Internal.State.pushValue, hnan, Bool.false_eq_true, ↓reduceDIte, hinf,
      Internal.State.pushInfinity, hsign, ↓reduceIte, List.foldl_nil, Bool.and_false,
      Bool.or_self, Bool.or_true, cast, Internal.Status.cast, Internal.Directed.cast,
      Internal.Nearest.cast, Bool.and_true, Bool.or_false] <;>
    split <;> rfl

/-- The empty correctly rounded sum is an exact positive zero with no exception indicator. -/
@[simp] theorem sum_status_empty
    (destination source : FloatFormat) (mode : IEEERoundingMode) :
    sum destination (#[] : Array (Model source)) mode (status := true) =
      { value := zero destination false, status := .clear, ternary := .eq } := by
  simp [sum, Internal.Status.sum, Internal.State.finish, outcomeWithInvalid]

/-- The sum with `status := true` delivers the value of the sum in the same direction. -/
@[simp] theorem value_sum (destination : FloatFormat) {source : FloatFormat}
    (values : Array (Model source)) (mode : IEEERoundingMode) :
    (sum destination values mode (status := true)).value = sum destination values mode :=
  rfl

end Reduction
end Model
end FloatLib.Floats.Formats.BinaryInterchange
