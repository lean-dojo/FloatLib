/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.State.Proof

/-!
# Correctness and exceptional results of binary dot products

Pairwise products accumulate exactly and are rounded once into any destination descriptor. Finite-
input results, cancellation, empty products and length errors are covered. Real-valued nearest-
rounding statements require a finite output; generated-invalid flags are governed by the shared
accumulator invariants.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace Reduction

/--
A mathematically nonzero finite dot product gives a nonzero exact accumulator.

The premise uses the public list specification, and equal array lengths rule out the error branch.
Exceptional entries contribute zero to both sides.
-/
theorem dotAccumulator_significand_ne_zero_of_finiteDot_ne_zero
    (destination : FloatFormat) {leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (hsize : left.size = right.size)
    (hnonzero : Semantics.finiteDot left.toList right.toList ≠ .ok 0) :
    (Internal.dotState left right hsize :
      Internal.State destination).exact.significand ≠ 0 := by
  intro hzero
  apply hnonzero
  rw [Semantics.finiteDot_toList_eq_slice left right hsize]
  congr 1
  rw [← Internal.dotState_exact_toRat left right hsize]
  exact (Numerics.Dyadic.toRat_eq_zero_iff _).2 hzero

/-- With equal lengths, the dot product with status finishes the accumulated dot-product state. -/
private theorem dot_status_eq_ok_finish
    (destination : FloatFormat) {leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (mode : IEEERoundingMode) (hsize : left.size = right.size) :
    dot destination left right mode (status := true) =
      .ok ((Internal.dotState left right hsize : Internal.State destination).finish mode) := by
  simp [dot, Internal.Status.dot, hsize]

/--
A nonzero dot product of finite inputs performs one final dyadic rounding and reports that
rounding's status and ternary value.
-/
theorem dot_status_eq_round_of_finite_nonzero
    (destination : FloatFormat) {leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (mode : IEEERoundingMode) (hsize : left.size = right.size)
    (hleftFinite :
      ∀ position (hposition : position < left.size),
        isFinite left[position] = true)
    (hrightFinite :
      ∀ position (hposition : position < right.size),
        isFinite right[position] = true)
    (hnonzero : Semantics.finiteDot left.toList right.toList ≠ .ok 0) :
    dot destination left right mode (status := true) =
      .ok {
        value := Internal.Directed.roundDyadic destination mode
          (Internal.dotState left right hsize :
            Internal.State destination).exact
        status := dyadicRoundingStatus destination mode
          (Internal.dotState left right hsize :
            Internal.State destination).exact
          (Internal.Directed.roundDyadic destination mode
            (Internal.dotState left right hsize :
              Internal.State destination).exact)
        ternary := dyadicTernary
          (Internal.dotState left right hsize :
            Internal.State destination).exact
          (Internal.Directed.roundDyadic destination mode
            (Internal.dotState left right hsize :
              Internal.State destination).exact)
      } := by
  rw [dot_status_eq_ok_finish destination left right mode hsize,
    Internal.State.finish_of_hasOnlyFiniteTerms_of_ne_zero _ mode
      (Internal.dotState_hasOnlyFiniteTerms left right hsize hleftFinite hrightFinite)
      (dotAccumulator_significand_ne_zero_of_finiteDot_ne_zero
        destination left right hsize hnonzero)]

/--
A finite dot product whose exact accumulator is zero returns a zero and raises no status indicator.

Its sign follows the accumulator's signed-zero rule, applied to the exact products. If at least one
product was accumulated, the zero is negative when every product was a negative zero, or when the
products were not all positive zeros and the direction is downward. The empty dot product
accumulates no product and gives a positive zero (`dot_status_empty`). A destination without signed
zero returns its single zero.
-/
theorem dot_status_eq_zero_of_finite
    (destination : FloatFormat) {leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (mode : IEEERoundingMode) (hsize : left.size = right.size)
    (hleftFinite :
      ∀ position (hposition : position < left.size),
        isFinite left[position] = true)
    (hrightFinite :
      ∀ position (hposition : position < right.size),
        isFinite right[position] = true)
    (hzero :
      (Internal.dotState left right hsize :
        Internal.State destination).exact.significand = 0) :
    dot destination left right mode (status := true) =
      .ok {
        value := zero destination <|
          (Internal.dotState left right hsize :
            Internal.State destination).sawFiniteTerm &&
          ((Internal.dotState left right hsize :
              Internal.State destination).allTermsNegativeZero ||
            (!(Internal.dotState left right hsize :
                Internal.State destination).allTermsPositiveZero &&
              mode == .down))
        status := .clear
        ternary := .eq
      } := by
  rw [dot_status_eq_ok_finish destination left right mode hsize,
    Internal.State.finish_of_hasOnlyFiniteTerms_of_eq_zero _ mode
      (Internal.dotState_hasOnlyFiniteTerms left right hsize hleftFinite hrightFinite) hzero]

/--
Every successful finite-input nearest-even dot product with a finite result is one real rounding
of the exact product sum, including cancellation to zero. The successful specification forces equal
input lengths, and the finite-result premise excludes exceptional outputs.
-/
theorem dot_status_value_toReal_eq_roundAt_of_finite
    (destination : FloatFormat) {leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (exact : Rat) (outcome : IEEEOutcome destination)
    (hfmt : destination.isIEEE = true)
    (hleftFinite : ∀ position (hposition : position < left.size), isFinite left[position] = true)
    (hrightFinite : ∀ position (hposition : position < right.size), isFinite right[position] = true)
    (hspec : Semantics.finiteDot left.toList right.toList = .ok exact)
    (houtcome : dot destination left right .nearest (status := true) = .ok outcome)
    (hresult : isFinite outcome.value = true) :
    toReal outcome.value = roundAt destination (exact : ℝ) := by
  have hsize : left.size = right.size := by
    by_contra hne
    simp [Semantics.finiteDot, hne] at hspec
  rw [dot_status_eq_ok_finish destination left right .nearest hsize, Except.ok.injEq] at houtcome
  subst outcome
  rw [Internal.State.toReal_finish_nearest_eq_roundAt _ hfmt
      (Internal.dotState_hasOnlyFiniteTerms left right hsize hleftFinite hrightFinite) hresult,
    Internal.dotState_exact_toRat_of_finiteDot_eq_ok left right hsize hspec]

/-- A mismatched dot product reports both observed lengths and performs no reduction. -/
theorem dot_status_lengthMismatch
    (destination : FloatFormat) {leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (mode : IEEERoundingMode) (hsize : left.size ≠ right.size) :
    dot destination left right mode (status := true) =
      .error (.lengthMismatch left.size right.size) := by
  simp [dot, Internal.Status.dot, hsize]

/--
The empty correctly rounded dot product is an exact positive zero with no exception indicator.
-/
@[simp] theorem dot_status_empty
    (destination leftFormat rightFormat : FloatFormat) (mode : IEEERoundingMode) :
    dot destination
        (#[] : Array (Model leftFormat)) (#[] : Array (Model rightFormat)) mode (status := true) =
      .ok { value := zero destination false, status := .clear, ternary := .eq } := by
  simp [dot, Internal.Status.dot, Internal.dotState, Internal.dotStateLoop,
    Internal.State.finish, outcomeWithInvalid]

/--
The dot product with `status := true` has the value and the length check of the dot product in
the same direction.
-/
@[simp] theorem map_value_dot (destination : FloatFormat)
    {leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (mode : IEEERoundingMode) :
    (dot destination left right mode (status := true)).map IEEEOutcome.value =
      dot destination left right mode := by
  unfold dot Internal.Status.dot Internal.Value.dot
  split <;> rfl

end Reduction
end Model
end FloatLib.Floats.Formats.BinaryInterchange
