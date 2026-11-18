/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Runtime

/-!
# Rational specifications of binary sums and dots

Finite contributions are the exact rational values of decoded words; exceptional words contribute
zero. The list sum is invariant under permutations. The array dot specification agrees with the
corresponding bounded list slice and records a length error when the two lists differ in length.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace Reduction

namespace Semantics

/-- Exact rational contribution to the accumulator. Exceptional encodings contribute zero. -/
def finiteContribution {format : FloatFormat} (value : Model format) : Rat :=
  match toDyadic? value with
  | some exact => exact.toRat
  | none => 0

/-- Exact sum of the finite contributions. -/
def finiteSum {format : FloatFormat} (values : List (Model format)) : Rat :=
  (values.map finiteContribution).sum

/-- Exact sum of pairwise products, with an error for unequal lengths. -/
def finiteDot {leftFormat rightFormat : FloatFormat}
    (left : List (Model leftFormat)) (right : List (Model rightFormat)) :
    Except Numerics.ReductionError Rat :=
  if left.length != right.length then
    .error (.lengthMismatch left.length right.length)
  else
    .ok ((List.zipWith
      (fun x y => finiteContribution x * finiteContribution y)
      left right).sum)

/-- Exact dot product of `remaining` pairs from `index`, with bounds for both arrays. -/
def finiteDotSlice
    {leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (index remaining : Nat)
    (hleft : index + remaining ≤ left.size)
    (hright : index + remaining ≤ right.size) : Rat :=
  match remaining with
  | 0 => 0
  | count + 1 =>
      have hleftIndex : index < left.size := by omega
      have hrightIndex : index < right.size := by omega
      finiteContribution left[index] * finiteContribution right[index] +
        finiteDotSlice left right (index + 1) count (by omega) (by omega)
termination_by remaining

/--
The bounded Array specification is the corresponding list dot product over the same slice.

This bridge lets the kernel traverse indexed arrays while public theorems use ordinary
list operations. The bounds make `drop` and `take` select all `remaining` pairs.
-/
theorem finiteDotSlice_eq_zipWith_sum
    {leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (index remaining : Nat)
    (hleft : index + remaining ≤ left.size)
    (hright : index + remaining ≤ right.size) :
    finiteDotSlice left right index remaining hleft hright =
      (List.zipWith
        (fun x y => finiteContribution x * finiteContribution y)
        (left.toList.drop index |>.take remaining)
        (right.toList.drop index |>.take remaining)).sum := by
  induction remaining generalizing index with
  | zero =>
      simp [finiteDotSlice]
  | succ count ih =>
      have hleftIndex : index < left.size := by omega
      have hrightIndex : index < right.size := by omega
      have hleftDrop :
          left.toList.drop index =
            left[index] :: left.toList.drop (index + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using hleftIndex), Array.getElem_toList]
      have hrightDrop :
          right.toList.drop index =
            right[index] :: right.toList.drop (index + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using hrightIndex), Array.getElem_toList]
      rw [finiteDotSlice]
      rw [hleftDrop, hrightDrop]
      simp only [List.take_succ_cons, List.zipWith_cons_cons, List.sum_cons]
      rw [ih]

/-- On equal-sized arrays, the list and bounded-Array dot specifications agree. -/
theorem finiteDot_toList_eq_slice
    {leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (hsize : left.size = right.size) :
    finiteDot left.toList right.toList =
      .ok (finiteDotSlice left right 0 left.size
        (by simp) (by simp [hsize])) := by
  simp [finiteDot, finiteDotSlice_eq_zipWith_sum, List.take_of_length_le, hsize]

/-- The finite-sum specification is independent of traversal order. -/
theorem finiteSum_eq_of_perm
    {format : FloatFormat} {left right : List (Model format)}
    (hperm : left.Perm right) :
    finiteSum left = finiteSum right :=
  (hperm.map finiteContribution).sum_eq

/-- A one-pair finite dot product is the product of the two contributions. -/
@[simp] theorem finiteDot_singleton
    {leftFormat rightFormat : FloatFormat}
    (left : Model leftFormat) (right : Model rightFormat) :
    finiteDot [left] [right] =
      .ok (finiteContribution left *
        finiteContribution right) := by
  simp [finiteDot]

end Semantics

end Reduction
end Model
end FloatLib.Floats.Formats.BinaryInterchange
