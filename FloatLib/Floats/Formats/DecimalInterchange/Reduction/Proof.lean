/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.Reduction.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Arithmetic.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Semantics

/-!
# The decimal reductions round the exact result once

For finite operands whose exact values are the rationals `exacts`, each reduction is one
`project` of the exact result: the sum of `exacts` for `sum`, of their magnitudes for `sumAbs`,
of their squares for `sumSquare`, and the sum of the products for `dot`
(`sum_eq_project` and its siblings). The theorems of `project` then apply. Two are stated here
for `sum`, and hold for the other three reductions by the same one-line argument:
`sum_error_le_half` (to nearest, the result is within half a unit of the rounding quantum of
the exact sum, when no overflow is signaled) and `sum_inexact_iff` (`inexact` is raised exactly
when the result is not the exact sum, in every direction). `sum_valid` and its siblings say that
every result is a datum of the format, for all operands.

No intermediate overflow or underflow can occur, because the terms are added as rationals.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange
namespace Arithmetic

namespace Reduction

/-- The exact value of a finite term. -/
def Term.value? : Term → Option ℚ
  | .finite _ value _ => some value
  | _ => none

/-- The term of a datum has the exact value of the datum. -/
theorem Term.value?_ofDatum (x : Datum) : (Term.ofDatum x).value? = x.toRat? := by
  cases x <;> simp [Term.ofDatum, Term.value?, Datum.toRat?_eq, Datum.finiteValue]

/-- The magnitude of a finite term has the magnitude of its value. -/
theorem Term.value?_abs {term : Term} {exact : ℚ} (h : term.value? = some exact) :
    term.abs.value? = some |exact| := by
  cases term <;> simp_all [Term.abs, Term.value?]

/-- The product of two finite terms has the product of their values. -/
theorem Term.value?_mul {left right : Term} {p q : ℚ} (hp : left.value? = some p)
    (hq : right.value? = some q) : (left.mul right).value? = some (p * q) := by
  cases left <;> cases right <;> simp_all [Term.mul, Term.value?]

/--
Pairs of finite data, combined by an operation on terms that acts on the values of finite terms
as `op`, are finite terms with the combined values.
-/
theorem map_value?_zipWith (combine : Term → Term → Term) (op : ℚ → ℚ → ℚ)
    (hcombine : ∀ {left right : Term} {p q : ℚ}, left.value? = some p → right.value? = some q →
      (combine left right).value? = some (op p q)) :
    ∀ (leftData rightData : List Datum) (xs ys : List ℚ),
      leftData.map Datum.toRat? = xs.map some → rightData.map Datum.toRat? = ys.map some →
      (List.zipWith (fun x y => combine (Term.ofDatum x) (Term.ofDatum y)) leftData
        rightData).map Term.value? = (List.zipWith op xs ys).map some
  | [], _, xs, _, hleft, _ => by cases xs <;> simp_all
  | _ :: _, _, [], _, hleft, _ => by simp at hleft
  | _ :: _, [], _ :: _, ys, _, hright => by cases ys <;> simp_all
  | _ :: _, _ :: _, _ :: _, [], _, hright => by simp at hright
  | x :: leftData, y :: rightData, p :: xs, q :: ys, hleft, hright => by
      simp only [List.map_cons, List.cons.injEq] at hleft hright
      simp only [List.zipWith_cons_cons, List.map_cons, List.cons.injEq]
      exact ⟨hcombine (by rw [Term.value?_ofDatum]; exact hleft.1)
        (by rw [Term.value?_ofDatum]; exact hright.1),
        map_value?_zipWith combine op hcombine leftData rightData xs ys hleft.2 hright.2⟩

/-- Finite terms only add their values to the exact sum. -/
theorem foldl_push_of_values (mode : RoundingMode) :
    ∀ (terms : List Term) (exacts : List ℚ) (total : Total),
      terms.map Term.value? = exacts.map some →
      ∃ quantum negative, terms.foldl (Total.push mode) total =
        { total with value := total.value + exacts.sum, quantum := quantum, negative := negative }
  | [], exacts, total, h => by
      cases exacts with
      | nil => exact ⟨total.quantum, total.negative, by simp⟩
      | cons exact rest => simp at h
  | term :: terms, exacts, total, h => by
      cases exacts with
      | nil => simp at h
      | cons exact rest =>
          simp only [List.map_cons, List.cons.injEq] at h
          cases term with
          | finite s value quantum =>
              obtain rfl : value = exact := by simpa [Term.value?] using h.1
              obtain ⟨quantum', negative', hfold⟩ :=
                foldl_push_of_values mode terms rest (total.push mode (.finite s value quantum)) h.2
              refine ⟨quantum', negative', ?_⟩
              rw [List.foldl_cons, hfold]
              simp [Total.push, add_assoc]
          | infinity s => simp [Term.value?] at h
          | nan s t p => simp [Term.value?] at h
          | invalid => simp [Term.value?] at h

/-- The exact sum of finite terms is the sum of their values, with no exceptional term. -/
theorem total_of_values (mode : RoundingMode) (terms : List Term) (exacts : List ℚ)
    (h : terms.map Term.value? = exacts.map some) :
    ∃ quantum negative,
      total mode terms = { value := exacts.sum, quantum := quantum, negative := negative } := by
  obtain ⟨quantum, negative, hfold⟩ := foldl_push_of_values mode terms exacts {} h
  exact ⟨quantum, negative, by rw [total, hfold]; simp⟩

/-- A sum of finite terms is one rounding of the sum of their values. -/
theorem deliver_total_of_values (f : Format) (mode : RoundingMode) (terms : List Term)
    (exacts : List ℚ) (h : terms.map Term.value? = exacts.map some) :
    ∃ preferred negativeZero,
      (total mode terms).deliver f mode = project f mode exacts.sum preferred negativeZero ∧
        (total mode terms).deliverMagnitude f mode =
          project f mode exacts.sum preferred negativeZero := by
  obtain ⟨quantum, negative, htotal⟩ := total_of_values mode terms exacts h
  exact ⟨quantum.getD 0, negative.getD false, by
    rw [htotal]; simp [Total.deliver, Total.deliverMagnitude]⟩

/-- The outcome of a sum is a datum of the format. -/
theorem Total.deliver_valid (f : Format) (mode : RoundingMode) (total : Total) :
    (total.deliver f mode).value.Valid f := by
  unfold Total.deliver
  split
  · exact nanResult_valid ..
  · split
    · exact invalidResult_valid f
    · split
      · trivial
      · exact project_valid ..

/-- The outcome of a sum of magnitudes is a datum of the format. -/
theorem Total.deliverMagnitude_valid (f : Format) (mode : RoundingMode) (total : Total) :
    (total.deliverMagnitude f mode).value.Valid f := by
  unfold Total.deliverMagnitude
  split
  · exact Total.deliver_valid f mode total
  · split
    · trivial
    · exact Total.deliver_valid f mode total

end Reduction

open Reduction

/-- `sum` always returns a datum of the format. -/
theorem sum_valid (f : Format) (mode : RoundingMode) (values : Array Datum) :
    (sum f mode values).value.Valid f :=
  Total.deliver_valid f mode _

/-- `sumAbs` always returns a datum of the format. -/
theorem sumAbs_valid (f : Format) (mode : RoundingMode) (values : Array Datum) :
    (sumAbs f mode values).value.Valid f :=
  Total.deliverMagnitude_valid f mode _

/-- `sumSquare` always returns a datum of the format. -/
theorem sumSquare_valid (f : Format) (mode : RoundingMode) (values : Array Datum) :
    (sumSquare f mode values).value.Valid f :=
  Total.deliverMagnitude_valid f mode _

/--
**The decimal `sum` rounds the exact sum once.** For finite operands with the exact values
`exacts`, it is one `project` of their sum, in every format and rounding direction.
-/
theorem sum_eq_project (f : Format) (mode : RoundingMode) (values : Array Datum)
    (exacts : List ℚ) (hexact : values.toList.map Datum.toRat? = exacts.map some) :
    ∃ preferred negativeZero,
      sum f mode values = project f mode exacts.sum preferred negativeZero := by
  obtain ⟨preferred, negativeZero, h, -⟩ :=
    deliver_total_of_values f mode (values.toList.map Term.ofDatum) exacts
      (by simpa [Function.comp_def, Term.value?_ofDatum] using hexact)
  exact ⟨preferred, negativeZero, h⟩

/--
**The decimal `sumAbs` rounds the exact sum of the magnitudes once**, for finite operands with
the exact values `exacts`.
-/
theorem sumAbs_eq_project (f : Format) (mode : RoundingMode) (values : Array Datum)
    (exacts : List ℚ) (hexact : values.toList.map Datum.toRat? = exacts.map some) :
    ∃ preferred negativeZero,
      sumAbs f mode values = project f mode (exacts.map abs).sum preferred negativeZero := by
  have hterms : (values.toList.map fun x => (Term.ofDatum x).abs).map Term.value? =
      (exacts.map abs).map some := by
    generalize values.toList = data at hexact
    induction data generalizing exacts with
    | nil => cases exacts <;> simp_all
    | cons x data ih =>
        cases exacts with
        | nil => simp at hexact
        | cons exact rest =>
            simp only [List.map_cons, List.cons.injEq] at hexact ⊢
            exact ⟨Term.value?_abs (by rw [Term.value?_ofDatum]; exact hexact.1), ih rest hexact.2⟩
  obtain ⟨preferred, negativeZero, -, h⟩ := deliver_total_of_values f mode _ _ hterms
  exact ⟨preferred, negativeZero, h⟩

/--
**The decimal `sumSquare` rounds the exact sum of the squares once**, for finite operands with
the exact values `exacts`.
-/
theorem sumSquare_eq_project (f : Format) (mode : RoundingMode) (values : Array Datum)
    (exacts : List ℚ) (hexact : values.toList.map Datum.toRat? = exacts.map some) :
    ∃ preferred negativeZero,
      sumSquare f mode values =
        project f mode (exacts.map fun exact => exact * exact).sum preferred negativeZero := by
  have hterms : (values.toList.map fun x => (Term.ofDatum x).mul (Term.ofDatum x)).map
      Term.value? = (exacts.map fun exact => exact * exact).map some := by
    generalize values.toList = data at hexact
    induction data generalizing exacts with
    | nil => cases exacts <;> simp_all
    | cons x data ih =>
        cases exacts with
        | nil => simp at hexact
        | cons exact rest =>
            simp only [List.map_cons, List.cons.injEq] at hexact ⊢
            have hx : (Term.ofDatum x).value? = some exact := by
              rw [Term.value?_ofDatum]; exact hexact.1
            exact ⟨Term.value?_mul hx hx, ih rest hexact.2⟩
  obtain ⟨preferred, negativeZero, -, h⟩ := deliver_total_of_values f mode _ _ hterms
  exact ⟨preferred, negativeZero, h⟩

/--
**The decimal `dot` rounds the exact sum of the products once**, for finite operands with the
exact values `xs` and `ys` in arrays of one length.
-/
theorem dot_eq_project (f : Format) (mode : RoundingMode) (left right : Array Datum)
    (xs ys : List ℚ) (hleft : left.toList.map Datum.toRat? = xs.map some)
    (hright : right.toList.map Datum.toRat? = ys.map some) (hsize : left.size = right.size) :
    ∃ preferred negativeZero,
      dot f mode left right =
        .ok (project f mode (List.zipWith (· * ·) xs ys).sum preferred negativeZero) := by
  have hterms := map_value?_zipWith Term.mul (· * ·) Term.value?_mul left.toList right.toList
    xs ys hleft hright
  obtain ⟨preferred, negativeZero, h, -⟩ := deliver_total_of_values f mode _ _ hterms
  exact ⟨preferred, negativeZero, by simp only [dot, hsize, ↓reduceIte, h]⟩

/--
To nearest, the decimal `sum` of finite operands is within half a unit of the rounding quantum
of the exact sum, when no overflow is signaled.
-/
theorem sum_error_le_half (f : Format) (mode : RoundingMode)
    (hm : mode = .nearest ∨ mode = .nearestAway) (values : Array Datum) (exacts : List ℚ)
    (hexact : values.toList.map Datum.toRat? = exacts.map some)
    (hfinite : (sum f mode values).status.overflow = false) :
    ∃ value, (sum f mode values).value.toRat? = some value ∧
      |value - exacts.sum| ≤ (10 : ℚ) ^ roundingQuantum f |exacts.sum| / 2 := by
  obtain ⟨preferred, negativeZero, h⟩ := sum_eq_project f mode values exacts hexact
  rw [h] at hfinite ⊢
  exact project_error_le_half f mode hm _ _ _ hfinite

/--
In every rounding direction, the decimal `sum` of finite operands raises `inexact` exactly when
its result is not the exact sum.
-/
theorem sum_inexact_iff (f : Format) (mode : RoundingMode) (values : Array Datum)
    (exacts : List ℚ) (hexact : values.toList.map Datum.toRat? = exacts.map some) (value : ℚ)
    (hvalue : (sum f mode values).value.toRat? = some value) :
    (sum f mode values).status.inexact = true ↔ value ≠ exacts.sum := by
  obtain ⟨preferred, negativeZero, h⟩ := sum_eq_project f mode values exacts hexact
  rw [h] at hvalue ⊢
  exact project_inexact_iff f mode _ _ _ _ hvalue

end Arithmetic
end FloatLib.Floats.Formats.DecimalInterchange
