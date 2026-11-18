/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Order.Bisection.Runtime
public import Mathlib.Data.Bool.Basic
public import Mathlib.Order.Basic

/-!
# Range, cutoff and bracket theorems for bounded bisection

The range and predicate-inclusion laws require no monotonicity. Exact comparisons
and an initial bracket suffice to find adjacent values in any linear order.
-/

@[expose] public section

namespace FloatLib.Numerics

/--
A bisection step on a nontrivial interval tests the strictly interior midpoint and recurses on
the half that it selects.
-/
private theorem bisect_succ_of_lt
    (accept : Nat → Bool) (fuel lower upper : Nat)
    (hnontrivial : lower + 1 < upper) :
    lower < (lower + upper) / 2 ∧ (lower + upper) / 2 < upper ∧
      bisect accept (fuel + 1) lower upper =
        if accept ((lower + upper) / 2) then
          bisect accept fuel ((lower + upper) / 2) upper
        else
          bisect accept fuel lower ((lower + upper) / 2) :=
  ⟨by omega, by omega, by rw [bisect, ite_eq_left hnontrivial]⟩

/--
Bounded bisection never reaches its exclusive upper endpoint.

This is a structural range fact and needs no monotonicity of `accept`. Every recursive branch
keeps a nonempty half-open interval and eventually returns one of its lower endpoints.
-/
theorem bisect_lt_upper
    (accept : Nat → Bool) (fuel lower upper : Nat)
    (hlower : lower < upper) :
    bisect accept fuel lower upper < upper := by
  induction fuel generalizing lower upper with
  | zero =>
      simpa [bisect] using hlower
  | succ fuel inductionHypothesis =>
      by_cases hnontrivial : lower + 1 < upper
      · obtain ⟨hlowerMiddle, hmiddleUpper, hstep⟩ :=
          bisect_succ_of_lt accept fuel lower upper hnontrivial
        rw [hstep]
        split
        · exact inductionHypothesis _ upper hmiddleUpper
        · exact (inductionHypothesis lower _ hlowerMiddle).trans hmiddleUpper
      · rw [bisect, ite_eq_right hnontrivial]
        exact hlower

/-- Bounded bisection never returns below its initial lower endpoint. -/
theorem le_bisect
    (accept : Nat → Bool) (fuel lower upper : Nat) :
    lower ≤ bisect accept fuel lower upper := by
  induction fuel generalizing lower upper with
  | zero =>
      rfl
  | succ fuel inductionHypothesis =>
      by_cases hnontrivial : lower + 1 < upper
      · obtain ⟨hlowerMiddle, -, hstep⟩ :=
          bisect_succ_of_lt accept fuel lower upper hnontrivial
        rw [hstep]
        split
        · exact hlowerMiddle.le.trans (inductionHypothesis _ upper)
        · exact inductionHypothesis lower _
      · rw [bisect, ite_eq_right hnontrivial]

/--
Bounded bisection is monotone under pointwise inclusion of accepted candidates.

The theorem is independent of monotonicity in the candidate index. It only uses that changing a
rejected midpoint to accepted moves the active interval upward.
-/
theorem bisect_mono_accept
    (leftAccept rightAccept : Nat → Bool)
    (fuel lower upper : Nat)
    (haccept :
      ∀ code, leftAccept code = true → rightAccept code = true) :
    bisect leftAccept fuel lower upper ≤
      bisect rightAccept fuel lower upper := by
  induction fuel generalizing lower upper with
  | zero =>
      exact le_rfl
  | succ fuel inductionHypothesis =>
      by_cases hnontrivial : lower + 1 < upper
      · obtain ⟨hlowerMiddle, -, hleftStep⟩ :=
          bisect_succ_of_lt leftAccept fuel lower upper hnontrivial
        obtain ⟨-, -, hrightStep⟩ :=
          bisect_succ_of_lt rightAccept fuel lower upper hnontrivial
        rw [hleftStep, hrightStep]
        by_cases hleft : leftAccept ((lower + upper) / 2)
        · simp only [hleft, haccept _ hleft, ite_true]
          exact inductionHypothesis _ upper
        · simp only [Bool.eq_false_of_not_eq_true hleft, Bool.false_eq_true, ite_false]
          by_cases hright : rightAccept ((lower + upper) / 2)
          · simp only [hright, ite_true]
            exact
              (bisect_lt_upper
                leftAccept fuel lower _ hlowerMiddle).le.trans
                (le_bisect
                  rightAccept fuel _ upper)
          · simp only [Bool.eq_false_of_not_eq_true hright, Bool.false_eq_true, ite_false]
            exact inductionHypothesis lower _
      · rw [bisect, bisect,
          ite_eq_right hnontrivial, ite_eq_right hnontrivial]

/--
Bounded bisection depends only on predicate values strictly inside its current interval.

This lets semantic monotonicity replace the exact-rational comparison predicate with a plain code
prefix without making any claim about out-of-range natural arguments.
-/
theorem bisect_congr
    (leftAccept rightAccept : Nat → Bool)
    (fuel lower upper : Nat)
    (hagrees : ∀ code, lower < code → code < upper →
      leftAccept code = rightAccept code) :
    bisect leftAccept fuel lower upper =
      bisect rightAccept fuel lower upper := by
  induction fuel generalizing lower upper with
  | zero =>
      rfl
  | succ fuel inductionHypothesis =>
      by_cases hnontrivial : lower + 1 < upper
      · obtain ⟨hlowerMiddle, hmiddleUpper, hleftStep⟩ :=
          bisect_succ_of_lt leftAccept fuel lower upper hnontrivial
        obtain ⟨-, -, hrightStep⟩ :=
          bisect_succ_of_lt rightAccept fuel lower upper hnontrivial
        rw [hleftStep, hrightStep, hagrees _ hlowerMiddle hmiddleUpper]
        by_cases haccept : rightAccept ((lower + upper) / 2)
        · simp only [haccept, ite_true]
          exact inductionHypothesis _ upper fun code hmiddleCode hcodeUpper =>
            hagrees code (hlowerMiddle.trans hmiddleCode) hcodeUpper
        · simp only [Bool.eq_false_of_not_eq_true haccept, Bool.false_eq_true, ite_false]
          exact inductionHypothesis lower _ fun code hlowerCode hcodeMiddle =>
            hagrees code hlowerCode (hcodeMiddle.trans hmiddleUpper)
      · rw [bisect, bisect,
          ite_eq_right hnontrivial, ite_eq_right hnontrivial]

/--
Bounded bisection returns the cutoff when the accepted codes form a prefix of the naturals.

The interval invariant is `lower ≤ cutoff < upper`. The span bound says the remaining interval
holds at most `2 ^ fuel` unit steps, so every nontrivial midpoint leaves at most half the old span.
Nothing here depends on posit decoding, and every exact comparison domain that drives the same
search reuses this theorem.
-/
theorem bisect_eq_cutoff
    (fuel lower upper cutoff : Nat)
    (hlower : lower ≤ cutoff)
    (hupper : cutoff < upper)
    (hspan : upper - lower ≤ 2 ^ fuel) :
    bisect
        (fun code => decide (code ≤ cutoff)) fuel lower upper =
      cutoff := by
  induction fuel generalizing lower upper with
  | zero =>
      simp only [bisect]
      simp only [Nat.pow_zero] at hspan
      omega
  | succ fuel inductionHypothesis =>
      by_cases hnontrivial : lower + 1 < upper
      · obtain ⟨hlowerMiddle, hmiddleUpper, hstep⟩ :=
          bisect_succ_of_lt (fun code => decide (code ≤ cutoff))
            fuel lower upper hnontrivial
        rw [hstep]
        rw [Nat.pow_succ] at hspan
        by_cases hmiddle : (lower + upper) / 2 ≤ cutoff
        · rw [ite_eq_left (decide_eq_true hmiddle)]
          exact inductionHypothesis _ upper hmiddle hupper (by omega)
        · rw [ite_eq_right (fun h => hmiddle (of_decide_eq_true h))]
          exact inductionHypothesis lower _ hlower (by omega) (by omega)
      · rw [bisect, ite_eq_right hnontrivial]
        omega

/--
A sufficiently deep bounded search ends at adjacent candidates enclosing the target.
Only exact comparison and an initial bracket are needed. The proof follows both search branches.
-/
theorem bisect_bracket {α : Type*} [LinearOrder α]
    (accept : Nat → Bool) (valueAt : Nat → α) (target : α)
    (haccept : ∀ index, accept index = true ↔ valueAt index ≤ target)
    (fuel lower upper : Nat) (horder : lower < upper)
    (hspan : upper - lower ≤ 2 ^ fuel)
    (hlower : valueAt lower ≤ target) (hupper : target < valueAt upper) :
    valueAt (bisect accept fuel lower upper) ≤ target ∧
      target < valueAt (bisect accept fuel lower upper + 1) := by
  induction fuel generalizing lower upper with
  | zero =>
    have hupperEq : upper = lower + 1 := by
      simp only [Nat.pow_zero] at hspan
      omega
    simpa [bisect, hupperEq] using And.intro hlower hupper
  | succ fuel ih =>
    rw [bisect]
    split
    · rename_i hnontrivial
      let middle := (lower + upper) / 2
      have hlo : lower < middle := by dsimp [middle]; omega
      have hhi : middle < upper := by dsimp [middle]; omega
      have hleft : middle - lower ≤ 2 ^ fuel := by
        dsimp [middle]
        rw [Nat.pow_succ] at hspan
        omega
      have hright : upper - middle ≤ 2 ^ fuel := by
        dsimp [middle]
        rw [Nat.pow_succ] at hspan
        omega
      dsimp only
      split
      · rename_i hmid
        exact ih middle upper hhi hright ((haccept middle).mp hmid) hupper
      · rename_i hmid
        exact ih lower middle hlo hleft hlower
          (lt_of_not_ge (fun h => hmid ((haccept middle).mpr h)))
    · have hupperEq : upper = lower + 1 := by omega
      simpa [hupperEq] using And.intro hlower hupper


/-- A downward-closed Boolean test has a maximum in any sufficiently short initial bracket. -/
theorem bisect_spec (below : Nat → Bool)
    (hdown : ∀ i j, i ≤ j → below j = true → below i = true)
    (fuel lower upper : Nat) (horder : lower < upper)
    (hspan : upper - lower ≤ 2 ^ fuel)
    (hlower : below lower = true) (hupper : ∀ j, upper ≤ j → below j = false) :
    below (bisect below fuel lower upper) = true ∧
      ∀ j, bisect below fuel lower upper < j → below j = false := by
  have hbracket := bisect_bracket below (fun i => if below i then (0 : Nat) else 1) 0
    (fun i => by cases below i <;> decide)
    fuel lower upper horder hspan (by simp only [hlower, ite_true, le_refl])
    (by simp only [hupper upper le_rfl, Bool.false_eq_true, ite_false, Nat.zero_lt_succ])
  have hlo : below (bisect below fuel lower upper) = true := by
    cases h : below (bisect below fuel lower upper)
    · simp only [h, Bool.false_eq_true, ite_false] at hbracket
      omega
    · rfl
  have hnext : below (bisect below fuel lower upper + 1) = false := by
    cases h : below (bisect below fuel lower upper + 1)
    · rfl
    · simp only [h, ite_true, lt_self_iff_false, and_false] at hbracket
  refine ⟨hlo, fun j hj => ?_⟩
  cases h : below j
  · rfl
  · have := hdown _ j hj h
    rw [hnext] at this
    cases this

end FloatLib.Numerics
