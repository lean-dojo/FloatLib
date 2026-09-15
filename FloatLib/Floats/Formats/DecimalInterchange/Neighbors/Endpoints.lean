/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Neighbors.Adjacency
import Mathlib.Tactic.Linarith

/-!
# Infinite endpoints of decimal adjacency

An infinite neighbor of a finite datum is justified by a bound on every finite
datum in the format. Moving inward from infinity selects the extreme finite
value. The status theorem remains unchanged at each endpoint.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange
namespace Arithmetic

/-- A finite input can have positive infinity as successor only at the finite maximum. -/
theorem nextUp_infinity_value (f : Format) (s : Bool) (c : Nat) (q : Int)
    (hx : (Datum.finite s c q).Valid f)
    (hout : (nextUp f (.finite s c q)).value = .infinity false) :
    Datum.finiteValue s c q =
      ((f.coefficientBound - 1 : Nat) : ℚ) * (10 : ℚ) ^ f.maxQuantum := by
  by_cases hc : c = 0
  · simp [nextUp, hc] at hout
  · obtain ⟨a, b, hp, ha, hapos, hbmin, hbmax, hfull, he⟩ :=
      neighbor_normalize f s c q hx hc
    simp only [nextUp, if_neg hc, hp] at hout
    cases s
    · obtain ⟨rfl, rfl⟩ := neighborAbove_infinity f a b ha hbmax hout
      simpa [Datum.finiteValue] using he.symm
    · obtain ⟨d, r, hv, _, _, _⟩ := neighborBelow_spec f a b ha hapos hbmin hbmax hfull
      simp [hv, Datum.negate] at hout

/-- There is no larger finite datum when `nextUp` reaches positive infinity. -/
theorem nextUp_infinite_bound (f : Format) (x : Datum) (hx : x.Valid f)
    (a : ℚ) (ha : x.toRat? = some a)
    (hout : (nextUp f x).value = .infinity false)
    (y : Datum) (v : ℚ) (hy : y.Valid f) (hv : y.toRat? = some v) : v ≤ a := by
  cases x <;> cases y <;>
    simp only [Datum.toRat?_eq, Option.some.injEq, reduceCtorEq] at ha hv
  subst a
  subst v
  rename_i s c q t d r
  have he := nextUp_infinity_value f s c q hx hout
  change Datum.finiteValue t d r ≤ Datum.finiteValue s c q
  rw [he]
  have hy' := (Datum.valid_quantum_iff ..).mp hy
  have hmax := neighbor_le_max f d r hy'.1 hy'.2.2
  have hn : 0 ≤ (d : ℚ) * (10 : ℚ) ^ r :=
    mul_nonneg (Nat.cast_nonneg _) (zpow_pos (by norm_num) _).le
  cases t <;> simp only [Datum.finiteValue, Bool.false_eq_true, ↓reduceIte,
    neg_mul, one_mul] <;> linarith

/-- There is no smaller finite datum when `nextDown` reaches negative infinity. -/
theorem nextDown_infinite_bound (f : Format) (x : Datum) (hx : x.Valid f)
    (a : ℚ) (ha : x.toRat? = some a)
    (hout : (nextDown f x).value = .infinity true)
    (y : Datum) (v : ℚ) (hy : y.Valid f) (hv : y.toRat? = some v) : a ≤ v := by
  have hn : x.negate.Valid f := by simpa [Datum.negate_eq_withSign] using hx
  have hna : x.negate.toRat? = some (-a) := by rw [Datum.negate_toRat?, ha]; rfl
  have hno : (nextUp f x.negate).value = .infinity false := by
    have h := congrArg Datum.negate hout
    change (nextUp f x.negate).value.negate.negate = (Datum.infinity true).negate at h
    rw [Datum.negate_negate] at h
    exact h
  have hyn : y.negate.Valid f := by simpa [Datum.negate_eq_withSign] using hy
  have hyv : y.negate.toRat? = some (-v) := by rw [Datum.negate_toRat?, hv]; rfl
  have h := nextUp_infinite_bound f x.negate hn (-a) hna hno y.negate (-v) hyn hyv
  linarith

@[simp] theorem nextUp_positive_infinity (f : Format) :
    nextUp f (.infinity false) = { value := .infinity false } := rfl

@[simp] theorem nextUp_negative_infinity (f : Format) :
    nextUp f (.infinity true) = { value := f.maxFinite true } := rfl

@[simp] theorem nextDown_negative_infinity (f : Format) :
    nextDown f (.infinity true) = { value := .infinity true } := rfl

@[simp] theorem nextDown_positive_infinity (f : Format) :
    nextDown f (.infinity false) = { value := f.maxFinite false } := rfl

/-- Moving inward from negative infinity returns the smallest finite value. -/
theorem nextUp_negative_infinity_le (f : Format) (s : Bool) (c : Nat) (q : Int)
    (hx : (Datum.finite s c q).Valid f) :
    -(((f.coefficientBound - 1 : Nat) : ℚ) * (10 : ℚ) ^ f.maxQuantum) ≤
      Datum.finiteValue s c q := by
  have hx' := (Datum.valid_quantum_iff ..).mp hx
  have hmax := neighbor_le_max f c q hx'.1 hx'.2.2
  have hn : 0 ≤ (c : ℚ) * (10 : ℚ) ^ q :=
    mul_nonneg (Nat.cast_nonneg _) (zpow_pos (by norm_num) _).le
  cases s <;> simp only [Datum.finiteValue, Bool.false_eq_true, ↓reduceIte,
    neg_mul, one_mul] <;> linarith

/-- Moving inward from positive infinity returns the largest finite value. -/
theorem nextDown_positive_infinity_ge (f : Format) (s : Bool) (c : Nat) (q : Int)
    (hx : (Datum.finite s c q).Valid f) :
    Datum.finiteValue s c q ≤
      ((f.coefficientBound - 1 : Nat) : ℚ) * (10 : ℚ) ^ f.maxQuantum := by
  have hx' := (Datum.valid_quantum_iff ..).mp hx
  have hmax := neighbor_le_max f c q hx'.1 hx'.2.2
  have hn : 0 ≤ (c : ℚ) * (10 : ℚ) ^ q :=
    mul_nonneg (Nat.cast_nonneg _) (zpow_pos (by norm_num) _).le
  cases s <;> simp only [Datum.finiteValue, Bool.false_eq_true, ↓reduceIte,
    neg_mul, one_mul] <;> linarith

end Arithmetic
end FloatLib.Floats.Formats.DecimalInterchange
