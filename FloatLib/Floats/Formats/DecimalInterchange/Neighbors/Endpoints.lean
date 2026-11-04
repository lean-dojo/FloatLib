/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Neighbors.Adjacency

/-!
# Infinite endpoints of decimal adjacency

When the neighbor of a finite datum is infinite, the justification is a bound on every finite
datum in the format. Going the other way, inward from infinity, gives the extreme finite value,
and no valid finite datum lies beyond it. At the infinities, `nextUp` and `nextDown` raise no
flags.
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
    simp only [nextUp, ite_eq_right hc, hp] at hout
    cases s
    · obtain ⟨rfl, rfl⟩ := neighborAbove_infinity f a b ha hbmax hout
      simpa [Datum.finiteValue] using he.symm
    · obtain ⟨d, r, hv, _, _, _⟩ := neighborBelow_spec f a b ha hapos hbmin hbmax hfull
      simp [hv, Datum.negate] at hout

/-- Every valid finite datum is no larger in magnitude than the greatest finite value. -/
private theorem abs_le_max_of_valid (f : Format) {y : Datum} {v : ℚ} (hy : y.Valid f)
    (hv : y.toRat? = some v) :
    |v| ≤ ((f.coefficientBound - 1 : Nat) : ℚ) * (10 : ℚ) ^ f.maxQuantum := by
  obtain ⟨s, c, q, rfl, rfl⟩ := Datum.toRat?_eq_some_iff.mp hv
  have hx := (Datum.valid_quantum_iff ..).mp hy
  have hn : 0 ≤ (c : ℚ) * (10 : ℚ) ^ q :=
    mul_nonneg (Nat.cast_nonneg _) (zpow_pos (by norm_num) _).le
  cases s <;> simpa only [Datum.finiteValue, Bool.false_eq_true, ↓reduceIte, neg_mul, one_mul,
    abs_neg, abs_of_nonneg hn] using neighbor_le_max f c q hx.1 hx.2.2

/-- There is no larger finite datum when `nextUp` reaches positive infinity. -/
theorem nextUp_infinite_bound (f : Format) (x : Datum) (hx : x.Valid f)
    (a : ℚ) (ha : x.toRat? = some a)
    (hout : (nextUp f x).value = .infinity false)
    (y : Datum) (v : ℚ) (hy : y.Valid f) (hv : y.toRat? = some v) : v ≤ a := by
  obtain ⟨s, c, q, rfl, rfl⟩ := Datum.toRat?_eq_some_iff.mp ha
  rw [nextUp_infinity_value f s c q hx hout]
  exact (abs_le.mp (abs_le_max_of_valid f hy hv)).2

/-- There is no smaller finite datum when `nextDown` reaches negative infinity. -/
theorem nextDown_infinite_bound (f : Format) (x : Datum) (hx : x.Valid f)
    (a : ℚ) (ha : x.toRat? = some a)
    (hout : (nextDown f x).value = .infinity true)
    (y : Datum) (v : ℚ) (hy : y.Valid f) (hv : y.toRat? = some v) : a ≤ v := by
  rw [nextDown_value, Datum.negate_eq_iff_eq_negate] at hout
  have h := nextUp_infinite_bound f x.negate (by simpa using hx) (-a)
    (Datum.negate_toRat?_of_eq_some ha) hout y.negate (-v) (by simpa using hy)
    (Datum.negate_toRat?_of_eq_some hv)
  linarith

/-- `nextUp` leaves `+∞` unchanged, with no flags. -/
@[simp] theorem nextUp_positive_infinity (f : Format) :
    nextUp f (.infinity false) = { value := .infinity false } := rfl

/-- `nextUp` of `-∞` is the most negative finite datum, at the largest quantum, with no flags. -/
@[simp] theorem nextUp_negative_infinity (f : Format) :
    nextUp f (.infinity true) = { value := f.maxFinite true } := rfl

/-- `nextDown` leaves `-∞` unchanged, with no flags. -/
@[simp] theorem nextDown_negative_infinity (f : Format) :
    nextDown f (.infinity true) = { value := .infinity true } := rfl

/-- `nextDown` of `+∞` is the greatest finite datum, at the largest quantum, with no flags. -/
@[simp] theorem nextDown_positive_infinity (f : Format) :
    nextDown f (.infinity false) = { value := f.maxFinite false } := rfl

/--
Moving inward from negative infinity reaches the least finite value: no valid finite datum lies
below the result. The result is `f.maxFinite true` (`nextUp_negative_infinity`), a valid finite
datum by `Format.maxFinite_valid`, so the bound is attained.
-/
theorem nextUp_negative_infinity_le (f : Format) (b : ℚ)
    (hb : (nextUp f (.infinity true)).value.toRat? = some b)
    (y : Datum) (v : ℚ) (hy : y.Valid f) (hv : y.toRat? = some v) : b ≤ v := by
  simp only [nextUp_negative_infinity, Format.maxFinite, Datum.toRat?_eq, Option.some.injEq,
    ↓reduceIte, neg_mul, one_mul] at hb
  subst b
  exact (abs_le.mp (abs_le_max_of_valid f hy hv)).1

/--
Moving inward from positive infinity reaches the greatest finite value: no valid finite datum lies
above the result. The result is `f.maxFinite false` (`nextDown_positive_infinity`), a valid
finite datum by `Format.maxFinite_valid`, so the bound is attained.
-/
theorem nextDown_positive_infinity_ge (f : Format) (b : ℚ)
    (hb : (nextDown f (.infinity false)).value.toRat? = some b)
    (y : Datum) (v : ℚ) (hy : y.Valid f) (hv : y.toRat? = some v) : v ≤ b := by
  simp only [nextDown_positive_infinity, Format.maxFinite, Datum.toRat?_eq, Option.some.injEq,
    Bool.false_eq_true, ↓reduceIte, one_mul] at hb
  subst b
  exact (abs_le.mp (abs_le_max_of_valid f hy hv)).2

end Arithmetic
end FloatLib.Floats.Formats.DecimalInterchange
