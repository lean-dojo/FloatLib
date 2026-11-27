/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Numerics.Enclosure.Interval.ExactProof

meta import FloatLib.Numerics.Enclosure.Interval.Exact

/-!
# Exact operations on rational intervals

The operations of `Interval.Exact` on intervals worked out by hand, each endpoint theorem at
literal intervals, the bridge theorems to the partial operations with exact rational endpoints,
and the containment theorems on real members. `decide +kernel` evaluates the kernel definitions
themselves, so the checks at literals don't go through the theorems they test. The last section
checks that the operations still have compiled code.
-/

namespace FloatLibTests.Numerics.Exact

open FloatLib.Numerics FloatLib.Numerics.Interval

/-! ### Values worked out by hand -/

example : Exact.add ⟨-1, 2⟩ ⟨1 / 3, 5⟩ = ⟨-2 / 3, 7⟩ ∧ Exact.sub ⟨-1, 2⟩ ⟨1 / 3, 5⟩ = ⟨-6, 5 / 3⟩ ∧
    Exact.neg ⟨-1, 2⟩ = ⟨-2, 1⟩ := by
  decide +kernel

example : Exact.mul ⟨-1, 2⟩ ⟨-3, 1⟩ = ⟨-6, 3⟩ ∧ Exact.mul ⟨1 / 2, 3⟩ ⟨2, 4⟩ = ⟨1, 12⟩ ∧
    Exact.scaleNonneg (3 / 2) ⟨-2, 4⟩ = ⟨-3, 6⟩ := by
  decide +kernel

example : Exact.abs ⟨1, 3⟩ = ⟨1, 3⟩ ∧ Exact.abs ⟨-3, -1⟩ = ⟨1, 3⟩ ∧ Exact.abs ⟨-3, 2⟩ = ⟨0, 3⟩ := by
  decide +kernel

example : Exact.powNat ⟨-3, 2⟩ 0 = ⟨1, 1⟩ ∧ Exact.powNat ⟨-3, 2⟩ 2 = ⟨0, 9⟩ ∧
    Exact.powNat ⟨-3, 2⟩ 3 = ⟨-27, 8⟩ ∧ Exact.powNat ⟨-3, -1 / 2⟩ 4 = ⟨1 / 16, 81⟩ := by
  decide +kernel

/-- Reciprocals and quotients by intervals on either side of zero. -/
example : Exact.inv ⟨2, 4⟩ = ⟨1 / 4, 1 / 2⟩ ∧ Exact.inv ⟨-4, -2⟩ = ⟨-1 / 2, -1 / 4⟩ ∧
    Exact.div ⟨1, 3⟩ ⟨-4, -2⟩ = ⟨-3 / 2, -1 / 4⟩ ∧ Exact.div ⟨-1, 3⟩ ⟨2, 4⟩ = ⟨-1 / 2, 3 / 2⟩ := by
  decide +kernel

example : Exact.absMax ⟨-3, 1⟩ = 3 ∧ Exact.absMax ⟨-1, 2⟩ = 2 ∧
    Exact.divAbsLower ⟨-3, 1⟩ (1 / 2) = ⟨-6, 6⟩ := by
  decide +kernel

/-- Overlapping, disjoint and touching intersections. Disjoint inputs give reversed endpoints. -/
example : Exact.hull ⟨-1, 2⟩ ⟨0, 5⟩ = ⟨-1, 5⟩ ∧ Exact.intersect ⟨-1, 2⟩ ⟨0, 5⟩ = ⟨0, 2⟩ ∧
    Exact.intersect ⟨-1, 2⟩ ⟨3, 5⟩ = ⟨3, 2⟩ ∧ Exact.intersect ⟨3, 5⟩ ⟨-1, 2⟩ = ⟨3, 2⟩ ∧
    Exact.intersect ⟨-1, 2⟩ ⟨2, 5⟩ = ⟨2, 2⟩ := by
  decide +kernel

/-- A wrong product endpoint is refused. -/
example : Exact.mul ⟨-1, 2⟩ ⟨-3, 1⟩ ≠ ⟨-6, 2⟩ := by decide +kernel

/-! ### The endpoint theorems at literal intervals -/

example : (Exact.add ⟨-1, 2⟩ ⟨1 / 3, 5⟩).lo = -1 + 1 / 3 ∧
    (Exact.add ⟨-1, 2⟩ ⟨1 / 3, 5⟩).hi = 2 + 5 ∧
    (Exact.neg ⟨-1, 2⟩).lo = -2 ∧ (Exact.neg ⟨-1, 2⟩).hi = -(-1) ∧
    (Exact.sub ⟨-1, 2⟩ ⟨1 / 3, 5⟩).lo = -1 - 5 ∧ (Exact.sub ⟨-1, 2⟩ ⟨1 / 3, 5⟩).hi = 2 - 1 / 3 := by
  decide +kernel

example : (Exact.mul ⟨-1, 2⟩ ⟨-3, 1⟩).lo = min (min (-1 * -3) (-1 * 1)) (min (2 * -3) (2 * 1)) ∧
    (Exact.mul ⟨-1, 2⟩ ⟨-3, 1⟩).hi = max (max (-1 * -3) (-1 * 1)) (max (2 * -3) (2 * 1)) ∧
    (Exact.scaleNonneg (3 / 2) ⟨-2, 4⟩).lo = 3 / 2 * -2 ∧
    (Exact.scaleNonneg (3 / 2) ⟨-2, 4⟩).hi = 3 / 2 * 4 := by
  decide +kernel

example : (Exact.abs ⟨-3, 2⟩).lo = (if (0 : ℚ) ≤ -3 then -3 else if (2 : ℚ) ≤ 0 then -2 else 0) ∧
    (Exact.abs ⟨-3, 2⟩).hi = (if (0 : ℚ) ≤ -3 then 2 else if (2 : ℚ) ≤ 0 then 3 else max 3 2) ∧
    (Exact.powNat ⟨-3, 2⟩ 3).lo = (-3) ^ 3 ∧ (Exact.powNat ⟨-3, 2⟩ 3).hi = 2 ^ 3 ∧
    (Exact.powNat ⟨-3, 2⟩ 2).lo = (Exact.abs ⟨-3, 2⟩).lo ^ 2 ∧
    (Exact.powNat ⟨-3, 2⟩ 2).hi = (Exact.abs ⟨-3, 2⟩).hi ^ 2 := by
  decide +kernel

example : (Exact.inv ⟨-4, -2⟩).lo = (-2)⁻¹ ∧ (Exact.inv ⟨-4, -2⟩).hi = (-4)⁻¹ ∧
    (Exact.div ⟨1, 3⟩ ⟨-4, -2⟩).lo = min (min (1 / -2) (1 / -4)) (min (3 / -2) (3 / -4)) ∧
    (Exact.div ⟨1, 3⟩ ⟨-4, -2⟩).hi = max (max (1 / -2) (1 / -4)) (max (3 / -2) (3 / -4)) := by
  decide +kernel

example : Exact.absMax ⟨-3, 1⟩ = max |(-3 : ℚ)| |1| ∧
    (Exact.divAbsLower ⟨-3, 1⟩ (1 / 2)).lo = -(Exact.absMax ⟨-3, 1⟩ / (1 / 2)) ∧
    (Exact.divAbsLower ⟨-3, 1⟩ (1 / 2)).hi = Exact.absMax ⟨-3, 1⟩ / (1 / 2) := by
  decide +kernel

example : (Exact.hull ⟨-1, 2⟩ ⟨0, 5⟩).lo = min (-1) 0 ∧ (Exact.hull ⟨-1, 2⟩ ⟨0, 5⟩).hi = max 2 5 ∧
    (Exact.intersect ⟨-1, 2⟩ ⟨0, 5⟩).lo = max (-1) 0 ∧
    (Exact.intersect ⟨-1, 2⟩ ⟨0, 5⟩).hi = min 2 5 ∧
    (Exact.intersect ⟨-1, 2⟩ ⟨3, 5⟩).lo = 3 ∧ (Exact.intersect ⟨-1, 2⟩ ⟨3, 5⟩).hi = 2 := by
  decide +kernel

/-- `absBounds` and `powBounds` at `ℚ` against `abs` and `powNat`. -/
example : absBounds (⟨-3, 2⟩ : Interval ℚ) = Exact.abs ⟨-3, 2⟩ ∧
    powBounds (⟨-3, 2⟩ : Interval ℚ) 4 = Exact.powNat ⟨-3, 2⟩ 4 ∧
    powBounds (⟨-3, 2⟩ : Interval ℚ) 5 = Exact.powNat ⟨-3, 2⟩ 5 := by
  decide +kernel

/-! ### The partial operations with exact rational endpoints -/

/-- The bridge theorems at literal intervals, decided by evaluating both sides. -/
example : add? Internal.rationalOutwardRounding ⟨-1, 2⟩ ⟨1 / 3, 5⟩ =
      some (Exact.add ⟨-1, 2⟩ ⟨1 / 3, 5⟩) ∧
    mul? Internal.rationalOutwardRounding ⟨-1, 2⟩ ⟨-3, 1⟩ = some (Exact.mul ⟨-1, 2⟩ ⟨-3, 1⟩) ∧
    pow? Internal.rationalOutwardRounding ⟨-3, 2⟩ 4 = some (Exact.powNat ⟨-3, 2⟩ 4) ∧
    inv? Internal.rationalOutwardRounding ⟨-4, -2⟩ = some (Exact.inv ⟨-4, -2⟩) ∧
    inv? Internal.rationalOutwardRounding ⟨-1, 2⟩ = none ∧
    div? Internal.rationalOutwardRounding ⟨1, 3⟩ ⟨-4, -2⟩ = some (Exact.div ⟨1, 3⟩ ⟨-4, -2⟩) ∧
    hull? Internal.rationalOutwardRounding ⟨-1, 2⟩ ⟨0, 5⟩ = some (Exact.hull ⟨-1, 2⟩ ⟨0, 5⟩) ∧
    hull? Internal.rationalOutwardRounding ⟨2, -1⟩ ⟨0, 5⟩ = none ∧
    intersect? Internal.rationalOutwardRounding ⟨-1, 2⟩ ⟨0, 5⟩ =
      some (Exact.intersect ⟨-1, 2⟩ ⟨0, 5⟩) ∧
    intersect? Internal.rationalOutwardRounding ⟨-1, 2⟩ ⟨3, 5⟩ = none := by
  decide +kernel

example (I J : Interval ℚ) (hI : I.lo ≤ I.hi) (hJ : J.lo ≤ J.hi) :
    hull? Internal.rationalOutwardRounding I J = some (Exact.hull I J) := by
  rw [Exact.hull?_eq, ite_eq_left ⟨hI, hJ⟩]

example (I J : Interval ℚ) (h : max I.lo J.lo ≤ min I.hi J.hi) :
    intersect? Internal.rationalOutwardRounding I J = some (Exact.intersect I J) := by
  rw [Exact.intersect?_eq, ite_eq_left h]

example (I J : Interval ℚ) (h : J.hi < 0 ∨ 0 < J.lo) :
    div? Internal.rationalOutwardRounding I J = some (Exact.div I J) := by
  rw [Exact.div?_eq, ite_eq_left h]

/-- Scaling by `2` is the product with `[2, 2]` on an ordered interval. -/
example (I : Interval ℚ) (h : I.lo ≤ I.hi) : Exact.scaleNonneg 2 I = Exact.mul (point 2) I :=
  Exact.scaleNonneg_eq_mul (by decide +kernel) h

/-- The symmetric quotient bound is a quotient of intervals. -/
example (I : Interval ℚ) :
    Exact.divAbsLower I 3 = Exact.div ⟨-Exact.absMax I, Exact.absMax I⟩ (point 3) :=
  Exact.divAbsLower_eq_div (by decide +kernel)

example (I J : Interval ℚ) (x : ℝ) (h : (Exact.intersect I J).ContainsReal some x) :
    I.ContainsReal some x ∧ J.ContainsReal some x :=
  (Exact.containsReal_intersect_iff I J x).1 h

/-! ### Containment of real members -/

/-- Rational bounds on a real number, as containment in a rational interval. -/
theorem containsReal_of_le {a b : ℚ} {x : ℝ} (ha : (a : ℝ) ≤ x) (hb : x ≤ b) :
    (⟨a, b⟩ : Interval ℚ).ContainsReal some x :=
  (containsReal_some_iff _ _).2 ⟨ha, hb⟩

/-- The real bounds of a containment, read off the interval that the kernel computed. -/
theorem bounds_of_eq {I : Interval ℚ} {a b : ℚ} {x : ℝ} (hx : I.ContainsReal some x)
    (h : I = ⟨a, b⟩) : (a : ℝ) ≤ x ∧ x ≤ b := by
  subst h
  exact (containsReal_some_iff _ _).1 hx

example (x y : ℝ) (hx : -1 ≤ x ∧ x ≤ 2) (hy : -3 ≤ y ∧ y ≤ 1) : -6 ≤ x * y ∧ x * y ≤ 3 := by
  have h := bounds_of_eq (Exact.containsReal_mul
    (containsReal_of_le (a := -1) (b := 2) (by exact_mod_cast hx.1) (by exact_mod_cast hx.2))
    (containsReal_of_le (a := -3) (b := 1) (by exact_mod_cast hy.1) (by exact_mod_cast hy.2)))
    (show Exact.mul ⟨-1, 2⟩ ⟨-3, 1⟩ = ⟨-6, 3⟩ by decide +kernel)
  push_cast at h
  exact h

/-- For `x ∈ [-3, 1]` and `|y| ≥ 1 / 2`, `x / y ∈ [-6, 6]`, whatever the sign of `y`. -/
example (x y : ℝ) (hx : -3 ≤ x ∧ x ≤ 1) (hy : 1 / 2 ≤ |y|) : -6 ≤ x / y ∧ x / y ≤ 6 := by
  have h := bounds_of_eq (Exact.containsReal_divAbsLower (δ := 1 / 2) (by decide +kernel)
    (containsReal_of_le (a := -3) (b := 1) (by exact_mod_cast hx.1) (by exact_mod_cast hx.2))
    (by push_cast; exact hy))
    (show Exact.divAbsLower ⟨-3, 1⟩ (1 / 2) = ⟨-6, 6⟩ by decide +kernel)
  push_cast at h
  exact h

example (x : ℝ) (hx : 2 ≤ x ∧ x ≤ 4) : 1 / 4 ≤ x⁻¹ ∧ x⁻¹ ≤ 1 / 2 := by
  have h := bounds_of_eq (Exact.containsReal_inv (I := ⟨2, 4⟩) (Or.inr (by decide +kernel))
    (containsReal_of_le (by exact_mod_cast hx.1) (by exact_mod_cast hx.2)))
    (show Exact.inv ⟨2, 4⟩ = ⟨1 / 4, 1 / 2⟩ by decide +kernel)
  push_cast at h
  exact h

example (x y : ℝ) (hx : -1 ≤ x ∧ x ≤ 3) (hy : 2 ≤ y ∧ y ≤ 4) : -1 / 2 ≤ x / y ∧ x / y ≤ 3 / 2 := by
  have h := bounds_of_eq (Exact.containsReal_div (I := ⟨-1, 3⟩) (J := ⟨2, 4⟩)
    (Or.inr (by decide +kernel))
    (containsReal_of_le (by exact_mod_cast hx.1) (by exact_mod_cast hx.2))
    (containsReal_of_le (by exact_mod_cast hy.1) (by exact_mod_cast hy.2)))
    (show Exact.div ⟨-1, 3⟩ ⟨2, 4⟩ = ⟨-1 / 2, 3 / 2⟩ by decide +kernel)
  push_cast at h
  exact h

/-- An even power of an interval that crosses zero starts at zero. -/
example (x : ℝ) (hx : -3 ≤ x ∧ x ≤ 2) : 0 ≤ x ^ 2 ∧ x ^ 2 ≤ 9 ∧ 0 ≤ |x| ∧ |x| ≤ 3 := by
  have hI := containsReal_of_le (a := -3) (b := 2) (by exact_mod_cast hx.1) (by exact_mod_cast hx.2)
  have hpow := bounds_of_eq (Exact.containsReal_powNat 2 hI)
    (show Exact.powNat ⟨-3, 2⟩ 2 = ⟨0, 9⟩ by decide +kernel)
  have habs := bounds_of_eq (Exact.containsReal_abs hI)
    (show Exact.abs ⟨-3, 2⟩ = ⟨0, 3⟩ by decide +kernel)
  push_cast at hpow habs
  exact ⟨hpow.1, hpow.2, habs.1, habs.2⟩

example (x y : ℝ) (hx : -1 ≤ x ∧ x ≤ 2) (hy : 1 ≤ y ∧ y ≤ 5) :
    -6 ≤ x - y ∧ x - y ≤ 1 ∧ 0 ≤ x + y ∧ x + y ≤ 7 ∧ -2 ≤ -x ∧ -x ≤ 1 ∧
      -3 / 2 ≤ 3 / 2 * x ∧ 3 / 2 * x ≤ 3 := by
  have hI := containsReal_of_le (a := -1) (b := 2) (by exact_mod_cast hx.1) (by exact_mod_cast hx.2)
  have hJ := containsReal_of_le (a := 1) (b := 5) (by exact_mod_cast hy.1) (by exact_mod_cast hy.2)
  have hsub := bounds_of_eq (Exact.containsReal_sub hI hJ)
    (show Exact.sub ⟨-1, 2⟩ ⟨1, 5⟩ = ⟨-6, 1⟩ by decide +kernel)
  have hadd := bounds_of_eq (Exact.containsReal_add hI hJ)
    (show Exact.add ⟨-1, 2⟩ ⟨1, 5⟩ = ⟨0, 7⟩ by decide +kernel)
  have hneg := bounds_of_eq (Exact.containsReal_neg hI)
    (show Exact.neg ⟨-1, 2⟩ = ⟨-2, 1⟩ by decide +kernel)
  have hscale := bounds_of_eq (Exact.containsReal_scaleNonneg (q := 3 / 2) (by decide +kernel) hI)
    (show Exact.scaleNonneg (3 / 2) ⟨-1, 2⟩ = ⟨-3 / 2, 3⟩ by decide +kernel)
  push_cast at hsub hadd hneg hscale
  exact ⟨hsub.1, hsub.2, hadd.1, hadd.2, hneg.1, hneg.2, hscale.1, hscale.2⟩

/-- A common member lies in the intersection, and a member of either interval in the hull. -/
example (x : ℝ) (h₁ : 0 ≤ x ∧ x ≤ 3) (h₂ : 1 ≤ x ∧ x ≤ 5) :
    1 ≤ x ∧ x ≤ 3 ∧ 0 ≤ x ∧ x ≤ 6 := by
  have hI := containsReal_of_le (a := 0) (b := 3) (by exact_mod_cast h₁.1) (by exact_mod_cast h₁.2)
  have hJ := containsReal_of_le (a := 1) (b := 5) (by exact_mod_cast h₂.1) (by exact_mod_cast h₂.2)
  have hmeet := bounds_of_eq (Exact.containsReal_intersect hI hJ)
    (show Exact.intersect ⟨0, 3⟩ ⟨1, 5⟩ = ⟨1, 3⟩ by decide +kernel)
  have hhull := bounds_of_eq (Exact.containsReal_hull (J := ⟨4, 6⟩) (Or.inl hI))
    (show Exact.hull ⟨0, 3⟩ ⟨4, 6⟩ = ⟨0, 6⟩ by decide +kernel)
  push_cast at hmeet hhull
  exact ⟨hmeet.1, hmeet.2, hhull.1, hhull.2⟩

/-- The endpoint theorems turn containment into inequalities on arbitrary intervals. -/
example (I J : Interval ℚ) (x y : ℝ) (hx : I.ContainsReal some x) (hy : J.ContainsReal some y) :
    ((min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)) : ℚ) : ℝ) ≤ x * y ∧
      |x| ≤ Exact.absMax I := by
  have h := Exact.containsReal_mul hx hy
  rw [containsReal_some_iff, Exact.mul_lo] at h
  exact ⟨h.1, Exact.abs_le_absMax hx⟩

/-! ### Compiled code -/

#guard Exact.mul ⟨-1, 2⟩ ⟨-3, 1⟩ == ⟨-6, 3⟩
#guard Exact.powNat ⟨-3, 2⟩ 3 == ⟨-27, 8⟩ && Exact.abs ⟨-3, 2⟩ == ⟨0, 3⟩
#guard Exact.div ⟨1, 3⟩ ⟨-4, -2⟩ == ⟨-3 / 2, -1 / 4⟩
#guard Exact.intersect ⟨-1, 2⟩ ⟨3, 5⟩ == ⟨3, 2⟩ && Exact.hull ⟨-1, 2⟩ ⟨3, 5⟩ == ⟨-1, 5⟩
#guard Exact.divAbsLower ⟨-3, 1⟩ (1 / 2) == ⟨-6, 6⟩

end FloatLibTests.Numerics.Exact
