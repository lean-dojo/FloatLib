/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Rational.Product
public import FloatLib.Numerics.Enclosure.Rational.AffineConvergence
public import FloatLib.Numerics.Enclosure.Comparison.Proof
public import FloatLib.Numerics.Enclosure.Interval.Bounds
public import Mathlib.Topology.Algebra.Order.Field

/-!
# Convergent sequences of rational enclosures

`Converges intervals x` says that every interval of the sequence contains the real `x` and that
both endpoint sequences tend to `x`. The relation is closed under the interval operations
(`neg`, `add`, `sub`, `scale`, `mul`), under replacing a finite prefix by sound enclosures
(`prefixed`) and under sampling at the degrees `2 ^ n` (`comp_two_pow`). The product and the
quotient of two intervals contain the product and the quotient of the enclosed reals
(`contains_mul`, `contains_divPositive`).

A convergent sequence is eventually clear of every rational different from its limit
(`exists_separates`), which is the termination argument of `Comparison.compare`. So the sign of
any expression built from convergent enclosures is decided exactly as soon as the expression is
known not to vanish.
-/

public section

namespace FloatLib.Numerics.RationalInterval

open Filter
open scoped Topology

/-- Every interval contains `x`, and both endpoint sequences tend to `x`. -/
structure Converges (intervals : Nat → RationalInterval) (x : ℝ) : Prop where
  /-- Every interval contains the limit. -/
  contains : ∀ n, (intervals n).Contains x
  /-- The lower endpoints tend to the limit. -/
  lo : Tendsto (fun n => ((intervals n).lo : ℝ)) atTop (𝓝 x)
  /-- The upper endpoints tend to the limit. -/
  hi : Tendsto (fun n => ((intervals n).hi : ℝ)) atTop (𝓝 x)

/-- The product interval contains the product of every pair of enclosed reals. -/
theorem contains_mul {left right : RationalInterval} {x y : ℝ} (hx : left.Contains x)
    (hy : right.Contains y) : (left.mul right).Contains (x * y) := by
  have h := Interval.mul_bounds_Icc (left.lo : ℝ) left.hi right.lo right.hi x y hx hy
  constructor
  · simpa [RationalInterval.mul, Interval.minOfFour] using h.1
  · simpa [RationalInterval.mul, Interval.maxOfFour] using h.2

/--
The quotient by an interval with a positive lower end contains the quotient of every pair of
enclosed reals.
-/
theorem contains_divPositive {numerator denominator : RationalInterval} {x y : ℝ}
    (hx : numerator.Contains x) (hy : denominator.Contains y) (hpos : 0 < denominator.lo) :
    (numerator.divPositive denominator).Contains (x / y) := by
  have hlo : (0 : ℝ) < denominator.lo := by exact_mod_cast hpos
  have hy0 : 0 < y := hlo.trans_le hy.1
  rw [div_eq_mul_inv]
  refine contains_mul hx ⟨?_, ?_⟩
  · push_cast
    rw [one_div]
    exact inv_anti₀ hy0 hy.2
  · push_cast
    rw [one_div]
    exact inv_anti₀ hlo hy.1

namespace Converges

variable {left right intervals : Nat → RationalInterval} {x y : ℝ}

/-- A rational point is a constant convergent sequence. -/
theorem const (q : ℚ) : Converges (fun _ => point q) (q : ℝ) :=
  ⟨fun _ => contains_point q, tendsto_const_nhds, tendsto_const_nhds⟩

/-- Negated enclosures converge to the negated limit. -/
theorem neg (h : Converges intervals x) : Converges (fun n => (intervals n).neg) (-x) :=
  ⟨fun n => contains_neg (h.contains n), tendsto_neg_lo h.hi, tendsto_neg_hi h.lo⟩

/-- Sums of enclosures converge to the sum of the limits. -/
theorem add (hx : Converges left x) (hy : Converges right y) :
    Converges (fun n => (left n).add (right n)) (x + y) :=
  ⟨fun n => contains_add (hx.contains n) (hy.contains n), tendsto_add_lo hx.lo hy.lo,
    tendsto_add_hi hx.hi hy.hi⟩

/-- Differences of enclosures converge to the difference of the limits. -/
theorem sub (hx : Converges left x) (hy : Converges right y) :
    Converges (fun n => (left n).sub (right n)) (x - y) :=
  ⟨fun n => contains_sub (hx.contains n) (hy.contains n), tendsto_sub_lo hx.lo hy.hi,
    tendsto_sub_hi hx.hi hy.lo⟩

/-- Enclosures scaled by a rational converge to the scaled limit. -/
theorem scale (h : Converges intervals x) (factor : ℚ) :
    Converges (fun n => (intervals n).scale factor) ((factor : ℝ) * x) :=
  ⟨fun n => contains_scale (h.contains n) factor, tendsto_scale_lo h.lo h.hi factor,
    tendsto_scale_hi h.lo h.hi factor⟩

/-- Products of enclosures converge to the product of the limits. -/
theorem mul (hx : Converges left x) (hy : Converges right y) :
    Converges (fun n => (left n).mul (right n)) (x * y) := by
  refine ⟨fun n => contains_mul (hx.contains n) (hy.contains n), ?_, ?_⟩
  · have h := ((hx.lo.mul hy.lo).min (hx.lo.mul hy.hi)).min
      ((hx.hi.mul hy.lo).min (hx.hi.mul hy.hi))
    simpa [RationalInterval.mul] using h
  · have h := ((hx.lo.mul hy.lo).max (hx.lo.mul hy.hi)).max
      ((hx.hi.mul hy.lo).max (hx.hi.mul hy.hi))
    simpa [RationalInterval.mul] using h

/-- Sound enclosures in place of a finite prefix leave the sequence convergent. -/
theorem prefixed (h : Converges intervals x) {first : Nat → RationalInterval} {count : Nat}
    (hfirst : ∀ n, n < count → (first n).Contains x) :
    Converges (RationalInterval.prefixed first count intervals) x := by
  have hev : ∀ᶠ n in atTop, RationalInterval.prefixed first count intervals n = intervals n :=
    eventually_atTop.mpr ⟨count, fun n hn => by simp [RationalInterval.prefixed, not_lt.mpr hn]⟩
  refine ⟨fun n => ?_, ?_, ?_⟩
  · unfold RationalInterval.prefixed
    split
    · exact hfirst n ‹_›
    · exact h.contains n
  · exact h.lo.congr' (hev.mono fun n hn => by simp only [hn])
  · exact h.hi.congr' (hev.mono fun n hn => by simp only [hn])

/-- A convergent sequence sampled at the degrees `2 ^ n` converges. -/
theorem comp_two_pow (h : Converges intervals x) : Converges (fun n => intervals (2 ^ n)) x :=
  have htwo : Tendsto (fun n : Nat => 2 ^ n) atTop atTop :=
    StrictMono.tendsto_atTop fun _ _ hlt => Nat.pow_lt_pow_right (by decide) hlt
  ⟨fun n => h.contains _, h.lo.comp htwo, h.hi.comp htwo⟩

/-- A convergent sequence is eventually clear of every rational other than its limit. -/
theorem exists_separates (h : Converges intervals x) {boundary : ℚ}
    (hne : x ≠ (boundary : ℝ)) : ∃ n, Enclosure.Comparison.Separates (intervals n) boundary :=
  Enclosure.Comparison.exists_separating boundary hne h.lo h.hi

/-- The comparison of a convergent sequence with a rational is the order of its limit. -/
theorem compare_eq (h : Converges intervals x) {boundary : ℚ}
    (terminates : ∃ n, Enclosure.Comparison.Separates (intervals n) boundary) :
    Enclosure.Comparison.compare intervals boundary terminates = cmp x (boundary : ℝ) :=
  Enclosure.Comparison.compare_eq_real intervals boundary terminates x h.contains

end Converges

end FloatLib.Numerics.RationalInterval
