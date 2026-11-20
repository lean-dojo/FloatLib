/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Confocal.Sequences
public import FloatLib.Numerics.Exact.Tanh.Proof
public import FloatLib.Numerics.Enclosure.Interval.ElementaryProof
public import FloatLib.Numerics.Enclosure.Elementary.TrigonometricIrrational
public import Mathlib.Analysis.SpecialFunctions.Arcosh

/-!
# The confocal coordinates of a rational point are algebraic

`major p q` and `minor p q` are the half sum and the half difference of the distances of `(p, q)`
to the foci `(0, -1)` and `(0, 1)`. This file proves the facts that the inverse functions of a
complex argument need:

* `1 ≤ major p q`, with equality exactly on the segment between the foci, and
  `-1 ≤ minor p q ≤ 1`, with `1 ≤ minor p q` exactly on the ray above the upper focus;
* `major p q * minor p q = q` and `major p q ^ 2 + minor p q ^ 2 = p ^ 2 + q ^ 2 + 1`;
* the ladders of `Confocal.Sequences` converge;
* at rational `p` and `q` both coordinates are algebraic, so they differ from `cosh t`, `sin t`
  and `cos t` at every rational `t ≠ 0`, which are transcendental. The exact comparisons of
  `Confocal.Prepared` terminate for that reason.
-/

@[expose] public section

namespace FloatLib.Numerics.ConfocalComparison

open RationalInterval ProductComparison Filter
open scoped Topology

/-- The half sum of the distances of `(p, q)` to the foci `(0, -1)` and `(0, 1)`. -/
noncomputable def major (p q : ℝ) : ℝ :=
  (√(p ^ 2 + (q + 1) ^ 2) + √(p ^ 2 + (q - 1) ^ 2)) / 2

/-- The half difference of the distances of `(p, q)` to the foci `(0, -1)` and `(0, 1)`. -/
noncomputable def minor (p q : ℝ) : ℝ :=
  (√(p ^ 2 + (q + 1) ^ 2) - √(p ^ 2 + (q - 1) ^ 2)) / 2

section Real

variable (p q : ℝ)

private theorem sq_near : √(p ^ 2 + (q + 1) ^ 2) ^ 2 = p ^ 2 + (q + 1) ^ 2 :=
  Real.sq_sqrt (by positivity)

private theorem sq_far : √(p ^ 2 + (q - 1) ^ 2) ^ 2 = p ^ 2 + (q - 1) ^ 2 :=
  Real.sq_sqrt (by positivity)

private theorem abs_le_near : |q + 1| ≤ √(p ^ 2 + (q + 1) ^ 2) :=
  Real.abs_le_sqrt (by linarith [sq_nonneg p])

private theorem abs_le_far : |q - 1| ≤ √(p ^ 2 + (q - 1) ^ 2) :=
  Real.abs_le_sqrt (by linarith [sq_nonneg p])

private theorem near_le : √(p ^ 2 + (q + 1) ^ 2) ≤ √(p ^ 2 + (q - 1) ^ 2) + 2 :=
  Real.sqrt_le_iff.mpr ⟨by positivity, by
    linarith [sq_far p q, abs_le_far p q, le_abs_self (q - 1)]⟩

private theorem far_le : √(p ^ 2 + (q - 1) ^ 2) ≤ √(p ^ 2 + (q + 1) ^ 2) + 2 :=
  Real.sqrt_le_iff.mpr ⟨by positivity, by
    linarith [sq_near p q, abs_le_near p q, neg_abs_le (q + 1)]⟩

/-- The half sum of the distances to two foci at distance two is at least one. -/
theorem one_le_major : 1 ≤ major p q := by
  have h₁ := abs_le_near p q
  have h₂ := abs_le_far p q
  have h₃ := le_abs_self (q + 1)
  have h₄ := neg_abs_le (q - 1)
  unfold major
  linarith

/-- The half difference of the distances is at most one. -/
theorem minor_le_one : minor p q ≤ 1 := by
  unfold minor
  linarith [near_le p q]

/-- The half difference of the distances is at least minus one. -/
theorem neg_one_le_minor : -1 ≤ minor p q := by
  unfold minor
  linarith [far_le p q]

/-- The product of the two coordinates is the coordinate along the focal axis. -/
theorem major_mul_minor : major p q * minor p q = q := by
  unfold major minor
  linear_combination (sq_near p q - sq_far p q) / 4

/-- The squares of the two coordinates add up to `p ^ 2 + q ^ 2 + 1`. -/
theorem major_sq_add_minor_sq : major p q ^ 2 + minor p q ^ 2 = p ^ 2 + q ^ 2 + 1 := by
  unfold major minor
  linear_combination (sq_near p q + sq_far p q) / 2

/-- The half sum of the distances is at most `|p| + |q| + 1`. -/
theorem major_le : major p q ≤ |p| + |q| + 1 := by
  have h₁ : √(p ^ 2 + (q + 1) ^ 2) ≤ |p| + |q| + 1 :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by
      linarith [abs_nonneg p, abs_nonneg q, sq_abs p, sq_abs q, le_abs_self q,
        mul_nonneg (abs_nonneg p) (abs_nonneg q)]⟩
  have h₂ : √(p ^ 2 + (q - 1) ^ 2) ≤ |p| + |q| + 1 :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by
      linarith [abs_nonneg p, abs_nonneg q, sq_abs p, sq_abs q, neg_abs_le q,
        mul_nonneg (abs_nonneg p) (abs_nonneg q)]⟩
  unfold major
  linarith

/-- The half difference of the distances has the sign of `q`: positive case. -/
theorem minor_pos_iff : 0 < minor p q ↔ 0 < q := by
  have hmajor : 0 < major p q := zero_lt_one.trans_le (one_le_major p q)
  have hproduct := major_mul_minor p q
  constructor
  · intro h
    have := mul_pos hmajor h
    linarith
  · intro h
    exact (mul_pos_iff_of_pos_left hmajor).mp (by linarith)

/-- The half difference is odd in its second argument. -/
theorem minor_neg : minor p (-q) = -minor p q := by
  unfold minor
  rw [show (-q + 1) ^ 2 = (q - 1) ^ 2 by ring, show (-q - 1) ^ 2 = (q + 1) ^ 2 by ring]
  ring

/-- The half difference of the distances has the sign of `q`: negative case. -/
theorem minor_neg_iff : minor p q < 0 ↔ q < 0 := by
  have hmajor : 0 < major p q := zero_lt_one.trans_le (one_le_major p q)
  have hproduct := major_mul_minor p q
  constructor
  · intro h
    have := mul_neg_of_pos_of_neg hmajor h
    linarith
  · intro h
    by_contra hnonneg
    have := mul_nonneg hmajor.le (not_lt.mp hnonneg)
    linarith

variable {p q}

/-- The half difference is not negative where its second argument is not. -/
theorem minor_nonneg (hq : 0 ≤ q) : 0 ≤ minor p q :=
  not_lt.mp fun h => not_lt.mpr hq ((minor_neg_iff p q).mp h)

/--
The inverse cosine of `m` in `[0, 1]` by the tangent of the half angle:
`arccos m = 2 arctan √((1 - m) / (1 + m))`.
-/
theorem arccos_eq_two_mul_arctan {m : ℝ} (h0 : 0 ≤ m) (h1 : m ≤ 1) :
    Real.arccos m = 2 * Real.arctan (√((1 - m) / (1 + m))) := by
  have hpi := Real.pi_pos
  have hlower := Real.arccos_nonneg m
  have hupper : Real.arccos m ≤ Real.pi / 2 := Real.arccos_le_pi_div_two.mpr h0
  have hcos : 0 < Real.cos (Real.arccos m / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hm : m = 2 * Real.cos (Real.arccos m / 2) ^ 2 - 1 := by
    rw [← Real.cos_two_mul, show 2 * (Real.arccos m / 2) = Real.arccos m by ring,
      Real.cos_arccos (by linarith) h1]
  have hpyth := Real.sin_sq_add_cos_sq (Real.arccos m / 2)
  have hsq : (1 - m) / (1 + m) = Real.tan (Real.arccos m / 2) ^ 2 := by
    rw [Real.tan_eq_sin_div_cos, div_pow, div_eq_div_iff (by linarith) (by positivity)]
    nlinarith
  rw [hsq, Real.sqrt_sq (Real.tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith) (by linarith)),
    Real.arctan_tan (by linarith) (by linarith)]
  ring

/-- On the segment between the foci the half sum of the distances is one. -/
theorem major_eq_one (hp : p = 0) (hq : |q| ≤ 1) : major p q = 1 := by
  obtain ⟨hlower, hupper⟩ := abs_le.mp hq
  subst hp
  unfold major
  rw [zero_pow two_ne_zero, zero_add, zero_add, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
  ring

/-- Off the segment between the foci the half sum of the distances exceeds one. -/
theorem one_lt_major (h : ¬(p = 0 ∧ |q| ≤ 1)) : 1 < major p q := by
  refine lt_of_le_of_ne (one_le_major p q) fun heq => h ?_
  have h₁ := abs_le_near p q
  have h₂ := abs_le_far p q
  have h₃ := le_abs_self (q + 1)
  have h₄ := neg_abs_le (q - 1)
  have hsum : √(p ^ 2 + (q + 1) ^ 2) + √(p ^ 2 + (q - 1) ^ 2) = 2 := by
    unfold major at heq
    linarith
  have hnear : √(p ^ 2 + (q + 1) ^ 2) = q + 1 := by linarith
  have hsquare := sq_near p q
  rw [hnear] at hsquare
  refine ⟨pow_eq_zero_iff two_ne_zero |>.mp (by linarith), abs_le.mpr ⟨?_, ?_⟩⟩
  · have := Real.sqrt_nonneg (p ^ 2 + (q + 1) ^ 2)
    linarith
  · have := Real.sqrt_nonneg (p ^ 2 + (q - 1) ^ 2)
    linarith

/-- The half difference of the distances reaches one exactly on the ray above the upper focus. -/
theorem one_le_minor_iff : 1 ≤ minor p q ↔ p = 0 ∧ 1 ≤ q := by
  constructor
  · intro h
    have hle : √(p ^ 2 + (q - 1) ^ 2) + 2 ≤ √(p ^ 2 + (q + 1) ^ 2) := by
      unfold minor at h
      linarith
    have hnonneg := Real.sqrt_nonneg (p ^ 2 + (q - 1) ^ 2)
    have hsquare : (√(p ^ 2 + (q - 1) ^ 2) + 2) ^ 2 ≤ √(p ^ 2 + (q + 1) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hle 2
    have h₂ := abs_le_far p q
    have h₄ := le_abs_self (q - 1)
    have hfar : √(p ^ 2 + (q - 1) ^ 2) = q - 1 :=
      le_antisymm (by linarith [sq_near p q, sq_far p q]) (by linarith)
    have hfarSquare := sq_far p q
    rw [hfar] at hfarSquare
    exact ⟨pow_eq_zero_iff two_ne_zero |>.mp (by linarith), by linarith⟩
  · rintro ⟨rfl, hq⟩
    unfold minor
    rw [zero_pow two_ne_zero, zero_add, zero_add, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith

/-- `2 ^ k` is below the hyperbolic cosine of `k + 1`. -/
theorem two_pow_lt_cosh (k : ℕ) : (2 : ℝ) ^ k < Real.cosh ((k : ℝ) + 1) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hpow : (2 : ℝ) ^ (k + 1) ≤ Real.exp 1 ^ (k + 1) := pow_le_pow_left₀ (by norm_num) htwo _
  rw [Real.exp_one_pow, Nat.cast_add_one, pow_succ] at hpow
  have hneg := Real.exp_pos (-((k : ℝ) + 1))
  rw [Real.cosh_eq]
  linarith

end Real

/-- `guard p q` exceeds the inverse hyperbolic cosine of the half sum of the distances. -/
theorem arcosh_major_lt_guard (p q : ℚ) : Real.arcosh (major p q) < (guard p q : ℝ) := by
  have hmajor := one_le_major (p : ℝ) q
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌈|p| + |q| + 1⌉₊ := ⟨_, rfl⟩
  have hceil : (|p| + |q| + 1 : ℚ) ≤ N := hN ▸ Nat.le_ceil _
  have hceilReal : |(p : ℝ)| + |(q : ℝ)| + 1 ≤ (N : ℝ) := by exact_mod_cast hceil
  have hlog : (N : ℝ) < 2 ^ (N.log2 + 1) := by exact_mod_cast Nat.lt_log2_self (n := N)
  have hlt : major p q < Real.cosh (((N.log2 + 1 : ℕ) : ℝ) + 1) :=
    (major_le _ _).trans_lt (hceilReal.trans_lt (hlog.trans (two_pow_lt_cosh _)))
  have h := (Real.arcosh_lt_arcosh (by linarith) (Real.cosh_pos _)).mpr hlt
  rw [Real.arcosh_cosh (by positivity)] at h
  have hguard : (guard p q : ℝ) = ((N.log2 + 1 : ℕ) : ℝ) + 1 := by
    rw [guard, ← hN]
    push_cast
    ring
  rw [hguard]
  exact h

/-- The square-root ladder converges to the square root of a nonnegative rational. -/
theorem converges_sqrtLadder (x : ℚ) (hx : 0 ≤ x) : Converges (sqrtLadder x) (√(x : ℝ)) := by
  have hcontains (n : Nat) : (sqrtLadder x n).Contains (√(x : ℝ)) :=
    (Interval.containsReal_some_iff _ _).mp
      (Interval.containsReal_sqrtPointBounds x (32 * 2 ^ n) hx)
  have hwidth (n : Nat) :
      ((sqrtLadder x n).hi : ℝ) - (sqrtLadder x n).lo ≤ (1 / 2 : ℝ) ^ (32 * 2 ^ n) := by
    have h := Interval.sqrtPointBounds_width_le x (32 * 2 ^ n)
    have hreal : (((Interval.sqrtPointBounds x (32 * 2 ^ n)).hi -
        (Interval.sqrtPointBounds x (32 * 2 ^ n)).lo : ℚ) : ℝ) ≤
          ((1 / (2 : ℚ) ^ (32 * 2 ^ n) : ℚ) : ℝ) := by exact_mod_cast h
    simpa [sqrtLadder, one_div, inv_pow] using hreal
  have hradius : Tendsto (fun n : Nat => (1 / 2 : ℝ) ^ (32 * 2 ^ n)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      (StrictMono.tendsto_atTop fun _ _ h =>
        (Nat.mul_lt_mul_left (by norm_num)).mpr (Nat.pow_lt_pow_right (by decide) h))
  refine ⟨hcontains, tendsto_of_abs_sub_le (fun n => ?_) hradius,
    tendsto_of_abs_sub_le (fun n => ?_) hradius⟩
  · have hc := hcontains n
    have hw := hwidth n
    rw [abs_le]
    constructor <;> linarith [hc.1, hc.2]
  · have hc := hcontains n
    have hw := hwidth n
    rw [abs_le]
    constructor <;> linarith [hc.1, hc.2]

variable (p q : ℚ)

/-- The ladder of the half sum of the distances converges. -/
theorem converges_majorLadder : Converges (majorLadder p q) (major p q) := by
  have h := ((converges_sqrtLadder (p ^ 2 + (q + 1) ^ 2) (by positivity)).add
    (converges_sqrtLadder (p ^ 2 + (q - 1) ^ 2) (by positivity))).scale (1 / 2)
  convert h using 1
  · rfl
  · unfold major
    push_cast
    ring

/-- The ladder of the half difference of the distances converges. -/
theorem converges_minorLadder : Converges (minorLadder p q) (minor p q) := by
  have h := ((converges_sqrtLadder (p ^ 2 + (q + 1) ^ 2) (by positivity)).sub
    (converges_sqrtLadder (p ^ 2 + (q - 1) ^ 2) (by positivity))).scale (1 / 2)
  convert h using 1
  · rfl
  · unfold minor
    push_cast
    ring

/-- The hyperbolic cosine ladder converges. -/
theorem converges_coshLadder (t : ℚ) : Converges (coshLadder t) (Real.cosh t) := by
  have h := ((TanhComparison.converges_expLadder t).add
    (TanhComparison.converges_expLadder (-t))).scale (1 / 2)
  convert h using 1
  · rfl
  · rw [Real.cosh_eq]
    push_cast
    ring

/-- The hyperbolic cosine at a nonzero rational argument is transcendental. -/
theorem transcendental_cosh_ratCast (t : ℚ) (ht : t ≠ 0) :
    Transcendental ℚ (Real.cosh (t : ℝ)) := by
  intro hcosh
  apply Enclosure.transcendental_exp_ratCast t ht
  have hsinh : IsAlgebraic ℚ (Real.sinh (t : ℝ)) := by
    apply IsAlgebraic.of_pow (n := 2) (by decide)
    rw [Real.sinh_sq]
    exact (hcosh.pow 2).sub isAlgebraic_one
  rw [← Real.cosh_add_sinh]
  exact hcosh.add hsinh

/-- The square root of a rational is algebraic. -/
theorem isAlgebraic_sqrt_ratCast (x : ℚ) : IsAlgebraic ℚ (√(x : ℝ)) := by
  rcases le_or_gt 0 x with hx | hx
  · apply IsAlgebraic.of_pow (n := 2) (by decide)
    rw [Real.sq_sqrt (by exact_mod_cast hx)]
    exact isAlgebraic_algebraMap (R := ℚ) (A := ℝ) x
  · rw [Real.sqrt_eq_zero_of_nonpos (by exact_mod_cast hx.le)]
    exact isAlgebraic_zero

private theorem isAlgebraic_half_add {x y : ℝ} (hx : IsAlgebraic ℚ x) (hy : IsAlgebraic ℚ y) :
    IsAlgebraic ℚ ((x + y) / 2) := by
  have h := (hx.add hy).mul (isAlgebraic_algebraMap (R := ℚ) (A := ℝ) (1 / 2))
  convert h using 1
  simp only [eq_ratCast]
  push_cast
  ring

/-- The half sum of the distances of a rational point is algebraic. -/
theorem isAlgebraic_major : IsAlgebraic ℚ (major p q) := by
  have h := isAlgebraic_half_add (isAlgebraic_sqrt_ratCast (p ^ 2 + (q + 1) ^ 2))
    (isAlgebraic_sqrt_ratCast (p ^ 2 + (q - 1) ^ 2))
  convert h using 1
  unfold major
  push_cast
  ring

/-- The half difference of the distances of a rational point is algebraic. -/
theorem isAlgebraic_minor : IsAlgebraic ℚ (minor p q) := by
  have h := isAlgebraic_half_add (isAlgebraic_sqrt_ratCast (p ^ 2 + (q + 1) ^ 2))
    (isAlgebraic_sqrt_ratCast (p ^ 2 + (q - 1) ^ 2)).neg
  convert h using 1
  unfold minor
  push_cast
  ring

variable {t : ℚ}

/-- The half sum of the distances is not the hyperbolic cosine of a nonzero rational. -/
theorem major_sub_cosh_ne_zero (ht : t ≠ 0) : major p q - Real.cosh t ≠ 0 := fun h =>
  transcendental_cosh_ratCast t ht (by
    rw [← sub_eq_zero.mp h]
    exact isAlgebraic_major p q)

/-- The half difference of the distances is not the sine of a nonzero rational. -/
theorem minor_sub_sin_ne_zero (ht : t ≠ 0) : minor p q - Real.sin t ≠ 0 := fun h =>
  Enclosure.transcendental_sin_ratCast t ht (by
    rw [← sub_eq_zero.mp h]
    exact isAlgebraic_minor p q)

/-- The half difference of the distances is not the cosine of a nonzero rational. -/
theorem minor_sub_cos_ne_zero (ht : t ≠ 0) : minor p q - Real.cos t ≠ 0 := fun h =>
  Enclosure.transcendental_cos_ratCast t ht (by
    rw [← sub_eq_zero.mp h]
    exact isAlgebraic_minor p q)

end FloatLib.Numerics.ConfocalComparison
