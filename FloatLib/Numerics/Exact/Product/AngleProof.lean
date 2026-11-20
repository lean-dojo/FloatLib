/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Product.Angle
public import FloatLib.Numerics.Exact.Product.FactorsProof
public import FloatLib.Numerics.Enclosure.Constants.Proof
public import FloatLib.Numerics.Enclosure.Expression.ClosedProof
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The enclosures of the cosine and sine of an enclosed angle are sound

Every enclosure that `trigBounds?` returns for an interval contains the cosine or the sine of
every real in the interval (`contains_trigBounds?`). The proof subtracts `k` quarter turns with
the enclosure of `π / 2` and applies `eval_add_quarterTurns`: `cos` and `sin` of `r + k π / 2`
are `±cos r` or `±sin r` by `k` modulo four.

The sequence `Trig.intervals` contains the cosine or the sine and converges to it
(`Trig.converges_intervals`), so the comparison of an admissible product terminates at every
rational boundary (`Admissible.exists_decide?_isSome`), with no premise on the boundary.
-/

@[expose] public section

namespace FloatLib.Numerics.ProductComparison

/-- Every enclosure that `smallAngleBounds?` returns contains the cosine or the sine. -/
theorem contains_smallAngleBounds? {trig : Trig} {angle : RationalInterval} {a : ℝ}
    {precision : Nat} {interval : RationalInterval} (ha : angle.Contains a)
    (h : smallAngleBounds? trig angle precision = some interval) :
    interval.Contains (trig.eval a) := by
  have hbound : ((1 / 2 ^ (precision / 2) : ℚ) : ℝ) ≤ 1 := by
    have hpow : (1 : ℝ) ≤ 2 ^ (precision / 2) := one_le_pow₀ (by norm_num)
    push_cast
    exact (div_le_one (by positivity)).mpr hpow
  obtain ⟨hlo, hhi⟩ := ha
  unfold smallAngleBounds? at h
  split at h
  · rename_i hpositive
    have hlo0 : (0 : ℝ) < angle.lo := by exact_mod_cast hpositive.1
    have hhi1 : (angle.hi : ℝ) ≤ 1 := (by exact_mod_cast hpositive.2 : (angle.hi : ℝ) ≤ _).trans
      hbound
    have ha0 : 0 < a := hlo0.trans_le hlo
    rw [← Option.some.inj h]
    cases trig
    · refine ⟨?_, ?_⟩
      · have hcos := Real.one_sub_sq_div_two_le_cos (x := a)
        simp only [Trig.eval]
        push_cast
        nlinarith
      · simpa [Trig.eval] using Real.cos_le_one a
    · refine ⟨?_, ?_⟩
      · have hsin := Real.sin_gt_sub_cube ha0
        simp only [Trig.eval]
        push_cast
        linarith [mul_nonneg (sub_nonneg.mpr hlo) (by nlinarith : 0 ≤ 6 - (a ^ 2 +
          a * (angle.lo : ℝ) + (angle.lo : ℝ) ^ 2))]
      · exact (Real.sin_lt ha0).le.trans hhi
  · split at h
    · rename_i hnegative
      have hhi0 : (angle.hi : ℝ) < 0 := by exact_mod_cast hnegative.1
      have hlo1 : (-1 : ℝ) ≤ angle.lo := by
        have hcast : -((1 / 2 ^ (precision / 2) : ℚ) : ℝ) ≤ angle.lo := by
          exact_mod_cast hnegative.2
        linarith
      have ha0 : a < 0 := hhi.trans_lt hhi0
      rw [← Option.some.inj h]
      cases trig
      · refine ⟨?_, ?_⟩
        · have hcos := Real.one_sub_sq_div_two_le_cos (x := a)
          simp only [Trig.eval]
          push_cast
          nlinarith
        · simpa [Trig.eval] using Real.cos_le_one a
      · have hupper := Real.sin_gt_sub_cube (neg_pos.mpr ha0)
        have hlower := Real.sin_lt (neg_pos.mpr ha0)
        rw [Real.sin_neg] at hupper hlower
        refine ⟨?_, ?_⟩
        · simp only [Trig.eval]
          linarith
        · simp only [Trig.eval]
          push_cast
          linarith [mul_nonneg (sub_nonneg.mpr hhi) (by nlinarith : 0 ≤ 6 - (a ^ 2 +
            a * (angle.hi : ℝ) + (angle.hi : ℝ) ^ 2))]
    · simp at h

/-- The cached bounds enclose `π / 2`. -/
theorem contains_halfPiBounds (bits : Nat) : (halfPiBounds bits).Contains (Real.pi / 2) := by
  obtain ⟨hlower, hupper⟩ := Enclosure.Constants.halfPiLower_spec bits
  have hpow : (0 : ℝ) < 2 ^ bits := by positivity
  constructor
  · simp only [halfPiBounds]
    push_cast
    exact (div_le_iff₀ hpow).mpr hlower
  · simp only [halfPiBounds]
    push_cast
    exact (le_div_iff₀ hpow).mpr hupper.le

/-- The cosine at an integer number of quarter turns. -/
theorem cos_int_mul_pi_div_two (m : ℤ) :
    Real.cos (m * (Real.pi / 2)) = if m % 4 = 0 then 1 else if m % 4 = 2 then -1 else 0 := by
  have hsplit : (m : ℝ) * (Real.pi / 2) =
      ((m % 4 : ℤ) : ℝ) * (Real.pi / 2) + ((m / 4 : ℤ) : ℝ) * (2 * Real.pi) := by
    have hm : m = m % 4 + 4 * (m / 4) := by omega
    conv_lhs => rw [hm]
    push_cast
    ring
  rw [hsplit, Real.cos_add_int_mul_two_pi]
  have hlower := Int.emod_nonneg m (by norm_num : (4 : ℤ) ≠ 0)
  obtain h | h | h | h : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
  · simp [h]
  · simp [h]
  · rw [h, show ((2 : ℤ) : ℝ) * (Real.pi / 2) = Real.pi by push_cast; ring, Real.cos_pi]
    simp
  · rw [h, show ((3 : ℤ) : ℝ) * (Real.pi / 2) = Real.pi / 2 + Real.pi by push_cast; ring,
      Real.cos_add_pi]
    simp

/-- The sine at an integer number of quarter turns. -/
theorem sin_int_mul_pi_div_two (m : ℤ) :
    Real.sin (m * (Real.pi / 2)) = if m % 4 = 1 then 1 else if m % 4 = 3 then -1 else 0 := by
  have hsplit : (m : ℝ) * (Real.pi / 2) =
      ((m % 4 : ℤ) : ℝ) * (Real.pi / 2) + ((m / 4 : ℤ) : ℝ) * (2 * Real.pi) := by
    have hm : m = m % 4 + 4 * (m / 4) := by omega
    conv_lhs => rw [hm]
    push_cast
    ring
  rw [hsplit, Real.sin_add_int_mul_two_pi]
  have hlower := Int.emod_nonneg m (by norm_num : (4 : ℤ) ≠ 0)
  obtain h | h | h | h : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
  · simp [h]
  · simp [h]
  · rw [h, show ((2 : ℤ) : ℝ) * (Real.pi / 2) = Real.pi by push_cast; ring, Real.sin_pi]
    simp
  · rw [h, show ((3 : ℤ) : ℝ) * (Real.pi / 2) = Real.pi / 2 + Real.pi by push_cast; ring,
      Real.sin_add_pi]
    simp

/--
The cosine or sine after `k` quarter turns is the function of the reduced angle that the
quadrant selects, negated in two quadrants of the four.
-/
theorem eval_add_quarterTurns (trig : Trig) (r : ℝ) (k : ℤ) :
    trig.eval (r + k * (Real.pi / 2)) =
      (if trig.turnedNegative k then -1 else 1) * (trig.turned k).eval r := by
  have hlower := Int.emod_nonneg k (by norm_num : (4 : ℤ) ≠ 0)
  cases trig
  · simp only [Trig.eval, Real.cos_add, cos_int_mul_pi_div_two, sin_int_mul_pi_div_two]
    obtain h | h | h | h : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
    · have h2 : k % 2 = 0 := by omega
      simp [Trig.turned, Trig.turnedNegative, h, h2]
    · have h2 : k % 2 = 1 := by omega
      simp [Trig.turned, Trig.turnedNegative, Trig.swap, h, h2]
    · have h2 : k % 2 = 0 := by omega
      simp [Trig.turned, Trig.turnedNegative, h, h2]
    · have h2 : k % 2 = 1 := by omega
      simp [Trig.turned, Trig.turnedNegative, Trig.swap, h, h2]
  · simp only [Trig.eval, Real.sin_add, cos_int_mul_pi_div_two, sin_int_mul_pi_div_two]
    obtain h | h | h | h : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
    · have h2 : k % 2 = 0 := by omega
      simp [Trig.turned, Trig.turnedNegative, h, h2]
    · have h2 : k % 2 = 1 := by omega
      simp [Trig.turned, Trig.turnedNegative, Trig.swap, h, h2]
    · have h2 : k % 2 = 0 := by omega
      simp [Trig.turned, Trig.turnedNegative, h, h2]
    · have h2 : k % 2 = 1 := by omega
      simp [Trig.turned, Trig.turnedNegative, Trig.swap, h, h2]

/-- Every enclosure that `reducedTrigBounds?` returns contains the cosine or the sine. -/
theorem contains_reducedTrigBounds? {trig : Trig} {reduced : RationalInterval} {r : ℝ}
    {precision : Nat} {interval : RationalInterval} (hr : reduced.Contains r)
    (h : reducedTrigBounds? trig reduced precision = some interval) :
    interval.Contains (trig.eval r) := by
  unfold reducedTrigBounds? at h
  dsimp only at h
  split at h
  · rename_i small hsmall
    rw [← Option.some.inj h]
    exact contains_smallAngleBounds? hr hsmall
  · have hvalue := Interval.Expr.contains_gridEnclosureWith? (values := fun _ => r)
      (fun i I hI => by
        rcases i with _ | i
        · simp only [List.getElem?_cons_zero, Option.some.injEq] at hI
          rw [← hI]
          exact hr
        · simp at hI) h
    cases trig <;>
      simpa [Trig.op, Trig.eval, Interval.Expr.eval, Interval.UnaryOp.eval] using hvalue

/-- Every enclosure that `trigBounds?` returns contains the cosine or the sine. -/
theorem contains_trigBounds? {trig : Trig} {angle : RationalInterval} {x : ℝ}
    {precision : Nat} {interval : RationalInterval} (hx : angle.Contains x)
    (h : trigBounds? trig angle precision = some interval) :
    interval.Contains (trig.eval x) := by
  unfold trigBounds? at h
  split at h
  · exact contains_reducedTrigBounds? hx h
  obtain ⟨bounds, hbounds, rfl⟩ := Option.map_eq_some_iff.mp h
  generalize quarterTurns angle
    (halfPiBounds (precision + ⌈max |angle.lo| |angle.hi|⌉₊.log2 + 8)) = k at hbounds ⊢
  have hreduced := RationalInterval.contains_sub hx (RationalInterval.contains_scale
    (contains_halfPiBounds (precision + ⌈max |angle.lo| |angle.hi|⌉₊.log2 + 8)) k)
  have hvalue := contains_reducedTrigBounds? hreduced hbounds
  have hturn := eval_add_quarterTurns trig (x - ((k : ℚ) : ℝ) * (Real.pi / 2)) k
  rw [show x - ((k : ℚ) : ℝ) * (Real.pi / 2) + (k : ℝ) * (Real.pi / 2) = x by push_cast; ring]
    at hturn
  rw [hturn]
  split
  · simpa using RationalInterval.contains_neg hvalue
  · simpa using hvalue

/-- The enclosures of the bounded factor contain it and converge to it. -/
theorem Trig.converges_intervals (trig : Trig) (b : ℚ) :
    RationalInterval.Converges (trig.intervals b) (trig.eval (b : ℝ)) :=
  (trig.converges_reduced b).prefixed fun n _ => by
    cases h : trigBounds? trig ⟨b, b⟩ (64 * 2 ^ n) with
    | none =>
        rw [Option.getD_none]
        cases trig
        · exact ⟨by simpa [Trig.eval] using Real.neg_one_le_cos (b : ℝ),
            by simpa [Trig.eval] using Real.cos_le_one (b : ℝ)⟩
        · exact ⟨by simpa [Trig.eval] using Real.neg_one_le_sin (b : ℝ),
            by simpa [Trig.eval] using Real.sin_le_one (b : ℝ)⟩
    | some bounds =>
        rw [Option.getD_some]
        exact contains_trigBounds? ⟨le_refl _, le_refl _⟩ h

variable {growth : Growth} {trig : Trig} {a b : ℚ}

/--
At every rational boundary some enclosure of the bounded factor settles the order of an
admissible product, also after sharing the first enclosures through a cache.
-/
theorem Admissible.exists_decide?_isSome (h : Admissible growth trig a b) (levels : Nat)
    (boundary : ℚ) :
    ∃ n, (decide? (growth.compare a)
      ((Enclosure.Comparison.cacheIntervals (trig.intervals b) levels).get n) boundary).isSome := by
  simp only [Enclosure.Comparison.cacheIntervals_apply]
  exact ProductComparison.exists_decide?_isSome (growth.compare_eq_real a) h.trig_ne_zero
    (h.eval_mul_eval_ne_ratCast boundary) (trig.converges_intervals b).lo
    (trig.converges_intervals b).hi

end FloatLib.Numerics.ProductComparison
