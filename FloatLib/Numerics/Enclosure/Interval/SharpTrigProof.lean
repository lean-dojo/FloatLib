/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.ElementaryProof
public import FloatLib.Numerics.Enclosure.Interval.ExactProof
public import FloatLib.Numerics.Enclosure.Interval.RoundingProof
public import FloatLib.Numerics.Enclosure.Interval.SharpTrig
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Real containment for the sharp sine and cosine

Each enclosure of `SharpTrig` contains the sine or cosine of every real member of its interval
(`containsReal_sharpSinBounds`, `containsReal_sharpCosBounds`). The grid hulls of `sinBounds` and
`cosBounds` are sound by the Lipschitz bound and the outward rounding. The bounds from the ends of
an interval use Mathlib's monotonicity of sine on `[-π/2, π/2]` and of cosine on `[0, π]`, through
`containsReal_monotoneBounds` and `containsReal_antitoneBounds`, and `Real.pi_gt_d20` places
`piLower` below `π` (`piLower_le_pi`).

The derivative branch rests on `containsReal_hull_of_derivative_sign`, which holds for any
differentiable function: when an enclosure of the derivative on the interval has one sign, the
function is monotone there, so the hull of the enclosures at the two ends contains its values.
-/

public section

namespace FloatLib.Numerics.Interval

/--
If `D` encloses the derivative of `f` on `I` and has one sign, then `f` is monotone or antitone
on `I`, so the hull of enclosures `J` of `f I.lo` and `K` of `f I.hi` contains `f x` for every
real `x` of `I`.
-/
theorem containsReal_hull_of_derivative_sign {f f' : ℝ → ℝ} {I D J K : Interval ℚ}
    (hderiv : ∀ y, I.ContainsReal some y → HasDerivAt f (f' y) y)
    (hD : ∀ y, I.ContainsReal some y → D.ContainsReal some (f' y))
    (hsign : 0 ≤ D.lo ∨ D.hi ≤ 0)
    (hJ : J.ContainsReal some (f I.lo)) (hK : K.ContainsReal some (f I.hi))
    {x : ℝ} (hx : I.ContainsReal some x) :
    (Exact.hull J K).ContainsReal some (f x) := by
  simp only [containsReal_some_iff, Exact.hull_lo, Exact.hull_hi] at hderiv hD hJ hK hx ⊢
  obtain ⟨hlo, hhi⟩ := hx
  have hcont : ContinuousOn f (Set.Icc (I.lo : ℝ) I.hi) :=
    fun y hy => (hderiv y hy).continuousAt.continuousWithinAt
  have hderivWithin : ∀ y ∈ interior (Set.Icc (I.lo : ℝ) I.hi),
      HasDerivWithinAt f (f' y) (interior (Set.Icc (I.lo : ℝ) I.hi)) y :=
    fun y hy => (hderiv y (interior_subset hy)).hasDerivWithinAt
  push_cast
  rcases hsign with hnonneg | hnonpos
  · have hmono : MonotoneOn f (Set.Icc (I.lo : ℝ) I.hi) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _) hcont hderivWithin
        fun y hy => (show (0 : ℝ) ≤ D.lo by exact_mod_cast hnonneg).trans
          (hD y (interior_subset hy)).1
    exact ⟨min_le_of_left_le (hJ.1.trans (hmono ⟨le_rfl, hlo.trans hhi⟩ ⟨hlo, hhi⟩ hlo)),
      le_max_of_le_right ((hmono ⟨hlo, hhi⟩ ⟨hlo.trans hhi, le_rfl⟩ hhi).trans hK.2)⟩
  · have hanti : AntitoneOn f (Set.Icc (I.lo : ℝ) I.hi) :=
      antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) hcont hderivWithin
        fun y hy => (hD y (interior_subset hy)).2.trans
          (show (D.hi : ℝ) ≤ 0 by exact_mod_cast hnonpos)
    exact ⟨min_le_of_right_le (hK.1.trans (hanti ⟨hlo, hhi⟩ ⟨hlo.trans hhi, le_rfl⟩ hhi)),
      le_max_of_le_left ((hanti ⟨le_rfl, hlo.trans hhi⟩ ⟨hlo, hhi⟩ hlo).trans hJ.2)⟩

/-- `piLower` is below `π`: it is the twenty-decimal bound of `Real.pi_gt_d20`. -/
theorem piLower_le_pi : (piLower : ℝ) ≤ Real.pi := by
  have h : (piLower : ℝ) = 3.14159265358979323846 := by
    rw [piLower, Kernel.Q.mk_eq, Rat.mkRat_eq_div]
    norm_num
  exact h ▸ Real.pi_gt_d20.le

/-- Sine decreases on `[π/2, π]`. -/
private theorem antitoneOn_sin : AntitoneOn Real.sin (Set.Icc (Real.pi / 2) Real.pi) := by
  intro a ha b hb hab
  rw [← Real.cos_sub_pi_div_two, ← Real.cos_sub_pi_div_two]
  exact Real.antitoneOn_cos ⟨by linarith [ha.1], by linarith [ha.2, Real.pi_pos]⟩
    ⟨by linarith [hb.1], by linarith [hb.2, Real.pi_pos]⟩ (by linarith)

/-- Cosine increases on `[-π, 0]`. -/
private theorem monotoneOn_cos : MonotoneOn Real.cos (Set.Icc (-Real.pi) 0) := by
  intro a ha b hb hab
  rw [← Real.cos_neg a, ← Real.cos_neg b]
  exact Real.antitoneOn_cos ⟨by linarith [hb.2], by linarith [hb.1]⟩
    ⟨by linarith [ha.2], by linarith [ha.1]⟩ (by linarith)

/-- A function at most one that rises on `[I.lo, c]` and falls on `[c, I.hi]` is, on `I`, at
least the smaller of the lower bounds `J` of `f I.lo` and `K` of `f I.hi`. -/
private theorem containsReal_rise_fall {f : ℝ → ℝ} {I J K : Interval ℚ} {c x : ℝ}
    (hmono : MonotoneOn f (Set.Icc (I.lo : ℝ) c)) (hanti : AntitoneOn f (Set.Icc c (I.hi : ℝ)))
    (hJ : J.ContainsReal some (f I.lo)) (hK : K.ContainsReal some (f I.hi)) (hone : f x ≤ 1)
    (hx : I.ContainsReal some x) :
    (⟨Kernel.Q.min J.lo K.lo, 1⟩ : Interval ℚ).ContainsReal some (f x) := by
  rw [containsReal_some_iff] at hJ hK hx ⊢
  simp only [Kernel.Q.min_eq, Rat.cast_min, Rat.cast_one]
  refine ⟨?_, hone⟩
  rcases le_total x c with hxc | hcx
  · exact min_le_of_left_le
      (hJ.1.trans (hmono ⟨le_rfl, hx.1.trans hxc⟩ ⟨hx.1, hxc⟩ hx.1))
  · exact min_le_of_right_le
      (hK.1.trans (hanti ⟨hcx, hx.2⟩ ⟨hcx.trans hx.2, le_rfl⟩ hx.2))

/-- `sinBase I terms bits` contains `Real.sin x` for every real `x` of `I`. -/
theorem containsReal_sinBase (I : Interval ℚ) (terms bits : Nat) {x : ℝ}
    (hx : I.ContainsReal some x) : (sinBase I terms bits).ContainsReal some (Real.sin x) :=
  containsReal_dyadicHull bits (containsReal_sinBounds I terms hx)

/-- `cosBase I terms bits` contains `Real.cos x` for every real `x` of `I`. -/
theorem containsReal_cosBase (I : Interval ℚ) (terms bits : Nat) {x : ℝ}
    (hx : I.ContainsReal some x) : (cosBase I terms bits).ContainsReal some (Real.cos x) :=
  containsReal_dyadicHull bits (containsReal_cosBounds I terms hx)

/-- `sinPoint q terms bits` contains `Real.sin q`. -/
theorem containsReal_sinPoint (q : ℚ) (terms bits : Nat) :
    (sinPoint q terms bits).ContainsReal some (Real.sin q) :=
  containsReal_sinBase (point q) terms bits (containsReal_point q)

/-- `cosPoint q terms bits` contains `Real.cos q`. -/
theorem containsReal_cosPoint (q : ℚ) (terms bits : Nat) :
    (cosPoint q terms bits).ContainsReal some (Real.cos q) :=
  containsReal_cosBase (point q) terms bits (containsReal_point q)

/-- On an interval of `[-piLower/2, piLower/2]`, the point bounds at the ends contain the sine
of every real of the interval. -/
theorem containsReal_sinEndpoint (I : Interval ℚ) (terms bits : Nat)
    (hprincipal : -(piLower / 2) ≤ I.lo ∧ I.hi ≤ piLower / 2) {x : ℝ}
    (hx : I.ContainsReal some x) :
    (sinEndpoint I terms bits).ContainsReal some (Real.sin x) := by
  -- Unfold first: the kernel then checks an instance of `containsReal_monotoneBounds` and never
  -- compares two enclosures by unfolding the point bounds.
  unfold sinEndpoint
  have hpi := piLower_le_pi
  have hlo : -((piLower : ℝ) / 2) ≤ I.lo := by exact_mod_cast hprincipal.1
  have hhi : (I.hi : ℝ) ≤ piLower / 2 := by exact_mod_cast hprincipal.2
  exact containsReal_monotoneBounds _ Real.sin I
    (Real.monotoneOn_sin.mono (Set.Icc_subset_Icc (by linarith) (by linarith)))
    (fun q _ => containsReal_sinPoint q terms bits) hx

/-- On an interval of `[0, piLower]`, the point bounds at the ends contain the cosine of every
real of the interval. -/
theorem containsReal_cosEndpoint (I : Interval ℚ) (terms bits : Nat)
    (hprincipal : 0 ≤ I.lo ∧ I.hi ≤ piLower) {x : ℝ} (hx : I.ContainsReal some x) :
    (cosEndpoint I terms bits).ContainsReal some (Real.cos x) := by
  -- Unfold first, as in `containsReal_sinEndpoint`.
  unfold cosEndpoint
  have hlo : (0 : ℝ) ≤ I.lo := by exact_mod_cast hprincipal.1
  have hhi : (I.hi : ℝ) ≤ piLower := by exact_mod_cast hprincipal.2
  exact containsReal_antitoneBounds _ Real.cos I
    (Real.antitoneOn_cos.mono (Set.Icc_subset_Icc hlo (hhi.trans piLower_le_pi)))
    (fun q _ => containsReal_cosPoint q terms bits) hx

/-- On an interval of `[-piLower, 0]`, the point bounds at the negated ends contain the cosine of
every real of the interval. -/
theorem containsReal_cosNegativeEndpoint (I : Interval ℚ) (terms bits : Nat)
    (hnegative : -piLower ≤ I.lo ∧ I.hi ≤ 0) {x : ℝ} (hx : I.ContainsReal some x) :
    (cosNegativeEndpoint I terms bits).ContainsReal some (Real.cos x) := by
  unfold cosNegativeEndpoint
  rw [← Real.cos_neg]
  refine containsReal_cosEndpoint _ terms bits ?_ (Exact.containsReal_neg hx)
  rw [Exact.neg_lo, Exact.neg_hi]
  constructor <;> linarith [hnegative.1, hnegative.2]

/-- On an interval of `[0, piLower]`, sine is at least the smaller of its lower point bounds at the
ends, and at most one. -/
theorem containsReal_sinPositiveEndpoint (I : Interval ℚ) (terms bits : Nat)
    (hpositive : 0 ≤ I.lo ∧ I.hi ≤ piLower) {x : ℝ} (hx : I.ContainsReal some x) :
    (sinPositiveEndpoint I terms bits).ContainsReal some (Real.sin x) := by
  unfold sinPositiveEndpoint
  have hlo : (0 : ℝ) ≤ I.lo := by exact_mod_cast hpositive.1
  have hhi : (I.hi : ℝ) ≤ piLower := by exact_mod_cast hpositive.2
  have hpi := piLower_le_pi
  exact containsReal_rise_fall (c := Real.pi / 2)
    (Real.monotoneOn_sin.mono (Set.Icc_subset_Icc (by linarith [Real.pi_pos]) le_rfl))
    (antitoneOn_sin.mono (Set.Icc_subset_Icc le_rfl (by linarith)))
    (containsReal_sinPoint I.lo terms bits) (containsReal_sinPoint I.hi terms bits)
    (Real.sin_le_one x) hx

/-- On an interval in `[-piLower, piLower]` that contains zero, cosine is at least the smaller of
its lower point bounds at the ends, and at most one. -/
theorem containsReal_cosCrossZeroEndpoint (I : Interval ℚ) (terms bits : Nat)
    (hcross : -piLower ≤ I.lo ∧ I.lo ≤ 0 ∧ 0 ≤ I.hi ∧ I.hi ≤ piLower) {x : ℝ}
    (hx : I.ContainsReal some x) :
    (cosCrossZeroEndpoint I terms bits).ContainsReal some (Real.cos x) := by
  unfold cosCrossZeroEndpoint
  have hlo : -(piLower : ℝ) ≤ I.lo := by exact_mod_cast hcross.1
  have hhi : (I.hi : ℝ) ≤ piLower := by exact_mod_cast hcross.2.2.2
  have hpi := piLower_le_pi
  exact containsReal_rise_fall (c := 0)
    (monotoneOn_cos.mono (Set.Icc_subset_Icc (by linarith) le_rfl))
    (Real.antitoneOn_cos.mono (Set.Icc_subset_Icc le_rfl (by linarith)))
    (containsReal_cosPoint I.lo terms bits) (containsReal_cosPoint I.hi terms bits)
    (Real.cos_le_one x) hx

/-- `sinMonotoneBase I terms bits` contains `Real.sin x` for every real `x` of `I`. -/
theorem containsReal_sinMonotoneBase (I : Interval ℚ) (terms bits : Nat) {x : ℝ}
    (hx : I.ContainsReal some x) :
    (sinMonotoneBase I terms bits).ContainsReal some (Real.sin x) := by
  rw [sinMonotoneBase_def]
  refine Exact.containsReal_intersect (containsReal_sinBase I terms bits hx) ?_
  split_ifs with hprincipal hpositive hsign
  · exact containsReal_sinEndpoint I terms bits hprincipal hx
  · exact containsReal_sinPositiveEndpoint I terms bits hpositive hx
  · exact containsReal_hull_of_derivative_sign (fun y _ => Real.hasDerivAt_sin y)
      (fun y hy => containsReal_cosBase I terms bits hy) hsign
      (containsReal_sinPoint I.lo terms bits) (containsReal_sinPoint I.hi terms bits) hx
  · exact containsReal_sinBase I terms bits hx

/-- `cosMonotoneBase I terms bits` contains `Real.cos x` for every real `x` of `I`. -/
theorem containsReal_cosMonotoneBase (I : Interval ℚ) (terms bits : Nat) {x : ℝ}
    (hx : I.ContainsReal some x) :
    (cosMonotoneBase I terms bits).ContainsReal some (Real.cos x) := by
  rw [cosMonotoneBase_def]
  refine Exact.containsReal_intersect (containsReal_cosBase I terms bits hx) ?_
  split_ifs with hprincipal hnegative hcross hsign
  · exact containsReal_cosEndpoint I terms bits hprincipal hx
  · exact containsReal_cosNegativeEndpoint I terms bits hnegative hx
  · exact containsReal_cosCrossZeroEndpoint I terms bits hcross hx
  · refine containsReal_hull_of_derivative_sign (D := Exact.neg (sinBase I terms bits))
      (fun y _ => Real.hasDerivAt_cos y)
      (fun y hy => Exact.containsReal_neg (containsReal_sinBase I terms bits hy)) ?_
      (containsReal_cosPoint I.lo terms bits) (containsReal_cosPoint I.hi terms bits) hx
    rw [Exact.neg_lo, Exact.neg_hi, neg_nonneg, neg_nonpos]
    exact hsign.symm
  · exact containsReal_cosBase I terms bits hx

/-- `sharpSinBounds I terms bits` contains `Real.sin x` for every real `x` of `I`. -/
theorem containsReal_sharpSinBounds (I : Interval ℚ) (terms bits : Nat) {x : ℝ}
    (hx : I.ContainsReal some x) :
    (sharpSinBounds I terms bits).ContainsReal some (Real.sin x) := by
  have hJ := containsReal_sinMonotoneBase I terms bits hx
  rw [sharpSinBounds_def]
  dsimp only
  split_ifs with hpositive
  · have hlo : (0 : ℝ) ≤ I.lo := by exact_mod_cast hpositive.1
    have hhi : (I.hi : ℝ) ≤ piLower := by exact_mod_cast hpositive.2
    rw [containsReal_some_iff] at hx hJ ⊢
    have hsin := Real.sin_nonneg_of_nonneg_of_le_pi (hlo.trans hx.1)
      (hx.2.trans (hhi.trans piLower_le_pi))
    push_cast
    exact ⟨max_le hJ.1 hsin, hJ.2⟩
  · exact hJ

/-- `sharpCosBounds I terms bits` contains `Real.cos x` for every real `x` of `I`. -/
theorem containsReal_sharpCosBounds (I : Interval ℚ) (terms bits : Nat) {x : ℝ}
    (hx : I.ContainsReal some x) :
    (sharpCosBounds I terms bits).ContainsReal some (Real.cos x) := by
  have hJ := containsReal_cosMonotoneBase I terms bits hx
  rw [sharpCosBounds_def]
  dsimp only
  split_ifs with hprincipal
  · have hpi := piLower_le_pi
    have hlo : -((piLower : ℝ) / 2) ≤ I.lo := by exact_mod_cast hprincipal.1
    have hhi : (I.hi : ℝ) ≤ piLower / 2 := by exact_mod_cast hprincipal.2
    rw [containsReal_some_iff] at hx hJ ⊢
    have hcos := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (x := x) (by linarith [hx.1])
      (by linarith [hx.2])
    push_cast
    exact ⟨max_le hJ.1 hcos, hJ.2⟩
  · exact hJ

end FloatLib.Numerics.Interval
