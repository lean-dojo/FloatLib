/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.Elementary
public import FloatLib.Numerics.Enclosure.Interval.Real
public import FloatLib.Numerics.Enclosure.Elementary.Proof
public import FloatLib.Numerics.Enclosure.Trigonometric.Reduction.Proof
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linarith

/-!
# Real containment for interval elementary functions

Endpoint monotonicity proves the exponential, logarithm, arctangent, and square-root bounds.
The sine and cosine proofs use Mathlib's global Lipschitz estimates, so their intervals remain
valid across extrema. The square-root proof reduces to `Nat.sqrt_le'` and `Nat.lt_succ_sqrt'`.
No theorem restricts an interval's members to rational values.
-/

public section

namespace FloatLib.Numerics.Interval

/-- Point enclosures and monotonicity on the input interval enclose its entire real image. -/
theorem containsReal_monotoneBounds (enclose : ℚ → Interval ℚ) (f : ℝ → ℝ)
    (I : Interval ℚ)
    (hf : MonotoneOn f (Set.Icc (I.lo : ℝ) (I.hi : ℝ)))
    (henclose : ∀ q ∈ Set.Icc I.lo I.hi, (enclose q).ContainsReal some (f q))
    {x : ℝ} (hx : I.ContainsReal some x) :
    (monotoneBounds enclose I).ContainsReal some (f x) := by
  obtain ⟨hlo, hhi⟩ := (containsReal_some_iff I x).1 hx
  have horder : I.lo ≤ I.hi := by exact_mod_cast hlo.trans hhi
  have hl := (containsReal_some_iff _ _).1 (henclose I.lo ⟨le_rfl, horder⟩)
  have hh := (containsReal_some_iff _ _).1 (henclose I.hi ⟨horder, le_rfl⟩)
  have hfl := hf ⟨le_rfl, hlo.trans hhi⟩ ⟨hlo, hhi⟩ hlo
  have hfh := hf ⟨hlo, hhi⟩ ⟨hlo.trans hhi, le_rfl⟩ hhi
  apply (containsReal_some_iff _ _).2
  by_cases heq : I.lo = I.hi
  · simp only [monotoneBounds, heq, ↓reduceIte]
    exact ⟨by simpa only [heq] using hl.1.trans hfl, hfh.trans hh.2⟩
  · simp only [monotoneBounds, heq, ↓reduceIte]
    exact ⟨hl.1.trans hfl, hfh.trans hh.2⟩

/-- The exponential bounds contain `exp x` for every real member of the input interval. -/
theorem containsReal_expBounds (I : Interval ℚ) (terms : Nat) {x : ℝ}
    (hx : I.ContainsReal some x) : (expBounds I terms).ContainsReal some (Real.exp x) := by
  apply containsReal_monotoneBounds _ Real.exp I
    (fun _ _ _ _ h => Real.exp_le_exp.mpr h) ?_ hx
  intro q _
  apply (containsReal_some_iff _ _).2
  have h := Enclosure.contains_exp q terms
  simpa only [Rat.cast_max, Rat.cast_zero] using
    And.intro (max_le (Real.exp_pos _).le h.1) h.2

/-- A successful logarithm enclosure contains the logarithm of every enclosed real value. -/
theorem containsReal_logBounds? {I K : Interval ℚ} {terms : Nat}
    (h : logBounds? I terms = some K) {x : ℝ} (hx : I.ContainsReal some x) :
    K.ContainsReal some (Real.log x) := by
  unfold logBounds? at h
  split at h
  · rename_i hpos
    cases h
    have hreal : (0 : ℝ) < I.lo := by exact_mod_cast hpos
    apply containsReal_monotoneBounds _ Real.log I ?_ ?_ hx
    · intro a ha b hb hab
      exact Real.strictMonoOn_log.monotoneOn
        (hreal.trans_le ha.1) (hreal.trans_le hb.1) hab
    · intro q hq
      exact (containsReal_some_iff _ _).2
        (Enclosure.contains_log q terms (hpos.trans_le hq.1))
  · simp at h

/-- The arctangent bounds contain the image of every enclosed real value. -/
theorem containsReal_atanBounds (I : Interval ℚ) (terms : Nat) {x : ℝ}
    (hx : I.ContainsReal some x) :
    (atanBounds I terms).ContainsReal some (Real.arctan x) := by
  apply containsReal_monotoneBounds _ Real.arctan I (Real.arctan_mono.monotoneOn _) ?_ hx
  intro q _
  exact (containsReal_some_iff _ _).2 (Enclosure.contains_atan q terms)

/-- A unit-Lipschitz function is enclosed by its midpoint bounds plus the half-width. -/
theorem containsReal_lipschitzUnitBounds (enclose : ℚ → Interval ℚ) (f : ℝ → ℝ)
    (hf : LipschitzWith 1 f) (hrange : ∀ x, |f x| ≤ 1)
    (henclose : ∀ q, (enclose q).ContainsReal some (f q))
    (I : Interval ℚ) {x : ℝ} (hx : I.ContainsReal some x) :
    (lipschitzUnitBounds enclose I).ContainsReal some (f x) := by
  have hunit := abs_le.mp (hrange x)
  apply (containsReal_some_iff _ _).2
  unfold lipschitzUnitBounds
  split
  · simpa using hunit
  · obtain ⟨hlo, hhi⟩ := (containsReal_some_iff I x).1 hx
    let midpoint := (I.lo + I.hi) / 2
    let radius := (I.hi - I.lo) / 2
    have hdist : |x - (midpoint : ℝ)| ≤ (radius : ℝ) := by
      dsimp [midpoint, radius]
      push_cast
      rw [abs_le]
      constructor <;> linarith
    have hdiff : |f x - f midpoint| ≤ (radius : ℝ) := by
      have h := hf.dist_le_mul x (midpoint : ℝ)
      simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
      exact h.trans hdist
    have hpoint := (containsReal_some_iff _ _).1 (henclose midpoint)
    have habs := abs_le.mp hdiff
    change (max (-1) ((enclose midpoint).lo - radius) : ℚ) ≤ (f x : ℝ) ∧
      (f x : ℝ) ≤ (min 1 ((enclose midpoint).hi + radius) : ℚ)
    push_cast
    exact ⟨max_le hunit.1 (by linarith), le_min hunit.2 (by linarith)⟩

/-- Sine containment holds throughout the interval, including interior extrema. -/
theorem containsReal_sinBounds (I : Interval ℚ) (terms : Nat) {x : ℝ}
    (hx : I.ContainsReal some x) : (sinBounds I terms).ContainsReal some (Real.sin x) := by
  apply containsReal_lipschitzUnitBounds _ Real.sin Real.lipschitzWith_sin
    Real.abs_sin_le_one ?_ I hx
  intro q
  apply (containsReal_some_iff _ _).2
  split
  · exact Enclosure.contains_sin q terms
  · exact Enclosure.contains_sinReduced q terms

/-- Cosine containment holds throughout the interval, including interior extrema. -/
theorem containsReal_cosBounds (I : Interval ℚ) (terms : Nat) {x : ℝ}
    (hx : I.ContainsReal some x) : (cosBounds I terms).ContainsReal some (Real.cos x) := by
  apply containsReal_lipschitzUnitBounds _ Real.cos Real.lipschitzWith_cos
    Real.abs_cos_le_one ?_ I hx
  intro q
  apply (containsReal_some_iff _ _).2
  split
  · exact Enclosure.contains_cos q terms
  · exact Enclosure.contains_cosReduced q terms

/-- Integer square-root bounds enclose the real square root of every nonnegative rational. -/
theorem containsReal_sqrtPointBounds (x : ℚ) (precision : Nat) (hx : 0 ≤ x) :
    (sqrtPointBounds x precision).ContainsReal some (Real.sqrt x) := by
  let scale := (2 : ℚ) ^ precision
  let n := ⌊x * scale ^ 2⌋₊
  let root := Nat.sqrt n
  let lower := (root : ℚ) / scale
  let upper := (root + 1 : ℚ) / scale
  have hscale : 0 < scale := by positivity
  have hscaled : 0 ≤ x * scale ^ 2 := mul_nonneg hx (sq_nonneg _)
  have hroot : (root : ℚ) ^ 2 ≤ x * scale ^ 2 := by
    calc
      (root : ℚ) ^ 2 ≤ (n : ℚ) := by exact_mod_cast Nat.sqrt_le' n
      _ ≤ x * scale ^ 2 := Nat.floor_le hscaled
  have hnext : x * scale ^ 2 < (root + 1 : ℚ) ^ 2 := by
    calc
      x * scale ^ 2 < (n : ℚ) + 1 := Nat.lt_floor_add_one _
      _ ≤ (root + 1 : ℚ) ^ 2 := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.lt_succ_sqrt' n)
  have hlower : lower ^ 2 ≤ x := by
    dsimp [lower]
    rw [div_pow]
    exact (div_le_iff₀ (sq_pos_of_pos hscale)).mpr hroot
  have hupper : x ≤ upper ^ 2 := by
    dsimp [upper]
    rw [div_pow]
    exact (le_div_iff₀ (sq_pos_of_pos hscale)).mpr hnext.le
  have hlower_nonneg : (0 : ℝ) ≤ (lower : ℚ) := by
    exact_mod_cast (show (0 : ℚ) ≤ lower from div_nonneg (Nat.cast_nonneg _) hscale.le)
  apply (containsReal_some_iff _ _).2
  change (lower : ℝ) ≤ Real.sqrt (x : ℝ) ∧
    Real.sqrt (x : ℝ) ≤ ((if lower ^ 2 = x then lower else upper : ℚ) : ℝ)
  refine ⟨Real.le_sqrt_of_sq_le (by exact_mod_cast hlower), ?_⟩
  by_cases heq : lower ^ 2 = x
  · simp only [heq, ↓reduceIte]
    have hxreal : (x : ℝ) = (lower : ℝ) ^ 2 := by exact_mod_cast heq.symm
    rw [hxreal, Real.sqrt_sq hlower_nonneg]
  · simp only [heq, ↓reduceIte]
    apply (Real.sqrt_le_left ?_).2 (by exact_mod_cast hupper)
    exact_mod_cast
      (show (0 : ℚ) ≤ upper from div_nonneg (by positivity) hscale.le)

/-- The point square-root enclosure is at most one dyadic grid step wide. -/
theorem sqrtPointBounds_width_le (x : ℚ) (precision : Nat) :
    (sqrtPointBounds x precision).hi - (sqrtPointBounds x precision).lo ≤
      1 / (2 : ℚ) ^ precision := by
  dsimp [sqrtPointBounds]
  split_ifs
  · simp
  · simp only [add_div, add_sub_cancel_left, le_refl]

/-- Successful dyadic square-root bounds contain the image of every enclosed real value. -/
theorem containsReal_sqrtBounds? {I K : Interval ℚ} {precision : Nat}
    (h : sqrtBounds? I precision = some K) {x : ℝ} (hx : I.ContainsReal some x) :
    K.ContainsReal some (Real.sqrt x) := by
  unfold sqrtBounds? at h
  split at h
  · rename_i hnonneg
    cases h
    apply containsReal_monotoneBounds _ Real.sqrt I (Real.sqrt_monotone.monotoneOn _) ?_ hx
    intro q hq
    exact containsReal_sqrtPointBounds q precision (hnonneg.trans hq.1)
  · simp at h

end FloatLib.Numerics.Interval
