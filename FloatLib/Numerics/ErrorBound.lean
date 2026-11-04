/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.Real
public import FloatLib.Numerics.MixedError.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Absolute error propagation

These lemmas compose absolute errors `|actual - reference| ≤ error` through exact real operations,
whatever the number format. Each one adds the local error of an operation to the propagated errors
of its operands, as the `roundoff` analysis does node by node.

- A real power propagates the error of its base with an exact exponent, and both errors at a
  positive base.
- Branches keep the case that the program selects.
- An error below the reference's magnitude keeps the sign of the result.
- A rational enclosure of the reference bounds the error of any candidate.

Last come the mixed-error branch rule and the order facts that the analysis applies.
-/

@[expose] public section

namespace FloatLib.Numerics

noncomputable section

/-- An exact input introduces no arithmetic error. -/
theorem exact_error (x : ℝ) : |x - x| ≤ 0 := by simp

/-- Numerical interpretation and propagation of input errors are independent proof steps. -/
theorem compose_error {actual intermediate reference localError inputError : ℝ}
    (hlocal : |actual - intermediate| ≤ localError)
    (hinput : |intermediate - reference| ≤ inputError) :
    |actual - reference| ≤ inputError + localError :=
  ((abs_sub_le actual intermediate reference).trans (add_le_add hlocal hinput)).trans_eq
    (add_comm localError inputError)

/-- A Lipschitz function scales the input error before the implementation's local error is added. -/
theorem lipschitz_error {f : ℝ → ℝ} {constant : NNReal}
    {a x result inputError localError : ℝ} (hf : LipschitzWith constant f)
    (hinput : |a - x| ≤ inputError) (hlocal : |result - f a| ≤ localError) :
    |result - f x| ≤ (constant : ℝ) * inputError + localError := by
  have difference : |f a - f x| ≤ (constant : ℝ) * inputError := by
    simpa only [Real.dist_eq] using hf.dist_le_mul_of_le
      (show dist a x ≤ inputError by simpa only [Real.dist_eq] using hinput)
  exact compose_error hlocal difference

/-- A derivative bound is needed only on the interval between the two inputs. -/
theorem derivative_error {f : ℝ → ℝ}
    {a x result inputError localError derivativeBound : ℝ} (hbound : 0 ≤ derivativeBound)
    (hdifferentiable : ∀ y ∈ Set.Icc (min a x) (max a x), DifferentiableAt ℝ f y)
    (hderivative : ∀ y ∈ Set.Icc (min a x) (max a x), |deriv f y| ≤ derivativeBound)
    (hinput : |a - x| ≤ inputError) (hlocal : |result - f a| ≤ localError) :
    |result - f x| ≤ derivativeBound * inputError + localError := by
  have difference : |f a - f x| ≤ derivativeBound * |a - x| := by
    simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_deriv_le
      (𝕜 := ℝ) (s := Set.Icc (min a x) (max a x)) (f := f) (C := derivativeBound)
      hdifferentiable
      (fun y hy => by simpa only [Real.norm_eq_abs] using hderivative y hy)
      (convex_Icc _ _) (Set.mem_Icc.mpr ⟨min_le_right _ _, le_max_right _ _⟩)
      (Set.mem_Icc.mpr ⟨min_le_left _ _, le_max_left _ _⟩)
  exact compose_error hlocal (difference.trans (mul_le_mul_of_nonneg_left hinput hbound))

/-- Negation introduces no additional rounding. -/
theorem neg_error {actual reference error : ℝ} (h : |actual - reference| ≤ error) :
    |-actual - -reference| ≤ error := by simpa only [neg_sub_neg, abs_sub_comm] using h

/-- Absolute value does not amplify its input error, including when the sign changes. -/
theorem abs_error {actual reference error : ℝ} (h : |actual - reference| ≤ error) :
    abs (|actual| - |reference|) ≤ error :=
  (abs_abs_sub_abs_le_abs_sub actual reference).trans h

/-- A maximum propagates both input errors without requiring agreement on the winning input. -/
theorem max_error {a b x y firstError secondError : ℝ}
    (ha : |a - x| ≤ firstError) (hb : |b - y| ≤ secondError) :
    |max a b - max x y| ≤ max firstError secondError :=
  (abs_max_sub_max_le_max a b x y).trans (max_le_max ha hb)

/-- A minimum has the same perturbation bound as a maximum. -/
theorem min_error {a b x y firstError secondError : ℝ}
    (ha : |a - x| ≤ firstError) (hb : |b - y| ≤ secondError) :
    |min a b - min x y| ≤ max firstError secondError :=
  (abs_min_sub_min_le_max a b x y).trans (max_le_max ha hb)

/-- Square root propagates input error without requiring a positive lower margin. The bound
also covers a real reference below zero, where `Real.sqrt` is totalized to zero. -/
theorem sqrt_error {a x result inputError localError : ℝ}
    (hinput : |a - x| ≤ inputError)
    (hlocal : |result - Real.sqrt a| ≤ localError) :
    |result - Real.sqrt x| ≤ Real.sqrt inputError + localError := by
  have he : 0 ≤ inputError := (abs_nonneg _).trans hinput
  have root_le (u v : ℝ) (hu : u ≤ v + inputError) :
      Real.sqrt u ≤ Real.sqrt v + Real.sqrt inputError := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ?_⟩
    have hv : v ≤ Real.sqrt v ^ 2 := by
      rw [Real.sq_sqrt']
      exact le_max_left _ _
    nlinarith [Real.sq_sqrt he,
      mul_nonneg (Real.sqrt_nonneg v) (Real.sqrt_nonneg inputError)]
  have lower := root_le x a (by linarith [(abs_le.mp hinput).1])
  have upper := root_le a x (by linarith [(abs_le.mp hinput).2])
  exact compose_error hlocal (abs_le.mpr ⟨by linarith, by linarith⟩)

/-- The error of a square root propagated from an input error `e` between `a` and `x`: the
smaller of the Hölder bound `√e` and the Lipschitz bound `e / (√a + √x)` of the two roots. -/
def sqrtError (e a x : ℝ) : ℝ := min (Real.sqrt e) (e / (Real.sqrt a + Real.sqrt x))

/-- The propagated square-root error is at most the Hölder bound `√e`. -/
theorem sqrtError_le_sqrt (e a x : ℝ) : sqrtError e a x ≤ Real.sqrt e := min_le_left _ _

/-- Square root propagates an input error `e` as `sqrtError e a x`, the Hölder bound near zero
and the Lipschitz bound of the two square roots elsewhere. -/
theorem sqrt_error_min {a x result inputError localError : ℝ}
    (hinput : |a - x| ≤ inputError)
    (hlocal : |result - Real.sqrt a| ≤ localError) :
    |result - Real.sqrt x| ≤ sqrtError inputError a x + localError := by
  have holder : |Real.sqrt a - Real.sqrt x| ≤ Real.sqrt inputError := by
    simpa using sqrt_error hinput (show |Real.sqrt a - Real.sqrt a| ≤ 0 by simp)
  have lipschitz : |Real.sqrt a - Real.sqrt x| ≤ inputError / (Real.sqrt a + Real.sqrt x) :=
    (abs_sqrt_sub_sqrt_le_div_add a x).trans
      (div_le_div_of_nonneg_right hinput (by positivity))
  exact compose_error hlocal (le_min holder lipschitz)

/-- The exponential's derivative on the interval between the inputs bounds its input error. -/
theorem exp_error {a x result inputError localError : ℝ}
    (hinput : |a - x| ≤ inputError)
    (hlocal : |result - Real.exp a| ≤ localError) :
    |result - Real.exp x| ≤ Real.exp (max a x) * inputError + localError := by
  apply derivative_error (Real.exp_nonneg _)
    (fun _ _ => Real.differentiableAt_exp) _ hinput hlocal
  intro value hvalue
  simpa only [Real.deriv_exp, abs_of_pos (Real.exp_pos value)] using
    Real.exp_le_exp.mpr hvalue.2

/-- On the interval between `a` and `x`, a power `|t| ^ e` of the magnitude is at most its larger
value at the ends, when `e ≥ 0` or the interval does not contain zero. -/
private theorem abs_rpow_le_max {a x t e : ℝ} (ht : t ∈ Set.Icc (min a x) (max a x))
    (hsign : 0 < a * x ∨ 0 ≤ e) : |t| ^ e ≤ max (|a| ^ e) (|x| ^ e) := by
  obtain ⟨lower, upper⟩ := ht
  have hend : ∀ u, u = |a| ∨ u = |x| → u ^ e ≤ max (|a| ^ e) (|x| ^ e) := by
    rintro u (rfl | rfl)
    · exact le_max_left _ _
    · exact le_max_right _ _
  have choose : ∀ (f : ℝ → ℝ → ℝ), (f |a| |x| = |a| ∨ f |a| |x| = |x|) →
      f |a| |x| ^ e ≤ max (|a| ^ e) (|x| ^ e) := fun f h => hend _ h
  have hmax : |t| ≤ max |a| |x| := by
    rcases le_total a x with h | h
    · rw [min_eq_left h] at lower; rw [max_eq_right h] at upper
      exact abs_le.2 ⟨by linarith [neg_abs_le a, le_max_left |a| |x|], by
        linarith [le_abs_self x, le_max_right |a| |x|]⟩
    · rw [min_eq_right h] at lower; rw [max_eq_left h] at upper
      exact abs_le.2 ⟨by linarith [neg_abs_le x, le_max_right |a| |x|], by
        linarith [le_abs_self a, le_max_left |a| |x|]⟩
  have monotone (he : 0 ≤ e) : |t| ^ e ≤ max (|a| ^ e) (|x| ^ e) :=
    (Real.rpow_le_rpow (abs_nonneg t) hmax he).trans
      (choose max (by rcases le_total |a| |x| with h | h
                      · exact .inr (max_eq_right h)
                      · exact .inl (max_eq_left h)))
  rcases hsign with hsame | he
  · rcases le_total 0 e with he | he
    · exact monotone he
    have hmin : 0 < min |a| |x| ∧ min |a| |x| ≤ |t| := by
      rcases pos_and_pos_or_neg_and_neg_of_mul_pos hsame with ⟨ha, hx⟩ | ⟨ha, hx⟩
      · have ht : 0 < t := lt_of_lt_of_le (lt_min ha hx) lower
        rw [abs_of_pos ha, abs_of_pos hx, abs_of_pos ht]
        exact ⟨lt_min ha hx, lower⟩
      · have ht : t < 0 := lt_of_le_of_lt upper (max_lt ha hx)
        rw [abs_of_neg ha, abs_of_neg hx, abs_of_neg ht]
        refine ⟨lt_min (by linarith) (by linarith), ?_⟩
        rcases le_total a x with h | h
        · rw [max_eq_right h] at upper; exact min_le_of_right_le (by linarith)
        · rw [max_eq_left h] at upper; exact min_le_of_left_le (by linarith)
    exact (Real.rpow_le_rpow_of_nonpos hmin.1 hmin.2 he).trans
      (choose min (by rcases le_total |a| |x| with h | h
                      · exact .inl (min_eq_left h)
                      · exact .inr (min_eq_right h)))
  · exact monotone he

/-- A point between two values of the same sign is not zero. -/
private theorem ne_zero_of_mem_of_mul_pos {a x t : ℝ} (ht : t ∈ Set.Icc (min a x) (max a x))
    (hsame : 0 < a * x) : t ≠ 0 := by
  obtain ⟨lower, upper⟩ := ht
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos hsame with ⟨ha, hx⟩ | ⟨ha, hx⟩
  · exact (lt_of_lt_of_le (lt_min ha hx) lower).ne'
  · exact (lt_of_le_of_lt upper (max_lt ha hx)).ne

/-- A real power with an exact exponent `y` propagates the error of its base with the slope
`|y| * |t| ^ (y - 1)` at the larger end, when the base keeps its sign or `1 ≤ y`. -/
theorem rpow_const_error {a b x y result baseError localError : ℝ}
    (hsign : 0 < a * x ∨ 1 ≤ y) (hbase : |a - x| ≤ baseError) (hexponent : |b - y| ≤ 0)
    (hlocal : |result - a ^ b| ≤ localError) :
    |result - x ^ y| ≤ |y| * max (|a| ^ (y - 1)) (|x| ^ (y - 1)) * baseError + localError := by
  obtain rfl : b = y := sub_eq_zero.mp (abs_nonpos_iff.mp hexponent)
  have hderiv : ∀ t ∈ Set.Icc (min a x) (max a x),
      HasDerivAt (fun t => t ^ b) (b * t ^ (b - 1)) t := fun t ht =>
    Real.hasDerivAt_rpow_const (hsign.imp (ne_zero_of_mem_of_mul_pos ht) id)
  refine derivative_error (f := fun t => t ^ b) (by positivity)
    (fun t ht => (hderiv t ht).differentiableAt) ?_ hbase hlocal
  intro t ht
  rw [(hderiv t ht).deriv, abs_mul]
  gcongr
  exact (Real.abs_rpow_le_abs_rpow t (b - 1)).trans
    (abs_rpow_le_max ht (hsign.imp id fun h => by linarith))

/-- A real power of a positive base propagates the errors of its base and its exponent, each by
the mean value theorem with the larger slope at the ends of its interval. -/
theorem rpow_error {a b x y result baseError exponentError localError : ℝ}
    (ha : 0 < a) (hx : 0 < x) (hbase : |a - x| ≤ baseError) (hexponent : |b - y| ≤ exponentError)
    (hlocal : |result - a ^ b| ≤ localError) :
    |result - x ^ y| ≤ |b| * max (a ^ (b - 1)) (x ^ (b - 1)) * baseError +
      max (x ^ b) (x ^ y) * |Real.log x| * exponentError + localError := by
  have base : |a ^ b - x ^ b| ≤ |b| * max (a ^ (b - 1)) (x ^ (b - 1)) * baseError + 0 := by
    simpa only [abs_of_pos ha, abs_of_pos hx] using rpow_const_error (.inl (mul_pos ha hx)) hbase
      (by simp) (show |a ^ b - a ^ b| ≤ 0 by simp)
  have hderiv : ∀ s : ℝ, HasDerivAt (fun s : ℝ => x ^ s) (x ^ s * Real.log x) s := fun s =>
    (Real.hasStrictDerivAt_const_rpow hx s).hasDerivAt
  have exponent : |x ^ b - x ^ y| ≤ max (x ^ b) (x ^ y) * |Real.log x| * exponentError + 0 := by
    refine derivative_error (f := fun s : ℝ => x ^ s) (by positivity)
      (fun s _ => (hderiv s).differentiableAt) ?_ hexponent (by simp)
    intro s ⟨lower, upper⟩
    rw [(hderiv s).deriv, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hx s)]
    gcongr
    rcases le_total 1 x with hx1 | hx1
    · refine (Real.rpow_le_rpow_of_exponent_le hx1 upper).trans ?_
      rcases le_total b y with h | h
      · rw [max_eq_right h]; exact le_max_right _ _
      · rw [max_eq_left h]; exact le_max_left _ _
    · refine (Real.rpow_le_rpow_of_exponent_ge hx hx1 lower).trans ?_
      rcases le_total b y with h | h
      · rw [min_eq_left h]; exact le_max_left _ _
      · rw [min_eq_right h]; exact le_max_right _ _
  calc |result - x ^ y| ≤ |result - a ^ b| + (|a ^ b - x ^ b| + |x ^ b - x ^ y|) := by
        have := abs_sub_le (a ^ b) (x ^ b) (x ^ y)
        have := abs_sub_le result (a ^ b) (x ^ y)
        linarith
    _ ≤ _ := by linarith

/-- Logarithmic input error needs a positive margin for both the computed and reference values. -/
theorem log_error {a x result inputError localError : ℝ} (ha : 0 < a) (hx : 0 < x)
    (hinput : |a - x| ≤ inputError)
    (hlocal : |result - Real.log a| ≤ localError) :
    |result - Real.log x| ≤ inputError / min a x + localError := by
  have hmin : 0 < min a x := lt_min ha hx
  have estimate : |result - Real.log x| ≤ (1 / min a x) * inputError + localError := by
    apply derivative_error (le_of_lt (one_div_pos.mpr hmin))
      (fun value hvalue =>
        Real.differentiableAt_log (lt_of_lt_of_le hmin hvalue.1).ne') _ hinput hlocal
    intro value hvalue
    have hpositive := lt_of_lt_of_le hmin hvalue.1
    simpa [Real.deriv_log, abs_of_pos hpositive, one_div] using
      one_div_le_one_div_of_le hmin hvalue.1
  simpa only [one_div, div_eq_mul_inv, mul_one, mul_comm] using
    estimate

/-- Sine does not amplify the input error. -/
theorem sin_error {a x result inputError localError : ℝ}
    (hinput : |a - x| ≤ inputError) (hlocal : |result - Real.sin a| ≤ localError) :
    |result - Real.sin x| ≤ inputError + localError := by
  simpa only [NNReal.coe_one, one_mul] using
    lipschitz_error Real.lipschitzWith_sin hinput hlocal

/-- Cosine has the same global input-error bound as sine. -/
theorem cos_error {a x result inputError localError : ℝ}
    (hinput : |a - x| ≤ inputError) (hlocal : |result - Real.cos a| ≤ localError) :
    |result - Real.cos x| ≤ inputError + localError := by
  simpa only [NNReal.coe_one, one_mul] using
    lipschitz_error Real.lipschitzWith_cos hinput hlocal

/-- Hyperbolic tangent has slope at most one on the whole real line. -/
theorem tanh_error {a x result inputError localError : ℝ}
    (hinput : |a - x| ≤ inputError) (hlocal : |result - Real.tanh a| ≤ localError) :
    |result - Real.tanh x| ≤ inputError + localError := by
  have derivative (value : ℝ) : HasDerivAt Real.tanh (1 / Real.cosh value ^ 2) value := by
    convert (Real.hasDerivAt_sinh value).div (Real.hasDerivAt_cosh value)
      (Real.cosh_pos value).ne' using 1
    · funext point
      exact Real.tanh_eq_sinh_div_cosh point
    · simp only [← pow_two, Real.cosh_sq_sub_sinh_sq]
  have bound (value : ℝ) : |deriv Real.tanh value| ≤ (1 : ℝ) := by
    rw [(derivative value).deriv,
      abs_of_nonneg (one_div_nonneg.mpr (sq_nonneg (Real.cosh value)))]
    apply (div_le_one (sq_pos_of_pos (Real.cosh_pos value))).mpr
    nlinarith [Real.one_le_cosh value, sq_nonneg (Real.cosh value - 1)]
  simpa only [one_mul] using derivative_error (f := Real.tanh) (derivativeBound := 1)
    zero_le_one (fun value _ => (derivative value).differentiableAt)
    (fun value _ => bound value) hinput hlocal

private theorem abs_le_input_radius {a x value : ℝ}
    (hvalue : value ∈ Set.Icc (min a x) (max a x)) : |value| ≤ max |a| |x| := by
  rcases le_total a x with h | h
  · simp only [min_eq_left h, max_eq_right h] at hvalue
    exact abs_le_max_abs_abs hvalue.1 hvalue.2
  · simp only [min_eq_right h, max_eq_left h] at hvalue
    exact (abs_le_max_abs_abs hvalue.1 hvalue.2).trans_eq (max_comm _ _)

private theorem cosh_le_input_radius {a x value : ℝ}
    (hvalue : value ∈ Set.Icc (min a x) (max a x)) :
    Real.cosh value ≤ Real.cosh (max |a| |x|) := by
  apply Real.cosh_le_cosh.mpr
  rw [abs_of_nonneg ((abs_nonneg a).trans (le_max_left _ _))]
  exact abs_le_input_radius hvalue

/-- Hyperbolic sine uses a derivative bound over the inputs' absolute radius. -/
theorem sinh_error {a x result inputError localError : ℝ}
    (hinput : |a - x| ≤ inputError) (hlocal : |result - Real.sinh a| ≤ localError) :
    |result - Real.sinh x| ≤ Real.cosh (max |a| |x|) * inputError + localError := by
  apply derivative_error (Real.cosh_pos _).le
    (fun _ _ => Real.differentiableAt_sinh) _ hinput hlocal
  intro value hvalue
  simpa only [Real.deriv_sinh, abs_of_pos (Real.cosh_pos value)] using
    cosh_le_input_radius hvalue

/-- Hyperbolic cosine uses the same local derivative bound as hyperbolic sine. -/
theorem cosh_error {a x result inputError localError : ℝ}
    (hinput : |a - x| ≤ inputError) (hlocal : |result - Real.cosh a| ≤ localError) :
    |result - Real.cosh x| ≤ Real.cosh (max |a| |x|) * inputError + localError := by
  apply derivative_error (Real.cosh_pos _).le
    (fun _ _ => Real.differentiableAt_cosh) _ hinput hlocal
  intro value hvalue
  have hsinh : |Real.sinh value| ≤ Real.cosh value := by
    simpa only [Real.abs_sinh, Real.cosh_abs] using (Real.sinh_lt_cosh (x := |value|)).le
  simpa only [Real.deriv_cosh] using hsinh.trans (cosh_le_input_radius hvalue)

/--
Analyze the branch the program selects. Conditions on an inactive branch don't matter, and agreement
with a different, real-valued branch test needs a proof of its own.
-/
theorem dite_error {α : Type*} (observe : α → ℝ) (condition : Prop) [Decidable condition]
    (yes : condition → α) (no : ¬condition → α)
    {yesReference yesError : condition → ℝ} {noReference noError : ¬condition → ℝ}
    (hyes : ∀ h, |observe (yes h) - yesReference h| ≤ yesError h)
    (hno : ∀ h, |observe (no h) - noReference h| ≤ noError h) :
    |observe (if h : condition then yes h else no h) -
        (if h : condition then yesReference h else noReference h)| ≤
      if h : condition then yesError h else noError h := by
  split_ifs with h
  · exact hyes h
  · exact hno h

/--
An error strictly smaller than the reference's magnitude keeps the actual value nonzero. The margin
is `|reference| - error > 0`, which depends on the reference, so no fixed tolerance is involved.
-/
theorem nonzero_of_error_lt {actual reference error : ℝ}
    (herror : |actual - reference| ≤ error) (hsmall : error < |reference|) : actual ≠ 0 := by
  intro hzero
  subst actual
  simp only [zero_sub, abs_neg] at herror
  exact (not_lt_of_ge herror) hsmall

/-- A positive reference larger than the error budget gives a strictly positive result. -/
theorem positive_of_error_lt {actual reference error : ℝ}
    (herror : |actual - reference| ≤ error) (hsmall : error < reference) : 0 < actual := by
  have lower := (abs_le.mp herror).1
  linarith

/-- Compose input perturbations with the error of the operation actually executed. -/
theorem add_error {a b x y r ea eb er : ℝ}
    (ha : |a - x| ≤ ea) (hb : |b - y| ≤ eb)
    (hr : |r - (a + b)| ≤ er) :
    |r - (x + y)| ≤ ea + eb + er := by
  have hp : |(a + b) - (x + y)| ≤ ea + eb := by
    rw [add_sub_add_comm]
    exact (abs_add_le _ _).trans (add_le_add ha hb)
  exact ((abs_sub_le r (a + b) (x + y)).trans (add_le_add hr hp)).trans_eq
    (add_comm er (ea + eb))

/-- Subtraction retains both input errors even when its exact result is very small. -/
theorem sub_error {a b x y r ea eb er : ℝ}
    (ha : |a - x| ≤ ea) (hb : |b - y| ≤ eb)
    (hr : |r - (a - b)| ≤ er) :
    |r - (x - y)| ≤ ea + eb + er := by
  have hp : |(a - b) - (x - y)| ≤ ea + eb := by
    have he : (a - b) - (x - y) = (a - x) - (b - y) := by ring
    rw [he]
    exact (abs_sub _ _).trans (add_le_add ha hb)
  exact ((abs_sub_le r (a - b) (x - y)).trans (add_le_add hr hp)).trans_eq
    (add_comm er (ea + eb))

/-- An asymmetric product bound avoids discarding the higher-order input error.
One factor is the computed value and the other is the exact reference value. -/
theorem mul_error {a b x y r ea eb er : ℝ}
    (ha : |a - x| ≤ ea) (hb : |b - y| ≤ eb)
    (hr : |r - a * b| ≤ er) :
    |r - x * y| ≤ |b| * ea + |x| * eb + er := by
  have hp : |a * b - x * y| ≤ |b| * ea + |x| * eb := by
    calc
      |a * b - x * y| = |(a - x) * b + x * (b - y)| := by congr 1; ring
      _ ≤ |(a - x) * b| + |x * (b - y)| := abs_add_le _ _
      _ = |b| * |a - x| + |x| * |b - y| := by rw [abs_mul, abs_mul]; ring
      _ ≤ |b| * ea + |x| * eb :=
        add_le_add (mul_le_mul_of_nonneg_left ha (abs_nonneg b))
          (mul_le_mul_of_nonneg_left hb (abs_nonneg x))
  exact ((abs_sub_le r (a * b) (x * y)).trans (add_le_add hr hp)).trans_eq
    (add_comm er (|b| * ea + |x| * eb))

/-- Division exposes both the computed and reference denominator.
The reference denominator must be nonzero independently of the floating-point zero test. -/
theorem div_error {a b x y r ea eb er : ℝ} (hb0 : b ≠ 0) (hy0 : y ≠ 0)
    (ha : |a - x| ≤ ea) (hb : |b - y| ≤ eb)
    (hr : |r - a / b| ≤ er) :
    |r - x / y| ≤ ea / |b| + |x| * eb / (|b| * |y|) + er := by
  have hp : |a / b - x / y| ≤ ea / |b| + |x| * eb / (|b| * |y|) := by
    calc
      |a / b - x / y| = |(a - x) / b + x * (y - b) / (b * y)| := by
        congr 1
        field_simp
        ring
      _ ≤ |(a - x) / b| + |x * (y - b) / (b * y)| := abs_add_le _ _
      _ = |a - x| / |b| + |x| * |b - y| / (|b| * |y|) := by
        rw [abs_div, abs_div, abs_mul, abs_mul, abs_sub_comm y b]
      _ ≤ ea / |b| + |x| * eb / (|b| * |y|) :=
        add_le_add (div_le_div_of_nonneg_right ha (abs_nonneg b))
          (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hb (abs_nonneg x))
            (mul_nonneg (abs_nonneg b) (abs_nonneg y)))
  exact ((abs_sub_le r (a / b) (x / y)).trans (add_le_add hr hp)).trans_eq
    (add_comm er (ea / |b| + |x| * eb / (|b| * |y|)))

/-- Distance to the farther endpoint bounds the error of any candidate against a real value
in the interval. The candidate itself need not belong to the interval. -/
theorem enclosure_error {reference : ℝ} {bounds : Interval Rat} (candidate : ℝ)
    (contained : bounds.ContainsReal some reference) :
    |candidate - reference| ≤
      max |candidate - (bounds.lo : ℝ)| |candidate - (bounds.hi : ℝ)| := by
  obtain ⟨lower, upper⟩ := (Interval.containsReal_some_iff bounds reference).mp contained
  apply abs_le.mpr
  constructor
  · have lowerDistance := neg_abs_le (candidate - (bounds.hi : ℝ))
    have largest := le_max_right |candidate - (bounds.lo : ℝ)| |candidate - (bounds.hi : ℝ)|
    linarith
  · have upperDistance := le_abs_self (candidate - (bounds.lo : ℝ))
    have largest := le_max_left |candidate - (bounds.lo : ℝ)| |candidate - (bounds.hi : ℝ)|
    linarith

/-- A dependent branch has the mixed bound of the branch it selects. -/
theorem mixedError_dite {α : Type*} (observe : α → ℝ) (condition : Prop) [Decidable condition]
    (yes : condition → α) (no : ¬condition → α)
    {yesReference yesRelative yesAbsolute : condition → ℝ}
    {noReference noRelative noAbsolute : ¬condition → ℝ}
    (hyes : ∀ h, MixedError (observe (yes h)) (yesReference h) (yesRelative h) (yesAbsolute h))
    (hno : ∀ h, MixedError (observe (no h)) (noReference h) (noRelative h) (noAbsolute h)) :
    MixedError (observe (if h : condition then yes h else no h))
      (if h : condition then yesReference h else noReference h)
      (if h : condition then yesRelative h else noRelative h)
      (if h : condition then yesAbsolute h else noAbsolute h) := by
  split_ifs with h
  · exact hyes h
  · exact hno h

/-- A property of both cases of a dependent `if` holds of the case it selects. -/
theorem dite_of_forall {α : Sort*} {P : α → Prop} {c : Prop} [Decidable c] {yes : c → α}
    {no : ¬c → α} (hyes : ∀ h, P (yes h)) (hno : ∀ h, P (no h)) : P (dite c yes no) := by
  split_ifs with h
  exacts [hyes h, hno h]

/-- A nonnegative real is above `-1`. -/
theorem neg_one_lt_of_nonneg {x : ℝ} (h : 0 ≤ x) : -1 < x :=
  neg_one_lt_zero.trans_le h

/-- A real is above `-1` when the lower end of an enclosure of one plus it is positive. -/
theorem neg_one_lt_of_mixedError_one_add {x c r a : ℝ} (h : MixedError (1 + x) c r a)
    (hm : 0 < c - (r * |c| + a)) : -1 < x := by
  linarith [h.lower_le]

/-- A nonpositive real minus a positive one is negative. -/
theorem sub_neg_of_nonpos_of_pos {a b : ℝ} (ha : a ≤ 0) (hb : 0 < b) : a - b < 0 := by
  linarith

end

end FloatLib.Numerics
