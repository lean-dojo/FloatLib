/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.Inverse
public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.LogarithmProof
public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.ExponentialProof
public import FloatLib.Numerics.Enclosure.Expression.ClosedProof

/-!
# The complex inverse sines and cosines are correctly rounded

For every IEEE binary format, every rounding direction and every finite argument, each part of
`ExecComplex.asinh`, `asin`, `acosh` and `acos` is the exact part rounded once (`asinh_eq`,
`asin_eq`, `acosh_eq`, `acos_eq`).

The exact results are stated with the real inverse functions of Mathlib at the confocal
coordinates of the argument (`asinhValue`, `acoshValue`). They are the principal values:
`sinh_asinhValue` and `cosh_acoshValue` prove that `Complex.sinh` and `Complex.cosh` invert them
in the closed right half-plane and in the closed upper half-plane, and their parts lie in the
principal ranges (`asinhValue_re_nonneg`, `abs_asinhValue_im_le`, `acoshValue_re_nonneg`,
`acoshValue_im_mem`). `ValueProof` identifies them there with the principal expressions in
Mathlib's `Complex.log` and square root (`asinhValue_eq_log`, `acoshValue_eq_log`).
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace ExecComplex

open FloatLib.Numerics
open ConfocalComparison (major minor)

variable {fmt : FloatFormat}

/-- The clamped closed expression of the half difference of the distances denotes it. -/
theorem eval_minorExpr (p q : Rat) :
    (minorExpr p q).eval (fun _ => 0) = minor p q := by
  have hlower := ConfocalComparison.neg_one_le_minor (p : ℝ) q
  have hupper := ConfocalComparison.minor_le_one (p : ℝ) q
  have hraw : (√((p : ℝ) ^ 2 + ((q : ℝ) + 1) ^ 2) - √((p : ℝ) ^ 2 + ((q : ℝ) - 1) ^ 2)) / 2 =
      minor p q := rfl
  simp only [minorExpr, Interval.Expr.eval, Interval.BinaryOp.eval, Interval.UnaryOp.eval]
  push_cast
  rw [hraw, min_eq_right hupper, max_eq_right hlower]

/-- The half-angle expression denotes `2 arctan √((1 - m) / (1 + m))`. -/
theorem eval_halfAngleExpr (m : Interval.Expr) (values : Nat → ℝ) :
    (halfAngleExpr m).eval values =
      2 * Real.arctan (√((1 - m.eval values) / (1 + m.eval values))) := by
  simp [halfAngleExpr, Interval.Expr.eval, Interval.BinaryOp.eval, Interval.UnaryOp.eval]

/-- The closed expression of the inverse cosine of the half difference denotes it. -/
theorem eval_arccosExpr (p q : Rat) :
    (arccosExpr p q).eval (fun _ => 0) = Real.arccos (minor p q) := by
  unfold arccosExpr
  split
  · rename_i hq
    rw [eval_halfAngleExpr, eval_minorExpr]
    exact (ConfocalComparison.arccos_eq_two_mul_arctan
      (ConfocalComparison.minor_nonneg (p := (p : ℝ)) (by exact_mod_cast hq))
      (ConfocalComparison.minor_le_one _ _)).symm
  · rename_i hq
    have hneg : (0 : ℝ) ≤ ((-q : Rat) : ℝ) := by
      have : (q : ℝ) < 0 := by exact_mod_cast not_le.mp hq
      push_cast
      linarith
    have hvalue := ConfocalComparison.arccos_eq_two_mul_arctan
      (ConfocalComparison.minor_nonneg (p := (p : ℝ)) hneg) (ConfocalComparison.minor_le_one _ _)
    simp only [Interval.Expr.eval, Interval.BinaryOp.eval, Interval.UnaryOp.eval,
      eval_halfAngleExpr, eval_minorExpr]
    rw [← hvalue]
    push_cast
    rw [ConfocalComparison.minor_neg, Real.arccos_neg, Real.arcsin_one]
    ring

/-- The closed expression of the inverse sine of the half difference denotes it. -/
theorem eval_arcsinExpr (p q : Rat) :
    (arcsinExpr p q).eval (fun _ => 0) = Real.arcsin (minor p q) := by
  unfold arcsinExpr
  split
  · simp only [Interval.Expr.eval, Interval.UnaryOp.eval, eval_minorExpr]
  · split
    · rename_i hq
      have hvalue := ConfocalComparison.arccos_eq_two_mul_arctan
        (ConfocalComparison.minor_nonneg (p := (p : ℝ))
          (by exact_mod_cast hq : (0 : ℝ) ≤ (q : ℝ)))
        (ConfocalComparison.minor_le_one _ _)
      simp only [Interval.Expr.eval, Interval.BinaryOp.eval, Interval.UnaryOp.eval,
        eval_halfAngleExpr, eval_minorExpr]
      rw [← hvalue]
      push_cast
      rw [Real.arcsin_one, Real.arcsin_eq_pi_div_two_sub_arccos]
    · rename_i hq
      have hneg : (0 : ℝ) ≤ ((-q : Rat) : ℝ) := by
        have : (q : ℝ) < 0 := by exact_mod_cast not_le.mp hq
        push_cast
        linarith
      have hvalue := ConfocalComparison.arccos_eq_two_mul_arctan
        (ConfocalComparison.minor_nonneg (p := (p : ℝ)) hneg)
        (ConfocalComparison.minor_le_one _ _)
      simp only [Interval.Expr.eval, Interval.BinaryOp.eval, Interval.UnaryOp.eval,
        eval_halfAngleExpr, eval_minorExpr]
      rw [← hvalue]
      push_cast
      rw [ConfocalComparison.minor_neg, Real.arccos_neg, Real.arcsin_one,
        Real.arcsin_eq_pi_div_two_sub_arccos]
      ring

/-- Every enclosure that `exprEnclosure?` returns contains the value of the expression. -/
theorem contains_exprEnclosure? {e : Interval.Expr} {extra : Nat} {interval : RationalInterval}
    (h : exprEnclosure? fmt e extra = some interval) : interval.Contains (e.eval fun _ => 0) :=
  contains_of_refineTwice (fun _ _ henclosure => Interval.Expr.contains_gridEnclosure? henclosure)
    interval h

/-- The bounds of `majorBounds` enclose the half sum of the distances, and the lower one is at
least one. -/
theorem majorBounds_spec (p q : Rat) (precision : Nat) :
    1 ≤ (majorBounds p q precision).1 ∧ ((majorBounds p q precision).1 : ℝ) ≤ major p q ∧
      major p q ≤ ((majorBounds p q precision).2 : ℝ) := by
  have hmajor := ConfocalComparison.one_le_major (p : ℝ) q
  have hnear := (Interval.containsReal_some_iff _ _).mp
    (Interval.containsReal_sqrtPointBounds (p ^ 2 + (q + 1) ^ 2) precision (by positivity))
  have hfar := (Interval.containsReal_some_iff _ _).mp
    (Interval.containsReal_sqrtPointBounds (p ^ 2 + (q - 1) ^ 2) precision (by positivity))
  push_cast at hnear hfar
  refine ⟨le_max_left _ _, ?_, ?_⟩
  · simp only [majorBounds]
    push_cast
    refine max_le hmajor ?_
    unfold major
    linarith [hnear.1, hfar.1]
  · simp only [majorBounds]
    push_cast
    unfold major
    linarith [hnear.2, hfar.2]

/-- `arcoshLower` at a rational lower bound of `y` is below `arcosh y`. -/
theorem arcoshLower_le {x : Rat} {y : ℝ} (hx : 1 ≤ x) (hxy : (x : ℝ) ≤ y) (precision : Nat) :
    (arcoshLower x precision : ℝ) ≤ Real.arcosh y := by
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hroot := ((Interval.containsReal_some_iff _ _).mp
    (Interval.containsReal_sqrtPointBounds (x ^ 2 - 1) precision (by nlinarith))).1
  push_cast at hroot
  have hmono : √((x : ℝ) ^ 2 - 1) ≤ √(y ^ 2 - 1) := Real.sqrt_le_sqrt (by nlinarith)
  have hargument : ((max 1 (x + (Interval.sqrtPointBounds (x ^ 2 - 1) precision).lo) : ℚ) : ℝ) ≤
      y + √(y ^ 2 - 1) := by
    push_cast
    exact max_le (by linarith [Real.sqrt_nonneg (y ^ 2 - 1)]) (by linarith)
  have hpositive : (0 : ℚ) < max 1 (x + (Interval.sqrtPointBounds (x ^ 2 - 1) precision).lo) :=
    lt_of_lt_of_le one_pos (le_max_left _ _)
  exact ((contains_ratLogEnclosure hpositive precision).1).trans
    (Real.log_le_log (by exact_mod_cast hpositive) hargument)

/-- `arcoshUpper` at a rational upper bound of `y ≥ 1` is above `arcosh y`. -/
theorem le_arcoshUpper {x : Rat} {y : ℝ} (hy : 1 ≤ y) (hyx : y ≤ (x : ℝ)) (precision : Nat) :
    Real.arcosh y ≤ (arcoshUpper x precision : ℝ) := by
  have hx : (1 : ℚ) ≤ x := by exact_mod_cast hy.trans hyx
  have hroot := ((Interval.containsReal_some_iff _ _).mp
    (Interval.containsReal_sqrtPointBounds (x ^ 2 - 1) precision (by nlinarith))).2
  push_cast at hroot
  have hmono : √(y ^ 2 - 1) ≤ √((x : ℝ) ^ 2 - 1) := Real.sqrt_le_sqrt (by nlinarith)
  have hargument : y + √(y ^ 2 - 1) ≤
      ((x + (Interval.sqrtPointBounds (x ^ 2 - 1) precision).hi : ℚ) : ℝ) := by
    push_cast
    linarith
  have hpositiveReal : (0 : ℝ) < y + √(y ^ 2 - 1) := by
    linarith [Real.sqrt_nonneg (y ^ 2 - 1)]
  have hpositive : (0 : ℚ) < x + (Interval.sqrtPointBounds (x ^ 2 - 1) precision).hi := by
    exact_mod_cast hpositiveReal.trans_le hargument
  exact (Real.log_le_log hpositiveReal hargument).trans
    (contains_ratLogEnclosure hpositive precision).2

/-- `arcoshEnclosure` contains the inverse hyperbolic cosine of the half sum of the distances. -/
theorem contains_arcoshEnclosure (p q : Rat) (precision : Nat) :
    (arcoshEnclosure p q precision).Contains (Real.arcosh (major p q)) := by
  obtain ⟨hone, hlower, hupper⟩ := majorBounds_spec p q precision
  exact ⟨arcoshLower_le hone hlower precision,
    le_arcoshUpper (ConfocalComparison.one_le_major _ _) hupper precision⟩

/-- `arcoshPart` denotes the inverse hyperbolic cosine of the half sum of the distances. -/
theorem arcoshPart_denotes (p q : Rat) :
    (arcoshPart fmt p q).Denotes (Real.arcosh (major p q)) false := by
  have hexact : (Part.real (fmt := fmt)
      (ConfocalComparison.compareArcosh p q (cacheLevels fmt)) false).Denotes
      (Real.arcosh (major p q)) false :=
    ⟨_, rfl, ConfocalComparison.compareArcosh_eq_real p q _⟩
  refine hexact.within fun interval hinterval => ?_
  split at hinterval
  · simp at hinterval
  · refine contains_of_refineTwice (fun precision enclosure henclosure => ?_) interval hinterval
    rw [← Option.some.inj henclosure]
    exact contains_arcoshEnclosure p q _

/-- `arcsinPart` denotes the inverse sine of the half difference of the distances. -/
theorem arcsinPart_denotes (p q : Rat) :
    (arcsinPart fmt p q).Denotes (Real.arcsin (minor p q)) false := by
  have hexact : (Part.real (fmt := fmt)
      (ConfocalComparison.compareArcsin p q (cacheLevels fmt)) false).Denotes
      (Real.arcsin (minor p q)) false :=
    ⟨_, rfl, ConfocalComparison.compareArcsin_eq_real p q _⟩
  refine hexact.within fun interval hinterval => ?_
  split at hinterval
  · simp at hinterval
  · rw [← eval_arcsinExpr]
    exact contains_exprEnclosure? hinterval

/-- `arccosPart` denotes the inverse cosine of the half difference of the distances. -/
theorem arccosPart_denotes (p q : Rat) :
    (arccosPart fmt p q).Denotes (Real.arccos (minor p q)) false := by
  have hexact : (Part.real (fmt := fmt)
      (ConfocalComparison.compareArccos p q (cacheLevels fmt)) false).Denotes
      (Real.arccos (minor p q)) false :=
    ⟨_, rfl, ConfocalComparison.compareArccos_eq_real p q _⟩
  refine hexact.within fun interval hinterval => ?_
  split at hinterval
  · simp at hinterval
  · rw [← eval_arccosExpr]
    exact contains_exprEnclosure? hinterval

/-! ## Inverse hyperbolic sine and inverse sine -/

/--
The principal inverse hyperbolic sine in the closed right half-plane:
`arcosh (M (x, y)) + i arcsin (m (x, y))`.
-/
noncomputable def asinhValue (w : ℂ) : ℂ :=
  ⟨Real.arcosh (major w.re w.im), Real.arcsin (minor w.re w.im)⟩

/-- The real part of `asinhValue` is not negative. -/
theorem asinhValue_re_nonneg (w : ℂ) : 0 ≤ (asinhValue w).re :=
  Real.arcosh_nonneg (ConfocalComparison.one_le_major _ _)

/-- The imaginary part of `asinhValue` lies in `[-π / 2, π / 2]`. -/
theorem abs_asinhValue_im_le (w : ℂ) : |(asinhValue w).im| ≤ Real.pi / 2 :=
  abs_le.mpr ⟨Real.neg_pi_div_two_le_arcsin _, Real.arcsin_le_pi_div_two _⟩

private theorem sqrt_mul_sqrt_confocal (p q : ℝ) :
    √(major p q ^ 2 - 1) * √(1 - minor p q ^ 2) = |p| := by
  have hmajor := ConfocalComparison.one_le_major p q
  have hproduct := ConfocalComparison.major_mul_minor p q
  have hsum := ConfocalComparison.major_sq_add_minor_sq p q
  rw [← Real.sqrt_mul (by nlinarith), ← Real.sqrt_sq_eq_abs]
  congr 1
  linear_combination hsum - (major p q * minor p q + q) * hproduct

/-- The complex hyperbolic sine inverts `asinhValue` in the closed right half-plane. -/
theorem sinh_asinhValue {w : ℂ} (hre : 0 ≤ w.re) : Complex.sinh (asinhValue w) = w := by
  have hmajor := ConfocalComparison.one_le_major w.re w.im
  rw [asinhValue, sinh_mk, Real.sinh_arcosh hmajor, Real.cos_arcsin, Real.cosh_arcosh hmajor,
    Real.sin_arcsin (ConfocalComparison.neg_one_le_minor _ _)
      (ConfocalComparison.minor_le_one _ _),
    sqrt_mul_sqrt_confocal, abs_of_nonneg hre, ConfocalComparison.major_mul_minor]

/--
The exact result of `casinh` at a finite argument: `asinhValue` where both sign bits are clear,
extended as an odd function that commutes with conjugation.
-/
noncomputable def asinhExact : ExecComplex fmt → Exact :=
  Exact.ofQuadrant true fun z => ⟨asinhValue (toComplex z), false, false⟩

/-- The parts of `asinhCore` at a finite argument are those of `asinhValue`. -/
theorem asinhCore_denotes {z : ExecComplex fmt} (hz : isFinite z = true) :
    (asinhCore z).Denotes ⟨asinhValue (toComplex z), false, false⟩ := by
  obtain ⟨x, y, hx, hy, hw, -⟩ := exists_toRat?_of_isFinite hz
  simp only [asinhCore, hx, hy, hw, asinhValue]
  exact ⟨arcoshPart_denotes x y, arcsinPart_denotes x y⟩

/-- At every finite argument the parts of `casinh` before rounding are the exact result. -/
theorem asinhParts_denotes (hfmt : fmt.isIEEE = true) {z : ExecComplex fmt}
    (hz : isFinite z = true) : (asinhParts z).Denotes (asinhExact z) :=
  Parts.ofQuadrant_denotes hfmt true (fun _ => True) (fun _ _ _ => trivial)
    (fun _ _ _ => trivial) (fun _ hζ _ _ _ => asinhCore_denotes hζ) hz trivial

/--
For an IEEE descriptor, `asinh` of a finite argument is the principal inverse hyperbolic sine
with each part rounded once in the direction `mode`.
-/
theorem asinh_eq (hfmt : fmt.isIEEE = true) {z : ExecComplex fmt} (hz : isFinite z = true)
    (mode : Model.IEEERoundingMode := .nearest) :
    asinh z mode = (asinhExact z).round fmt mode :=
  (asinhParts_denotes hfmt hz).round mode

/-- The exact result of `casin` at a finite argument: `-i casinh (i z)` (C23 G.6.1). -/
noncomputable def asinExact (z : ExecComplex fmt) : Exact := (asinhExact (mulI z)).mulNegI

/--
For an IEEE descriptor, `asin` of a finite argument is `-i asinh (i w)`, the principal inverse
sine, with each part rounded once in the direction `mode`.
-/
theorem asin_eq (hfmt : fmt.isIEEE = true) {z : ExecComplex fmt} (hz : isFinite z = true)
    (mode : Model.IEEERoundingMode := .nearest) :
    asin z mode = (asinExact z).round fmt mode :=
  (asinhParts_denotes hfmt (isFinite_mulI hz)).mulNegI.round mode

/-! ## Inverse hyperbolic cosine and inverse cosine -/

/--
The principal inverse hyperbolic cosine in the closed upper half-plane:
`arcosh (M (y, x)) + i arccos (m (y, x))`.
-/
noncomputable def acoshValue (w : ℂ) : ℂ :=
  ⟨Real.arcosh (major w.im w.re), Real.arccos (minor w.im w.re)⟩

/-- The real part of `acoshValue` is not negative. -/
theorem acoshValue_re_nonneg (w : ℂ) : 0 ≤ (acoshValue w).re :=
  Real.arcosh_nonneg (ConfocalComparison.one_le_major _ _)

/-- The imaginary part of `acoshValue` lies in `[0, π]`. -/
theorem acoshValue_im_mem (w : ℂ) : (acoshValue w).im ∈ Set.Icc 0 Real.pi :=
  ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩

/-- The complex hyperbolic cosine inverts `acoshValue` in the closed upper half-plane. -/
theorem cosh_acoshValue {w : ℂ} (him : 0 ≤ w.im) : Complex.cosh (acoshValue w) = w := by
  have hmajor := ConfocalComparison.one_le_major w.im w.re
  rw [acoshValue, cosh_mk, Real.sinh_arcosh hmajor, Real.sin_arccos, Real.cosh_arcosh hmajor,
    Real.cos_arccos (ConfocalComparison.neg_one_le_minor _ _)
      (ConfocalComparison.minor_le_one _ _),
    sqrt_mul_sqrt_confocal, abs_of_nonneg him, ConfocalComparison.major_mul_minor]

/--
The exact result of `cacosh` at a finite argument: `acoshValue` where the imaginary sign bit is
clear, extended by conjugation.
-/
noncomputable def acoshExact : ExecComplex fmt → Exact :=
  Exact.ofUpperHalf fun z => ⟨acoshValue (toComplex z), false, false⟩

/-- The parts of `acoshCore` at a finite argument are those of `acoshValue`. -/
theorem acoshCore_denotes {z : ExecComplex fmt} (hz : isFinite z = true) :
    (acoshCore z).Denotes ⟨acoshValue (toComplex z), false, false⟩ := by
  obtain ⟨x, y, hx, hy, hw, -⟩ := exists_toRat?_of_isFinite hz
  simp only [acoshCore, hx, hy, hw, acoshValue]
  exact ⟨arcoshPart_denotes y x, arccosPart_denotes y x⟩

/--
For an IEEE descriptor, `acosh` of a finite argument is the principal inverse hyperbolic cosine
with each part rounded once in the direction `mode`.
-/
theorem acosh_eq (hfmt : fmt.isIEEE = true) {z : ExecComplex fmt} (hz : isFinite z = true)
    (mode : Model.IEEERoundingMode := .nearest) :
    acosh z mode = (acoshExact z).round fmt mode :=
  (Parts.ofUpperHalf_denotes hfmt (fun _ => True) (fun _ _ _ => trivial)
    (fun _ hζ _ _ => acoshCore_denotes hζ) hz trivial).round mode

/--
The exact result of `cacos` at a finite argument: `-i acoshValue`, which is
`arccos (m (y, x)) - i arcosh (M (y, x))`, where the imaginary sign bit is clear, extended by
conjugation. A zero imaginary part is negative there.
-/
noncomputable def acosExact : ExecComplex fmt → Exact :=
  Exact.ofUpperHalf fun z => (⟨acoshValue (toComplex z), false, false⟩ : Exact).mulNegI

/--
For an IEEE descriptor, `acos` of a finite argument is the principal inverse cosine with each
part rounded once in the direction `mode`.
-/
theorem acos_eq (hfmt : fmt.isIEEE = true) {z : ExecComplex fmt} (hz : isFinite z = true)
    (mode : Model.IEEERoundingMode := .nearest) :
    acos z mode = (acosExact z).round fmt mode :=
  (Parts.ofUpperHalf_denotes hfmt (fun _ => True) (fun _ _ _ => trivial)
    (fun _ hζ _ _ => (acoshCore_denotes hζ).mulNegI) hz trivial).round mode

/-! ## Conjugation and parity at every argument -/

/--
`casinh (conj z) = conj (casinh z)` (C23 G.6.3.2), at every argument, a NaN or an infinity included,
in a rounding direction that negation fixes.
-/
theorem asinh_conj (hfmt : fmt.isIEEE = true) (z : ExecComplex fmt)
    {mode : Model.IEEERoundingMode} (hmode : mode.negate = mode) :
    asinh (ExecComplex.conj z) mode = ExecComplex.conj (asinh z mode) :=
  Parts.round_ofUpperHalf_conj hfmt _ z hmode

/--
`casinh` is odd (C23 G.6.3.2): `casinh (-z) = -casinh z` at every argument, a NaN or an infinity
included, in a rounding direction that negation fixes.
-/
theorem asinh_neg (hfmt : fmt.isIEEE = true) (z : ExecComplex fmt)
    {mode : Model.IEEERoundingMode} (hmode : mode.negate = mode) :
    asinh (ExecComplex.neg z) mode = ExecComplex.neg (asinh z mode) :=
  Parts.round_ofQuadrant_neg hfmt asinhCore z hmode

/--
`casin (conj z) = conj (casin z)` (C23 G.6.1, paragraph 8, from `casinh`), at every argument, a NaN
or an infinity included, in a rounding direction that negation fixes.
-/
theorem asin_conj (hfmt : fmt.isIEEE = true) (z : ExecComplex fmt)
    {mode : Model.IEEERoundingMode} (hmode : mode.negate = mode) :
    asin (ExecComplex.conj z) mode = ExecComplex.conj (asin z mode) :=
  Parts.round_mulNegI_conj hfmt asinhCore z hmode

/--
`casin` is odd (C23 G.6.1, paragraph 8, from `casinh`): `casin (-z) = -casin z` at every argument, a
NaN or an infinity included, in a rounding direction that negation fixes.
-/
theorem asin_neg (hfmt : fmt.isIEEE = true) (z : ExecComplex fmt)
    {mode : Model.IEEERoundingMode} (hmode : mode.negate = mode) :
    asin (ExecComplex.neg z) mode = ExecComplex.neg (asin z mode) :=
  Parts.round_mulNegI_neg hfmt asinhCore z hmode

/--
`cacosh (conj z) = conj (cacosh z)` (C23 G.6.3.1), at every argument, a NaN or an infinity included,
in a rounding direction that negation fixes.
-/
theorem acosh_conj (hfmt : fmt.isIEEE = true) (z : ExecComplex fmt)
    {mode : Model.IEEERoundingMode} (hmode : mode.negate = mode) :
    acosh (ExecComplex.conj z) mode = ExecComplex.conj (acosh z mode) :=
  Parts.round_ofUpperHalf_conj hfmt acoshCore z hmode

/--
`cacos (conj z) = conj (cacos z)` (C23 G.6.2.1), at every argument, a NaN or an infinity included,
in a rounding direction that negation fixes.
-/
theorem acos_conj (hfmt : fmt.isIEEE = true) (z : ExecComplex fmt)
    {mode : Model.IEEERoundingMode} (hmode : mode.negate = mode) :
    acos (ExecComplex.conj z) mode = ExecComplex.conj (acos z mode) :=
  Parts.round_ofUpperHalf_conj hfmt _ z hmode

end ExecComplex
end FloatLib.Floats.Formats.BinaryInterchange
