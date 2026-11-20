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

/-- Every enclosure that `smallArcsinCore?` returns contains the inverse sine of the half
difference of the distances. -/
theorem contains_smallArcsinCore? {p q : Rat} {interval : RationalInterval}
    (h : smallArcsinCore? fmt p q = some interval) :
    interval.Contains (Real.arcsin (minor p q)) := by
  unfold smallArcsinCore? at h
  dsimp only at h
  split at h
  · rename_i hcondition
    obtain ⟨hq, hq16, hrootLow, hslope0, hslope1⟩ := hcondition
    rw [← eq_of_tightOnly h]
    generalize smallDegree fmt _ = degree
    generalize fmt.fracWidth + 36 + 2 * bitsBelowOne (max |p| q) = precision
      at hrootLow hslope0 hslope1 ⊢
    obtain ⟨hone, hlower, hupper⟩ := majorBounds_spec p q precision
    have hmajor := ConfocalComparison.one_le_major (p : ℝ) q
    have hproduct := ConfocalComparison.major_mul_minor (p : ℝ) q
    have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    have hb1 : (0 : ℝ) < ((majorBounds p q precision).1 : ℝ) :=
      lt_of_lt_of_le one_pos (by exact_mod_cast hone)
    have hb2 : (0 : ℝ) < ((majorBounds p q precision).2 : ℝ) :=
      lt_of_lt_of_le (lt_of_lt_of_le one_pos hmajor) hupper
    have hminor : minor (p : ℝ) q = (q : ℝ) / major (p : ℝ) q := by
      rw [eq_div_iff (by linarith), mul_comm]
      exact hproduct
    generalize major (p : ℝ) q = M at hlower hupper hmajor hminor
    generalize minor (p : ℝ) q = m at hminor ⊢
    have hlowR : (((q / (majorBounds p q precision).2 : Rat)) : ℝ) ≤ m := by
      rw [hminor]
      push_cast
      exact div_le_div_of_nonneg_left hqR.le (by linarith) hupper
    have hhighR : m ≤ (((q / (majorBounds p q precision).1 : Rat)) : ℝ) := by
      rw [hminor]
      push_cast
      exact div_le_div_of_nonneg_left hqR.le hb1 hlower
    have hlow0 : (0 : Rat) ≤ q / (majorBounds p q precision).2 :=
      div_nonneg hq.le (by exact_mod_cast hb2.le)
    have hhigh16 : q / (majorBounds p q precision).1 ≤ 1 / 16 :=
      (div_le_self hq.le hone).trans hq16
    generalize q / (majorBounds p q precision).2 = low at hlowR hlow0 hrootLow hslope0 hslope1 ⊢
    generalize q / (majorBounds p q precision).1 = high
      at hhighR hhigh16 hrootLow hslope0 hslope1 ⊢
    have hlow0R : (0 : ℝ) ≤ (low : ℝ) := by exact_mod_cast hlow0
    have hhigh16R : (high : ℝ) ≤ 1 / 16 := by
      have hcast := (Rat.cast_le (K := ℝ)).mpr hhigh16
      push_cast at hcast
      exact hcast
    have hm0 : 0 ≤ m := hlow0R.trans hlowR
    have : m ≤ 1 / 16 := hhighR.trans hhigh16R
    have hlowHigh : low ≤ high := by exact_mod_cast hlowR.trans hhighR
    have hhigh1 : high ≤ 1 := hhigh16.trans (by norm_num)
    have hlowSq : (0 : Rat) ≤ 1 - low ^ 2 :=
      sub_nonneg.mpr (pow_le_one₀ hlow0 (hlowHigh.trans hhigh1))
    have hhighSq : (0 : Rat) ≤ 1 - high ^ 2 :=
      sub_nonneg.mpr (pow_le_one₀ (hlow0.trans hlowHigh) hhigh1)
    have hrootHigh := ((Interval.containsReal_some_iff _ _).mp
      (Interval.containsReal_sqrtPointBounds (1 - low ^ 2) precision hlowSq)).2
    have hrootLowR := ((Interval.containsReal_some_iff _ _).mp
      (Interval.containsReal_sqrtPointBounds (1 - high ^ 2) precision hhighSq)).1
    push_cast at hrootHigh hrootLowR
    have hupperRoot : √(1 - m ^ 2) ≤ √(1 - (low : ℝ) ^ 2) :=
      Real.sqrt_le_sqrt (sub_le_sub_left (pow_le_pow_left₀ hlow0R hlowR 2) 1)
    have hlowerRoot : √(1 - (high : ℝ) ^ 2) ≤ √(1 - m ^ 2) :=
      Real.sqrt_le_sqrt (sub_le_sub_left (pow_le_pow_left₀ hm0 hhighR 2) 1)
    generalize (Interval.sqrtPointBounds (1 - low ^ 2) precision).hi = rootHigh
      at hrootHigh hslope0 hslope1 ⊢
    generalize (Interval.sqrtPointBounds (1 - high ^ 2) precision).lo = rootLow
      at hrootLowR hrootLow hslope0 hslope1 ⊢
    have hrootLow0 : (0 : ℝ) < (rootLow : ℝ) := by exact_mod_cast hrootLow
    have hroot : (0 : ℝ) < √(1 - m ^ 2) := hrootLow0.trans_le (hrootLowR.trans hlowerRoot)
    have hslopeLow : (((dyadicAround (low / rootHigh) precision).lo : Rat) : ℝ) ≤
        m / √(1 - m ^ 2) := by
      have hcoarse : (((dyadicAround (low / rootHigh) precision).lo : Rat) : ℝ) ≤
          ((low / rootHigh : Rat) : ℝ) := by
        exact_mod_cast (dyadicAround_bounds (low / rootHigh) precision).1
      refine hcoarse.trans ?_
      push_cast
      exact div_le_div₀ hm0 hlowR hroot (hupperRoot.trans hrootHigh)
    have hslopeHigh : m / √(1 - m ^ 2) ≤
        (((dyadicAround (high / rootLow) precision).hi : Rat) : ℝ) := by
      have hcoarse : ((high / rootLow : Rat) : ℝ) ≤
          (((dyadicAround (high / rootLow) precision).hi : Rat) : ℝ) := by
        exact_mod_cast (dyadicAround_bounds (high / rootLow) precision).2
      refine le_trans ?_ hcoarse
      push_cast
      exact div_le_div₀ (hm0.trans hhighR) hhighR hrootLow0 (hrootLowR.trans hlowerRoot)
    generalize (dyadicAround (low / rootHigh) precision).lo = slopeLow
      at hslopeLow hslope0 ⊢
    generalize (dyadicAround (high / rootLow) precision).hi = slopeHigh
      at hslopeHigh hslope1 ⊢
    have hle : slopeLow ≤ slopeHigh := by exact_mod_cast hslopeLow.trans hslopeHigh
    have hhighLt : |slopeHigh| < 1 := by
      rw [abs_of_nonneg (hslope0.trans hle)]
      exact hslope1
    have hlowLt : |slopeLow| < 1 := by
      rw [abs_of_nonneg hslope0]
      exact lt_of_le_of_lt hle hslope1
    rw [Real.arcsin_eq_arctan ⟨by linarith, by linarith⟩]
    exact ⟨(Enclosure.contains_atanSmall _ degree hlowLt).1.trans
        (Real.arctan_strictMono.monotone hslopeLow),
      (Real.arctan_strictMono.monotone hslopeHigh).trans
        (Enclosure.contains_atanSmall _ degree hhighLt).2⟩
  · simp at h

/-- Every enclosure that `smallArcsin?` returns contains the inverse sine of the half
difference of the distances. -/
theorem contains_smallArcsin? {p q : Rat} {interval : RationalInterval}
    (h : smallArcsin? fmt p q = some interval) :
    interval.Contains (Real.arcsin (minor p q)) := by
  unfold smallArcsin? at h
  split at h
  · split at h
    · exact contains_smallArcsinCore? h
    · obtain ⟨core, hcore, rfl⟩ := Option.map_eq_some_iff.mp h
      have hmirror := RationalInterval.contains_neg (contains_smallArcsinCore? hcore)
      have hvalue : -Real.arcsin (minor (p : ℝ) ((-q : Rat) : ℝ)) =
          Real.arcsin (minor (p : ℝ) (q : ℝ)) := by
        rw [Rat.cast_neg, ConfocalComparison.minor_neg, Real.arcsin_neg, neg_neg]
      rwa [hvalue] at hmirror
  · simp at h

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
  · refine contains_orElse (fun _ hsmall => contains_smallArcsin? hsmall)
      (fun general hgeneral => ?_) interval hinterval
    rw [← eval_arcsinExpr]
    exact contains_exprEnclosure? hgeneral

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
