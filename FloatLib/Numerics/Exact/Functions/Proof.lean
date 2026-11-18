/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Functions.Runtime
public import FloatLib.Numerics.Exact.Hyperbolic.Proof
public import FloatLib.Numerics.Exact.RationalPower.Proof
public import FloatLib.Numerics.Exact.Softplus.Proof
public import FloatLib.Numerics.Exact.Trigonometric.Proof
public import FloatLib.Numerics.Exact.Trigonometric.Atan2.Proof
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Real interpretation of exact function expressions

Every prepared comparator returns the ordering of the expression's real value
and the rational boundary, equality included. Primitive cases reuse their
existing numerical proofs; affine composition only transports order.
-/

@[expose] public section

namespace FloatLib.Numerics.FunctionExpr

/-- Mathematical interpretation, independent of rational enclosures and their caches. -/
noncomputable def toReal : FunctionExpr → ℝ
  | .rational value => value
  | .exp argument => Real.exp argument
  | .log argument _ => Real.log argument
  | .power base exponent _ => (base : ℝ) ^ (exponent : ℝ)
  | .logb base argument _ _ => Real.logb base argument
  | .softplus argument => Real.log (1 + Real.exp argument)
  | .sin argument => Real.sin argument
  | .cos argument => Real.cos argument
  | .tan argument => Real.tan argument
  | .arcsin argument _ _ => Real.arcsin argument
  | .arccos argument _ _ => Real.arccos argument
  | .arctan argument => Real.arctan argument
  | .sinPi argument => Real.sin ((argument : ℝ) * Real.pi)
  | .cosPi argument => Real.cos ((argument : ℝ) * Real.pi)
  | .tanPi argument => Real.tan ((argument : ℝ) * Real.pi)
  | .arcsinPi argument _ _ => Real.arcsin argument / Real.pi
  | .arccosPi argument _ _ => Real.arccos argument / Real.pi
  | .arctanPi argument => Real.arctan argument / Real.pi
  | .sinh argument => Real.sinh argument
  | .cosh argument => Real.cosh argument
  | .tanh argument => Real.tanh argument
  | .arsinh argument => Real.arsinh argument
  | .arcosh argument _ => Real.arcosh argument
  | .artanh argument _ _ => Real.artanh argument
  | .arg x y piScaled =>
      let angle := Complex.arg ⟨(x : ℝ), (y : ℝ)⟩
      if piScaled then angle / Real.pi else angle
  | .affine scale offset value => (scale : ℝ) * value.toReal + offset

/-- Every finite expression compares exactly with every rational boundary at every cache depth. -/
theorem prepare_eq_real (expression : FunctionExpr) (levels : Nat) (boundary : Rat) :
    (expression.prepare levels).compare boundary = cmp expression.toReal (boundary : ℝ) := by
  induction expression generalizing boundary with
  | rational value =>
      exact (Rat.cast_strictMono.cmp_map_eq value boundary).symm
  | exp argument => exact ElementaryComparison.prepareExp_eq_real argument levels boundary
  | log argument h => exact ElementaryComparison.prepareLog_eq_real argument levels h boundary
  | power base exponent h => exact RationalPower.compare_eq_real base exponent boundary h
  | logb base argument hb ha =>
      dsimp only [prepare, toReal, Enclosure.Comparison.Prepared.compare]
      rw [RationalPower.compare_eq_real _ _ _ (le_trans (by norm_num) hb.le), cmp_swap]
      have hb' : (1 : ℝ) < base := by exact_mod_cast hb
      have ha' : (0 : ℝ) < argument := Rat.cast_pos.mpr ha
      simp only [cmp, cmpUsing, Real.logb_lt_iff_lt_rpow hb' ha',
        Real.lt_logb_iff_rpow_lt hb' ha']
  | softplus argument => exact Softplus.compare_eq_real argument boundary
  | sin argument => exact TrigonometricComparison.prepareSin_eq_real argument levels boundary
  | cos argument => exact TrigonometricComparison.prepareCos_eq_real argument levels boundary
  | tan argument => exact TrigonometricComparison.prepareTan_eq_real argument levels boundary
  | arcsin argument hl hu =>
      exact TrigonometricComparison.prepareArcsin_eq_real argument levels boundary hl hu
  | arccos argument hl hu =>
      exact TrigonometricComparison.prepareArccos_eq_real argument levels boundary hl hu
  | arctan argument => exact TrigonometricComparison.prepareArctan_eq_real argument levels boundary
  | sinPi argument => exact TrigonometricComparison.prepareSinPi_eq_real argument levels boundary
  | cosPi argument => exact TrigonometricComparison.prepareCosPi_eq_real argument levels boundary
  | tanPi argument => exact TrigonometricComparison.prepareTanPi_eq_real argument levels boundary
  | arcsinPi argument hl hu =>
      exact TrigonometricComparison.prepareArcsinPi_eq_real argument levels boundary hl hu
  | arccosPi argument hl hu =>
      exact TrigonometricComparison.prepareArccosPi_eq_real argument levels boundary hl hu
  | arctanPi argument =>
      exact TrigonometricComparison.prepareArctanPi_eq_real argument levels boundary
  | sinh argument => exact HyperbolicComparison.compareSinh_eq_real argument boundary
  | cosh argument => exact HyperbolicComparison.compareCosh_eq_real argument boundary
  | tanh argument => exact HyperbolicComparison.compareTanh_eq_real argument boundary
  | arsinh argument => exact HyperbolicComparison.prepareArsinh_eq_real argument levels boundary
  | arcosh argument h => exact HyperbolicComparison.prepareArcosh_eq_real argument levels boundary h
  | artanh argument hl hu =>
      exact HyperbolicComparison.prepareArtanh_eq_real argument levels hl hu boundary
  | arg x y piScaled =>
      cases piScaled
      · exact TrigonometricComparison.prepareAtan2_eq_real x y levels boundary
      · exact TrigonometricComparison.prepareAtan2Pi_eq_real x y levels boundary
  | affine scale offset value ih =>
      dsimp only [prepare, toReal]
      by_cases hzero : scale = 0
      · simp only [hzero, ite_true, Rat.cast_zero, zero_mul, zero_add,
          Enclosure.Comparison.Prepared.compare]
        exact (Rat.cast_strictMono.cmp_map_eq offset boundary).symm
      · simp only [hzero, ite_false]
        change (if scale < 0 then
          ((value.prepare levels).compare ((boundary - offset) / scale)).swap
          else (value.prepare levels).compare ((boundary - offset) / scale)) = _
        rw [ih]
        push_cast
        by_cases hnegative : scale < 0
        · have hreal : (scale : ℝ) < 0 := Rat.cast_lt_zero.mpr hnegative
          rw [ite_eq_left hnegative, cmp_swap]
          simp only [cmp, cmpUsing, div_lt_iff_of_neg hreal, lt_div_iff_of_neg hreal,
            sub_lt_iff_lt_add, lt_sub_iff_add_lt, mul_comm]
        · have hreal : (0 : ℝ) < scale := Rat.cast_pos.mpr (lt_of_le_of_ne
            (le_of_not_gt hnegative) (Ne.symm hzero))
          rw [ite_eq_right hnegative]
          simp only [cmp, cmpUsing, div_lt_iff₀ hreal, lt_div_iff₀ hreal,
            sub_lt_iff_lt_add, lt_sub_iff_add_lt, mul_comm]

end FloatLib.Numerics.FunctionExpr
