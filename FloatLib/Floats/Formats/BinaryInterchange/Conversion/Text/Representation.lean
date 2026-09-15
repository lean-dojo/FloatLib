/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Exact
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.TotalOrder.Encoding
import Mathlib.Tactic.Linarith

/-! # Uniqueness of finite binary representations

The decoded exponent is the canonical exponent of every nonzero finite value.
This connects numerical conversion theorems to representation round trips;
signed zero is handled separately because real numbers forget its sign.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Floats.Formats.Flocq

/-- A nonzero decoded dyadic already uses the format's canonical exponent. -/
theorem cexp_toDyadic? {fmt : FloatFormat} {x : Model fmt} {d : Numerics.Dyadic}
    (hd : toDyadic? x = some d) (hm : d.significand ≠ 0) :
    cexp Numerics.binaryRadix (fexpOf fmt) d.toReal = d.exponent := by
  rw [cexp, Dyadic.magnitude_toReal d hm]
  have hfin := isFinite_eq_true_of_toDyadic?_some hd
  have hshape := toDyadic?_ofFields_of_isFinite fmt (signBit x) (expField x) (fracField x)
    (expField_lt_pow2 x) (fracField_lt_pow2 x)
    (by simpa only [ofFields_signBit_expField_fracField] using hfin)
  rw [ofFields_signBit_expField_fracField, hd] at hshape
  have hf := fracField_lt_pow2 x
  by_cases he : expField x = 0
  · by_cases hz : fracField x = 0
    · simp only [he, hz, ite_true, Option.some.injEq] at hshape
      simp [hshape] at hm
    · simp only [he, hz, ite_true, ite_false, Option.some.injEq] at hshape
      rw [hshape]
      have hl : (fracField x).log2 < fmt.fracWidth := by
        rw [Nat.log2_eq_log_two]
        exact (Nat.log_lt_iff_lt_pow (by decide) hz).mpr hf
      simp only [fexpOf, fltExp, Int.ofNat_eq_natCast]
      exact max_eq_right (by omega)
  · simp only [he, ite_false, Option.some.injEq] at hshape
    rw [hshape]
    have hm' : pow2 fmt.fracWidth + fracField x ≠ 0 := by
      have hp : 0 < pow2 fmt.fracWidth := by simp [pow2_eq_two_pow]
      omega
    have hl : (pow2 fmt.fracWidth + fracField x).log2 = fmt.fracWidth := by
      rw [Nat.log2_eq_log_two]
      apply (Nat.log_eq_iff (Or.inr ⟨by decide, hm'⟩)).mpr
      simp only [pow2_eq_two_pow, pow_succ]
      omega
    simp only [hl, fexpOf, fltExp, FloatFormat.minSubnormalExponent,
      FloatFormat.minNormalExponent, Int.ofNat_eq_natCast]
    rw [max_eq_left (by omega)]
    omega

/-- Equal nonzero numerical values have the same canonical decoded exponent. -/
theorem toDyadic?_exponent_eq_of_toReal_eq {fmt : FloatFormat} {x y : Model fmt}
    {dx dy : Numerics.Dyadic} (hx : toDyadic? x = some dx) (hy : toDyadic? y = some dy)
    (hx0 : dx.significand ≠ 0) (hy0 : dy.significand ≠ 0)
    (hvalue : toReal x = toReal y) : dx.exponent = dy.exponent := by
  rw [← cexp_toDyadic? hx hx0, ← cexp_toDyadic? hy hy0]
  congr 1
  simpa only [toReal_eq, hx, hy] using hvalue

/-- A dyadic denotes zero exactly when its unsigned coefficient is zero. -/
theorem Dyadic.toReal_eq_zero_iff (d : Numerics.Dyadic) :
    d.toReal = 0 ↔ d.significand = 0 := by
  have hp := zpow_ne_zero d.exponent (by norm_num : (2 : ℝ) ≠ 0)
  cases hs : d.negative <;>
    simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, hs, hp]

/-- Equal nonzero finite real values determine the complete binary word. -/
theorem eq_of_toReal_eq_of_nonzero {fmt : FloatFormat} {x y : Model fmt}
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hvalue : toReal x = toReal y) (hzero : toReal x ≠ 0) : x = y := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  have hv : dx.toReal = dy.toReal := by simpa [toReal_eq, hdx, hdy] using hvalue
  have hx0 : dx.significand ≠ 0 := by
    apply (Dyadic.toReal_eq_zero_iff dx).not.mp
    simpa [toReal_eq, hdx] using hzero
  have hy0 : dy.significand ≠ 0 := by
    apply (Dyadic.toReal_eq_zero_iff dy).not.mp
    rw [← hv]
    exact (Dyadic.toReal_eq_zero_iff dx).not.mpr hx0
  have he := toDyadic?_exponent_eq_of_toReal_eq hdx hdy hx0 hy0 hvalue
  have hm : dx.signedSignificand = dy.signedSignificand := by
    have hmReal : (dx.signedSignificand : ℝ) = (dy.signedSignificand : ℝ) := by
      apply mul_right_cancel₀ (zpow_ne_zero dy.exponent (by norm_num : (2 : ℝ) ≠ 0))
      simpa [Numerics.Dyadic.toReal, he] using hv
    exact_mod_cast hmReal
  have hcoeff : dx.significand = dy.significand := by
    have hn := congrArg Int.natAbs hm
    cases hs : dx.negative <;> cases ht : dy.negative <;>
      simpa [Numerics.Dyadic.signedSignificand, hs, ht] using hn
  have hsign : dx.negative = dy.negative := by
    cases hs : dx.negative <;> cases ht : dy.negative <;>
      simp_all [Numerics.Dyadic.signedSignificand]
  have hd : dx = dy := by
    cases dx
    cases dy
    simp_all
  exact eq_of_toDyadic?_eq_some hdx (hdy.trans (congrArg some hd.symm))

/-- In a conventional IEEE format, rounding a decoded nonzero value restores its word. -/
theorem roundDyadicWithRounding_toDyadic?_of_nonzero {fmt : FloatFormat}
    (hfmt : fmt.isIEEE = true) (mode : IEEERoundingMode) {x : Model fmt}
    {d : Numerics.Dyadic} (hd : toDyadic? x = some d) (hm : d.significand ≠ 0) :
    roundDyadicWithRounding fmt mode d = x := by
  have hfin := isFinite_eq_true_of_toDyadic?_some hd
  have hv : toReal x = d.toReal := by simp [toReal_eq, hd]
  have hb : |d.toReal| ≤ toReal (posMaxFinite fmt) := by
    rw [← hv]
    exact abs_toReal_le_posMaxFinite_of_isIEEE_of_isFinite x hfmt hfin
  have hr := roundDyadicWithRounding_of_representable fmt hfmt mode d
    (toDyadic?_significand_lt x hd) (minSubnormalExponent_le_toDyadic? x hd) hb
  exact eq_of_toReal_eq_of_nonzero hr.1 hfin (hr.2.trans hv.symm)
    (by rw [hr.2]; exact (Dyadic.toReal_eq_zero_iff d).not.mpr hm)

/-- In a conventional IEEE format, rounding an exact zero preserves its sign. -/
theorem roundDyadicWithRounding_zero (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (mode : IEEERoundingMode) (negative : Bool) (exponent : Int) :
    roundDyadicWithRounding fmt mode ⟨negative, 0, exponent⟩ = zero fmt negative := by
  cases negative <;> cases mode <;>
    simp [roundDyadicWithRounding, roundDyadicTowardZero, roundDyadicUp, roundDyadicDown,
      roundDyadic, hfmt, ieeeRoundDyadic, zero, modelSign,
      posZero_eq_ofModel_zero, negZero_eq_ofModel_zero]

/-- In a conventional IEEE format, rounding a decoded finite dyadic restores its complete word. -/
theorem roundDyadicWithRounding_toDyadic? {fmt : FloatFormat}
    (hfmt : fmt.isIEEE = true) (mode : IEEERoundingMode) {x : Model fmt}
    {d : Numerics.Dyadic} (hd : toDyadic? x = some d) :
    roundDyadicWithRounding fmt mode d = x := by
  by_cases hm : d.significand = 0
  · have hz := isZero_eq_true_of_toDyadic?_some_of_mant_eq_zero hd hm
    have hdx := toDyadic?_eq_zero_of_isZero_eq_true x hz
    have hd' := Option.some.inj (hd.symm.trans hdx)
    rw [hd', roundDyadicWithRounding_zero fmt hfmt]
    apply eq_of_toDyadic?_eq_some (d := ⟨signBit x, 0, 0⟩) _ hdx
    simp [toDyadic?_zero, signBit_zero,
      FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt hfmt]
  · exact roundDyadicWithRounding_toDyadic?_of_nonzero hfmt mode hd hm

end FloatLib.Floats.Formats.BinaryInterchange.Model
