/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.Algebraic
public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.PartsProof
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Bounds
public import FloatLib.Floats.Formats.Posit.Algebraic.Root.Proof
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Correct rounding of the complex square root and its reciprocal

For an IEEE descriptor and every finite argument, `ExecComplex.sqrt` returns each part of the
principal square root rounded once in the requested direction (`sqrt_eq`), and `ExecComplex.rsqrt`
does the same for the reciprocal of that root at a nonzero argument (`rsqrt_eq`) and returns
`+∞ + NaN i` at a zero (`rsqrt_zero`). No premise restricts the argument: results that are exact,
that fall halfway between two representable values, or that are subnormal are all covered,
because the comparisons behind the rounding are exact rational arithmetic
(`compareHalfRoot_eq_real`).

The exact results are stated with Mathlib's principal power `w ^ (2⁻¹ : ℂ)` where the imaginary
sign bit is clear, and by conjugation elsewhere (`sqrtExact`, `rsqrtExact`). So an argument on the
negative real axis with imaginary part `-0` takes the root below the cut, as C23 7.3.3 and
G.6.5.2 specify, where the power alone is continuous from above.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace ExecComplex

open Posit.Model.RootRounding (compareRoot compareRoot_eq_real)

variable {fmt : FloatFormat}

/-- `compareHalfRoot` orders the nested root against every rational boundary. -/
theorem compareHalfRoot_eq_real (x normSq scale : Rat) (hnorm : x * x ≤ normSq)
    (hscale : 0 < scale) (boundary : Rat) :
    compareHalfRoot x normSq scale boundary =
      cmp (√((√(normSq : ℝ) + x) / (2 * scale))) (boundary : ℝ) := by
  have hn : (0 : ℝ) ≤ normSq := by exact_mod_cast (mul_self_nonneg x).trans hnorm
  have hroot : |(x : ℝ)| ≤ √(normSq : ℝ) :=
    Real.abs_le_sqrt (by rw [sq]; exact_mod_cast hnorm)
  have hs : (0 : ℝ) < 2 * scale := by exact_mod_cast (by linarith : (0 : Rat) < 2 * scale)
  have hv : 0 ≤ (√(normSq : ℝ) + x) / (2 * scale) :=
    div_nonneg (by linarith [neg_abs_le (x : ℝ)]) hs.le
  unfold compareHalfRoot
  split
  · rename_i hneg
    exact ((cmp_eq_gt_iff _ _).mpr
      ((by exact_mod_cast hneg : (boundary : ℝ) < 0).trans_le (Real.sqrt_nonneg _))).symm
  · rename_i hnonneg
    have hb : (0 : ℝ) ≤ boundary := by exact_mod_cast le_of_not_gt hnonneg
    rw [compareRoot_eq_real normSq 2 (√(normSq : ℝ)) (Real.sqrt_nonneg _) two_ne_zero
      (Real.sq_sqrt hn)]
    push_cast
    have hsq := Real.sq_sqrt hv
    have hlt : √(normSq : ℝ) < 2 * scale * boundary * boundary - x ↔
        √((√(normSq : ℝ) + x) / (2 * scale)) < boundary := by
      rw [← pow_lt_pow_iff_left₀ (Real.sqrt_nonneg _) hb two_ne_zero, hsq, div_lt_iff₀ hs]
      constructor <;> intro h <;> linarith
    have hgt : 2 * scale * boundary * boundary - x < √(normSq : ℝ) ↔
        (boundary : ℝ) < √((√(normSq : ℝ) + x) / (2 * scale)) := by
      rw [← pow_lt_pow_iff_left₀ hb (Real.sqrt_nonneg _) two_ne_zero, hsq, lt_div_iff₀ hs]
      constructor <;> intro h <;> linarith
    simp only [cmp, cmpUsing, hlt, hgt]

/-- The modulus of a complex number with rational parts is the root of a rational. -/
theorem norm_mk_ratCast (x y : Rat) :
    ‖(⟨(x : ℝ), (y : ℝ)⟩ : ℂ)‖ = √((x * x + y * y : Rat) : ℝ) := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  push_cast
  ring_nf

/--
A complex number of the closed right half-plane, with a nonnegative imaginary part where the
real part is zero, is the principal square root of its square.
-/
theorem sq_cpow_inv_two {c : ℂ} (hre : 0 ≤ c.re) (him : 0 < c.re ∨ 0 ≤ c.im) :
    (c ^ 2) ^ (2⁻¹ : ℂ) = c :=
  Complex.pow_cpow_ofNat_inv (Complex.neg_pi_div_two_lt_arg_iff.mpr him)
    (Complex.arg_le_pi_div_two_iff.mpr (Or.inl hre))

/--
The exact result of `csqrt` at a finite argument: the principal root `w ^ (2⁻¹ : ℂ)` where the
imaginary sign bit is clear, its conjugate elsewhere, and positive zeros there.
-/
noncomputable def sqrtExact : ExecComplex fmt → Exact :=
  Exact.ofUpperHalf fun z => ⟨toComplex z ^ (2⁻¹ : ℂ), false, false⟩

/-- Where the imaginary sign bit is clear, the parts of `sqrtCore` are the principal root. -/
theorem sqrtCore_denotes {z : ExecComplex fmt} (hz : isFinite z = true)
    (him : Model.signBit z.im = false) :
    (sqrtCore z).Denotes ⟨toComplex z ^ (2⁻¹ : ℂ), false, false⟩ := by
  obtain ⟨x, y, hx, hy, hw, hreNaN, hreInf, _, himInf⟩ := exists_toRat?_of_isFinite hz
  have hy0 : (0 : ℝ) ≤ y := by
    rw [← Model.Algebraic.toReal_of_toRat?_eq_some hy]
    exact Model.toReal_nonneg_of_signBit_eq_false him
  simp only [sqrtCore, himInf, hreNaN, hreInf, hx, hy, Bool.false_eq_true, ↓reduceIte]
  refine ⟨⟨_, rfl, fun q => ?_⟩, ⟨_, rfl, fun q => ?_⟩⟩
  · rw [compareHalfRoot_eq_real _ _ 1 (by linarith [mul_self_nonneg y]) one_pos,
      Complex.cpow_inv_two_re, hw, norm_mk_ratCast]
    simp
  · rw [compareHalfRoot_eq_real _ _ 1 (by linarith [mul_self_nonneg y]) one_pos,
      Complex.cpow_inv_two_im_eq_sqrt (by rw [hw]; exact hy0), hw, norm_mk_ratCast]
    simp [sub_eq_add_neg]

/--
For an IEEE descriptor, `sqrt` of a finite argument is the principal square root with each part
rounded once in the direction `mode`.
-/
theorem sqrt_eq (hfmt : fmt.isIEEE = true) {z : ExecComplex fmt} (hz : isFinite z = true)
    (mode : Model.IEEERoundingMode := .nearest) :
    sqrt z mode = (sqrtExact z).round fmt mode :=
  (Parts.ofUpperHalf_denotes hfmt (fun _ => True) (fun _ _ _ => trivial)
    (fun _ hζ _ him => sqrtCore_denotes hζ him) hz trivial).round mode

/-- The nested root over the squared modulus is the nested root over the modulus. -/
private theorem sqrt_div_normSq {normSq t : ℝ} (hnorm : 0 < normSq) (ht : 0 ≤ √normSq + t) :
    √((√normSq + t) / (2 * normSq)) = √((√normSq + t) / 2) / √normSq := by
  have hsplit : (√normSq + t) / (2 * normSq) = (√normSq + t) / 2 / (√normSq) ^ 2 := by
    rw [Real.sq_sqrt hnorm.le, div_div]
  rw [hsplit, Real.sqrt_div (by linarith), Real.sqrt_sq (Real.sqrt_nonneg _)]

/--
The exact result of `1 / csqrt z` at a finite nonzero argument: the reciprocal of the principal
root where the imaginary sign bit is clear, its conjugate elsewhere. A zero real part is positive
and a zero imaginary part negative there.
-/
noncomputable def rsqrtExact : ExecComplex fmt → Exact :=
  Exact.ofUpperHalf fun z => ⟨(toComplex z ^ (2⁻¹ : ℂ))⁻¹, false, true⟩

/--
Where the imaginary sign bit is clear and the argument is not zero, the parts of `rsqrtCore` are
the reciprocal of the principal root.
-/
theorem rsqrtCore_denotes {z : ExecComplex fmt} (hz : isFinite z = true)
    (hne : toComplex z ≠ 0) (him : Model.signBit z.im = false) :
    (rsqrtCore z).Denotes ⟨(toComplex z ^ (2⁻¹ : ℂ))⁻¹, false, true⟩ := by
  obtain ⟨x, y, hx, hy, hw, hreNaN, hreInf, himNaN, himInf⟩ := exists_toRat?_of_isFinite hz
  have hy0 : (0 : ℝ) ≤ y := by
    rw [← Model.Algebraic.toReal_of_toRat?_eq_some hy]
    exact Model.toReal_nonneg_of_signBit_eq_false him
  have hzero : (Model.isZero z.re && Model.isZero z.im) = false := by
    by_contra hboth
    simp only [Bool.not_eq_false, Bool.and_eq_true] at hboth
    exact hne (by
      rw [toComplex, Model.toReal_eq_zero_of_isZero _ hboth.1,
        Model.toReal_eq_zero_of_isZero _ hboth.2]
      rfl)
  have hnorm : (0 : Rat) < x * x + y * y := by
    rcases lt_or_eq_of_le (add_nonneg (mul_self_nonneg x) (mul_self_nonneg y)) with h | h
    · exact h
    · have hx0 : x = 0 := by nlinarith [mul_self_nonneg x, mul_self_nonneg y]
      have hy0 : y = 0 := by nlinarith [mul_self_nonneg x, mul_self_nonneg y]
      exact absurd (by rw [hw, hx0, hy0]; simp [Complex.ext_iff]) hne
  have hnormReal : (0 : ℝ) < ((x * x + y * y : Rat) : ℝ) := by exact_mod_cast hnorm
  have habs : |(x : ℝ)| ≤ √((x * x + y * y : Rat) : ℝ) :=
    Real.abs_le_sqrt (by push_cast; linarith [mul_self_nonneg (y : ℝ)])
  have hre := Complex.cpow_inv_two_re (toComplex z)
  have himag := Complex.cpow_inv_two_im_eq_sqrt (x := toComplex z) (by rw [hw]; exact hy0)
  rw [hw, norm_mk_ratCast] at hre himag
  have hnormSq : Complex.normSq ((⟨(x : ℝ), (y : ℝ)⟩ : ℂ) ^ (2⁻¹ : ℂ)) =
      √((x * x + y * y : Rat) : ℝ) := by
    rw [Complex.normSq_apply, hre, himag,
      Real.mul_self_sqrt (by linarith [neg_abs_le (x : ℝ)]),
      Real.mul_self_sqrt (by linarith [le_abs_self (x : ℝ)])]
    ring
  simp only [rsqrtCore, himInf, hreNaN, hreInf, himNaN, hzero, hx, hy, Bool.false_eq_true,
    Bool.or_self, ↓reduceIte]
  refine ⟨⟨_, rfl, fun q => ?_⟩, ?_⟩
  · rw [compareHalfRoot_eq_real _ _ _ (by linarith [mul_self_nonneg y]) hnorm, hw,
      Complex.inv_re, hnormSq, hre]
    rw [sqrt_div_normSq hnormReal (by linarith [neg_abs_le (x : ℝ)])]
  · have hpart : (Part.real (fmt := fmt) (compareHalfRoot (-x) (x * x + y * y) (x * x + y * y))
        false).Denotes (√((√((x * x + y * y : Rat) : ℝ) - x) / 2) /
          √((x * x + y * y : Rat) : ℝ)) false := by
      refine ⟨_, rfl, fun q => ?_⟩
      rw [compareHalfRoot_eq_real _ _ _ (by linarith [mul_self_nonneg y]) hnorm, Rat.cast_neg,
        sqrt_div_normSq hnormReal (by linarith [le_abs_self (x : ℝ)]), ← sub_eq_add_neg]
    have hneg := hpart.neg
    rw [hw, Complex.inv_im, hnormSq, himag]
    simpa [neg_div] using hneg

/--
For an IEEE descriptor, `rsqrt` of a finite nonzero argument is the reciprocal of the principal
square root with each part rounded once in the direction `mode`.
-/
theorem rsqrt_eq (hfmt : fmt.isIEEE = true) {z : ExecComplex fmt} (hz : isFinite z = true)
    (hne : toComplex z ≠ 0) (mode : Model.IEEERoundingMode := .nearest) :
    rsqrt z mode = (rsqrtExact z).round fmt mode :=
  (Parts.ofUpperHalf_denotes hfmt (fun ζ => toComplex ζ ≠ 0)
    (fun ζ hζ hd => by rwa [toComplex_conj ζ hζ, ne_eq, map_eq_zero])
    (fun _ hζ hd him => rsqrtCore_denotes hζ hd him) hz hne).round mode

/--
For an IEEE descriptor, `rsqrt` of a zero of either sign in each part is `+∞ + NaN i`, the
quotient `(1 + 0 i) / (0 + 0 i)` of C23 G.5.2, in every rounding direction.
-/
theorem rsqrt_zero (hfmt : fmt.isIEEE = true) {z : ExecComplex fmt} (hz : isFinite z = true)
    (hzero : toComplex z = 0) (mode : Model.IEEERoundingMode := .nearest) :
    (rsqrt z mode).re = Model.posInf fmt ∧ Model.isNaN (rsqrt z mode).im = true := by
  obtain ⟨hre, him⟩ := (isFinite_eq_true_iff z).1 hz
  have hzre : Model.isZero z.re = true :=
    (Model.isZero_eq_true_iff_toReal_eq_zero z.re hre).2 (congrArg Complex.re hzero)
  have hzim : Model.isZero z.im = true :=
    (Model.isZero_eq_true_iff_toReal_eq_zero z.im him).2 (congrArg Complex.im hzero)
  have hnan : Model.isNaN (Model.invalidResult fmt) = true := by
    have hencoding := FloatFormat.encoding_eq_ieee_of_isIEEE fmt hfmt
    simp [Model.invalidResult, hencoding, Model.isNaN_canonicalNaN hencoding]
  unfold rsqrt rsqrtParts Parts.ofUpperHalf
  split <;>
    simp [rsqrtCore, propagatedNaN, hzre, hzim, hnan, Parts.conj, Parts.round, Part.round,
      Part.neg, ExecComplex.conj, Model.isNaN_eq_false_of_isFinite_eq_true _ hre,
      Model.isNaN_eq_false_of_isFinite_eq_true _ him,
      Model.isInfinite_eq_false_of_isFinite_eq_true _ hre,
      Model.isInfinite_eq_false_of_isFinite_eq_true _ him]

/-! ## Conjugation at every argument -/

/--
`csqrt (conj z) = conj (csqrt z)` (C23 G.6.5.2), at every argument, a NaN or an infinity included,
in a rounding direction that negation fixes.
-/
theorem sqrt_conj (hfmt : fmt.isIEEE = true) (z : ExecComplex fmt)
    {mode : Model.IEEERoundingMode} (hmode : mode.negate = mode) :
    sqrt (ExecComplex.conj z) mode = ExecComplex.conj (sqrt z mode) :=
  Parts.round_ofUpperHalf_conj hfmt sqrtCore z hmode

/--
`rsqrt (conj z) = conj (rsqrt z)`, at every argument, a NaN or an infinity included, in a
rounding direction that negation fixes.
-/
theorem rsqrt_conj (hfmt : fmt.isIEEE = true) (z : ExecComplex fmt)
    {mode : Model.IEEERoundingMode} (hmode : mode.negate = mode) :
    rsqrt (ExecComplex.conj z) mode = ExecComplex.conj (rsqrt z mode) :=
  Parts.round_ofUpperHalf_conj hfmt rsqrtCore z hmode

end ExecComplex
end FloatLib.Floats.Formats.BinaryInterchange
