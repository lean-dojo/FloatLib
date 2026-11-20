/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.Tangent
public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.ExponentialProof

/-!
# Correct rounding of the complex tangents

For an IEEE descriptor and every finite argument, each part of `ExecComplex.tanh` is the exact
part of `Complex.tanh` rounded once in the requested direction (`tanh_eq`), and `ExecComplex.tan`
is `-i tanh (i w)` rounded the same way (`tan_eq`). No premise restricts the argument: a rational
is never a pole of either function, since the denominator `cosh 2a + cos 2b` does not vanish at
rational `a` and `b`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace ExecComplex

open FloatLib.Numerics

variable {fmt : FloatFormat}

/-- The parts of the complex hyperbolic tangent, where the denominator does not vanish. -/
theorem tanh_mk (a b : ℝ) (hD : Real.cosh (2 * a) + Real.cos (2 * b) ≠ 0) :
    Complex.tanh ⟨a, b⟩ = ⟨TanhComparison.re a b, TanhComparison.im a b⟩ := by
  have h1 := Real.cosh_sq a
  have h2 := Real.sin_sq_add_cos_sq b
  have hden : Real.cosh a * Real.cos b * (Real.cosh a * Real.cos b) +
      Real.sinh a * Real.sin b * (Real.sinh a * Real.sin b) =
      (Real.cosh (2 * a) + Real.cos (2 * b)) / 2 := by
    rw [Real.cosh_two_mul, Real.cos_two_mul]
    linear_combination (Real.cos b ^ 2 - 1 / 2) * h1 + Real.sinh a ^ 2 * h2
  have hhalf : (Real.cosh (2 * a) + Real.cos (2 * b)) / 2 ≠ 0 := div_ne_zero hD two_ne_zero
  rw [Complex.tanh_eq_sinh_div_cosh, sinh_mk, cosh_mk]
  apply Complex.ext
  · rw [Complex.div_re, Complex.normSq_mk, hden, ← add_div, TanhComparison.re,
      div_eq_div_iff hhalf hD, Real.sinh_two_mul]
    linear_combination (Real.sinh a * Real.cosh a * (Real.cosh (2 * a) + Real.cos (2 * b))) * h2
  · rw [Complex.div_im, Complex.normSq_mk, hden, ← sub_div, TanhComparison.im,
      div_eq_div_iff hhalf hD, Real.sin_two_mul]
    linear_combination (Real.sin b * Real.cos b * (Real.cosh (2 * a) + Real.cos (2 * b))) * h1

/-- Every enclosure that `tanBounds?` returns contains the tangent. -/
theorem contains_tanBounds? {b : Rat} {precision : Nat} {interval : RationalInterval}
    (h : tanBounds? b precision = some interval) : interval.Contains (Real.tan (b : ℝ)) := by
  unfold tanBounds? at h
  obtain ⟨sine, hsine, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨cosine, hcosine, h⟩ := Option.bind_eq_some_iff.mp h
  have hs : sine.Contains (Real.sin (b : ℝ)) :=
    ProductComparison.contains_trigBounds? (trig := .sin) ⟨le_refl _, le_refl _⟩ hsine
  have hc : cosine.Contains (Real.cos (b : ℝ)) :=
    ProductComparison.contains_trigBounds? (trig := .cos) ⟨le_refl _, le_refl _⟩ hcosine
  rw [Real.tan_eq_sin_div_cos]
  split at h
  · rename_i hpositive
    rw [← Option.some.inj h]
    exact RationalInterval.contains_divPositive hs hc hpositive
  · split at h
    · rename_i hnegative
      rw [← Option.some.inj h, ← neg_div_neg_eq]
      exact RationalInterval.contains_divPositive (RationalInterval.contains_neg hs)
        (RationalInterval.contains_neg hc) (neg_pos.mpr hnegative)
    · simp at h

/-- `decayBounds` contains `exp (-2a)`. -/
theorem contains_decayBounds (a : Rat) (precision : Nat) :
    (decayBounds fmt a precision).Contains (Real.exp (-(2 * (a : ℝ)))) := by
  unfold decayBounds
  split
  · exact contains_expBounds (exponent := ⟨-(2 * a), -(2 * a)⟩)
      ⟨by push_cast; exact le_refl _, by push_cast; exact le_refl _⟩ _ _
  · rename_i hcap
    have hle : -(2 * (a : ℝ)) ≤ ((-(growthCap fmt : Rat) : Rat) : ℝ) := by
      have h : ((growthCap fmt : Rat) : ℝ) < 2 * (a : ℝ) := by exact_mod_cast not_le.mp hcap
      push_cast at h ⊢
      linarith
    exact ⟨by simpa using (Real.exp_pos _).le,
      (Real.exp_le_exp.mpr hle).trans (contains_expBounds
        (exponent := ⟨-(growthCap fmt : Rat), -(growthCap fmt : Rat)⟩)
        ⟨le_refl _, le_refl _⟩ _ _).2⟩

/-- Every enclosure that `tanhFrom` returns contains the part of the tangent, from enclosures
of `exp (-2a)`, `cos b` and `sin b`. -/
theorem contains_tanhFrom {imaginary : Bool} {u cosine sine : RationalInterval} {a b : Rat}
    {interval : RationalInterval} (hu : u.Contains (Real.exp (-(2 * (a : ℝ)))))
    (hc : cosine.Contains (Real.cos (b : ℝ))) (hs : sine.Contains (Real.sin (b : ℝ)))
    (h : tanhFrom imaginary u cosine sine = some interval) :
    interval.Contains (if imaginary then TanhComparison.im a b else TanhComparison.re a b) := by
  unfold tanhFrom at h
  dsimp only at h
  have hv := RationalInterval.contains_sub (RationalInterval.contains_point 1) hu
  have hw := RationalInterval.contains_add (RationalInterval.contains_point 1) hu
  have hden := RationalInterval.contains_add (RationalInterval.contains_mul hv hv)
    (RationalInterval.contains_mul (RationalInterval.contains_scale hu 4)
      (RationalInterval.contains_mul hc hc))
  split at h
  · rename_i hpos
    rw [← Option.some.inj h]
    cases imaginary
    · have hvalue := RationalInterval.contains_divPositive
        (RationalInterval.contains_mul hv hw) hden hpos
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [TanhComparison.re_eq_decay]
      simpa only [Rat.cast_one, Rat.cast_ofNat] using hvalue
    · have hvalue := RationalInterval.contains_divPositive
        (RationalInterval.contains_mul (RationalInterval.contains_scale hu 4)
          (RationalInterval.contains_mul hs hc)) hden hpos
      simp only [↓reduceIte]
      rw [TanhComparison.im_eq_decay]
      simpa only [Rat.cast_one, Rat.cast_ofNat] using hvalue
  · simp at h

/-- Every enclosure that `tanhBounds?` returns contains the part of the tangent. -/
theorem contains_tanhBounds? {imaginary : Bool} {u : RationalInterval} {a b : Rat}
    {precision : Nat} {interval : RationalInterval}
    (hu : u.Contains (Real.exp (-(2 * (a : ℝ)))))
    (h : tanhBounds? imaginary u b precision = some interval) :
    interval.Contains (if imaginary then TanhComparison.im a b else TanhComparison.re a b) := by
  unfold tanhBounds? at h
  obtain ⟨cosine, hcosine, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨sine, hsine, h⟩ := Option.bind_eq_some_iff.mp h
  exact contains_tanhFrom hu
    (ProductComparison.contains_trigBounds? (trig := .cos) ⟨le_refl _, le_refl _⟩ hcosine)
    (ProductComparison.contains_trigBounds? (trig := .sin) ⟨le_refl _, le_refl _⟩ hsine) h

/-- Every enclosure that `smallTanh?` returns contains the part of the tangent. -/
theorem contains_smallTanh? {imaginary : Bool} {a b : Rat} {interval : RationalInterval}
    (ha : 0 < a) (h : smallTanh? fmt imaginary a b = some interval) :
    interval.Contains (if imaginary then TanhComparison.im a b else TanhComparison.re a b) := by
  unfold smallTanh? at h
  split at h
  · rename_i hsmall
    obtain ⟨given, hgiven, htight⟩ := Option.bind_eq_some_iff.mp h
    rw [← eq_of_tightOnly htight]
    have hdecay : |(-(2 * a) : Rat)| ≤ 1 := by
      rw [abs_neg, abs_of_pos (by linarith)]
      linarith [hsmall.1]
    have hu := Enclosure.contains_expSmall (-(2 * a)) (smallDegree fmt (max (2 * a) |b|)) hdecay
    have hcast : ((-(2 * a) : Rat) : ℝ) = -(2 * (a : ℝ)) := by push_cast; ring
    rw [hcast] at hu
    exact contains_tanhFrom hu (Enclosure.contains_cos b _) (Enclosure.contains_sin b _) hgiven
  · simp at h

/-- Every enclosure that `smallTan?` returns contains the tangent. -/
theorem contains_smallTan? {b : Rat} {interval : RationalInterval}
    (h : smallTan? fmt b = some interval) : interval.Contains (Real.tan (b : ℝ)) := by
  unfold smallTan? at h
  split at h
  · rename_i hsmall
    rw [← eq_of_tightOnly h, Real.tan_eq_sin_div_cos]
    exact RationalInterval.contains_divPositive (Enclosure.contains_sin b _)
      (Enclosure.contains_cos b _) hsmall.2
  · simp at h

/-- Every enclosure that `tanhEnclosure?` returns contains the part of the tangent. -/
theorem contains_tanhEnclosure? {imaginary : Bool} {a b : Rat} {interval : RationalInterval}
    (h : tanhEnclosure? fmt imaginary a b = some interval) :
    interval.Contains (if imaginary then TanhComparison.im a b else TanhComparison.re a b) := by
  unfold tanhEnclosure? at h
  split at h
  · rename_i ha
    exact contains_orElse (fun _ hsmall => contains_smallTanh? ha hsmall)
      (contains_of_refineTwice
        (fun precision _ henclosure =>
          contains_tanhBounds? (contains_decayBounds a precision) henclosure)) interval h
  · simp at h

/--
The exact result of `ctanh` at a finite argument: `Complex.tanh` where both sign bits are clear,
extended as an odd function that commutes with conjugation.
-/
noncomputable def tanhExact : ExecComplex fmt → Exact :=
  Exact.ofQuadrant true fun z => ⟨Complex.tanh (toComplex z), false, false⟩

/-- Where both sign bits are clear, the parts of `tanhCore` are the complex hyperbolic tangent. -/
theorem tanhCore_denotes {z : ExecComplex fmt} (hz : isFinite z = true)
    (hre : Model.signBit z.re = false) :
    (tanhCore z).Denotes ⟨Complex.tanh (toComplex z), false, false⟩ := by
  obtain ⟨a, b, ha, hb, hw, -⟩ := exists_toRat?_of_isFinite hz
  have ha0 := toRat?_nonneg_of_signBit ha hre
  simp only [tanhCore, ha, hb, hw]
  split
  · rename_i hzero
    have hcos : Real.cos (b : ℝ) ≠ 0 := by
      by_cases hb0 : b = 0
      · simp [hb0]
      · exact (Enclosure.irrational_cos_ratCast b hb0).ne_zero
    have hD : Real.cosh (2 * ((a : Rat) : ℝ)) + Real.cos (2 * (b : ℝ)) ≠ 0 := by
      rw [hzero, Real.cos_two_mul]
      simp only [Rat.cast_zero, mul_zero, Real.cosh_zero]
      have := pow_pos (abs_pos.mpr hcos) 2
      rw [sq_abs] at this
      linarith
    rw [tanh_mk _ _ hD]
    refine ⟨?_, ?_⟩
    · have h := Part.ofRat_denotes (fmt := fmt) 0 false
      simpa [TanhComparison.re, hzero] using h
    · have htan : Real.tan (b : ℝ) = TanhComparison.im ((a : Rat) : ℝ) (b : ℝ) := by
        simp only [TanhComparison.im, hzero, Rat.cast_zero, mul_zero, Real.cosh_zero]
        rw [Real.tan_eq_sin_div_cos, Real.sin_two_mul, Real.cos_two_mul, eq_div_iff (by
          have := pow_pos (abs_pos.mpr hcos) 2
          rw [sq_abs] at this
          linarith)]
        field_simp
        ring
      have hexact : (Part.real (fmt := fmt)
          (TrigonometricComparison.prepareTan b (cacheLevels fmt)).compare false).Denotes
          (TanhComparison.im ((a : Rat) : ℝ) (b : ℝ)) false :=
        ⟨_, rfl, fun boundary => by rw [TrigonometricComparison.prepareTan_eq_real, htan]⟩
      exact hexact.within fun interval hinterval => by
        rw [← htan]
        exact contains_orElse (fun _ hsmall => contains_smallTan? hsmall)
          (contains_of_refineTwice (fun _ _ henclosure => contains_tanBounds? henclosure))
          interval hinterval
  · rename_i hne
    have hpos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm hne)
    have haR : ((a : Rat) : ℝ) ≠ 0 := by exact_mod_cast hne
    rw [tanh_mk _ _ (TanhComparison.denominator_pos haR _).ne']
    refine ⟨?_, ?_⟩
    · have hexact : (Part.real (fmt := fmt)
          (TanhComparison.compareRe a b (cacheLevels fmt) hne) false).Denotes
          (TanhComparison.re a b) false :=
        ⟨_, rfl, TanhComparison.compareRe_eq_real a b _ hpos⟩
      exact hexact.within fun interval hinterval => by
        simpa using contains_tanhEnclosure? hinterval
    · have hexact : (Part.real (fmt := fmt)
          (TanhComparison.compareIm a b (cacheLevels fmt) hne) false).Denotes
          (TanhComparison.im a b) false :=
        ⟨_, rfl, TanhComparison.compareIm_eq_real a b _ hpos⟩
      exact hexact.within fun interval hinterval => by
        simpa using contains_tanhEnclosure? hinterval

/-- At every finite argument the parts of `ctanh` before rounding are the exact result. -/
theorem tanhParts_denotes (hfmt : fmt.isIEEE = true) {z : ExecComplex fmt}
    (hz : isFinite z = true) : (tanhParts z).Denotes (tanhExact z) :=
  Parts.ofQuadrant_denotes hfmt true (fun _ => True) (fun _ _ _ => trivial)
    (fun _ _ _ => trivial) (fun _ hζ _ hre _ => tanhCore_denotes hζ hre) hz trivial

/--
For an IEEE descriptor, `tanh` of a finite argument is the complex hyperbolic tangent with each
part rounded once in the direction `mode`.
-/
theorem tanh_eq (hfmt : fmt.isIEEE = true) {z : ExecComplex fmt} (hz : isFinite z = true)
    (mode : Model.IEEERoundingMode := .nearest) :
    tanh z mode = (tanhExact z).round fmt mode :=
  (tanhParts_denotes hfmt hz).round mode

/-- The exact result of `ctan` at a finite argument: `-i ctanh (i z)` (C23 G.6.1). -/
noncomputable def tanExact (z : ExecComplex fmt) : Exact := (tanhExact (mulI z)).mulNegI

/--
For an IEEE descriptor, `tan` of a finite argument is `-i tanh (i w)`, the complex tangent, with
each part rounded once in the direction `mode`.
-/
theorem tan_eq (hfmt : fmt.isIEEE = true) {z : ExecComplex fmt} (hz : isFinite z = true)
    (mode : Model.IEEERoundingMode := .nearest) :
    tan z mode = (tanExact z).round fmt mode :=
  (tanhParts_denotes hfmt (isFinite_mulI hz)).mulNegI.round mode

/-! ## Conjugation and parity at every argument -/

/--
`ctanh (conj z) = conj (ctanh z)` (C23 G.6.3.6), at every argument, a NaN or an infinity included,
in a rounding direction that negation fixes.
-/
theorem tanh_conj (hfmt : fmt.isIEEE = true) (z : ExecComplex fmt)
    {mode : Model.IEEERoundingMode} (hmode : mode.negate = mode) :
    tanh (ExecComplex.conj z) mode = ExecComplex.conj (tanh z mode) :=
  Parts.round_ofUpperHalf_conj hfmt _ z hmode

/--
`ctanh` is odd (C23 G.6.3.6): `ctanh (-z) = -ctanh z` at every argument, a NaN or an infinity
included, in a rounding direction that negation fixes.
-/
theorem tanh_neg (hfmt : fmt.isIEEE = true) (z : ExecComplex fmt)
    {mode : Model.IEEERoundingMode} (hmode : mode.negate = mode) :
    tanh (ExecComplex.neg z) mode = ExecComplex.neg (tanh z mode) :=
  Parts.round_ofQuadrant_neg hfmt tanhCore z hmode

/--
`ctan (conj z) = conj (ctan z)` (C23 G.6.1, paragraph 8, from `ctanh`), at every argument, a NaN or
an infinity included, in a rounding direction that negation fixes.
-/
theorem tan_conj (hfmt : fmt.isIEEE = true) (z : ExecComplex fmt)
    {mode : Model.IEEERoundingMode} (hmode : mode.negate = mode) :
    tan (ExecComplex.conj z) mode = ExecComplex.conj (tan z mode) :=
  Parts.round_mulNegI_conj hfmt tanhCore z hmode

/--
`ctan` is odd (C23 G.6.1, paragraph 8, from `ctanh`): `ctan (-z) = -ctan z` at every argument, a NaN
or an infinity included, in a rounding direction that negation fixes.
-/
theorem tan_neg (hfmt : fmt.isIEEE = true) (z : ExecComplex fmt)
    {mode : Model.IEEERoundingMode} (hmode : mode.negate = mode) :
    tan (ExecComplex.neg z) mode = ExecComplex.neg (tan z mode) :=
  Parts.round_mulNegI_neg hfmt tanhCore z hmode

end ExecComplex
end FloatLib.Floats.Formats.BinaryInterchange
