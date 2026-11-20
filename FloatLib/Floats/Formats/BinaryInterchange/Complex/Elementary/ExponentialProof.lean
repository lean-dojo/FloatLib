/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.Exponential
public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.LogarithmProof
public import FloatLib.Numerics.Exact.Trigonometric.Proof
public import FloatLib.Numerics.Exact.Product.AngleProof
public import FloatLib.Numerics.Enclosure.Rational.Converges
public import FloatLib.Numerics.Enclosure.Elementary.BinaryGridProof

/-!
# Correct rounding of the complex exponential, hyperbolic and trigonometric functions

For an IEEE descriptor and every finite argument, each part of `ExecComplex.exp`, `sinh`, `cosh`,
`sin` and `cos` is the exact part of Mathlib's `Complex.exp`, `Complex.sinh`, `Complex.cosh`,
`Complex.sin` and `Complex.cos` rounded once in the requested direction (`exp_eq`, `sinh_eq`,
`cosh_eq`, `sin_eq`, `cos_eq`), and `expm1` rounds `Complex.exp w - 1` once at every nonzero
finite argument (`expm1_eq`) and returns a zero unchanged (`expm1_zero`, for every descriptor).
No premise restricts the argument: a part that overflows gives the overflow result of the
direction, a part that underflows is rounded on the subnormal grid, and the comparisons behind
the rounding terminate because the parts are irrational
(`ProductComparison.Admissible.eval_mul_eval_ne_ratCast`).

A part that is exactly zero carries the sign of the limit: `sinh (+0 + i b)` has the real part
`+0 * cos b`, with the sign of `cos b`, and `cosh (+0 + i b)` the imaginary part `+0 * sin b`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace ExecComplex

open FloatLib.Numerics
open ProductComparison (Growth Trig Admissible)

variable {fmt : FloatFormat}

/-- A rational part is an oracle for its value. -/
theorem Part.ofRat_denotes (q : Rat) (zeroSign : Bool) :
    (Part.ofRat (fmt := fmt) q zeroSign).Denotes (q : ℝ) zeroSign :=
  ⟨_, rfl, fun boundary => by simp only [cmp, cmpUsing, Rat.cast_lt]⟩

/-- Subtracting one before rounding subtracts one from the real a part denotes. -/
theorem Part.Denotes.subOne {part : Part fmt} {x : ℝ} {zeroSign : Bool}
    (h : part.Denotes x zeroSign) : part.subOne.Denotes (x - 1) zeroSign := by
  obtain ⟨compare, rfl, hcompare⟩ := h
  refine ⟨_, rfl, fun boundary => ?_⟩
  rw [hcompare]
  push_cast
  simp only [cmp, cmpUsing, sub_lt_iff_lt_add, lt_sub_iff_add_lt]

/-- `expBounds` contains the exponential of every real in the interval. -/
theorem contains_expBounds {exponent : RationalInterval} {t : ℝ} (ht : exponent.Contains t)
    (degree precision : Nat) : (expBounds exponent degree precision).Contains (Real.exp t) :=
  ⟨(Enclosure.BinaryGrid.contains_exp exponent.lo degree precision).1.trans
      (Real.exp_le_exp.mpr ht.1),
    (Real.exp_le_exp.mpr ht.2).trans
      (Enclosure.BinaryGrid.contains_exp exponent.hi degree precision).2⟩

/-- `growthBounds` contains the unbounded factor. -/
theorem contains_growthBounds (growth : Growth) (a : Rat) (precision : Nat) :
    (growthBounds growth a precision).Contains (growth.eval (a : ℝ)) := by
  have hpositive (degree bits : Nat) := contains_expBounds (exponent := ⟨a, a⟩) (t := (a : ℝ))
    ⟨le_refl _, le_refl _⟩ degree bits
  have hnegative (degree bits : Nat) := contains_expBounds (exponent := ⟨-a, -a⟩)
    (t := ((-a : Rat) : ℝ)) ⟨le_refl _, le_refl _⟩ degree bits
  cases growth
  · exact hpositive _ _
  · have hvalue : Growth.sinh.eval (a : ℝ) =
        ((1 / 2 : Rat) : ℝ) * (Real.exp (a : ℝ) - Real.exp ((-a : Rat) : ℝ)) := by
      change Real.sinh (a : ℝ) = _
      rw [Real.sinh_eq]
      push_cast
      ring
    rw [hvalue]
    exact RationalInterval.contains_scale
      (RationalInterval.contains_sub (hpositive _ _) (hnegative _ _)) (1 / 2)
  · have hvalue : Growth.cosh.eval (a : ℝ) =
        ((1 / 2 : Rat) : ℝ) * (Real.exp (a : ℝ) + Real.exp ((-a : Rat) : ℝ)) := by
      change Real.cosh (a : ℝ) = _
      rw [Real.cosh_eq]
      push_cast
      ring
    rw [hvalue]
    exact RationalInterval.contains_scale
      (RationalInterval.contains_add (hpositive _ _) (hnegative _ _)) (1 / 2)

/-- Every enclosure that `productEnclosure?` returns contains the product. -/
theorem contains_productEnclosure? {growth : Growth} {trig : Trig} {a b : Rat}
    {interval : RationalInterval} (h : productEnclosure? fmt growth trig a b = some interval) :
    interval.Contains (growth.eval (a : ℝ) * trig.eval (b : ℝ)) := by
  unfold productEnclosure? at h
  refine contains_orElse (fun _ hsmall => contains_smallProduct? hsmall)
    (fun general hgeneral => ?_) interval h
  split at hgeneral
  · refine contains_of_refineTwice (fun precision enclosure henclosure => ?_) general hgeneral
    obtain ⟨bounded, hbounded, rfl⟩ := Option.map_eq_some_iff.mp henclosure
    exact RationalInterval.contains_mul (contains_growthBounds growth a _)
      (ProductComparison.contains_trigBounds? ⟨le_refl _, le_refl _⟩ hbounded)
  · simp at hgeneral

/--
`productPart` is an oracle for the product of its two factors, given that the supplied rational
is the product wherever the product is rational.
-/
theorem productPart_denotes (growth : Growth) (trig : Trig) (a b exactValue : Rat)
    (zeroSign : Bool)
    (hexact : ¬Admissible growth trig a b →
      growth.eval (a : ℝ) * trig.eval (b : ℝ) = (exactValue : ℝ)) :
    (productPart fmt growth trig a b exactValue zeroSign).Denotes
      (growth.eval (a : ℝ) * trig.eval (b : ℝ)) zeroSign := by
  unfold productPart
  split
  · rename_i h
    have hexact : (Part.real (fmt := fmt)
        (ProductComparison.prepare growth trig a b (cacheLevels fmt) h) zeroSign).Denotes
        (growth.eval (a : ℝ) * trig.eval (b : ℝ)) zeroSign :=
      ⟨_, rfl, fun boundary => ProductComparison.prepare_eq_real growth trig a b _ h boundary⟩
    exact hexact.within fun interval hinterval => contains_productEnclosure? hinterval
  · rename_i h
    rw [hexact h]
    exact Part.ofRat_denotes exactValue zeroSign

/-- A sign that an enclosure settles is the sign of the cosine or the sine. -/
theorem enclosedNegative?_eq {trig : Trig} {y : Rat} {negative : Bool}
    (h : enclosedNegative? trig y = some negative) :
    negative = decide (trig.eval (y : ℝ) < 0) := by
  unfold enclosedNegative? at h
  obtain ⟨bounds, hbounds, h⟩ := Option.bind_eq_some_iff.mp h
  have hcontains := ProductComparison.contains_trigBounds? (x := (y : ℝ))
    ⟨le_refl _, le_refl _⟩ hbounds
  split at h
  · rename_i hnegative
    have hlt : trig.eval (y : ℝ) < 0 :=
      hcontains.2.trans_lt (by exact_mod_cast hnegative)
    rw [← Option.some.inj h]
    exact (decide_eq_true hlt).symm
  · split at h
    · rename_i hpositive
      have hle : ¬trig.eval (y : ℝ) < 0 :=
        not_lt.mpr ((by exact_mod_cast hpositive : (0 : ℝ) < bounds.lo).trans_le hcontains.1).le
      rw [← Option.some.inj h]
      exact (decide_eq_false hle).symm
    · simp at h

/-- The sign test of the cosine at a rational. -/
theorem cosNegative_eq (y : Rat) : cosNegative y = decide (Real.cos (y : ℝ) < 0) := by
  unfold cosNegative
  split
  · rename_i negative h
    exact enclosedNegative?_eq h
  · rw [TrigonometricComparison.prepareCos_eq_real, Bool.eq_iff_iff]
    simp [cmp_eq_lt_iff]

/-- The sign test of the sine at a rational. -/
theorem sinNegative_eq (y : Rat) : sinNegative y = decide (Real.sin (y : ℝ) < 0) := by
  unfold sinNegative
  split
  · rename_i negative h
    exact enclosedNegative?_eq h
  · rw [TrigonometricComparison.prepareSin_eq_real, Bool.eq_iff_iff]
    simp [cmp_eq_lt_iff]

/-- The real and imaginary parts of the complex hyperbolic sine. -/
theorem sinh_mk (x y : ℝ) :
    Complex.sinh ⟨x, y⟩ = ⟨Real.sinh x * Real.cos y, Real.cosh x * Real.sin y⟩ := by
  apply Complex.ext <;>
    simp [Complex.sinh, Complex.exp_re, Complex.exp_im, Real.sinh_eq, Real.cosh_eq] <;> ring

/-- The real and imaginary parts of the complex hyperbolic cosine. -/
theorem cosh_mk (x y : ℝ) :
    Complex.cosh ⟨x, y⟩ = ⟨Real.cosh x * Real.cos y, Real.sinh x * Real.sin y⟩ := by
  apply Complex.ext <;>
    simp [Complex.cosh, Complex.exp_re, Complex.exp_im, Real.sinh_eq, Real.cosh_eq] <;> ring

/-! ## The exponential -/

/-- The exact result of `cexp` at a finite argument, with positive zeros where the imaginary sign
bit is clear. Its value is `Complex.exp` of the argument (`expExact_value`). -/
noncomputable def expExact : ExecComplex fmt → Exact :=
  Exact.ofUpperHalf fun z => ⟨Complex.exp (toComplex z), false, false⟩

/-- At a finite argument the parts of `expCore` are the complex exponential. -/
theorem expCore_denotes {z : ExecComplex fmt} (hz : isFinite z = true) :
    (expCore z).Denotes ⟨Complex.exp (toComplex z), false, false⟩ := by
  obtain ⟨a, b, ha, hb, hw, -⟩ := exists_toRat?_of_isFinite hz
  simp only [expCore, ha, hb, hw]
  refine ⟨?_, ?_⟩
  · rw [Complex.exp_re]
    refine productPart_denotes .exp .cos a b 1 false fun h => ?_
    have hzero : a = 0 ∧ b = 0 := by simpa [Admissible] using h
    simp [Growth.eval, Trig.eval, hzero.1, hzero.2]
  · rw [Complex.exp_im]
    refine productPart_denotes .exp .sin a b 0 false fun h => ?_
    have hzero : b = 0 := by
      by_contra hb0
      exact h ⟨by simp, fun _ => hb0, fun h0 => hb0 h0.2⟩
    simp [Growth.eval, Trig.eval, hzero]

/--
For an IEEE descriptor, `exp` of a finite argument is the complex exponential with each part
rounded once in the direction `mode`.
-/
theorem exp_eq (hfmt : fmt.isIEEE = true) {z : ExecComplex fmt} (hz : isFinite z = true)
    (mode : Model.IEEERoundingMode := .nearest) :
    exp z mode = (expExact z).round fmt mode :=
  (Parts.ofUpperHalf_denotes hfmt (fun _ => True) (fun _ _ _ => trivial)
    (fun _ hζ _ _ => expCore_denotes hζ) hz trivial).round mode

/--
The exact result of `expm1` at a finite nonzero argument: `Complex.exp w - 1` where the imaginary
sign bit is clear, and its conjugate elsewhere.
-/
noncomputable def expm1Exact : ExecComplex fmt → Exact :=
  Exact.ofUpperHalf fun z => ⟨Complex.exp (toComplex z) - 1, false, false⟩

/-- At a finite nonzero argument the parts of `expm1Core` are `Complex.exp w - 1`. -/
theorem expm1Core_denotes {z : ExecComplex fmt} (hz : isFinite z = true)
    (hne : toComplex z ≠ 0) :
    (expm1Core z).Denotes ⟨Complex.exp (toComplex z) - 1, false, false⟩ := by
  have hzero : (Model.isZero z.re && Model.isZero z.im) = false := by
    by_contra hboth
    simp only [Bool.not_eq_false, Bool.and_eq_true] at hboth
    exact hne (by
      rw [toComplex, Model.toReal_eq_zero_of_isZero _ hboth.1,
        Model.toReal_eq_zero_of_isZero _ hboth.2]
      rfl)
  have h := expCore_denotes hz
  simp only [expm1Core, hzero, Bool.false_eq_true, ↓reduceIte]
  exact ⟨by simpa using h.1.subOne, by simpa using h.2⟩

/--
For an IEEE descriptor, `expm1` of a finite nonzero argument is `Complex.exp w - 1` with each
part rounded once in the direction `mode`.
-/
theorem expm1_eq (hfmt : fmt.isIEEE = true) {z : ExecComplex fmt} (hz : isFinite z = true)
    (hne : toComplex z ≠ 0) (mode : Model.IEEERoundingMode := .nearest) :
    expm1 z mode = (expm1Exact z).round fmt mode :=
  (Parts.ofUpperHalf_denotes hfmt (fun ζ => toComplex ζ ≠ 0)
    (fun ζ hζ hd => by rwa [toComplex_conj ζ hζ, ne_eq, map_eq_zero])
    (fun _ hζ hd _ => expm1Core_denotes hζ hd) hz hne).round mode

/-- `expm1` returns a zero argument unchanged, with both signs. -/
theorem expm1_zero {z : ExecComplex fmt} (hz : isFinite z = true) (hzero : toComplex z = 0)
    (mode : Model.IEEERoundingMode := .nearest) : expm1 z mode = z := by
  obtain ⟨hre, him⟩ := (isFinite_eq_true_iff z).1 hz
  have hzre : Model.isZero z.re = true :=
    (Model.isZero_eq_true_iff_toReal_eq_zero z.re hre).2 (congrArg Complex.re hzero)
  have hzim : Model.isZero z.im = true :=
    (Model.isZero_eq_true_iff_toReal_eq_zero z.im him).2 (congrArg Complex.im hzero)
  unfold expm1 expm1Parts Parts.ofUpperHalf
  split <;>
    simp [expm1Core, hzre, hzim, Parts.conj, Parts.round, Part.round, Part.neg, ExecComplex.conj]

/-! ## The hyperbolic functions -/

/-- A finite value with a clear sign bit denotes a nonnegative real. -/
theorem toRat?_nonneg_of_signBit {value : Model fmt} {q : Rat}
    (hq : Model.toRat? value = some q) (hsign : Model.signBit value = false) : 0 ≤ q := by
  have h : (0 : ℝ) ≤ q := by
    rw [← Model.Algebraic.toReal_of_toRat?_eq_some hq]
    exact Model.toReal_nonneg_of_signBit_eq_false hsign
  exact_mod_cast h

/--
The exact result of `csinh` at a finite argument, where both sign bits are clear: the value of
`Complex.sinh`, a zero real part with the sign of `cos (im w)`, and a positive zero imaginary
part. Elsewhere it is extended as an odd function that commutes with conjugation.
-/
noncomputable def sinhExact : ExecComplex fmt → Exact :=
  Exact.ofQuadrant true fun z =>
    ⟨Complex.sinh (toComplex z), decide (Real.cos (toComplex z).im < 0), false⟩

/-- Where both sign bits are clear, the parts of `sinhCore` are the complex hyperbolic sine. -/
theorem sinhCore_denotes {z : ExecComplex fmt} (hz : isFinite z = true)
    (hre : Model.signBit z.re = false) :
    (sinhCore z).Denotes
      ⟨Complex.sinh (toComplex z), decide (Real.cos (toComplex z).im < 0), false⟩ := by
  obtain ⟨a, b, ha, hb, hw, -⟩ := exists_toRat?_of_isFinite hz
  have ha0 := toRat?_nonneg_of_signBit ha hre
  simp only [sinhCore, ha, hb, hw, sinh_mk, cosNegative_eq]
  refine ⟨?_, ?_⟩
  · refine productPart_denotes .sinh .cos a b 0 _ fun h => ?_
    have hzero : a = 0 := by
      by_contra ha1
      exact h ⟨fun _ => lt_of_le_of_ne ha0 (Ne.symm ha1), by simp, fun h0 => ha1 h0.1⟩
    simp [Growth.eval, hzero]
  · refine productPart_denotes .cosh .sin a b 0 false fun h => ?_
    have hzero : b = 0 := by
      by_contra hb0
      exact h ⟨by simp, fun _ => hb0, fun h0 => hb0 h0.2⟩
    simp [Trig.eval, hzero]

/-- At every finite argument the parts of `csinh` before rounding are the exact result. -/
theorem sinhParts_denotes (hfmt : fmt.isIEEE = true) {z : ExecComplex fmt}
    (hz : isFinite z = true) : (sinhParts z).Denotes (sinhExact z) :=
  Parts.ofQuadrant_denotes hfmt true (fun _ => True) (fun _ _ _ => trivial)
    (fun _ _ _ => trivial) (fun _ hζ _ hre _ => sinhCore_denotes hζ hre) hz trivial

/--
For an IEEE descriptor, `sinh` of a finite argument is the complex hyperbolic sine with each part
rounded once in the direction `mode`.
-/
theorem sinh_eq (hfmt : fmt.isIEEE = true) {z : ExecComplex fmt} (hz : isFinite z = true)
    (mode : Model.IEEERoundingMode := .nearest) :
    sinh z mode = (sinhExact z).round fmt mode :=
  (sinhParts_denotes hfmt hz).round mode

/--
The exact result of `ccosh` at a finite argument, where both sign bits are clear: the value of
`Complex.cosh`, and a zero imaginary part with the sign of `sin (im w)` when the real part of
the argument is zero. Elsewhere it is extended as an even function that commutes with
conjugation.
-/
noncomputable def coshExact : ExecComplex fmt → Exact :=
  Exact.ofQuadrant false fun z =>
    ⟨Complex.cosh (toComplex z), false,
      decide ((toComplex z).re = 0) && decide (Real.sin (toComplex z).im < 0)⟩

/-- Where both sign bits are clear, the parts of `coshCore` are the complex hyperbolic cosine. -/
theorem coshCore_denotes {z : ExecComplex fmt} (hz : isFinite z = true)
    (hre : Model.signBit z.re = false) :
    (coshCore z).Denotes
      ⟨Complex.cosh (toComplex z), false,
        decide ((toComplex z).re = 0) && decide (Real.sin (toComplex z).im < 0)⟩ := by
  obtain ⟨a, b, ha, hb, hw, -⟩ := exists_toRat?_of_isFinite hz
  have ha0 := toRat?_nonneg_of_signBit ha hre
  have hflag : decide (a = 0) = decide ((a : ℝ) = 0) := by simp
  simp only [coshCore, ha, hb, hw, cosh_mk, sinNegative_eq, hflag]
  refine ⟨?_, ?_⟩
  · refine productPart_denotes .cosh .cos a b 1 false fun h => ?_
    have hzero : a = 0 ∧ b = 0 := by simpa [Admissible] using h
    simp [Growth.eval, Trig.eval, hzero.1, hzero.2]
  · refine productPart_denotes .sinh .sin a b 0 _ fun h => ?_
    by_cases ha1 : a = 0
    · simp [Growth.eval, ha1]
    · have hzero : b = 0 := by
        by_contra hb0
        exact h ⟨fun _ => lt_of_le_of_ne ha0 (Ne.symm ha1), fun _ => hb0, fun h0 => ha1 h0.1⟩
      simp [Trig.eval, hzero]

/-- At every finite argument the parts of `ccosh` before rounding are the exact result. -/
theorem coshParts_denotes (hfmt : fmt.isIEEE = true) {z : ExecComplex fmt}
    (hz : isFinite z = true) : (coshParts z).Denotes (coshExact z) :=
  Parts.ofQuadrant_denotes hfmt false (fun _ => True) (fun _ _ _ => trivial)
    (fun _ _ _ => trivial) (fun _ hζ _ hre _ => coshCore_denotes hζ hre) hz trivial

/--
For an IEEE descriptor, `cosh` of a finite argument is the complex hyperbolic cosine with each
part rounded once in the direction `mode`.
-/
theorem cosh_eq (hfmt : fmt.isIEEE = true) {z : ExecComplex fmt} (hz : isFinite z = true)
    (mode : Model.IEEERoundingMode := .nearest) :
    cosh z mode = (coshExact z).round fmt mode :=
  (coshParts_denotes hfmt hz).round mode

/-! ## Sine and cosine -/

/-- The exact result of `csin` at a finite argument: `-i csinh (i z)` (C23 G.6.1). -/
noncomputable def sinExact (z : ExecComplex fmt) : Exact := (sinhExact (mulI z)).mulNegI

/--
For an IEEE descriptor, `sin` of a finite argument is `-i sinh (i w)`, the complex sine, with
each part rounded once in the direction `mode`.
-/
theorem sin_eq (hfmt : fmt.isIEEE = true) {z : ExecComplex fmt} (hz : isFinite z = true)
    (mode : Model.IEEERoundingMode := .nearest) :
    sin z mode = (sinExact z).round fmt mode :=
  (sinhParts_denotes hfmt (isFinite_mulI hz)).mulNegI.round mode

/-- The exact result of `ccos` at a finite argument: `ccosh (i z)` (C23 G.6.1). -/
noncomputable def cosExact (z : ExecComplex fmt) : Exact := coshExact (mulI z)

/--
For an IEEE descriptor, `cos` of a finite argument is `cosh (i w)`, the complex cosine, with each
part rounded once in the direction `mode`.
-/
theorem cos_eq (hfmt : fmt.isIEEE = true) {z : ExecComplex fmt} (hz : isFinite z = true)
    (mode : Model.IEEERoundingMode := .nearest) :
    cos z mode = (cosExact z).round fmt mode :=
  (coshParts_denotes hfmt (isFinite_mulI hz)).round mode

/-! ## Conjugation and parity at every argument -/

/--
`cexp (conj z) = conj (cexp z)` (C23 G.6.4.1), at every argument, a NaN or an infinity included, in
a rounding direction that negation fixes.
-/
theorem exp_conj (hfmt : fmt.isIEEE = true) (z : ExecComplex fmt)
    {mode : Model.IEEERoundingMode} (hmode : mode.negate = mode) :
    exp (ExecComplex.conj z) mode = ExecComplex.conj (exp z mode) :=
  Parts.round_ofUpperHalf_conj hfmt expCore z hmode

/--
`expm1 (conj z) = conj (expm1 z)`, at every argument, a NaN or an infinity included, in a
rounding direction that negation fixes.
-/
theorem expm1_conj (hfmt : fmt.isIEEE = true) (z : ExecComplex fmt)
    {mode : Model.IEEERoundingMode} (hmode : mode.negate = mode) :
    expm1 (ExecComplex.conj z) mode = ExecComplex.conj (expm1 z mode) :=
  Parts.round_ofUpperHalf_conj hfmt expm1Core z hmode

/--
`csinh (conj z) = conj (csinh z)` (C23 G.6.3.5), at every argument, a NaN or an infinity included,
in a rounding direction that negation fixes.
-/
theorem sinh_conj (hfmt : fmt.isIEEE = true) (z : ExecComplex fmt)
    {mode : Model.IEEERoundingMode} (hmode : mode.negate = mode) :
    sinh (ExecComplex.conj z) mode = ExecComplex.conj (sinh z mode) :=
  Parts.round_ofUpperHalf_conj hfmt _ z hmode

/--
`csinh` is odd (C23 G.6.3.5): `csinh (-z) = -csinh z` at every argument, a NaN or an infinity
included, in a rounding direction that negation fixes.
-/
theorem sinh_neg (hfmt : fmt.isIEEE = true) (z : ExecComplex fmt)
    {mode : Model.IEEERoundingMode} (hmode : mode.negate = mode) :
    sinh (ExecComplex.neg z) mode = ExecComplex.neg (sinh z mode) :=
  Parts.round_ofQuadrant_neg hfmt sinhCore z hmode

/--
`ccosh (conj z) = conj (ccosh z)` (C23 G.6.3.4), at every argument, a NaN or an infinity included,
in a rounding direction that negation fixes.
-/
theorem cosh_conj (hfmt : fmt.isIEEE = true) (z : ExecComplex fmt)
    {mode : Model.IEEERoundingMode} (hmode : mode.negate = mode) :
    cosh (ExecComplex.conj z) mode = ExecComplex.conj (cosh z mode) :=
  Parts.round_ofUpperHalf_conj hfmt _ z hmode

/--
`ccosh` is even (C23 G.6.3.4): `ccosh (-z) = ccosh z` at every argument, a NaN or an infinity
included, in every rounding direction.
-/
theorem cosh_neg (hfmt : fmt.isIEEE = true) (z : ExecComplex fmt)
    (mode : Model.IEEERoundingMode := .nearest) :
    cosh (ExecComplex.neg z) mode = cosh z mode :=
  Parts.round_ofQuadrant_neg_even hfmt coshCore z mode

/--
`csin (conj z) = conj (csin z)` (C23 G.6.1, paragraph 8, from `csinh`), at every argument, a NaN or
an infinity included, in a rounding direction that negation fixes.
-/
theorem sin_conj (hfmt : fmt.isIEEE = true) (z : ExecComplex fmt)
    {mode : Model.IEEERoundingMode} (hmode : mode.negate = mode) :
    sin (ExecComplex.conj z) mode = ExecComplex.conj (sin z mode) :=
  Parts.round_mulNegI_conj hfmt sinhCore z hmode

/--
`csin` is odd (C23 G.6.1, paragraph 8, from `csinh`): `csin (-z) = -csin z` at every argument, a NaN
or an infinity included, in a rounding direction that negation fixes.
-/
theorem sin_neg (hfmt : fmt.isIEEE = true) (z : ExecComplex fmt)
    {mode : Model.IEEERoundingMode} (hmode : mode.negate = mode) :
    sin (ExecComplex.neg z) mode = ExecComplex.neg (sin z mode) :=
  Parts.round_mulNegI_neg hfmt sinhCore z hmode

/--
`ccos (conj z) = conj (ccos z)` (C23 G.6.1, paragraph 8, from `ccosh`), at every argument, a NaN or
an infinity included, in a rounding direction that negation fixes.
-/
theorem cos_conj (hfmt : fmt.isIEEE = true) (z : ExecComplex fmt)
    {mode : Model.IEEERoundingMode} (hmode : mode.negate = mode) :
    cos (ExecComplex.conj z) mode = ExecComplex.conj (cos z mode) := by
  have h := Parts.ofQuadrant_neg_re hfmt false coshCore (mulI z)
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  rw [cos, cosParts, coshParts,
    show mulI (ExecComplex.conj z) = ⟨Model.neg (mulI z).re, (mulI z).im⟩ from rfl, h,
    Parts.round_conj_of_negate hfmt _ hmode]
  rfl

/--
`ccos` is even (C23 G.6.1, paragraph 8, from `ccosh`): `ccos (-z) = ccos z` at every argument, in
every rounding direction.
-/
theorem cos_neg (hfmt : fmt.isIEEE = true) (z : ExecComplex fmt)
    (mode : Model.IEEERoundingMode := .nearest) :
    cos (ExecComplex.neg z) mode = cos z mode :=
  Parts.round_ofQuadrant_neg_even hfmt coshCore (mulI z) mode

end ExecComplex
end FloatLib.Floats.Formats.BinaryInterchange
