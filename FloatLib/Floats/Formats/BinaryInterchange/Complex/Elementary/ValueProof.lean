/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.AlgebraicProof
public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.InverseProof
public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.TangentProof

/-!
# The exact results are the complex functions of Mathlib

The exact result of each function is stated as C23 Annex G states the function: in a half-plane
or a quadrant, and extended by `f (conj z) = conj (f z)` and the parity. This file states the
value at every finite argument.

* `expExact_value`, `expm1Exact_value`, `sinhExact_value`, `coshExact_value`, `tanhExact_value`,
  `sinExact_value`, `cosExact_value`, `tanExact_value`: the value is `Complex.exp`,
  `Complex.sinh`, ... of Mathlib at the argument, in every half-plane and quadrant.
* `sqrtExact_value`, `rsqrtExact_value`, `logExact_value`, `log1pExact_value`,
  `atanhExact_value`, `atanExact_value`: the value is Mathlib's principal `w ^ (2⁻¹ : ℂ)`, its
  reciprocal, `Complex.log w`, `Complex.log (1 + w)`, `Complex.log ((1 + w) / (1 - w)) / 2` and
  `Complex.arctan w` at every finite argument off the branch cut, and on the cut where the sign
  bit that selects its side is clear (away from the pole `1` of `atanh` and `-i` of `atan`). On
  the cut with that sign bit set the value is the mirror image, the limit from the other side
  (C23 7.3.3), which a function of the complex number cannot return.
* Mathlib has no complex inverse sine or cosine. `asinhValue_eq_log` and `acoshValue_eq_log`
  identify the explicit values with the principal expressions of Kahan's Table 1,
  `log (w + √(1 + w²))` and `2 log (√((w + 1) / 2) + √((w - 1) / 2))`, in Mathlib's principal
  logarithm and square root, in the half-plane where C23 Annex G states each function, and
  `asinhExact_value`, `asinExact_value`, `acoshExact_value`, `acosExact_value` state it for the
  exact results where the sign bits put the argument there.
* On both sides of a cut the value solves the equation of the function: `sqrtExact_value_sq`,
  `rsqrtExact_value_sq`, `exp_logExact_value`, `exp_log1pExact_value`, `sinh_asinhExact_value`,
  `sin_asinExact_value`, `cosh_acoshExact_value`, `cos_acosExact_value`, `tanh_atanhExact_value`
  and `tan_atanExact_value`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace ExecComplex

open FloatLib.Numerics
open ConfocalComparison (major minor)

variable {fmt : FloatFormat}

/--
The value of an extension by conjugation is the function of the argument, where the imaginary
sign bit is clear or the function commutes with conjugation at the argument.
-/
theorem Exact.ofUpperHalf_value {f : ℂ → ℂ} {spec : ExecComplex fmt → Exact}
    (hspec : ∀ ζ : ExecComplex fmt, isFinite ζ = true → (spec ζ).value = f (toComplex ζ))
    {z : ExecComplex fmt} (hz : isFinite z = true)
    (hside : Model.signBit z.im = false ∨
      f (starRingEnd ℂ (toComplex z)) = starRingEnd ℂ (f (toComplex z))) :
    (Exact.ofUpperHalf spec z).value = f (toComplex z) := by
  unfold Exact.ofUpperHalf
  split
  · rename_i hsign
    rcases hside with h | h
    · rw [hsign] at h
      contradiction
    · simp only [Exact.conj]
      rw [hspec _ (isFinite_conj hz), toComplex_conj z hz, h, Complex.conj_conj]
  · exact hspec z hz

/--
The value of an extension by conjugation and parity, for an odd or even function of the argument
that commutes with conjugation.
-/
theorem Exact.ofQuadrant_value (odd : Bool) {f : ℂ → ℂ}
    (hf : ∀ w, f (starRingEnd ℂ w) = starRingEnd ℂ (f w))
    (hparity : ∀ w, f (-w) = if odd then -f w else f w) {spec : ExecComplex fmt → Exact}
    (hspec : ∀ ζ : ExecComplex fmt, isFinite ζ = true → (spec ζ).value = f (toComplex ζ))
    {z : ExecComplex fmt} (hz : isFinite z = true) :
    (Exact.ofQuadrant odd spec z).value = f (toComplex z) := by
  unfold Exact.ofQuadrant
  refine Exact.ofUpperHalf_value (fun ζ hζ => ?_) hz (Or.inr (hf _))
  split
  · have hfinite : isFinite (⟨Model.neg ζ.re, ζ.im⟩ : ExecComplex fmt) = true := by
      simpa [isFinite] using hζ
    have hreflect : toComplex (⟨Model.neg ζ.re, ζ.im⟩ : ExecComplex fmt) =
        -starRingEnd ℂ (toComplex ζ) := by
      rw [toComplex_neg_re hζ]
      apply Complex.ext <;> simp
    have hvalue := hspec _ hfinite
    rw [hreflect, hparity, hf] at hvalue
    cases odd
    · simp only [Bool.false_eq_true, ↓reduceIte, Exact.conj] at hvalue ⊢
      rw [hvalue, Complex.conj_conj]
    · simp only [↓reduceIte] at hvalue ⊢
      rw [hvalue]
      apply Complex.ext <;> simp
  · exact hspec ζ hζ

/--
An extension by conjugation is inverted by a function that commutes with conjugation and inverts
the results where the imaginary sign bit is clear, on a set of arguments closed under
conjugation.
-/
theorem Exact.ofUpperHalf_inverse (hfmt : fmt.isIEEE = true) {F : ℂ → ℂ}
    (hF : ∀ w, F (starRingEnd ℂ w) = starRingEnd ℂ (F w)) (domain : ℂ → Prop)
    (hconj : ∀ w, domain w → domain (starRingEnd ℂ w)) {spec : ExecComplex fmt → Exact}
    (hspec : ∀ ζ : ExecComplex fmt, isFinite ζ = true → domain (toComplex ζ) →
      Model.signBit ζ.im = false → F (spec ζ).value = toComplex ζ)
    {z : ExecComplex fmt} (hz : isFinite z = true) (hdomain : domain (toComplex z)) :
    F (Exact.ofUpperHalf spec z).value = toComplex z := by
  unfold Exact.ofUpperHalf
  cases hsign : Model.signBit z.im with
  | false => simpa using hspec z hz hdomain hsign
  | true =>
      simp only [↓reduceIte, Exact.conj]
      rw [hF, hspec _ (isFinite_conj hz) (by rw [toComplex_conj z hz]; exact hconj _ hdomain)
          (by simp [ExecComplex.conj, signBit_neg hfmt, hsign]),
        toComplex_conj z hz, Complex.conj_conj]

/--
An odd extension by conjugation and parity is inverted by an odd function that commutes with
conjugation and inverts the results where both sign bits are clear, on a set of arguments closed
under conjugation and negation.
-/
theorem Exact.ofQuadrant_inverse (hfmt : fmt.isIEEE = true) {F : ℂ → ℂ}
    (hF : ∀ w, F (starRingEnd ℂ w) = starRingEnd ℂ (F w)) (hodd : ∀ w, F (-w) = -F w)
    (domain : ℂ → Prop) (hconj : ∀ w, domain w → domain (starRingEnd ℂ w))
    (hneg : ∀ w, domain w → domain (-w)) {spec : ExecComplex fmt → Exact}
    (hspec : ∀ ζ : ExecComplex fmt, isFinite ζ = true → domain (toComplex ζ) →
      Model.signBit ζ.re = false → F (spec ζ).value = toComplex ζ)
    {z : ExecComplex fmt} (hz : isFinite z = true) (hdomain : domain (toComplex z)) :
    F (Exact.ofQuadrant true spec z).value = toComplex z := by
  unfold Exact.ofQuadrant
  refine Exact.ofUpperHalf_inverse hfmt hF domain hconj (fun ζ hζ hd _ => ?_) hz hdomain
  cases hsign : Model.signBit ζ.re with
  | false => simpa using hspec ζ hζ hd hsign
  | true =>
      have hfinite : isFinite (⟨Model.neg ζ.re, ζ.im⟩ : ExecComplex fmt) = true := by
        simpa [isFinite] using hζ
      have hreflect : toComplex (⟨Model.neg ζ.re, ζ.im⟩ : ExecComplex fmt) =
          -starRingEnd ℂ (toComplex ζ) := by
        rw [toComplex_neg_re hζ]
        apply Complex.ext <;> simp
      have hvalue := hspec _ hfinite (by rw [hreflect]; exact hneg _ (hconj _ hd))
        (by simp [signBit_neg hfmt, hsign])
      rw [hreflect] at hvalue
      simp only [↓reduceIte]
      rw [show (⟨-(spec ⟨Model.neg ζ.re, ζ.im⟩).value.re,
          (spec ⟨Model.neg ζ.re, ζ.im⟩).value.im⟩ : ℂ) =
          -starRingEnd ℂ (spec ⟨Model.neg ζ.re, ζ.im⟩).value by apply Complex.ext <;> simp,
        hodd, hF, hvalue]
      simp

variable {z : ExecComplex fmt}

/-! ## Entire functions and the tangents -/

/-- The exact result of `cexp` is `Complex.exp` at every finite argument. -/
theorem expExact_value (hz : isFinite z = true) :
    (expExact z).value = Complex.exp (toComplex z) :=
  Exact.ofUpperHalf_value (fun _ _ => rfl) hz (Or.inr (Complex.exp_conj _))

/-- The exact result of `expm1` is `Complex.exp w - 1` at every finite argument. -/
theorem expm1Exact_value (hz : isFinite z = true) :
    (expm1Exact z).value = Complex.exp (toComplex z) - 1 :=
  Exact.ofUpperHalf_value (f := fun w => Complex.exp w - 1) (fun _ _ => rfl) hz
    (Or.inr (by simp [Complex.exp_conj]))

/-- The exact result of `csinh` is `Complex.sinh` at every finite argument. -/
theorem sinhExact_value (hz : isFinite z = true) :
    (sinhExact z).value = Complex.sinh (toComplex z) :=
  Exact.ofQuadrant_value true Complex.sinh_conj (fun w => by simp [Complex.sinh_neg])
    (fun _ _ => rfl) hz

/-- The exact result of `ccosh` is `Complex.cosh` at every finite argument. -/
theorem coshExact_value (hz : isFinite z = true) :
    (coshExact z).value = Complex.cosh (toComplex z) :=
  Exact.ofQuadrant_value false Complex.cosh_conj (fun w => by simp [Complex.cosh_neg])
    (fun _ _ => rfl) hz

/-- The exact result of `ctanh` is `Complex.tanh` at every finite argument. -/
theorem tanhExact_value (hz : isFinite z = true) :
    (tanhExact z).value = Complex.tanh (toComplex z) :=
  Exact.ofQuadrant_value true Complex.tanh_conj (fun w => by simp [Complex.tanh_neg])
    (fun _ _ => rfl) hz

/-- The exact result of `csin` is `Complex.sin` at every finite argument. -/
theorem sinExact_value (hz : isFinite z = true) :
    (sinExact z).value = Complex.sin (toComplex z) := by
  simp only [sinExact, Exact.mulNegI]
  rw [sinhExact_value (isFinite_mulI hz), toComplex_mulI hz, mul_comm Complex.I,
    Complex.sinh_mul_I]
  linear_combination (-(Complex.sin (toComplex z))) * Complex.I_mul_I

/-- The exact result of `ccos` is `Complex.cos` at every finite argument. -/
theorem cosExact_value (hz : isFinite z = true) :
    (cosExact z).value = Complex.cos (toComplex z) := by
  rw [cosExact, coshExact_value (isFinite_mulI hz), toComplex_mulI hz, mul_comm Complex.I,
    Complex.cosh_mul_I]

/-- The exact result of `ctan` is `Complex.tan` at every finite argument. -/
theorem tanExact_value (hz : isFinite z = true) :
    (tanExact z).value = Complex.tan (toComplex z) := by
  simp only [tanExact, Exact.mulNegI]
  rw [tanhExact_value (isFinite_mulI hz), toComplex_mulI hz, mul_comm Complex.I,
    Complex.tanh_mul_I]
  linear_combination (-(Complex.tan (toComplex z))) * Complex.I_mul_I

/-! ## Roots and logarithms -/

/-- The principal square root commutes with conjugation off the negative real axis. -/
theorem conj_cpow_inv_two {x : ℂ} (hx : x.arg ≠ Real.pi) :
    starRingEnd ℂ x ^ (2⁻¹ : ℂ) = starRingEnd ℂ (x ^ (2⁻¹ : ℂ)) := by
  have h := Complex.conj_cpow x (2⁻¹ : ℂ) hx
  rwa [map_inv₀, map_ofNat] at h

/--
The exact result of `csqrt` is Mathlib's principal power `w ^ (2⁻¹ : ℂ)` at every finite argument
off the negative real axis, and on that axis where the imaginary sign bit is clear.
-/
theorem sqrtExact_value (hz : isFinite z = true)
    (hside : Model.signBit z.im = false ∨ (toComplex z).arg ≠ Real.pi) :
    (sqrtExact z).value = toComplex z ^ (2⁻¹ : ℂ) :=
  Exact.ofUpperHalf_value (f := fun w => w ^ (2⁻¹ : ℂ)) (fun _ _ => rfl) hz
    (hside.imp_right conj_cpow_inv_two)

/--
The exact result of `rsqrt` is the reciprocal of Mathlib's principal power `w ^ (2⁻¹ : ℂ)` at
every finite argument off the negative real axis, and on that axis where the imaginary sign bit
is clear.
-/
theorem rsqrtExact_value (hz : isFinite z = true)
    (hside : Model.signBit z.im = false ∨ (toComplex z).arg ≠ Real.pi) :
    (rsqrtExact z).value = (toComplex z ^ (2⁻¹ : ℂ))⁻¹ :=
  Exact.ofUpperHalf_value (f := fun w => (w ^ (2⁻¹ : ℂ))⁻¹) (fun _ _ => rfl) hz
    (hside.imp_right fun h => by simp [conj_cpow_inv_two h])

/-- The exact result of `csqrt` squares to the argument, at every finite argument. -/
theorem sqrtExact_value_sq (hfmt : fmt.isIEEE = true) (hz : isFinite z = true) :
    (sqrtExact z).value ^ 2 = toComplex z :=
  Exact.ofUpperHalf_inverse hfmt (F := fun w => w ^ 2) (fun w => by simp) (fun _ => True)
    (fun _ _ => trivial) (fun ζ _ _ _ => Complex.cpow_ofNat_inv_pow (toComplex ζ) 2) hz trivial

/-- The exact result of `rsqrt` is a reciprocal square root of every finite nonzero argument. -/
theorem rsqrtExact_value_sq (hfmt : fmt.isIEEE = true) (hz : isFinite z = true)
    (hne : toComplex z ≠ 0) : (rsqrtExact z).value ^ 2 * toComplex z = 1 := by
  have h := Exact.ofUpperHalf_inverse hfmt (F := fun w => (w ^ 2)⁻¹) (fun w => by simp)
    (fun _ => True) (fun _ _ => trivial)
    (spec := fun ζ => (⟨(toComplex ζ ^ (2⁻¹ : ℂ))⁻¹, false, true⟩ : Exact))
    (fun ζ _ _ _ => by
      change (((toComplex ζ ^ (2⁻¹ : ℂ))⁻¹) ^ 2)⁻¹ = toComplex ζ
      rw [inv_pow, inv_inv, Complex.cpow_ofNat_inv_pow]) hz trivial
  change ((rsqrtExact z).value ^ 2)⁻¹ = toComplex z at h
  rw [← h, mul_inv_cancel₀]
  intro hzero
  rw [hzero, inv_zero] at h
  exact hne h.symm

/--
The exact result of `clog` is Mathlib's principal `Complex.log` at every finite argument off the
negative real axis, and on that axis where the imaginary sign bit is clear.
-/
theorem logExact_value (hz : isFinite z = true)
    (hside : Model.signBit z.im = false ∨ (toComplex z).arg ≠ Real.pi) :
    (logExact z).value = Complex.log (toComplex z) :=
  Exact.ofUpperHalf_value (f := Complex.log) (fun _ _ => rfl) hz
    (hside.imp_right (Complex.log_conj _))

/--
The exact result of `log1p` is Mathlib's principal `Complex.log (1 + w)` at every finite argument
with `1 + w` off the negative real axis, and on that axis where the imaginary sign bit is clear.
-/
theorem log1pExact_value (hz : isFinite z = true)
    (hside : Model.signBit z.im = false ∨ (1 + toComplex z).arg ≠ Real.pi) :
    (log1pExact z).value = Complex.log (1 + toComplex z) :=
  Exact.ofUpperHalf_value (f := fun w => Complex.log (1 + w)) (fun _ _ => rfl) hz
    (hside.imp_right fun h => by simpa using Complex.log_conj _ h)

/-- The exact result of `clog` is a logarithm of every finite nonzero argument. -/
theorem exp_logExact_value (hz : isFinite z = true) (hne : toComplex z ≠ 0) :
    Complex.exp (logExact z).value = toComplex z := by
  unfold logExact Exact.ofUpperHalf
  split
  · simp only [Exact.conj]
    rw [Complex.exp_conj, Complex.exp_log, toComplex_conj z hz, Complex.conj_conj]
    rw [toComplex_conj z hz]
    simpa using hne
  · exact Complex.exp_log hne

/-- The exact result of `log1p` is a logarithm of `1 + w` at every finite argument but `-1`. -/
theorem exp_log1pExact_value (hz : isFinite z = true) (hpole : 1 + toComplex z ≠ 0) :
    Complex.exp (log1pExact z).value = 1 + toComplex z := by
  unfold log1pExact Exact.ofUpperHalf
  split
  · have hconj : 1 + toComplex (ExecComplex.conj z) = starRingEnd ℂ (1 + toComplex z) := by
      rw [toComplex_conj z hz]
      simp
    simp only [Exact.conj]
    rw [Complex.exp_conj, Complex.exp_log, hconj, Complex.conj_conj]
    rw [hconj]
    exact (map_ne_zero (starRingEnd ℂ)).mpr hpole
  · exact Complex.exp_log hpole

/-! ## Inverse sines and cosines -/

/--
In the closed right half-plane, off the cut below `-i`, `asinhValue` is the principal expression
`log (w + √(1 + w²))` of the inverse hyperbolic sine (Kahan, "Branch cuts for complex elementary
functions", 1987, Table 1), with Mathlib's principal logarithm and square root.
-/
theorem asinhValue_eq_log {w : ℂ} (hre : 0 ≤ w.re) (hcut : ¬(w.re = 0 ∧ w.im < -1)) :
    asinhValue w = Complex.log (w + (1 + w ^ 2) ^ (2⁻¹ : ℂ)) := by
  have hmajor := ConfocalComparison.one_le_major w.re w.im
  have ha : 0 ≤ Real.arcosh (major w.re w.im) := Real.arcosh_nonneg hmajor
  have hlower := Real.neg_pi_div_two_le_arcsin (minor w.re w.im)
  have hupper := Real.arcsin_le_pi_div_two (minor w.re w.im)
  have hsinh := sinh_asinhValue hre
  have hsq : 1 + w ^ 2 = Complex.cosh (asinhValue w) ^ 2 := by
    rw [Complex.cosh_sq, hsinh]
    ring
  have hcosh : (1 + w ^ 2) ^ (2⁻¹ : ℂ) = Complex.cosh (asinhValue w) := by
    rw [hsq]
    refine sq_cpow_inv_two ?_ ?_
    · rw [asinhValue, cosh_mk]
      exact mul_nonneg (Real.cosh_pos _).le
        (Real.cos_nonneg_of_neg_pi_div_two_le_of_le hlower hupper)
    · rw [asinhValue, cosh_mk]
      by_cases hb : 0 ≤ Real.arcsin (minor w.re w.im)
      · exact Or.inr (mul_nonneg (Real.sinh_nonneg_iff.mpr ha)
          (Real.sin_nonneg_of_nonneg_of_le_pi hb (by linarith [Real.pi_pos])))
      · by_cases hminor : -1 < minor w.re w.im
        · exact Or.inl (mul_pos (Real.cosh_pos _) (Real.cos_pos_of_mem_Ioo
            ⟨Real.neg_pi_div_two_lt_arcsin.mpr hminor, by linarith [Real.pi_pos]⟩))
        · have hmirror : 1 ≤ minor w.re (-w.im) := by
            rw [ConfocalComparison.minor_neg]
            linarith
          obtain ⟨hp, hq⟩ := ConfocalComparison.one_le_minor_iff.mp hmirror
          have hq1 : w.im = -1 := by
            by_contra hne
            exact hcut ⟨hp, lt_of_le_of_ne (by linarith) hne⟩
          have hone : major w.re w.im = 1 :=
            ConfocalComparison.major_eq_one hp (by rw [hq1]; simp)
          refine Or.inr ?_
          change 0 ≤ Real.sinh (Real.arcosh (major w.re w.im)) * _
          rw [hone, Real.arcosh_zero, Real.sinh_zero, zero_mul]
  have hexp : Complex.exp (asinhValue w) = w + (1 + w ^ 2) ^ (2⁻¹ : ℂ) := by
    rw [hcosh, ← Complex.cosh_add_sinh, hsinh, add_comm]
  rw [← hexp, Complex.log_exp]
  · change -Real.pi < Real.arcsin _
    linarith [Real.pi_pos]
  · change Real.arcsin _ ≤ Real.pi
    linarith [Real.pi_pos]

/--
In the closed upper half-plane, `acoshValue` is the principal expression
`2 log (√((w + 1) / 2) + √((w - 1) / 2))` of the inverse hyperbolic cosine (Kahan, "Branch cuts
for complex elementary functions", 1987, Table 1), with Mathlib's principal logarithm and square
root.
-/
theorem acoshValue_eq_log {w : ℂ} (him : 0 ≤ w.im) :
    acoshValue w = 2 * Complex.log (((w + 1) / 2) ^ (2⁻¹ : ℂ) + ((w - 1) / 2) ^ (2⁻¹ : ℂ)) := by
  have hmajor := ConfocalComparison.one_le_major w.im w.re
  have ha : 0 ≤ Real.arcosh (major w.im w.re) / 2 :=
    div_nonneg (Real.arcosh_nonneg hmajor) (by norm_num)
  have hb0 : 0 ≤ Real.arccos (minor w.im w.re) / 2 :=
    div_nonneg (Real.arccos_nonneg _) (by norm_num)
  have hb1 : Real.arccos (minor w.im w.re) / 2 ≤ Real.pi / 2 := by
    linarith [Real.arccos_le_pi (minor w.im w.re)]
  have hcos : 0 ≤ Real.cos (Real.arccos (minor w.im w.re) / 2) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) hb1
  have hsin : 0 ≤ Real.sin (Real.arccos (minor w.im w.re) / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hb0 (by linarith [Real.pi_pos])
  obtain ⟨u, hu⟩ : ∃ u : ℂ, u = ⟨Real.arcosh (major w.im w.re) / 2,
      Real.arccos (minor w.im w.re) / 2⟩ := ⟨_, rfl⟩
  have hhalf : acoshValue w = 2 * u := by
    rw [hu]
    apply Complex.ext <;> simp [acoshValue] <;> ring
  have hcosh := cosh_acoshValue him
  rw [hhalf, Complex.cosh_two_mul] at hcosh
  have hfirst : (w + 1) / 2 = Complex.cosh u ^ 2 := by
    linear_combination (-1 / 2 : ℂ) * hcosh + (-1 / 2 : ℂ) * Complex.cosh_sq u
  have hsecond : (w - 1) / 2 = Complex.sinh u ^ 2 := by
    linear_combination (-1 / 2 : ℂ) * hcosh + (1 / 2 : ℂ) * Complex.cosh_sq u
  rw [hfirst, hsecond, sq_cpow_inv_two, sq_cpow_inv_two, Complex.cosh_add_sinh, Complex.log_exp,
    ← hhalf]
  · rw [hu]
    change -Real.pi < Real.arccos _ / 2
    linarith [Real.pi_pos]
  · rw [hu]
    change Real.arccos _ / 2 ≤ Real.pi
    linarith [Real.pi_pos]
  · rw [hu, sinh_mk]
    exact mul_nonneg (Real.sinh_nonneg_iff.mpr ha) hcos
  · rw [hu, sinh_mk]
    exact Or.inr (mul_nonneg (Real.cosh_pos _).le hsin)
  · rw [hu, cosh_mk]
    exact mul_nonneg (Real.cosh_pos _).le hcos
  · rw [hu, cosh_mk]
    exact Or.inr (mul_nonneg (Real.sinh_nonneg_iff.mpr ha) hsin)

/--
Where both sign bits are clear, the exact result of `casinh` is the principal expression
`log (w + √(1 + w²))`. Elsewhere it is the extension of C23 G.6.3.2 by parity and conjugation.
-/
theorem asinhExact_value (hre : Model.signBit z.re = false) (him : Model.signBit z.im = false) :
    (asinhExact z).value =
      Complex.log (toComplex z + (1 + toComplex z ^ 2) ^ (2⁻¹ : ℂ)) := by
  have hx : 0 ≤ (toComplex z).re := Model.toReal_nonneg_of_signBit_eq_false hre
  have hy : 0 ≤ (toComplex z).im := Model.toReal_nonneg_of_signBit_eq_false him
  simp only [asinhExact, Exact.ofQuadrant, Exact.ofUpperHalf, hre, him, Bool.false_eq_true,
    ↓reduceIte]
  exact asinhValue_eq_log hx fun h => by linarith [h.2]

/--
Where the real sign bit is clear and the imaginary one set, the exact result of `casin` is the
principal expression `-i log (i w + √(1 - w²))`, which is `-i casinh (i w)` at an argument `i w`
with both sign bits clear.
-/
theorem asinExact_value (hfmt : fmt.isIEEE = true) (hz : isFinite z = true)
    (hre : Model.signBit z.re = false) (him : Model.signBit z.im = true) :
    (asinExact z).value = -Complex.I *
      Complex.log (Complex.I * toComplex z + (1 - toComplex z ^ 2) ^ (2⁻¹ : ℂ)) := by
  have h := asinhExact_value (z := mulI z) (by simp [mulI, signBit_neg hfmt, him]) hre
  rw [toComplex_mulI hz] at h
  simp only [asinExact, Exact.mulNegI]
  rw [h, show 1 + (Complex.I * toComplex z) ^ 2 = 1 - toComplex z ^ 2 by
    rw [mul_pow, Complex.I_sq]
    ring]

/--
Where the imaginary sign bit is clear, the exact result of `cacosh` is the principal expression
`2 log (√((w + 1) / 2) + √((w - 1) / 2))`. Elsewhere it is its conjugate at the conjugate
argument (C23 G.6.3.1).
-/
theorem acoshExact_value (him : Model.signBit z.im = false) :
    (acoshExact z).value = 2 * Complex.log (((toComplex z + 1) / 2) ^ (2⁻¹ : ℂ) +
      ((toComplex z - 1) / 2) ^ (2⁻¹ : ℂ)) := by
  simp only [acoshExact, Exact.ofUpperHalf, him, Bool.false_eq_true, ↓reduceIte]
  exact acoshValue_eq_log (Model.toReal_nonneg_of_signBit_eq_false him)

/--
Where the imaginary sign bit is clear, the exact result of `cacos` is `-i` times the principal
expression of the inverse hyperbolic cosine.
-/
theorem acosExact_value (him : Model.signBit z.im = false) :
    (acosExact z).value = -Complex.I * (2 * Complex.log
      (((toComplex z + 1) / 2) ^ (2⁻¹ : ℂ) + ((toComplex z - 1) / 2) ^ (2⁻¹ : ℂ))) := by
  simp only [acosExact, Exact.ofUpperHalf, him, Bool.false_eq_true, ↓reduceIte, Exact.mulNegI]
  rw [acoshValue_eq_log (Model.toReal_nonneg_of_signBit_eq_false him)]

/-- The exact result of `casinh` is an inverse hyperbolic sine of every finite argument. -/
theorem sinh_asinhExact_value (hfmt : fmt.isIEEE = true) (hz : isFinite z = true) :
    Complex.sinh (asinhExact z).value = toComplex z :=
  Exact.ofQuadrant_inverse hfmt Complex.sinh_conj Complex.sinh_neg (fun _ => True)
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ _ _ hsign => sinh_asinhValue (Model.toReal_nonneg_of_signBit_eq_false hsign)) hz trivial

/-- The exact result of `casin` is an inverse sine of every finite argument. -/
theorem sin_asinExact_value (hfmt : fmt.isIEEE = true) (hz : isFinite z = true) :
    Complex.sin (asinExact z).value = toComplex z := by
  have h := sinh_asinhExact_value hfmt (isFinite_mulI hz)
  rw [toComplex_mulI hz] at h
  simp only [asinExact, Exact.mulNegI]
  rw [show -Complex.I * (asinhExact (mulI z)).value =
      (-(asinhExact (mulI z)).value) * Complex.I by ring, Complex.sin_mul_I, Complex.sinh_neg, h]
  linear_combination (-(toComplex z)) * Complex.I_mul_I

/-- The exact result of `cacosh` is an inverse hyperbolic cosine of every finite argument. -/
theorem cosh_acoshExact_value (hfmt : fmt.isIEEE = true) (hz : isFinite z = true) :
    Complex.cosh (acoshExact z).value = toComplex z :=
  Exact.ofUpperHalf_inverse hfmt Complex.cosh_conj (fun _ => True) (fun _ _ => trivial)
    (fun _ _ _ hsign => cosh_acoshValue (Model.toReal_nonneg_of_signBit_eq_false hsign)) hz
    trivial

/-- The exact result of `cacos` is an inverse cosine of every finite argument. -/
theorem cos_acosExact_value (hfmt : fmt.isIEEE = true) (hz : isFinite z = true) :
    Complex.cos (acosExact z).value = toComplex z :=
  Exact.ofUpperHalf_inverse hfmt Complex.cos_conj (fun _ => True) (fun _ _ => trivial)
    (fun ζ _ _ hsign => by
      simp only [Exact.mulNegI]
      rw [show -Complex.I * acoshValue (toComplex ζ) =
          (-acoshValue (toComplex ζ)) * Complex.I by ring, Complex.cos_mul_I, Complex.cosh_neg]
      exact cosh_acoshValue (Model.toReal_nonneg_of_signBit_eq_false hsign)) hz trivial

/-! ## Inverse tangents -/

/-- `atanhValue` is half the principal logarithm of `(1 + w) / (1 - w)`, away from `1`. -/
theorem atanhValue_eq_log {w : ℂ} (hpos : w ≠ 1) :
    atanhValue w = Complex.log ((1 + w) / (1 - w)) / 2 := by
  have hsub : 1 - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hpos)
  have hN : (1 + w.re) * (1 + w.re) + w.im * w.im = Complex.normSq (1 + w) := by
    simp [Complex.normSq_apply]
  have hD : (1 - w.re) * (1 - w.re) + w.im * w.im = Complex.normSq (1 - w) := by
    simp [Complex.normSq_apply]
  have hP : (⟨(1 - w.re) * (1 + w.re) - w.im * w.im, 2 * w.im⟩ : ℂ) =
      ((Complex.normSq (1 - w) : ℝ) : ℂ) * ((1 + w) / (1 - w)) := by
    rw [← Complex.mul_conj, show (1 - w) * starRingEnd ℂ (1 - w) * ((1 + w) / (1 - w)) =
      (1 + w) * starRingEnd ℂ (1 - w) by field_simp]
    apply Complex.ext <;> simp <;> ring
  have hlog : Complex.log ((1 + w) / (1 - w)) =
      ⟨Real.log (Complex.normSq (1 + w) / Complex.normSq (1 - w)) / 2,
        Complex.arg ⟨(1 - w.re) * (1 + w.re) - w.im * w.im, 2 * w.im⟩⟩ := by
    apply Complex.ext
    · rw [Complex.log_re, norm_div, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
        ← div_pow, Real.log_pow]
      push_cast
      ring
    · rw [Complex.log_im, hP, Complex.arg_real_mul _ (Complex.normSq_pos.mpr hsub)]
  rw [hlog, atanhValue, hN, hD]
  apply Complex.ext <;> simp
  ring

/-- The complex hyperbolic tangent inverts `atanhValue` away from `±1`. -/
theorem tanh_atanhValue {w : ℂ} (hpos : w ≠ 1) (hneg : w ≠ -1) :
    Complex.tanh (atanhValue w) = w := by
  have hsub : 1 - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hpos)
  have hadd : 1 + w ≠ 0 := fun h => hneg (by linear_combination h)
  have hexp : Complex.exp (atanhValue w) ^ 2 = (1 + w) / (1 - w) := by
    rw [← Complex.exp_nat_mul, atanhValue_eq_log hpos,
      show ((2 : ℕ) : ℂ) * (Complex.log ((1 + w) / (1 - w)) / 2) =
        Complex.log ((1 + w) / (1 - w)) by push_cast; ring]
    exact Complex.exp_log (div_ne_zero hadd hsub)
  have hE := Complex.exp_ne_zero (atanhValue w)
  have hproduct : Complex.exp (atanhValue w) * Complex.exp (atanhValue w) * (1 - w) = 1 + w := by
    rw [← sq, hexp, div_mul_cancel₀ _ hsub]
  have hinverse : (Complex.exp (atanhValue w))⁻¹ * Complex.exp (atanhValue w) = 1 :=
    inv_mul_cancel₀ hE
  have hkey : Complex.exp (atanhValue w) - (Complex.exp (atanhValue w))⁻¹ =
      w * (Complex.exp (atanhValue w) + (Complex.exp (atanhValue w))⁻¹) := by
    apply mul_right_cancel₀ hE
    linear_combination hproduct - (1 + w) * hinverse
  have hsinh : Complex.sinh (atanhValue w) = w * Complex.cosh (atanhValue w) := by
    rw [Complex.sinh, Complex.cosh, Complex.exp_neg, hkey]
    ring
  have hcosh : Complex.cosh (atanhValue w) ≠ 0 := by
    intro hzero
    have hsum := Complex.cosh_add_sinh (atanhValue w)
    rw [hsinh, hzero, mul_zero, add_zero] at hsum
    exact hE hsum.symm
  rw [Complex.tanh_eq_sinh_div_cosh, hsinh, mul_div_assoc, div_self hcosh, mul_one]

/-- Reflecting the argument of `atanhValue` in the imaginary axis reflects the value. -/
theorem atanhValue_neg_re (x y : ℝ) :
    atanhValue ⟨-x, y⟩ = ⟨-(atanhValue ⟨x, y⟩).re, (atanhValue ⟨x, y⟩).im⟩ := by
  apply Complex.ext
  · simp only [atanhValue]
    rw [show ((1 + -x) * (1 + -x) + y * y) / ((1 - -x) * (1 - -x) + y * y) =
        (((1 + x) * (1 + x) + y * y) / ((1 - x) * (1 - x) + y * y))⁻¹ by
      rw [inv_div]
      ring_nf, Real.log_inv]
    ring
  · simp only [atanhValue]
    rw [show (1 - -x) * (1 + -x) = (1 - x) * (1 + x) by ring]

/-- Conjugating the argument of `atanhValue` conjugates the value, off the cuts. -/
theorem atanhValue_conj {w : ℂ} (hcut : ¬(w.im = 0 ∧ 1 < |w.re|)) :
    atanhValue (starRingEnd ℂ w) = starRingEnd ℂ (atanhValue w) := by
  have harg : Complex.arg ⟨(1 - w.re) * (1 + w.re) - w.im * w.im, 2 * w.im⟩ ≠ Real.pi := by
    rw [Ne, Complex.arg_eq_pi_iff]
    rintro ⟨hre, him⟩
    have hy : w.im = 0 := by simpa using him
    refine hcut ⟨hy, ?_⟩
    simp only [hy, mul_zero, sub_zero] at hre
    by_contra hle
    have habs := abs_le.mp (not_lt.mp hle)
    nlinarith
  apply Complex.ext
  · simp [atanhValue]
  · have hconj : (⟨(1 - w.re) * (1 + w.re) - -w.im * -w.im, 2 * -w.im⟩ : ℂ) =
        starRingEnd ℂ ⟨(1 - w.re) * (1 + w.re) - w.im * w.im, 2 * w.im⟩ := by
      apply Complex.ext <;> simp
    simp only [atanhValue, Complex.conj_re, Complex.conj_im]
    rw [hconj, Complex.arg_conj]
    simp only [harg, ↓reduceIte]
    ring

/--
The exact result of `catanh` is `log ((1 + w) / (1 - w)) / 2`, with Mathlib's principal
`Complex.log`, at every finite argument other than `1` off the cuts (the real axis beyond `±1`),
and on a cut where the imaginary sign bit is clear.
-/
theorem atanhExact_value (hz : isFinite z = true)
    (hside : Model.signBit z.im = false ∨ ¬((toComplex z).im = 0 ∧ 1 < |(toComplex z).re|))
    (hpos : toComplex z ≠ 1) :
    (atanhExact z).value = Complex.log ((1 + toComplex z) / (1 - toComplex z)) / 2 := by
  rw [← atanhValue_eq_log hpos]
  unfold atanhExact Exact.ofQuadrant
  refine Exact.ofUpperHalf_value (f := atanhValue) (fun ζ hζ => ?_) hz
    (hside.imp_right atanhValue_conj)
  split
  · simp only [↓reduceIte]
    rw [toComplex_neg_re hζ, atanhValue_neg_re]
    simp
  · rfl

/--
The exact result of `catanh` is an inverse hyperbolic tangent of every finite argument but
`±1`.
-/
theorem tanh_atanhExact_value (hfmt : fmt.isIEEE = true) (hz : isFinite z = true)
    (hpos : toComplex z ≠ 1) (hneg : toComplex z ≠ -1) :
    Complex.tanh (atanhExact z).value = toComplex z :=
  Exact.ofQuadrant_inverse hfmt Complex.tanh_conj Complex.tanh_neg
    (fun w => w ≠ 1 ∧ w ≠ -1)
    (fun w hw => ⟨fun h => hw.1 (by simpa using congrArg (starRingEnd ℂ) h),
      fun h => hw.2 (by simpa using congrArg (starRingEnd ℂ) h)⟩)
    (fun w hw => ⟨fun h => hw.2 (by linear_combination -h),
      fun h => hw.1 (by linear_combination -h)⟩)
    (fun _ _ hd _ => tanh_atanhValue hd.1 hd.2) hz ⟨hpos, hneg⟩

/-- The exact result of `catan` is an inverse tangent of every finite argument but `±i`. -/
theorem tan_atanExact_value (hfmt : fmt.isIEEE = true) (hz : isFinite z = true)
    (hpos : toComplex z ≠ Complex.I) (hneg : toComplex z ≠ -Complex.I) :
    Complex.tan (atanExact z).value = toComplex z := by
  have h1 : toComplex (mulI z) ≠ 1 := by
    rw [toComplex_mulI hz]
    intro h
    exact hneg (by linear_combination (-Complex.I) * h + (toComplex z) * Complex.I_mul_I)
  have h2 : toComplex (mulI z) ≠ -1 := by
    rw [toComplex_mulI hz]
    intro h
    exact hpos (by linear_combination (-Complex.I) * h + (toComplex z) * Complex.I_mul_I)
  have h := tanh_atanhExact_value hfmt (isFinite_mulI hz) h1 h2
  rw [toComplex_mulI hz] at h
  simp only [atanExact, Exact.mulNegI]
  rw [show -Complex.I * (atanhExact (mulI z)).value =
      (-(atanhExact (mulI z)).value) * Complex.I by ring, Complex.tan_mul_I, Complex.tanh_neg, h]
  linear_combination (-(toComplex z)) * Complex.I_mul_I

/--
The exact result of `catan` is Mathlib's `Complex.arctan` at every finite argument other than
`-i` off the cuts (the imaginary axis beyond `±i`), and on a cut where the real sign bit is clear.
-/
theorem atanExact_value (hz : isFinite z = true)
    (hside : Model.signBit z.re = false ∨ ¬((toComplex z).re = 0 ∧ 1 < |(toComplex z).im|))
    (hneg : toComplex z ≠ -Complex.I) :
    (atanExact z).value = Complex.arctan (toComplex z) := by
  have h1 : toComplex (mulI z) ≠ 1 := by
    rw [toComplex_mulI hz]
    intro h
    exact hneg (by linear_combination (-Complex.I) * h + (toComplex z) * Complex.I_mul_I)
  have hside' : Model.signBit (mulI z).im = false ∨
      ¬((toComplex (mulI z)).im = 0 ∧ 1 < |(toComplex (mulI z)).re|) := by
    rw [toComplex_mulI hz]
    refine hside.imp id fun h => ?_
    simpa using h
  simp only [atanExact, Exact.mulNegI]
  rw [atanhExact_value (isFinite_mulI hz) hside' h1, toComplex_mulI hz, Complex.arctan,
    mul_comm Complex.I (toComplex z)]
  ring

end ExecComplex
end FloatLib.Floats.Formats.BinaryInterchange
