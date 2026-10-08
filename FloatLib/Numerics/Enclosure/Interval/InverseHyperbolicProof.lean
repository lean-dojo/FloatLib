/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.HyperbolicProof
public import FloatLib.Numerics.Enclosure.Interval.InverseHyperbolic
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
# Containment for inverse hyperbolic functions

Each successful enclosure follows the corresponding real logarithmic identity. Domain checks
for inverse hyperbolic cosine and tangent apply to every real member of the input interval.
-/

public section

namespace FloatLib.Numerics.Interval

private theorem containsReal_rationalPoint (q : ℚ) :
    (point q).ContainsReal Internal.rationalOutwardRounding.decode (q : ℝ) := by
  simp [containsReal_some_iff, Internal.rationalOutwardRounding, point]

private theorem containsReal_asinhFormulaBounds? {I K : Interval ℚ} {terms precision : Nat}
    (h : Internal.asinhFormulaBounds? I terms precision = some K) {x : ℝ}
    (hx : I.ContainsReal some x) : K.ContainsReal some (Real.arsinh x) := by
  simp only [Internal.asinhFormulaBounds?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨S, hs, R, hr, T, ht, A, ha, hl⟩ := h
  have hsq := containsReal_pow? Internal.rationalOutwardRounding 2 hs hx
  have hrad := containsReal_add? Internal.rationalOutwardRounding hr
    (containsReal_rationalPoint 1) hsq
  have hroot := containsReal_sqrtBounds? ht hrad
  have harg := containsReal_add? Internal.rationalOutwardRounding ha hx hroot
  simpa only [Real.arsinh, Rat.cast_one] using containsReal_logBounds? hl harg

private theorem containsReal_asinhPointBounds? {q : ℚ} {K : Interval ℚ}
    {terms precision : Nat} (h : Internal.asinhPointBounds? q terms precision = some K) :
    K.ContainsReal some (Real.arsinh q) := by
  unfold Internal.asinhPointBounds? at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨J, hj, hn⟩ := h
    have hvalue := containsReal_asinhFormulaBounds? hj (containsReal_rationalPoint (-q))
    simpa only [Internal.rationalOutwardRounding, Rat.cast_neg, Real.arsinh_neg, neg_neg]
      using containsReal_neg? Internal.rationalOutwardRounding hn hvalue
  · exact containsReal_asinhFormulaBounds? h (containsReal_rationalPoint q)

/-- Successful inverse hyperbolic sine bounds contain the image of every enclosed real value. -/
theorem containsReal_asinhBounds? {I K : Interval ℚ} {terms precision : Nat}
    (h : asinhBounds? I terms precision = some K) {x : ℝ}
    (hx : I.ContainsReal some x) : K.ContainsReal some (Real.arsinh x) := by
  simp only [asinhBounds?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨L, hl, U, hu, rfl⟩ := h
  have hlo := (containsReal_some_iff _ _).mp (containsReal_asinhPointBounds? hl)
  have hhi := (containsReal_some_iff _ _).mp (containsReal_asinhPointBounds? hu)
  have hxr := (containsReal_some_iff I x).mp hx
  exact (containsReal_some_iff _ _).mpr
    ⟨hlo.1.trans (Real.arsinh_strictMono.monotone hxr.1),
      (Real.arsinh_strictMono.monotone hxr.2).trans hhi.2⟩

/-- Successful inverse hyperbolic cosine bounds contain the image of every enclosed real value. -/
theorem containsReal_acoshBounds? {I K : Interval ℚ} {terms precision : Nat}
    (h : acoshBounds? I terms precision = some K) {x : ℝ}
    (hx : I.ContainsReal some x) : K.ContainsReal some (Real.arcosh x) := by
  unfold acoshBounds? at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨S, hs, R, hr, T, ht, A, ha, hl⟩ := h
    have hsq := containsReal_pow? Internal.rationalOutwardRounding 2 hs hx
    have hrad := containsReal_sub? Internal.rationalOutwardRounding hr hsq
      (containsReal_rationalPoint 1)
    have hroot := containsReal_sqrtBounds? ht hrad
    have harg := containsReal_add? Internal.rationalOutwardRounding ha hx hroot
    simpa only [Real.arcosh, Rat.cast_one] using containsReal_logBounds? hl harg
  · simp at h

/-- Successful inverse hyperbolic tangent bounds contain the image of every enclosed real value. -/
theorem containsReal_atanhBounds? {I K : Interval ℚ} {terms : Nat}
    (h : atanhBounds? I terms = some K) {x : ℝ}
    (hx : I.ContainsReal some x) : K.ContainsReal some (Real.artanh x) := by
  unfold atanhBounds? at h
  split at h
  · rename_i hdomain
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨N, hn, D, hd, Q, hq, L, hl, hm⟩ := h
    have hnum := containsReal_add? Internal.rationalOutwardRounding hn
      (containsReal_rationalPoint 1) hx
    have hden := containsReal_sub? Internal.rationalOutwardRounding hd
      (containsReal_rationalPoint 1) hx
    have hquot := containsReal_div? Internal.rationalOutwardRounding hq hnum hden
    have hlog := containsReal_logBounds? hl hquot
    have hresult := containsReal_mul? Internal.rationalOutwardRounding hm
      (containsReal_rationalPoint (1 / 2)) hlog
    have hxr := (containsReal_some_iff I x).mp hx
    have hdomainReal : (-1 : ℝ) < (I.lo : ℝ) ∧ (I.hi : ℝ) < 1 := by
      exact_mod_cast hdomain
    rw [Real.artanh_eq_half_log ⟨(hdomainReal.1.trans_le hxr.1).le,
      (hxr.2.trans_lt hdomainReal.2).le⟩]
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat,
      Internal.rationalOutwardRounding] using hresult
  · simp at h

end FloatLib.Numerics.Interval
