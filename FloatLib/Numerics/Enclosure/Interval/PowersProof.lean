/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.Powers
public import FloatLib.Numerics.Enclosure.Interval.HyperbolicProof
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Containment for real powers and logarithms with a specified base

The proofs compose logarithm, multiplication, exponential, and division contracts. The real-power
identity is used only after deriving positivity of every base value from the accepted interval.
-/

public section

namespace FloatLib.Numerics.Interval

/-- Successful real-power bounds contain the result for every real base and exponent member. -/
theorem containsReal_rpowBounds? {I J K : Interval ℚ} {terms : Nat}
    (h : rpowBounds? I J terms = some K) {x y : ℝ}
    (hx : I.ContainsReal some x) (hy : J.ContainsReal some y) :
    K.ContainsReal some (x ^ y) := by
  cases hl : logBounds? I terms with
  | none => simp [rpowBounds?, hl] at h
  | some L =>
    cases hm : mul? Internal.rationalOutwardRounding L J with
    | none => simp [rpowBounds?, hl, hm] at h
    | some M =>
      have hpos : 0 < I.lo := by
        by_contra hn
        simp [logBounds?, hn] at hl
      have hxpos : 0 < x :=
        (show (0 : ℝ) < (I.lo : ℝ) by exact_mod_cast hpos).trans_le
          ((containsReal_some_iff I x).mp hx).1
      have hlog := containsReal_logBounds? hl hx
      have hproduct := containsReal_mul? Internal.rationalOutwardRounding hm hlog hy
      have heq : expBounds M terms = K := by
        simpa [rpowBounds?, hl, hm] using h
      rw [← heq, Real.rpow_def_of_pos hxpos]
      exact containsReal_expBounds M terms hproduct

/-- Successful base-logarithm bounds contain the result at every pair of real input members. -/
theorem containsReal_logbBounds? {B I K : Interval ℚ} {terms : Nat}
    (h : logbBounds? B I terms = some K) {b x : ℝ}
    (hb : B.ContainsReal some b) (hx : I.ContainsReal some x) :
    K.ContainsReal some (Real.logb b x) := by
  cases hlb : logBounds? B terms with
  | none => simp [logbBounds?, hlb] at h
  | some Lb =>
    cases hlx : logBounds? I terms with
    | none => simp [logbBounds?, hlb, hlx] at h
    | some Lx =>
      simpa only [Real.logb, Internal.rationalOutwardRounding] using
        containsReal_div? Internal.rationalOutwardRounding
          (by simpa [logbBounds?, hlb, hlx] using h)
          (containsReal_logBounds? hlx hx) (containsReal_logBounds? hlb hb)

end FloatLib.Numerics.Interval
