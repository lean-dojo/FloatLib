/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.HyperbolicProof
public import FloatLib.Numerics.Enclosure.Interval.Powers
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Containment for real powers and logarithms with a specified base

These proofs compose the logarithm, multiplication, exponential, and division contracts. We use the
real-power identity only after deriving from the accepted interval that every base value is
positive.
-/

public section

namespace FloatLib.Numerics.Interval

/-- Successful real-power bounds contain the result for every real base and exponent member. -/
theorem containsReal_rpowBounds? {I J K : Interval ℚ} {terms : Nat}
    (h : rpowBounds? I J terms = some K) {x y : ℝ}
    (hx : I.ContainsReal some x) (hy : J.ContainsReal some y) :
    K.ContainsReal some (x ^ y) := by
  -- The two binds are opened by hand, which the kernel checks in milliseconds. It takes twenty
  -- seconds to check a rewriting of `rpowBounds?` by `simp`.
  have hbind : (logBounds? I terms).bind (fun logarithm =>
      (mul? Internal.rationalOutwardRounding logarithm J).bind fun product =>
        some (expBounds product terms)) = some K := h
  obtain ⟨L, hl, hrest⟩ := Option.bind_eq_some_iff.mp hbind
  obtain ⟨M, hm, hsome⟩ := Option.bind_eq_some_iff.mp hrest
  have heq : expBounds M terms = K := Option.some.inj hsome
  have hpos : 0 < I.lo := by
    by_contra hn
    rw [logBounds?, ite_eq_right hn] at hl
    cases hl
  have hxpos : 0 < x :=
    (show (0 : ℝ) < (I.lo : ℝ) by exact_mod_cast hpos).trans_le
      ((containsReal_some_iff I x).mp hx).1
  have hlog := containsReal_logBounds? hl hx
  have hproduct := containsReal_mul? Internal.rationalOutwardRounding hm hlog hy
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
