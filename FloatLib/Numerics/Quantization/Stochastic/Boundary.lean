/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Stochastic.Grid

/-!
# Bias from finite boundary policies

Input saturation has exactly the clipping displacement as its bias. An output policy
which flushes a specified set of endpoints to zero removes their weighted contribution
from the mean. These are real-valued statements; an exceptional encoding has no real
numerical mean. Its probability can instead be observed as an indicator.
-/

@[expose] public section

namespace FloatLib.Numerics.Quantization.Stochastic

open MeasureTheory ProbabilityTheory

/-- Clipping to a nonempty interval stays in that interval. -/
theorem clamp_mem (lo hi x : ℝ) (h : lo ≤ hi) :
    max lo (min hi x) ∈ Set.Icc lo hi :=
  ⟨le_max_left _ _, max_le h (min_le_left _ _)⟩

/-- The exact bias of saturating before an ideal in-range stochastic conversion. -/
theorem saturation_bias (lo hi a b x : ℝ) (horder : lo ≤ hi)
    (h : max lo (min hi x) ∈ Set.Icc a b) :
    (∫ y, y ∂neighborLaw a b (max lo (min hi x)) h) - x =
      if x < lo then lo - x else if hi < x then hi - x else 0 := by
  rw [neighborLaw_input_bias]
  split_ifs with hl hh
  · rw [max_eq_left (le_trans (min_le_right _ _) hl.le)]
  · rw [min_eq_left hh.le, max_eq_right horder]
  · have hlo : lo ≤ x := le_of_not_gt hl
    have hhi : x ≤ hi := le_of_not_gt hh
    rw [min_eq_right hhi, max_eq_right hlo, sub_self]

/-- Removing selected real outputs to zero gives exactly their missing weighted mass. -/
theorem flush_bias (a b x : ℝ) (hab : a < b) (hx : x ∈ Set.Icc a b)
    (flush : ℝ → Prop) [DecidablePred flush] :
    (∫ y, (if flush y then 0 else y) ∂cellLaw a b x hab hx) - x =
      -((x - a) / (b - a) * (if flush b then b else 0) +
        (1 - (x - a) / (b - a)) * (if flush a then a else 0)) := by
  have hm := mean_cellLaw a b x hab hx
  rw [integral_cellLaw] at hm ⊢
  split_ifs <;> linarith

/-- If both selected outputs are flushed, the result has mean zero. -/
theorem mean_flush_of_endpoints (a b x : ℝ) (hab : a < b) (hx : x ∈ Set.Icc a b)
    (flush : ℝ → Prop) [DecidablePred flush] (ha : flush a) (hb : flush b) :
    ∫ y, (if flush y then 0 else y) ∂cellLaw a b x hab hx = 0 := by
  simp [integral_cellLaw, ha, hb]

end FloatLib.Numerics.Quantization.Stochastic
