/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Stochastic.Grid

/-!
# Unbounded scaled-integer grids

Any encoding that can represent every integer coefficient has neighbors at the floor
and ceiling of the scaled input. This complements finite-grid existence: fixed point
does not need an artificial finite bound to use the same stochastic neighbor law.
-/

@[expose] public section

namespace FloatLib.Numerics.Quantization.Stochastic

/-- Floor and ceiling give the existing neighbor relation for every scaled integer lattice. -/
theorem lattice_brackets {Code : Type*} (coefficient : Code → ℤ) (encode : ℤ → Code)
    (he : Function.RightInverse encode coefficient) (scale : ℝ) (hs : 0 < scale) (x : ℝ) :
    Ordered.Brackets
      (NumericalSystem.ofFinite (fun c ↦ (coefficient c : ℝ) / scale)) x
      (encode ⌊x * scale⌋) (encode ⌈x * scale⌉) := by
  constructor
  · refine ⟨(⌊x * scale⌋ : ℝ) / scale, ?_, ?_, ?_⟩
    · simp only [NumericalSystem.ofFinite_represents_iff, he _]
    · exact (div_le_iff₀ hs).mpr (Int.floor_le _)
    · rintro y ⟨c, hc⟩ hy
      have hc' : (coefficient c : ℝ) / scale = y := by simpa using hc
      rw [← hc'] at hy ⊢
      exact div_le_div_of_nonneg_right
        (Int.cast_le.mpr (Int.le_floor.mpr ((div_le_iff₀ hs).mp hy))) hs.le
  · refine ⟨(⌈x * scale⌉ : ℝ) / scale, ?_, ?_, ?_⟩
    · simp only [NumericalSystem.ofFinite_represents_iff, he _]
    · exact (le_div_iff₀ hs).mpr (Int.le_ceil _)
    · rintro y ⟨c, hc⟩ hy
      have hc' : (coefficient c : ℝ) / scale = y := by simpa using hc
      rw [← hc'] at hy ⊢
      exact div_le_div_of_nonneg_right
        (Int.cast_le.mpr (Int.ceil_le.mpr ((le_div_iff₀ hs).mp hy))) hs.le

end FloatLib.Numerics.Quantization.Stochastic
