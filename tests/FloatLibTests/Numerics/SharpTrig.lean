/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Numerics.Enclosure.Interval.SharpTrigProof

/-!
# Sharp sine and cosine on monotone panels

The kernel computes the point enclosures `sinPoint` and `cosPoint` and the sharp enclosures of
sine and cosine at 32 Taylor terms on the grid of step `2 ^ (-128)`, for one interval of each
branch, and each has to equal the endpoints written next to it. The last checks show panels where
the sharp bounds prove what the Lipschitz bounds cannot.
-/

open FloatLib.Numerics FloatLib.Numerics.Interval

/-! ### Point enclosures, with and without period reduction -/

example : sinPoint (1 / 3) 32 128 =
    ⟨111338585869773486664328425711645364767 / 2 ^ 128,
      3479330808430421458260263303488917649 / 2 ^ 123⟩ := by
  decide +kernel

example : cosPoint (1 / 3) 32 128 =
    ⟨321552186330361111285496297740380957765 / 2 ^ 128,
      160776093165180555642748148870190478883 / 2 ^ 127⟩ := by
  decide +kernel

example : sinPoint 10 32 128 =
    ⟨-185120791268393090308440424640787012559 / 2 ^ 128,
      -92560395634196545154218951384246197009 / 2 ^ 127⟩ := by
  decide +kernel

example : cosPoint 10 32 128 =
    ⟨-71380311482526570016170451540126506413 / 2 ^ 126,
      -35690155741263285008084910536026425889 / 2 ^ 125⟩ := by
  decide +kernel

/-! ### Sine -/

-- Inside `[0, π/2]`: increasing, then clamped at zero.
example : sharpSinBounds ⟨1 / 2, 3 / 4⟩ 32 128 =
    ⟨163140057038583953344548562349566324121 / 2 ^ 128,
      231949650645793717757595367025189889161 / 2 ^ 128⟩ := by
  decide +kernel

-- Inside `[-π/2, 0]`: increasing.
example : sharpSinBounds ⟨-1, -1 / 2⟩ 32 128 =
    ⟨-286337738405724074564845076175058320435 / 2 ^ 128,
      -163140057038583953344548562349566324121 / 2 ^ 128⟩ := by
  decide +kernel

-- Inside `[0, π]` across the maximum.
example : sharpSinBounds ⟨1, 3⟩ 32 128 =
    ⟨24010325181256765684224015320907830009 / 2 ^ 127, 1⟩ := by
  decide +kernel

-- The cosine enclosure is negative: decreasing.
example : sharpSinBounds ⟨2, 7 / 2⟩ 32 128 =
    ⟨-119365346994390322346340562589376961461 / 2 ^ 128,
      154708940317680905982146277317945673669 / 2 ^ 127⟩ := by
  decide +kernel

-- The same branch beyond `4`, through the period reduction.
example : sharpSinBounds ⟨10, 41 / 4⟩ 32 128 =
    ⟨-250004920871242169617064291657477223417 / 2 ^ 128,
      -92560395634196545154218951384246197009 / 2 ^ 127⟩ := by
  decide +kernel

-- No branch applies.
example : sharpSinBounds ⟨3, 7⟩ 32 128 = ⟨-1, 1⟩ := by
  decide +kernel

/-! ### Cosine -/

-- Inside `[0, π/2]`: decreasing, then clamped at zero.
example : sharpCosBounds ⟨1 / 2, 1⟩ 32 128 =
    ⟨183855347493651442427684920285310598403 / 2 ^ 128,
      149312935664298498285733163416418086083 / 2 ^ 127⟩ := by
  decide +kernel

-- Inside `[-π, 0]`: increasing.
example : sharpCosBounds ⟨-2, -1⟩ 32 128 =
    ⟨-17700928815865313776411195955066318479 / 2 ^ 125,
      91927673746825721213842460142655299241 / 2 ^ 127⟩ := by
  decide +kernel

-- Around zero inside `[-π, π]`.
example : sharpCosBounds ⟨-1, 2⟩ 32 128 =
    ⟨-17700928815865313776411195955066318479 / 2 ^ 125, 1⟩ := by
  decide +kernel

-- Around zero inside `[-π/2, π/2]`, then clamped at zero.
example : sharpCosBounds ⟨-1 / 2, 1 / 2⟩ 32 128 =
    ⟨298625871328596996571466326832836172165 / 2 ^ 128, 1⟩ := by
  decide +kernel

-- The sine enclosure is negative: increasing.
example : sharpCosBounds ⟨7 / 2, 5⟩ 32 128 =
    ⟨-318659698070253290541495878780546981537 / 2 ^ 128,
      24131309968848214122304024550577831349 / 2 ^ 126⟩ := by
  decide +kernel

-- The same branch beyond `4`, through the period reduction.
example : sharpCosBounds ⟨10, 41 / 4⟩ 32 128 =
    ⟨-71380311482526570016170451540126506413 / 2 ^ 126,
      -28855683142981161069249901202251824285 / 2 ^ 125⟩ := by
  decide +kernel

-- No branch applies.
example : sharpCosBounds ⟨2, 8⟩ 32 128 = ⟨-1, 1⟩ := by
  decide +kernel

/-! ### A bound that needs the sharp enclosure -/

-- On `[1/2, 3/4]` the Lipschitz bound reaches above `0.71`, and `sin (3/4) < 0.682`.
example : 71 / 100 < (sinBounds ⟨1 / 2, 3 / 4⟩ 32).hi ∧
    (sharpSinBounds ⟨1 / 2, 3 / 4⟩ 32 128).hi < 682 / 1000 := by
  decide +kernel

example (x : ℝ) (hx : x ∈ Set.Icc (1 / 2 : ℝ) (3 / 4)) : Real.sin x < 0.682 := by
  have h := (containsReal_some_iff _ _).1 (containsReal_sharpSinBounds ⟨1 / 2, 3 / 4⟩ 32 128
    ((containsReal_some_iff _ _).2 (by norm_num at hx ⊢; exact hx)))
  have hhi : (sharpSinBounds ⟨1 / 2, 3 / 4⟩ 32 128).hi < 682 / 1000 := by decide +kernel
  have hhi' : ((sharpSinBounds ⟨1 / 2, 3 / 4⟩ 32 128).hi : ℝ) < 0.682 := by
    have := (Rat.cast_lt (K := ℝ)).2 hhi
    norm_num at this ⊢
    exact this
  exact h.2.trans_lt hhi'

-- Cosine on `[-1/2, 1/2]` stays above `0.877`; the Lipschitz bound only gives about `1/2`.
example : (cosBounds ⟨-1 / 2, 1 / 2⟩ 32).lo < 51 / 100 ∧
    877 / 1000 < (sharpCosBounds ⟨-1 / 2, 1 / 2⟩ 32 128).lo := by
  decide +kernel
