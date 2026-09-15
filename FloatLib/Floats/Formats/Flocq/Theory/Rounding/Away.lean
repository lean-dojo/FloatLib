/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Order

/-!
# Rounding Away from Zero

Away-from-zero rounding uses ceiling on nonnegative inputs and floor on negative inputs.  Together
with toward-zero rounding, it supplies the second endpoint decomposition for arbitrary valid
integer rounding modes.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

/-- Integer rounding away from zero. -/
noncomputable def awayRound (x : ℝ) : ℤ :=
  if x < 0 then ⌊x⌋ else ⌈x⌉

/-- Away-from-zero agrees with floor on negative inputs. -/
theorem awayRound_eq_floor {x : ℝ} (hx : x < 0) :
    awayRound x = floorRound x := by
  simp [awayRound, floorRound, hx]

/-- Away-from-zero agrees with ceiling on nonnegative inputs. -/
theorem awayRound_eq_ceil {x : ℝ} (hx : 0 ≤ x) :
    awayRound x = ceilRound x := by
  simp [awayRound, ceilRound, not_lt.mpr hx]

/-- On nonpositive inputs, away-from-zero agrees with floor, including at zero. -/
theorem awayRound_eq_floor_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    awayRound x = floorRound x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [awayRound, floorRound]
  · exact awayRound_eq_floor hx

/-- Away-from-zero rounding is monotone and fixes integers. -/
instance awayRoundValid : ValidRnd awayRound where
  monotone := by
    intro x y hxy
    by_cases hx : x < 0
    · by_cases hy : y < 0
      · rw [awayRound_eq_floor hx, awayRound_eq_floor hy]
        exact Int.floor_mono hxy
      · rw [awayRound_eq_floor hx, awayRound_eq_ceil (le_of_not_gt hy)]
        have hleft : floorRound x ≤ 0 := Int.floor_nonpos hx.le
        have hright : 0 ≤ ceilRound y := Int.ceil_nonneg (le_of_not_gt hy)
        exact hleft.trans hright
    · have hx0 : 0 ≤ x := le_of_not_gt hx
      have hy0 : 0 ≤ y := hx0.trans hxy
      rw [awayRound_eq_ceil hx0, awayRound_eq_ceil hy0]
      exact Int.ceil_mono hxy
  id := by
    intro n
    by_cases hn : n < 0
    · simp [awayRound, hn]
    · simp [awayRound, hn]

/-- Arbitrary valid integer rounding chooses toward-zero or away-from-zero. -/
theorem valid_round_eq_trunc_or_away (rnd : ℝ → ℤ) [ValidRnd rnd] (x : ℝ) :
    rnd x = truncRound x ∨ rnd x = awayRound x := by
  rcases valid_round_eq_floor_or_ceil rnd x with hfloor | hceil
  · by_cases hx : x < 0
    · exact Or.inr (hfloor.trans (awayRound_eq_floor hx).symm)
    · exact Or.inl (hfloor.trans (truncRound_eq_floor (le_of_not_gt hx)).symm)
  · by_cases hx : 0 ≤ x
    · exact Or.inr (hceil.trans (awayRound_eq_ceil hx).symm)
    · exact Or.inl (hceil.trans (truncRound_eq_ceil (le_of_not_ge hx)).symm)

/-- Upward rounding on nonnegative inputs and downward rounding on nonpositive inputs. -/
def RoundAwayFromZeroPoint (F : ℝ → Prop) (x f : ℝ) : Prop :=
  (0 ≤ x → RoundUpPoint F x f) ∧ (x ≤ 0 → RoundDownPoint F x f)

/-- Generic away-from-zero rounding satisfies its semantic point specification. -/
theorem round_away_point {β : Numerics.Radix} {fexp : ℤ → ℤ} [ValidExp fexp]
    (x : ℝ) :
    RoundAwayFromZeroPoint (genericFormat β fexp) x
      (round (β := β) (fexp := fexp) awayRound x) := by
  constructor
  · intro hx
    have hs : 0 ≤ scaledMantissa β fexp x := by
      rw [scaledMantissa_eq_div]
      exact div_nonneg hx (bpow.nonneg β _)
    have hr : round (β := β) (fexp := fexp) awayRound x =
        round (β := β) (fexp := fexp) ceilRound x := by
      unfold round
      rw [awayRound_eq_ceil hs]
    rw [hr]
    exact round_ceil_point x
  · intro hx
    have hs : scaledMantissa β fexp x ≤ 0 := by
      rw [scaledMantissa_eq_div]
      exact div_nonpos_of_nonpos_of_nonneg hx (bpow.nonneg β _)
    have hr : round (β := β) (fexp := fexp) awayRound x =
        round (β := β) (fexp := fexp) floorRound x := by
      unfold round
      rw [awayRound_eq_floor_of_nonpos hs]
    rw [hr]
    exact round_floor_point x

end FloatLib.Floats.Formats.Flocq
