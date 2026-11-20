/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.StandardModel
public import FloatLib.Numerics.Quantization.Rounding
public import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Affine

import FloatLib.Numerics.ErrorBound.Algebra

/-!
# Binary and fixed-point formats as rounding maps

The element and scale formats of block scaling, over the reals, for every binary descriptor and
every fixed-point grid:

* `Rounding.grid fmt mode` rounds onto the precision and gradual-underflow grid of `fmt`, with no
  upper limit.
* `Rounding.saturating fmt mode` clips that rounding to the finite range of `fmt`. This is the SAT
  conversion of OCP MX and the only conversion of the fully finite encodings E2M1, E2M3 and E3M2.
* `Rounding.ofFormat fmt` is the descriptor's own policy: saturating for a fully finite encoding
  and the unclipped grid otherwise, where an overflow is an infinity or a NaN and has no value.
  `toReal_cast_eq_ofFormat` states that FloatLib's executable cast from any descriptor stores this
  value whenever its result is finite.
* `Rounding.fixed frac lo hi mode` rounds to a multiple of `2 ^ (-frac)` and clips to `[lo, hi]`:
  two's-complement fixed point and integers. OCP MX INT8 and the S2F6 format of the combine step
  are `Rounding.fixed 6 (-2) (127 / 64)`.

## Main results

* `saturating_budget`, `grid_budget`, `ofFormat_budget`: nearest-even rounding has relative error
  `2 ^ (-precision)`, absolute error half the least subnormal, and saturates at the largest finite
  value.
* `roundAt_eq_zero_iff_mem`, `saturating_round_eq_zero_iff_mem`, `fixed_round_eq_zero_iff_mem`:
  flush to zero in every rounding direction. A binary descriptor or a fixed-point grid stores an
  input as zero exactly when the input, in units of the least subnormal or of the step, lies in
  `modeZeroSet mode`: magnitude at most one half for ties to even, below one half for ties away,
  below one toward zero, the half-open unit intervals for the directed modes, and zero alone
  away from zero.
* `roundAt_eq_zero_iff`, `saturating_round_eq_zero_iff`, `ofFormat_round_eq_zero_iff`,
  `fixed_round_eq_zero_iff`: the nearest-even case, magnitudes up to half the least subnormal or
  half a step, with the tie stored as zero.
* `saturating_fixes`, `saturating_monotone`: finite values are stored exactly, and order is kept.
  `saturating_round_clamp`: clipping the input to the finite range first changes nothing.
* `saturating_nearest`, `saturating_round_neg`: saturating nearest-even rounding is a nearest
  rounding onto its stored values, and it is odd.
* `saturating_round_ratCast`, `RoundsTo.round_eq`: its value at a dyadic rational, computed by
  integer arithmetic (`dyadicRound`), as a decidable check.
* `fixed_budget`: fixed point has no relative error and absolute error half a step.
* `fixed_round_ratCast`, `fixedRat_nearest`: on rationals, nearest-even fixed point is the
  rational computation `fixedRat`, which is a nearest rounding onto its stored values.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Block

open FloatLib.Floats.Formats.BinaryInterchange FloatLib.Floats.Formats.BinaryInterchange.Model
open FloatLib.Floats.Formats.Flocq FloatLib.Numerics

/-- Nearest-even integer rounding sends exactly the magnitudes up to one half to zero. -/
theorem nearestEven_eq_zero_iff (z : ℝ) : nearestEven z = 0 ↔ |z| ≤ 1 / 2 := by
  have hhalf : nearestEven (1 / 2 : ℝ) = 0 := by
    have hfloor : ⌊(2⁻¹ : ℝ)⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨by norm_num, by norm_num⟩
    simp [nearestEven, hfloor]
  constructor
  · intro h
    have := ValidRndToNearest.abs_sub_le_half (rnd := nearestEven) z
    rw [h] at this
    simpa [abs_neg] using this
  · intro h
    rcases abs_le.mp h with ⟨hlo, hhi⟩
    have h1 : nearestEven z ≤ 0 := hhalf ▸ ValidRnd.monotone (rnd := nearestEven) z (1 / 2) hhi
    have h2 : 0 ≤ nearestEven z := by
      have := ValidRnd.monotone (rnd := nearestEven) (-(1 / 2)) z hlo
      rw [nearestEven_neg, hhalf] at this
      simpa using this
    exact le_antisymm h1 h2

namespace Rounding

/-- Rounding onto the grid of a binary descriptor, in direction `mode`, with no upper limit. -/
noncomputable def grid (fmt : FloatFormat) (mode : IEEERoundingMode := .nearest) :
    Rounding ℝ where
  round x := roundAt fmt x mode

/-- Rounding onto the grid of a binary descriptor, clipped to its finite range. -/
noncomputable def saturating (fmt : FloatFormat) (mode : IEEERoundingMode := .nearest) :
    Rounding ℝ where
  round x := clampAt fmt (roundAt fmt x mode)

/--
The descriptor's own conversion policy under nearest-even rounding: a fully finite encoding
saturates, and every other encoding keeps the grid rounding, whose overflows are not finite.
-/
noncomputable def ofFormat (fmt : FloatFormat) : Rounding ℝ :=
  if fmt.encoding = .finite then saturating fmt else grid fmt

/--
Signed fixed point with `frac` fractional bits, clipped to `[lo, hi]`: round to a multiple of
`2 ^ (-frac)` in direction `mode`.
-/
noncomputable def fixed (frac : ℤ) (lo hi : ℝ) (mode : IEEERoundingMode := .nearest) :
    Rounding ℝ where
  round x := Numerics.Quantization.Saturating.clamp lo hi
    (Flocq.round (β := binaryRadix) (fexp := fixExp (-frac)) (roundingFunction mode) x)

end Rounding

/-! ## Zero sets of the rounding directions -/

/-- The reals an integer rounding in direction `mode` sends to zero. In units of the grid step,
these are the inputs a format stores as zero. -/
noncomputable def modeZeroSet : IEEERoundingMode → Set ℝ
  | .nearest => Set.Icc (-(1 / 2)) (1 / 2)
  | .nearestAway => Set.Ioo (-(1 / 2)) (1 / 2)
  | .towardZero => Set.Ioo (-1) 1
  | .up => Set.Ioc (-1) 0
  | .down => Set.Ico 0 1
  | .away => {0}

/-- Zero is stored as zero in every direction. -/
theorem zero_mem_modeZeroSet (mode : IEEERoundingMode) : (0 : ℝ) ∈ modeZeroSet mode := by
  cases mode <;> simp [modeZeroSet]

/-- An input stored as zero is less than one grid step in magnitude, in every direction. -/
theorem abs_lt_one_of_mem_modeZeroSet {mode : IEEERoundingMode} {z : ℝ}
    (h : z ∈ modeZeroSet mode) : |z| < 1 := by
  rw [abs_lt]
  cases mode <;>
    simp only [modeZeroSet, Set.mem_Icc, Set.mem_Ioo, Set.mem_Ioc, Set.mem_Ico,
      Set.mem_singleton_iff] at h
  case away => subst h; norm_num
  all_goals constructor <;> linarith [h.1, h.2]

/-- Nearest rounding with ties away from zero sends exactly the magnitudes below one half to
zero. -/
private theorem nearestAway_eq_zero_iff (z : ℝ) :
    nearestChoice nearestAwayChoice z = 0 ↔ -(1 / 2) < z ∧ z < 1 / 2 := by
  have hfract : Int.fract z = z - ⌊z⌋ := rfl
  have hfloor := Int.floor_le z
  have hlt := Int.lt_floor_add_one z
  constructor
  · intro h
    simp only [nearestChoice, nearestAwayChoice] at h
    split_ifs at h with h1 h2 h3
    · have h0 : (⌊z⌋ : ℝ) = 0 := by exact_mod_cast h
      rw [hfract, h0] at h1
      constructor <;> linarith
    · have h0 : (⌊z⌋ : ℝ) = -1 := by
        have : ⌊z⌋ = -1 := by omega
        exact_mod_cast this
      rw [hfract, h0] at h2
      constructor <;> linarith
    · simp only [h3, ↓reduceIte] at h
      have h4 := of_decide_eq_true h3
      omega
    · have h4 : ¬ (0 : ℤ) ≤ ⌊z⌋ := fun hc => h3 (decide_eq_true hc)
      simp only [h3, Bool.false_eq_true, ↓reduceIte] at h
      omega
  · rintro ⟨hlo, hhi⟩
    simp only [nearestChoice, nearestAwayChoice]
    by_cases hz : 0 ≤ z
    · have h0 : ⌊z⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨hz, by linarith⟩
      have h1 : Int.fract z < 1 / 2 := by
        rw [hfract, h0]
        simpa using hhi
      simp only [h1, ↓reduceIte, h0]
    · have h0 : ⌊z⌋ = -1 := Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
      have h2 : Int.fract z > 1 / 2 := by
        rw [hfract, h0]
        push_cast
        linarith
      simp only [not_lt.mpr h2.le, h2, ↓reduceIte, h0]
      rfl

/-- An integer rounding in direction `mode` sends exactly `modeZeroSet mode` to zero. -/
theorem roundingFunction_eq_zero_iff (mode : IEEERoundingMode) (z : ℝ) :
    roundingFunction mode z = 0 ↔ z ∈ modeZeroSet mode := by
  cases mode with
  | nearest =>
    change nearestEven z = 0 ↔ z ∈ Set.Icc (-(1 / 2)) (1 / 2)
    rw [nearestEven_eq_zero_iff, abs_le, Set.mem_Icc]
  | nearestAway =>
    change nearestChoice nearestAwayChoice z = 0 ↔ z ∈ Set.Ioo (-(1 / 2)) (1 / 2)
    rw [nearestAway_eq_zero_iff, Set.mem_Ioo]
  | towardZero =>
    change (if z < 0 then ⌈z⌉ else ⌊z⌋) = 0 ↔ z ∈ Set.Ioo (-1) 1
    split_ifs with h
    · rw [Int.ceil_eq_zero_iff, Set.mem_Ioc, Set.mem_Ioo]
      simp only [h.le, h.trans zero_lt_one, and_true]
    · rw [Int.floor_eq_zero_iff, Set.mem_Ico, Set.mem_Ioo]
      simp only [not_lt.mp h, neg_one_lt_zero.trans_le (not_lt.mp h), true_and]
  | up => exact Int.ceil_eq_zero_iff
  | down => exact Int.floor_eq_zero_iff
  | away =>
    change (if z < 0 then ⌊z⌋ else ⌈z⌉) = 0 ↔ z ∈ ({0} : Set ℝ)
    rw [Set.mem_singleton_iff]
    split_ifs with h
    · rw [Int.floor_eq_zero_iff, Set.mem_Ico]
      constructor
      · rintro ⟨h1, -⟩
        exact (h.not_ge h1).elim
      · rintro rfl
        exact absurd h (lt_irrefl 0)
    · rw [Int.ceil_eq_zero_iff, Set.mem_Ioc]
      constructor
      · rintro ⟨-, h2⟩
        exact le_antisymm h2 (not_lt.mp h)
      · rintro rfl
        norm_num

/-- A rounding onto a grid is zero exactly when the integer rounding of the scaled mantissa is. -/
private theorem round_eq_zero_iff {fexp : ℤ → ℤ} [ValidExp fexp] (rnd : ℝ → ℤ) (x : ℝ) :
    Flocq.round (β := binaryRadix) (fexp := fexp) rnd x = 0 ↔
      rnd (scaledMantissa binaryRadix fexp x) = 0 := by
  have hb : (0 : ℝ) < Flocq.bpow binaryRadix (cexp binaryRadix fexp x) := bpow.pos _ _
  simp only [Flocq.round, Flocq.toReal, mul_eq_zero, hb.ne', or_false, Int.cast_eq_zero]

/-- A nonzero input whose scaled mantissa is below one in magnitude lies on the least exponent of
the grid of `fmt`, and so does an input below the least subnormal. -/
private theorem cexp_eq_minSubnormalExponent (fmt : FloatFormat) {x : ℝ} (hx : x ≠ 0)
    (h : |scaledMantissa binaryRadix (fexpOf fmt) x| < 1 ∨
      |x| < Flocq.bpow binaryRadix fmt.minSubnormalExponent) :
    cexp binaryRadix (fexpOf fmt) x = fmt.minSubnormalExponent := by
  have hfrac : (0 : ℤ) ≤ (fmt.fracWidth : ℤ) := Int.natCast_nonneg _
  have hlower := bpow_magnitude_sub_one_le binaryRadix x hx
  have hmag : magnitude binaryRadix x - 1 < cexp binaryRadix (fexpOf fmt) x ∨
      magnitude binaryRadix x ≤ fmt.minSubnormalExponent := by
    rcases h with h | h
    · left
      have hb := bpow.pos binaryRadix (cexp binaryRadix (fexpOf fmt) x)
      rw [scaledMantissa_eq_div, abs_div, abs_of_pos hb, div_lt_one hb] at h
      exact (bpow_lt_bpow_iff binaryRadix _ _).mp (hlower.trans_lt h)
    · exact Or.inr (magnitude_le_of_abs_lt_bpow binaryRadix x _ hx h)
  simp only [cexp, fexpOf, fltExp] at hmag ⊢
  omega

/--
Flush to zero of a binary descriptor in every rounding direction: rounding onto the grid of `fmt`
gives zero exactly when the input, in units of the least subnormal `2 * underflowErrorAt fmt`,
lies in `modeZeroSet mode`.
-/
theorem roundAt_eq_zero_iff_mem (fmt : FloatFormat) (mode : IEEERoundingMode) (x : ℝ) :
    roundAt fmt x mode = 0 ↔ x / (2 * underflowErrorAt fmt) ∈ modeZeroSet mode := by
  rw [roundAt_eq_round, round_eq_zero_iff, roundingFunction_eq_zero_iff,
    two_mul_underflowErrorAt]
  by_cases hx : x = 0
  · subst hx
    simp [scaledMantissa, zero_mem_modeZeroSet]
  have hb := bpow.pos binaryRadix fmt.minSubnormalExponent
  constructor
  · intro h
    have hc := cexp_eq_minSubnormalExponent fmt hx (Or.inl (abs_lt_one_of_mem_modeZeroSet h))
    rwa [scaledMantissa_eq_div, hc] at h
  · intro h
    have hlt : |x| < Flocq.bpow binaryRadix fmt.minSubnormalExponent := by
      have h1 := abs_lt_one_of_mem_modeZeroSet h
      rwa [abs_div, abs_of_pos hb, div_lt_one hb] at h1
    rw [scaledMantissa_eq_div, cexp_eq_minSubnormalExponent fmt hx (Or.inr hlt)]
    exact h

/-- Nearest-even rounding onto the grid of `fmt` stores exactly the magnitudes up to half the
least subnormal as zero. The tie goes to zero. -/
theorem roundAt_eq_zero_iff (fmt : FloatFormat) (x : ℝ) :
    roundAt fmt x = 0 ↔ |x| ≤ underflowErrorAt fmt := by
  have hpos := underflowErrorAt_pos fmt
  rw [roundAt_eq_zero_iff_mem]
  change x / (2 * underflowErrorAt fmt) ∈ Set.Icc (-(1 / 2)) (1 / 2) ↔ _
  rw [Set.mem_Icc, ← abs_le, abs_div, abs_of_pos (by positivity : 0 < 2 * underflowErrorAt fmt),
    div_le_iff₀ (by positivity)]
  simp_all

/-- Clipping to the finite range sends exactly zero to zero. -/
theorem clampAt_eq_zero_iff (fmt : FloatFormat) (x : ℝ) : clampAt fmt x = 0 ↔ x = 0 := by
  have hM := toReal_posMaxFinite_pos fmt
  constructor
  · intro h
    by_contra hx
    rcases lt_or_gt_of_ne hx with hneg | hpos
    · have : clampAt fmt x < 0 := by
        unfold clampAt
        exact max_lt (by linarith) ((min_le_left _ _).trans_lt hneg)
      exact this.ne h
    · have : 0 < clampAt fmt x := by
        unfold clampAt
        exact lt_max_of_lt_right (lt_min hpos hM)
      exact this.ne' h
  · rintro rfl
    exact clampAt_eq_self fmt (by simpa using hM.le)

namespace Rounding

/-- Nearest-even rounding with saturation: relative error `2 ^ (-precision)`, absolute error half
the least subnormal, saturation at the largest finite value. -/
theorem saturating_budget (fmt : FloatFormat) :
    (saturating fmt).Budget (unitRoundoffAt fmt) (underflowErrorAt fmt)
      (toReal (posMaxFinite fmt)) := by
  intro x
  have h1 := abs_clampAt_sub_clampAt_le fmt (roundAt fmt x) x
  have h2 := abs_clampAt_sub_self fmt x
  have h3 := abs_roundAt_sub_le_unitRoundoffAt fmt x
  change |clampAt fmt (roundAt fmt x) - x| ≤ _
  simpa only [add_comm] using Numerics.compose_error (h1.trans h3) h2.le

/-- Nearest-even rounding without an upper limit has the same budget at every threshold. -/
theorem grid_budget (fmt : FloatFormat) (M : ℝ) :
    (grid fmt).Budget (unitRoundoffAt fmt) (underflowErrorAt fmt) M := by
  intro x
  have h := abs_roundAt_sub_le_unitRoundoffAt fmt x
  have : (0 : ℝ) ≤ max 0 (|x| - M) := le_max_left _ _
  change |roundAt fmt x - x| ≤ _
  exact h.trans (le_add_of_nonneg_right this)

/-- The descriptor's own policy has the nearest-even budget with saturation at the largest finite
value. -/
theorem ofFormat_budget (fmt : FloatFormat) :
    (ofFormat fmt).Budget (unitRoundoffAt fmt) (underflowErrorAt fmt)
      (toReal (posMaxFinite fmt)) := by
  unfold ofFormat
  split
  · exact saturating_budget fmt
  · exact grid_budget fmt _

/-- Flush to zero of saturating rounding in every direction: the input, in units of the least
subnormal, lies in `modeZeroSet mode`. -/
theorem saturating_round_eq_zero_iff_mem (fmt : FloatFormat) (mode : IEEERoundingMode) (x : ℝ) :
    (saturating fmt mode).round x = 0 ↔ x / (2 * underflowErrorAt fmt) ∈ modeZeroSet mode := by
  change clampAt fmt (roundAt fmt x mode) = 0 ↔ _
  rw [clampAt_eq_zero_iff, roundAt_eq_zero_iff_mem]

/-- Saturating nearest-even rounding stores exactly the magnitudes up to half the least subnormal
as zero. -/
theorem saturating_round_eq_zero_iff (fmt : FloatFormat) (x : ℝ) :
    (saturating fmt).round x = 0 ↔ |x| ≤ underflowErrorAt fmt := by
  change clampAt fmt (roundAt fmt x) = 0 ↔ _
  rw [clampAt_eq_zero_iff, roundAt_eq_zero_iff]

/-- The descriptor's own policy stores exactly the magnitudes up to half the least subnormal as
zero. -/
theorem ofFormat_round_eq_zero_iff (fmt : FloatFormat) (x : ℝ) :
    (ofFormat fmt).round x = 0 ↔ |x| ≤ underflowErrorAt fmt := by
  unfold ofFormat
  split
  · exact saturating_round_eq_zero_iff fmt x
  · exact roundAt_eq_zero_iff fmt x

/-- Every finite value of the descriptor is stored exactly. -/
theorem saturating_fixes {fmt : FloatFormat} (x : Model fmt) (hx : isFinite x = true) :
    (saturating fmt).Fixes (toReal x) := by
  change clampAt fmt (roundAt fmt (toReal x)) = toReal x
  rw [roundAt_toReal_eq x hx, clampAt_eq_self fmt (abs_toReal_le_posMaxFinite_of_isFinite x hx)]

/-- Saturating rounding keeps order, in every direction. -/
theorem saturating_monotone (fmt : FloatFormat) (mode : IEEERoundingMode) :
    Monotone (saturating fmt mode).round := by
  intro x y hxy
  exact max_le_max le_rfl (min_le_min (roundAt_mono fmt hxy mode) le_rfl)

/-- The largest finite value is stored exactly, and so is everything above it after clipping. -/
theorem saturating_round_of_le {fmt : FloatFormat} {x : ℝ}
    (hx : toReal (posMaxFinite fmt) ≤ x) :
    (saturating fmt).round x = toReal (posMaxFinite fmt) := by
  have hM := toReal_posMaxFinite_pos fmt
  have hfix : roundAt fmt (toReal (posMaxFinite fmt)) = toReal (posMaxFinite fmt) :=
    roundAt_toReal_eq _ (isFinite_posMaxFinite fmt)
  have hle : toReal (posMaxFinite fmt) ≤ roundAt fmt x := hfix ▸ roundAt_mono fmt hx
  change clampAt fmt (roundAt fmt x) = _
  unfold clampAt
  rw [min_eq_right hle, max_eq_right ((neg_nonpos.mpr hM.le).trans hM.le)]

/-- Everything below minus the largest finite value is stored as minus the largest finite value. -/
theorem saturating_round_of_le_neg {fmt : FloatFormat} {x : ℝ}
    (hx : x ≤ -toReal (posMaxFinite fmt)) :
    (saturating fmt).round x = -toReal (posMaxFinite fmt) := by
  have hM := toReal_posMaxFinite_pos fmt
  have hfix : roundAt fmt (-toReal (posMaxFinite fmt)) = -toReal (posMaxFinite fmt) := by
    rw [roundAt_neg, IEEERoundingMode.negate_nearest,
      roundAt_toReal_eq _ (isFinite_posMaxFinite fmt)]
  have hle : roundAt fmt x ≤ -toReal (posMaxFinite fmt) := hfix ▸ roundAt_mono fmt hx
  change clampAt fmt (roundAt fmt x) = _
  unfold clampAt
  rw [min_eq_left (by linarith), max_eq_left hle]

/-- Clipping the input to the finite range first changes nothing: saturating rounding already
stores everything beyond the largest finite value as that value. -/
theorem saturating_round_clamp (fmt : FloatFormat) (x : ℝ) :
    (saturating fmt).round
        (max (-toReal (posMaxFinite fmt)) (min (toReal (posMaxFinite fmt)) x)) =
      (saturating fmt).round x := by
  have hM := toReal_posMaxFinite_pos fmt
  rcases le_total x (-toReal (posMaxFinite fmt)) with h1 | h1
  · rw [min_eq_right (by linarith), max_eq_left h1, saturating_round_of_le_neg le_rfl,
      saturating_round_of_le_neg h1]
  · rcases le_total (toReal (posMaxFinite fmt)) x with h2 | h2
    · rw [min_eq_left h2, max_eq_right (by linarith), saturating_round_of_le le_rfl,
        saturating_round_of_le h2]
    · rw [min_eq_right h2, max_eq_right h1]

/-- Saturating nearest-even rounding is odd. -/
theorem saturating_round_neg (fmt : FloatFormat) (x : ℝ) :
    (saturating fmt).round (-x) = -(saturating fmt).round x := by
  have hM := toReal_posMaxFinite_pos fmt
  change clampAt fmt (roundAt fmt (-x)) = -clampAt fmt (roundAt fmt x)
  rw [roundAt_neg, IEEERoundingMode.negate_nearest]
  unfold clampAt
  simp only [max_def, min_def]
  split_ifs <;> linarith

/-- Saturating nearest-even rounding stores, for every input, a value at least as close to it as
every other stored value. -/
theorem saturating_nearest (fmt : FloatFormat) : (saturating fmt).Nearest := by
  intro x y
  have hM := toReal_posMaxFinite_pos fmt
  have hgM : GenericRepresentable binaryRadix (fexpOf fmt) (toReal (posMaxFinite fmt)) :=
    toReal_genericFormat_of_isFinite _ (isFinite_posMaxFinite fmt)
  have hfix : roundAt fmt (toReal (posMaxFinite fmt)) = toReal (posMaxFinite fmt) :=
    roundAt_toReal_eq _ (isFinite_posMaxFinite fmt)
  have hfixn : roundAt fmt (-toReal (posMaxFinite fmt)) = -toReal (posMaxFinite fmt) := by
    rw [roundAt_neg, IEEERoundingMode.negate_nearest, hfix]
  -- The stored value of `y` is on the grid and inside the finite range.
  obtain ⟨hgen, hrange⟩ : GenericRepresentable binaryRadix (fexpOf fmt) ((saturating fmt).round y) ∧
      |(saturating fmt).round y| ≤ toReal (posMaxFinite fmt) := by
    have hr : GenericRepresentable binaryRadix (fexpOf fmt) (roundAt fmt y) :=
      genericRepresentable_round nearestEven y
    change GenericRepresentable binaryRadix (fexpOf fmt) (clampAt fmt (roundAt fmt y)) ∧
      |clampAt fmt (roundAt fmt y)| ≤ _
    unfold clampAt
    rcases le_total (roundAt fmt y) (toReal (posMaxFinite fmt)) with h1 | h1
    · rcases le_total (-toReal (posMaxFinite fmt)) (roundAt fmt y) with h2 | h2
      · rw [min_eq_left h1, max_eq_right h2]
        exact ⟨hr, abs_le.mpr ⟨h2, h1⟩⟩
      · rw [min_eq_left h1, max_eq_left h2]
        exact ⟨genericRepresentable_neg _ hgM, by rw [abs_neg, abs_of_pos hM]⟩
    · rw [min_eq_right h1, max_eq_right ((neg_nonpos.mpr hM.le).trans hM.le)]
      exact ⟨hgM, by rw [abs_of_pos hM]⟩
  have hnear : |roundAt fmt x - x| ≤ |(saturating fmt).round y - x| :=
    (round_nearestEven_point (β := binaryRadix) (fexp := fexpOf fmt) x).2 _ hgen
  obtain ⟨hlo, hhi⟩ := abs_le.mp hrange
  change |clampAt fmt (roundAt fmt x) - x| ≤ _
  unfold clampAt
  by_cases h1 : roundAt fmt x ≤ toReal (posMaxFinite fmt)
  · by_cases h2 : -toReal (posMaxFinite fmt) ≤ roundAt fmt x
    · rw [min_eq_left h1, max_eq_right h2]
      exact hnear
    · have hx : x < -toReal (posMaxFinite fmt) := by
        by_contra hcon
        have := roundAt_mono fmt (le_of_not_gt hcon)
        rw [hfixn] at this
        exact h2 this
      rw [min_eq_left h1, max_eq_left (le_of_not_ge h2), abs_of_nonneg (by positivity)]
      exact le_trans (by linarith) (le_abs_self _)
  · have hx : toReal (posMaxFinite fmt) < x := by
      by_contra hcon
      have := roundAt_mono fmt (le_of_not_gt hcon)
      rw [hfix] at this
      exact h1 this
    rw [min_eq_right (le_of_not_ge h1), max_eq_right (by linarith), abs_of_nonpos (by linarith)]
    exact le_trans (by linarith) (neg_le_abs _)

/--
The budget of saturating nearest-even rounding with its constants computed: precision `p`,
`2 ^ e` half the least subnormal, and largest finite value `k * 2 ^ q`. The four side conditions
are equalities of natural numbers and integers, which `decide` closes for a concrete descriptor.
-/
theorem saturating_budget_of_eq (fmt : FloatFormat) {p k : ℕ} {e q : ℤ}
    (hp : fmt.fracWidth + 1 = p) (he : fmt.minSubnormalExponent - 1 = e)
    (hk : pow2 fmt.fracWidth + fmt.maxFiniteFracField = k)
    (hq : fmt.maxNormalExponent - Int.ofNat fmt.fracWidth = q) :
    (saturating fmt).Budget ((2 : ℝ) ^ (-(p : ℤ))) ((2 : ℝ) ^ e) ((k : ℝ) * (2 : ℝ) ^ q) := by
  have h := saturating_budget fmt
  rwa [unitRoundoffAt_eq, underflowErrorAt_eq, toReal_posMaxFinite_of_eq fmt hk hq, he,
    show -((fmt.fracWidth : ℤ) + 1) = -(p : ℤ) by rw [← hp]; push_cast; ring] at h

/-- The zero set of saturating nearest-even rounding with its threshold computed. -/
theorem saturating_round_eq_zero_iff_of_eq (fmt : FloatFormat) {e : ℤ}
    (he : fmt.minSubnormalExponent - 1 = e) (x : ℝ) :
    (saturating fmt).round x = 0 ↔ |x| ≤ (2 : ℝ) ^ e := by
  rw [saturating_round_eq_zero_iff, underflowErrorAt_eq, he]

/-- The zero set of saturating rounding in direction `mode`, with the least subnormal `2 ^ e`
computed. -/
theorem saturating_round_eq_zero_iff_mem_of_eq (fmt : FloatFormat) (mode : IEEERoundingMode)
    {e : ℤ} (he : fmt.minSubnormalExponent = e) (x : ℝ) :
    (saturating fmt mode).round x = 0 ↔ x / (2 : ℝ) ^ e ∈ modeZeroSet mode := by
  rw [saturating_round_eq_zero_iff_mem, two_mul_underflowErrorAt, bpow_binaryRadix, he]

/-- The largest finite value with its closed form computed, as the ceiling of saturation. -/
theorem saturating_round_of_le_of_eq (fmt : FloatFormat) {k : ℕ} {q : ℤ}
    (hk : pow2 fmt.fracWidth + fmt.maxFiniteFracField = k)
    (hq : fmt.maxNormalExponent - Int.ofNat fmt.fracWidth = q) {x : ℝ}
    (hx : (k : ℝ) * (2 : ℝ) ^ q ≤ x) : (saturating fmt).round x = (k : ℝ) * (2 : ℝ) ^ q := by
  rw [← toReal_posMaxFinite_of_eq fmt hk hq] at hx ⊢
  exact saturating_round_of_le hx

/--
Nearest-even grid rounding of a nonnegative dyadic `sig * 2 ^ exp`, by integer arithmetic: the
grid exponent `t` and the rounded significand `r` are computed side conditions, which `decide`
closes for concrete numbers.
-/
theorem roundAt_natCast_mul_zpow (fmt : FloatFormat) (sig : ℕ) (exp : ℤ) {r : ℕ} {t : ℤ}
    (ht : max ((sig.log2 : ℤ) + exp - fmt.fracWidth) fmt.minSubnormalExponent = t)
    (hr : roundMantissaAtExponentEven sig exp t = r) :
    roundAt fmt ((sig : ℝ) * (2 : ℝ) ^ exp) = (r : ℝ) * (2 : ℝ) ^ t := by
  have h := roundAt_dyadic_grid fmt ⟨false, sig, exp⟩
  dsimp only at h
  rw [ht, hr, Numerics.Dyadic.toReal_mk_false] at h
  rw [h]
  simp [Flocq.bpow, binaryRadix, Radix.toReal]

/-- Saturating nearest-even rounding of a nonnegative dyadic inside the finite range, by integer
arithmetic. -/
theorem saturating_round_natCast_mul_zpow (fmt : FloatFormat) (sig : ℕ) (exp : ℤ) {r : ℕ}
    {t : ℤ} (ht : max ((sig.log2 : ℤ) + exp - fmt.fracWidth) fmt.minSubnormalExponent = t)
    (hr : roundMantissaAtExponentEven sig exp t = r)
    (hM : (r : ℝ) * (2 : ℝ) ^ t ≤ toReal (posMaxFinite fmt)) :
    (saturating fmt).round ((sig : ℝ) * (2 : ℝ) ^ exp) = (r : ℝ) * (2 : ℝ) ^ t := by
  change clampAt fmt (roundAt fmt _) = _
  rw [roundAt_natCast_mul_zpow fmt sig exp ht hr]
  apply clampAt_eq_self
  rwa [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (zpow_nonneg (zero_le_two) _))]

/-- Nearest-even rounding of a nonnegative rational with a power-of-two denominator onto the
grid of `fmt`, by integer arithmetic. It is meant to be evaluated, for instance by `decide`. -/
def dyadicRound (fmt : FloatFormat) (q : ℚ) : ℚ :=
  let exp : ℤ := -(q.den.log2 : ℤ)
  let t := max ((q.num.natAbs.log2 : ℤ) + exp - fmt.fracWidth) fmt.minSubnormalExponent
  (roundMantissaAtExponentEven q.num.natAbs exp t : ℚ) * 2 ^ t

/-- Saturating nearest-even rounding at a nonnegative rational with a power-of-two denominator
is the computed `dyadicRound`, when that value is inside the finite range. -/
theorem saturating_round_ratCast (fmt : FloatFormat) {q : ℚ} (hq : 0 ≤ q)
    (hden : q.den = 2 ^ q.den.log2)
    (hM : ((dyadicRound fmt q : ℚ) : ℝ) ≤ toReal (posMaxFinite fmt)) :
    (saturating fmt).round (q : ℝ) = ((dyadicRound fmt q : ℚ) : ℝ) := by
  have hnum : (q.num : ℝ) = (q.num.natAbs : ℝ) := by
    have h : ((q.num.natAbs : ℕ) : ℤ) = q.num := Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hq)
    calc (q.num : ℝ) = (((q.num.natAbs : ℕ) : ℤ) : ℝ) := by rw [h]
      _ = (q.num.natAbs : ℝ) := Int.cast_natCast _
  have hdenR : (q.den : ℝ) = (2 : ℝ) ^ q.den.log2 := by exact_mod_cast hden
  have hcast : (q : ℝ) = (q.num.natAbs : ℝ) * (2 : ℝ) ^ (-(q.den.log2 : ℤ)) := by
    rw [Rat.cast_def, hnum, hdenR, zpow_neg, zpow_natCast, div_eq_mul_inv]
  have hvalue : ((dyadicRound fmt q : ℚ) : ℝ) =
      (roundMantissaAtExponentEven q.num.natAbs (-(q.den.log2 : ℤ))
        (max ((q.num.natAbs.log2 : ℤ) + -(q.den.log2 : ℤ) - fmt.fracWidth)
          fmt.minSubnormalExponent) : ℝ) *
        (2 : ℝ) ^ max ((q.num.natAbs.log2 : ℤ) + -(q.den.log2 : ℤ) - fmt.fracWidth)
          fmt.minSubnormalExponent := by
    simp only [dyadicRound]
    push_cast
    rfl
  rw [hvalue] at hM ⊢
  rw [hcast]
  exact saturating_round_natCast_mul_zpow fmt _ _ rfl rfl hM

/--
The check, by integer arithmetic, that saturating nearest-even rounding stores the dyadic rational
`q` as `v`, with `M` the largest finite value of `fmt`. It is decidable, and `RoundsTo.round_eq`
turns it into the statement about the real rounding.
-/
def RoundsTo (fmt : FloatFormat) (M q v : ℚ) : Prop :=
  q.den = 2 ^ q.den.log2 ∧ dyadicRound fmt q ≤ M ∧
    (if q < 0 then -1 else 1) * dyadicRound fmt q = v

instance (fmt : FloatFormat) (M q v : ℚ) : Decidable (RoundsTo fmt M q v) := by
  unfold RoundsTo
  infer_instance

/-- A successful check gives the value of the real rounding, for an input of either sign. -/
theorem RoundsTo.round_eq {fmt : FloatFormat} {M q v : ℚ} (h : RoundsTo fmt M q v)
    (hM : toReal (posMaxFinite fmt) = (M : ℝ)) : (saturating fmt).round (q : ℝ) = (v : ℝ) := by
  obtain ⟨hden, hle, hv⟩ := h
  have hle' : ((dyadicRound fmt q : ℚ) : ℝ) ≤ toReal (posMaxFinite fmt) := by
    rw [hM]
    exact_mod_cast hle
  by_cases hq : q < 0
  · simp only [hq, ↓reduceIte] at hv
    have hneg : dyadicRound fmt (-q) = dyadicRound fmt q := by
      simp [dyadicRound]
    have h := saturating_round_ratCast fmt (q := -q) (by linarith)
      (by rw [Rat.den_neg_eq_den]; exact hden) (by rw [hneg]; exact hle')
    have hcast : (q : ℝ) = -((-q : ℚ) : ℝ) := by push_cast; ring
    rw [hcast, saturating_round_neg, h, hneg, ← hv]
    push_cast
    rw [neg_mul]
    ac_rfl
  · simp only [hq, ↓reduceIte, one_mul] at hv
    rw [saturating_round_ratCast fmt (not_lt.mp hq) hden hle', hv]

/-- A nonnegative dyadic on the grid of `fmt` is stored exactly by the unclipped rounding. The
side conditions are computed, as in `roundAt_natCast_mul_zpow`. -/
theorem grid_fixes_natCast_mul_zpow (fmt : FloatFormat) (sig : ℕ) (exp : ℤ) {r : ℕ} {t : ℤ}
    (ht : max ((sig.log2 : ℤ) + exp - fmt.fracWidth) fmt.minSubnormalExponent = t)
    (hr : roundMantissaAtExponentEven sig exp t = r)
    (hval : (r : ℝ) * (2 : ℝ) ^ t = (sig : ℝ) * (2 : ℝ) ^ exp) :
    (grid fmt).Fixes ((sig : ℝ) * (2 : ℝ) ^ exp) := by
  change roundAt fmt _ = _
  rw [roundAt_natCast_mul_zpow fmt sig exp ht hr, hval]

/-- A nonnegative dyadic on the grid of `fmt` and inside its finite range is stored exactly by
the saturating rounding. -/
theorem saturating_fixes_natCast_mul_zpow (fmt : FloatFormat) (sig : ℕ) (exp : ℤ) {r : ℕ}
    {t : ℤ} (ht : max ((sig.log2 : ℤ) + exp - fmt.fracWidth) fmt.minSubnormalExponent = t)
    (hr : roundMantissaAtExponentEven sig exp t = r)
    (hval : (r : ℝ) * (2 : ℝ) ^ t = (sig : ℝ) * (2 : ℝ) ^ exp)
    (hM : (sig : ℝ) * (2 : ℝ) ^ exp ≤ toReal (posMaxFinite fmt)) :
    (saturating fmt).Fixes ((sig : ℝ) * (2 : ℝ) ^ exp) := by
  change (saturating fmt).round _ = _
  rw [saturating_round_natCast_mul_zpow fmt sig exp ht hr (hval ▸ hM), hval]

/-- FloatLib's executable cast between any two binary descriptors stores the value of the
destination's own policy, whenever the source and the result are finite. -/
theorem toReal_cast_eq_ofFormat {src dst : FloatFormat} (x : Model src)
    (hx : isFinite x = true) (hout : isFinite (cast src dst x) = true) :
    toReal (cast src dst x) = (ofFormat dst).round (toReal x) := by
  rw [cast_policy x hx hout]
  unfold ofFormat
  split <;> rfl

/-- Nearest-even fixed-point rounding is within half a step of its input before clipping. -/
theorem abs_fixRound_sub_le (frac : ℤ) (x : ℝ) :
    |Flocq.round (β := binaryRadix) (fexp := fixExp (-frac)) nearestEven x - x| ≤
      (2 : ℝ) ^ (-frac - 1) := by
  have h := error_bound_ulp (β := binaryRadix) (fexp := fixExp (-frac)) nearestEven x
  have hulp : ulp binaryRadix (fixExp (-frac)) x = Flocq.bpow binaryRadix (-frac) := by
    by_cases hx : x = 0
    · rw [hx, ulp_zero_fix]
    · simp [ulp, hx, cexp, fixExp]
  rw [hulp] at h
  have hpow : Flocq.bpow binaryRadix (-frac) / 2 = (2 : ℝ) ^ (-frac - 1) := by
    simp [Flocq.bpow, binaryRadix, Radix.toReal, zpow_sub_one₀ (two_ne_zero (α := ℝ)),
      div_eq_mul_inv]
  rwa [hpow] at h

/--
Nearest-even fixed point clipped to `[lo, hi]`: no relative error, absolute error half a step, and
saturation at the smaller of `-lo` and `hi`.
-/
theorem fixed_budget (frac : ℤ) {lo hi : ℝ} :
    (fixed frac lo hi).Budget 0 ((2 : ℝ) ^ (-frac - 1)) (min (-lo) hi) := by
  intro x
  have h := abs_fixRound_sub_le frac x
  set r := Flocq.round (β := binaryRadix) (fexp := fixExp (-frac)) nearestEven x
  change |max lo (min hi r) - x| ≤ _
  rw [zero_mul, zero_add]
  have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ (-frac - 1) := (zpow_pos (two_pos) _).le
  rcases abs_le.mp h with ⟨h1, h2⟩
  have hmax0 : (0 : ℝ) ≤ max 0 (|x| - min (-lo) hi) := le_max_left _ _
  have hmax1 : |x| - min (-lo) hi ≤ max 0 (|x| - min (-lo) hi) := le_max_right _ _
  rw [abs_le]
  constructor
  · -- lower bound: the clipped value is at least `min hi r` and at least `lo`
    by_cases hc : r ≤ hi
    · rw [min_eq_right hc]
      have : r ≤ max lo r := le_max_right _ _
      linarith
    · rw [min_eq_left (le_of_not_ge hc)]
      have h3 : hi ≤ max lo hi := le_max_right _ _
      have h4 : min (-lo) hi ≤ hi := min_le_right _ _
      have h5 : x ≤ |x| := le_abs_self x
      linarith
  · -- upper bound
    by_cases hc : lo ≤ min hi r
    · rw [max_eq_right hc]
      have : min hi r ≤ r := min_le_right _ _
      linarith
    · rw [max_eq_left (le_of_not_ge hc)]
      have h4 : min (-lo) hi ≤ -lo := min_le_left _ _
      have h5 : -x ≤ |x| := neg_le_abs x
      linarith

/-- Flush to zero of fixed point in every rounding direction, with zero inside the range: the
input, in units of the step `2 ^ (-frac)`, lies in `modeZeroSet mode`. -/
theorem fixed_round_eq_zero_iff_mem (frac : ℤ) {lo hi : ℝ} (hlo : lo < 0) (hhi : 0 < hi)
    (mode : IEEERoundingMode) (x : ℝ) :
    (fixed frac lo hi mode).round x = 0 ↔ x * (2 : ℝ) ^ frac ∈ modeZeroSet mode := by
  set r := Flocq.round (β := binaryRadix) (fexp := fixExp (-frac)) (roundingFunction mode) x
    with hr
  have hclip : max lo (min hi r) = 0 ↔ r = 0 := by
    constructor
    · intro h
      by_contra hne
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · have : max lo (min hi r) < 0 := max_lt hlo ((min_le_right _ _).trans_lt hneg)
        exact this.ne h
      · have : 0 < max lo (min hi r) := lt_max_of_lt_right (lt_min hhi hpos)
        exact this.ne' h
    · rintro h
      rw [h, min_eq_right hhi.le, max_eq_right hlo.le]
  change max lo (min hi r) = 0 ↔ _
  rw [hclip, hr, round_eq_zero_iff, roundingFunction_eq_zero_iff]
  have hcexp : cexp binaryRadix (fixExp (-frac)) x = -frac := rfl
  have hsm : scaledMantissa binaryRadix (fixExp (-frac)) x = x * (2 : ℝ) ^ frac := by
    rw [scaledMantissa, hcexp, _root_.neg_neg]
    simp [Flocq.bpow, binaryRadix, Radix.toReal]
  rw [hsm]

/-- Nearest-even fixed point with zero inside its range stores exactly the magnitudes up to half a
step as zero. -/
theorem fixed_round_eq_zero_iff (frac : ℤ) {lo hi : ℝ} (hlo : lo < 0) (hhi : 0 < hi) (x : ℝ) :
    (fixed frac lo hi).round x = 0 ↔ |x| ≤ (2 : ℝ) ^ (-frac - 1) := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ frac := zpow_pos (two_pos) _
  have hpow : (2 : ℝ) ^ (-frac - 1) = 1 / 2 / (2 : ℝ) ^ frac := by
    rw [zpow_sub_one₀ (two_ne_zero (α := ℝ)), zpow_neg]
    field_simp
  rw [fixed_round_eq_zero_iff_mem frac hlo hhi, hpow, le_div_iff₀ h2]
  change x * (2 : ℝ) ^ frac ∈ Set.Icc (-(1 / 2)) (1 / 2) ↔ _
  rw [Set.mem_Icc, ← abs_le, abs_mul, abs_of_pos h2]

/--
Fixed point over the rationals, the executable counterpart of `fixed` with nearest-even rounding:
round to a multiple of `2 ^ (-frac)`, ties to the even multiple, and clip to `[lo, hi]`.
-/
def fixedRat (frac : ℤ) (lo hi : ℚ) : Rounding ℚ where
  round q := Numerics.Quantization.Saturating.clamp lo hi
    ((roundRatEven (q * 2 ^ frac) : ℚ) * 2 ^ (-frac))

/-- On rationals, nearest-even fixed point over the reals is the rational computation. -/
theorem fixed_round_ratCast (frac : ℤ) (lo hi q : ℚ) :
    (fixed frac (lo : ℝ) (hi : ℝ)).round (q : ℝ) = (((fixedRat frac lo hi).round q : ℚ) : ℝ) := by
  have hcexp : cexp binaryRadix (fixExp (-frac)) (q : ℝ) = -frac := rfl
  have hsm : scaledMantissa binaryRadix (fixExp (-frac)) (q : ℝ) =
      ((q * 2 ^ frac : ℚ) : ℝ) := by
    rw [scaledMantissa, hcexp, _root_.neg_neg]
    simp [Flocq.bpow, binaryRadix, Radix.toReal]
  have hround : Flocq.round (β := binaryRadix) (fexp := fixExp (-frac)) nearestEven (q : ℝ) =
      ((roundRatEven (q * 2 ^ frac) : ℤ) : ℝ) * (2 : ℝ) ^ (-frac) := by
    unfold Flocq.round
    rw [hsm, nearestEven_ratCast, hcexp]
    simp [Flocq.toReal, Flocq.bpow, binaryRadix, Radix.toReal]
  change max (lo : ℝ) (min (hi : ℝ)
    (Flocq.round (β := binaryRadix) (fexp := fixExp (-frac)) nearestEven (q : ℝ))) = _
  rw [hround]
  simp only [fixedRat, Numerics.Quantization.Saturating.clamp]
  push_cast
  rfl

/--
Rational fixed point clipped to two grid points `a * 2 ^ (-frac) ≤ b * 2 ^ (-frac)` stores, for
every input, a value at least as close to it as every other stored value.
-/
theorem fixedRat_nearest (frac : ℤ) {a b : ℤ} (hab : a ≤ b) :
    (fixedRat frac (a * 2 ^ (-frac)) (b * 2 ^ (-frac))).Nearest := by
  have hstep : (0 : ℚ) < 2 ^ (-frac) := zpow_pos (by decide) _
  have hinv : (2 : ℚ) ^ frac * 2 ^ (-frac) = 1 := by
    rw [← zpow_add₀ (by decide : (2 : ℚ) ≠ 0)]
    simp
  -- Every stored value is an integer multiple of the step between the two ends.
  have hvalue : ∀ y : ℚ, ∃ m : ℤ, a ≤ m ∧ m ≤ b ∧
      (fixedRat frac (a * 2 ^ (-frac)) (b * 2 ^ (-frac))).round y = m * 2 ^ (-frac) := by
    intro y
    refine ⟨Numerics.Quantization.Saturating.clamp a b (roundRatEven (y * 2 ^ frac)),
      Numerics.Quantization.Saturating.lower_le_clamp _ _ _,
      Numerics.Quantization.Saturating.clamp_le_upper hab, ?_⟩
    simp only [fixedRat, Numerics.Quantization.Saturating.clamp]
    rw [← min_mul_of_nonneg _ _ hstep.le, ← max_mul_of_nonneg _ _ hstep.le]
    push_cast
    rfl
  intro x y
  obtain ⟨m, hma, hmb, hm⟩ := hvalue y
  obtain ⟨n, _, _, _⟩ := hvalue x
  rw [hm]
  -- Work in units of the step.
  have hscale : ∀ k : ℤ, |(k : ℚ) * 2 ^ (-frac) - x| = |(k : ℚ) - x * 2 ^ frac| * 2 ^ (-frac) := by
    intro k
    rw [← abs_of_pos hstep, ← abs_mul, abs_of_pos hstep]
    congr 1
    rw [sub_mul, mul_assoc, hinv, mul_one]
  have hnear := roundRatEven_nearest (x * 2 ^ frac) m
  simp only [fixedRat, Numerics.Quantization.Saturating.clamp]
  set r := roundRatEven (x * 2 ^ frac)
  have hclip : max ((a : ℚ) * 2 ^ (-frac)) (min ((b : ℚ) * 2 ^ (-frac)) ((r : ℚ) * 2 ^ (-frac))) =
      ((max a (min b r) : ℤ) : ℚ) * 2 ^ (-frac) := by
    rw [← min_mul_of_nonneg _ _ hstep.le, ← max_mul_of_nonneg _ _ hstep.le]
    push_cast
    rfl
  rw [hclip, hscale, hscale]
  refine mul_le_mul_of_nonneg_right ?_ hstep.le
  by_cases h1 : r ≤ b
  · by_cases h2 : a ≤ r
    · rw [min_eq_right h1, max_eq_right h2]
      exact hnear
    · -- the rounded integer is below the range
      have hra : r < a := lt_of_not_ge h2
      rw [min_eq_right h1, max_eq_left hra.le]
      have hx : x * 2 ^ frac ≤ (a : ℚ) - 1 / 2 := by
        have := abs_le.mp (roundRatEven_error_le_half (x * 2 ^ frac))
        have hra' : (r : ℚ) ≤ (a : ℚ) - 1 := by exact_mod_cast Int.le_sub_one_of_lt hra
        linarith [this.1]
      have hma' : (a : ℚ) ≤ m := by exact_mod_cast hma
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
  · have hrb : b < r := lt_of_not_ge h1
    rw [min_eq_left hrb.le, max_eq_right hab]
    have hx : (b : ℚ) + 1 / 2 ≤ x * 2 ^ frac := by
      have := abs_le.mp (roundRatEven_error_le_half (x * 2 ^ frac))
      have hrb' : (b : ℚ) + 1 ≤ r := by exact_mod_cast Int.add_one_le_of_lt hrb
      linarith [this.2]
    have hmb' : (m : ℚ) ≤ b := by exact_mod_cast hmb
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith

end Rounding

end FloatLib.Floats.Formats.Block
