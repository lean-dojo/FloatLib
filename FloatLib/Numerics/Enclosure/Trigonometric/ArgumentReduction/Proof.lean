/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Trigonometric.ArgumentReduction.Runtime
public import FloatLib.Numerics.Enclosure.Constants.Proof
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Correctness of Payne-Hanek reduction

`reduceWindow_spec` proves that every window of at least two bits reduces `m * 2 ^ e`, for
`m > 0`: `x * 2/π = 4 j + quadrant + (fraction + η) / 2 ^ scale` with `0 ≤ η < 2 m`
(`QuarterTurns.Reduces`). The proof splits the cached `T ≤ 2/π * 2 ^ N < T + 2` into its bits above,
inside and below the window: the bits above contribute a multiple of four, the window gives the
fraction, and the bits below together with the error of `T` give `η`. The fraction has magnitude at
most half a quarter turn (`abs_fraction_reduceWindow_le`).

An accepted reduction has the sign of the true remainder and relative error at most `2 ^ -bits`
(`QuarterTurns.Reduces.exists_remainder`). With `r` the reduced argument in radians, the sine and
cosine of `x` are those of `r` rotated by the quadrant
(`QuarterTurns.Reduces.exists_sin_cos_eq_rotate`). The computed argument
`q.argumentNumerator precision / 2 ^ (scale + precision)` is within
`error / 2 ^ scale * π/2 + |fraction| / 2 ^ scale * 2 ^ (1 - precision)` of `r`
(`QuarterTurns.abs_argument_sub_le`), and its rotated sine and cosine are within the same bound of
those of `x` (`QuarterTurns.Reduces.abs_sin_sub_rotate_le` and its cosine form).

`reduce` returns the reduction of one of its attempts (`exists_reduce_eq_reduceWindow`),
so it reduces its argument too (`reduce_spec`), with error `2 m` and a fraction of at most
half a quarter turn. It returns an accepted reduction when some attempt within its fuel is accepted
(`accepts_reduce`). `fuelWithin?` keeps every attempt within its level limit
(`fuelWithin?_spec`) and gives no fuel exactly when the first window exceeds that limit
(`fuelWithin?_eq_none_iff`).
-/

@[expose] public section

namespace FloatLib.Numerics.Enclosure.ArgumentReduction

open Constants

/--
`q` reduces `x`: `x * 2/π = 4 j + quadrant + (fraction + η) / 2 ^ scale` for an integer `j` and some
`η` with `0 ≤ η < error`.
-/
def QuarterTurns.Reduces (q : QuarterTurns) (x : ℝ) : Prop :=
  ∃ j : ℤ, ∃ η : ℝ, 0 ≤ η ∧ η < q.error ∧
    x * (2 / Real.pi) = 4 * j + q.quadrant.val + (q.fraction + η) / 2 ^ q.scale

/-! ## The window -/

/-- The window identity behind `reduceWindow_spec`, over the reals. -/
private theorem window_identity {m T δ H piece L Q y k F u twoD : ℝ}
    (hT : T = twoD * (4 * u * H + piece) + L) (hpiece : m * piece = 4 * u * Q + y)
    (hy : y = k * u + F) (hD : twoD ≠ 0) (hu : u ≠ 0) :
    4 * m * (T + δ) / (twoD * (4 * u)) =
      4 * (m * H + Q) + k + (F + m * (L + δ) / twoD) / u := by
  subst hT
  field_simp
  linear_combination twoD * hpiece + twoD * hy

/-- The level of a window holds at least `e + window + 6` bits of `2/π`. -/
theorem le_levelBits_windowLevel (e : ℤ) (window : ℕ) :
    e + window + 6 ≤ (levelBits (windowLevel e window) : ℤ) := by
  have h := le_levelBits_levelFor (max (e + window + 6).toNat (window + 6))
  have h' : (e + window + 6).toNat ≤ levelBits (windowLevel e window) :=
    (le_max_left _ _).trans h
  have := Int.self_le_toNat (e + window + 6)
  omega

/-- Every window of at least two bits reduces `m * 2 ^ e`, for `m > 0`. -/
theorem reduceWindow_spec {m : ℕ} (hm : 0 < m) (e : ℤ) {window : ℕ} (hwindow : 2 ≤ window) :
    (reduceWindow m e window).Reduces (m * 2 ^ e) := by
  set level := windowLevel e window with hlevel
  set N := levelBits level with hN
  set T := (piLevelAt level).twoOverPi with hTdef
  set D := ((N : ℤ) - e + 2).toNat - window with hDdef
  set piece := (T >>> D) % 2 ^ window with hpiecedef
  set y := m * piece % 2 ^ window with hydef
  set unit := 2 ^ (window - 2) with hunitdef
  set k := (y + unit / 2) / unit with hkdef
  have hq : reduceWindow m e window =
      { quadrant := ⟨k % 4, Nat.mod_lt _ (by decide)⟩
        fraction := (y : ℤ) - (k * unit : ℕ)
        scale := window - 2
        error := 2 * m } := rfl
  rw [hq]
  have hlevelBits : e + window + 6 ≤ (N : ℤ) := le_levelBits_windowLevel e window
  have hDW : (D : ℤ) + window = N - e + 2 := by
    have h0 : 0 ≤ (N : ℤ) - e + 2 := by omega
    have h1 := Int.toNat_of_nonneg h0
    have h2 : window ≤ ((N : ℤ) - e + 2).toNat := by omega
    omega
  obtain ⟨hTlo, hThi⟩ : LowerApprox (2 / Real.pi) N T := by
    rw [hTdef, piLevelAt_eq]
    exact piLevel_twoOverPi_spec _
  -- Bits of `T` above, inside and below the window.
  have hsplitLow : 2 ^ D * (T / 2 ^ D) + T % 2 ^ D = T := Nat.div_add_mod T (2 ^ D)
  have hsplitHigh : 2 ^ window * (T / 2 ^ D / 2 ^ window) + piece = T / 2 ^ D := by
    rw [hpiecedef, Nat.shiftRight_eq_div_pow]
    exact Nat.div_add_mod (T / 2 ^ D) (2 ^ window)
  have hproduct : 2 ^ window * (m * piece / 2 ^ window) + y = m * piece :=
    Nat.div_add_mod (m * piece) (2 ^ window)
  have hwindowPow : (2 : ℝ) ^ window = 4 * unit := by
    rw [hunitdef]
    push_cast
    rw [show window = 2 + (window - 2) by omega, pow_add]
    norm_num
  have hk : (k : ℝ) = 4 * ((k / 4 : ℕ) : ℝ) + ((k % 4 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod k 4).symm
  set L := T % 2 ^ D with hLdef
  set δ : ℝ := 2 / Real.pi * 2 ^ N - T with hδdef
  refine ⟨((m * (T / 2 ^ D / 2 ^ window) + m * piece / 2 ^ window + k / 4 : ℕ) : ℤ),
    m * (L + δ) / 2 ^ D, ?_, ?_, ?_⟩
  · have : (0 : ℝ) ≤ δ := by rw [hδdef]; linarith
    positivity
  · have hL : (L : ℝ) + 1 ≤ 2 ^ D := by
      have : L < 2 ^ D := Nat.mod_lt _ (Nat.two_pow_pos D)
      exact_mod_cast this
    have hδ : δ < 2 := by rw [hδdef]; linarith
    have hpowD : (1 : ℝ) ≤ 2 ^ D := one_le_pow₀ (by norm_num)
    have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
    rw [div_lt_iff₀ (by positivity)]
    push_cast
    nlinarith
  · -- Scale `2 ^ e / 2 ^ N` to `4 / (2 ^ D * 2 ^ window)`.
    have hpow : (2 : ℝ) ^ e * (2 ^ D * 2 ^ window) = 4 * 2 ^ N := by
      have he : e = ((N + 2 : ℕ) : ℤ) - ((D + window : ℕ) : ℤ) := by push_cast; omega
      rw [he, zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast, pow_add, pow_add]
      field_simp
      norm_num
    have htwo : 2 / Real.pi = (T + δ) / 2 ^ N := by
      rw [hδdef]
      field_simp
      ring
    have hscaled : (m * 2 ^ e : ℝ) * (2 / Real.pi) =
        4 * m * (T + δ) / (2 ^ D * (4 * unit)) := by
      have hDW0 : (0 : ℝ) < 2 ^ D * 2 ^ window := by positivity
      have h2e : (2 : ℝ) ^ e = 4 * 2 ^ N / (2 ^ D * 2 ^ window) := by
        rw [eq_div_iff hDW0.ne']
        exact hpow
      rw [htwo, ← hwindowPow, h2e]
      field_simp
    rw [hscaled]
    have hTReal :
        (T : ℝ) = 2 ^ D * (4 * unit * ((T / 2 ^ D / 2 ^ window : ℕ) : ℝ) + piece) + L := by
      have h1 : (T : ℝ) = 2 ^ D * ((T / 2 ^ D : ℕ) : ℝ) + L := by exact_mod_cast hsplitLow.symm
      have h2 :
          ((T / 2 ^ D : ℕ) : ℝ) = 2 ^ window * ((T / 2 ^ D / 2 ^ window : ℕ) : ℝ) + piece := by
        exact_mod_cast hsplitHigh.symm
      rw [h1, h2, hwindowPow]
    have hpieceReal : (m : ℝ) * piece = 4 * unit * ((m * piece / 2 ^ window : ℕ) : ℝ) + y := by
      have : ((m * piece : ℕ) : ℝ) = 2 ^ window * ((m * piece / 2 ^ window : ℕ) : ℝ) + y := by
        exact_mod_cast hproduct.symm
      push_cast at this
      rw [this, hwindowPow]
    have hyReal : (y : ℝ) = k * unit + ((y : ℤ) - (k * unit : ℕ) : ℤ) := by push_cast; ring
    have hD0 : (2 : ℝ) ^ D ≠ 0 := by positivity
    have hunit0 : (unit : ℝ) ≠ 0 := by rw [hunitdef]; positivity
    rw [window_identity hTReal hpieceReal hyReal hD0 hunit0]
    have hscale : ((2 : ℝ) ^ (window - 2)) = unit := by rw [hunitdef]; push_cast; rfl
    rw [hscale, hk]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_natCast, Nat.cast_add,
      Nat.cast_mul]
    ring

/-- The fraction of a window of at least three bits is at most half a quarter turn. -/
theorem abs_fraction_reduceWindow_le (m : ℕ) (e : ℤ) {window : ℕ} (hwindow : 3 ≤ window) :
    |(reduceWindow m e window).fraction| ≤ 2 ^ (window - 3) := by
  set level := windowLevel e window
  set D := ((levelBits level : ℤ) - e + 2).toNat - window
  set piece := ((piLevelAt level).twoOverPi >>> D) % 2 ^ window
  set y := m * piece % 2 ^ window
  set unit := 2 ^ (window - 2) with hunitdef
  set k := (y + unit / 2) / unit with hkdef
  have hq : (reduceWindow m e window).fraction = (y : ℤ) - (k * unit : ℕ) := rfl
  rw [hq]
  have hunit : unit = 2 * 2 ^ (window - 3) := by
    rw [hunitdef, show window - 2 = (window - 3) + 1 by omega, pow_succ]
    ring
  have hpos : 0 < unit := by rw [hunitdef]; exact Nat.two_pow_pos _
  have hlow : k * unit ≤ y + unit / 2 := Nat.div_mul_le_self _ _
  have hhigh : y + unit / 2 < (k + 1) * unit := by
    rw [hkdef, mul_comm]
    exact Nat.lt_mul_div_succ _ hpos
  rw [hunit] at hlow hhigh
  rw [show 2 * 2 ^ (window - 3) / 2 = 2 ^ (window - 3) by omega] at hlow hhigh
  rw [abs_le]
  push_cast
  constructor <;> push_cast [hunit] <;> nlinarith

/-! ## Accepted reductions -/

/--
An accepted reduction has a nonzero fraction that keeps its sign: for `0 ≤ η < error`,
`fraction + η` has the sign of `fraction`, and `η * (2 ^ (bits + 1) - 1) ≤ |fraction + η|`.
-/
theorem QuarterTurns.accepts_spec {q : QuarterTurns} {bits : ℕ} (h : q.accepts bits = true)
    {η : ℝ} (hη : 0 ≤ η) (hηlt : η < q.error) :
    q.fraction ≠ 0 ∧ (0 < q.fraction ↔ 0 < (q.fraction : ℝ) + η) ∧
      η * (2 ^ (bits + 1) - 1) ≤ |(q.fraction : ℝ) + η| := by
  have hacc : q.error * 2 ^ (bits + 1) ≤ q.fraction.natAbs := by
    simpa [QuarterTurns.accepts, Nat.shiftLeft_eq] using h
  have hacc' : (q.error : ℝ) * 2 ^ (bits + 1) ≤ |(q.fraction : ℝ)| := by
    have : ((q.error * 2 ^ (bits + 1) : ℕ) : ℝ) ≤ (q.fraction.natAbs : ℝ) := by
      exact_mod_cast hacc
    push_cast at this
    rwa [Nat.cast_natAbs, Int.cast_abs] at this
  have herr : (0 : ℝ) < q.error := lt_of_le_of_lt hη hηlt
  have hpow : (2 : ℝ) ≤ 2 ^ (bits + 1) := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (bits + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hF : (q.fraction : ℝ) ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hacc'
    nlinarith
  refine ⟨by exact_mod_cast hF, ?_, ?_⟩
  · constructor
    · intro hpos
      have : (0 : ℝ) < q.fraction := by exact_mod_cast hpos
      linarith
    · intro hsum
      by_contra hnot
      have hneg : (q.fraction : ℝ) ≤ 0 := by exact_mod_cast not_lt.mp hnot
      rw [abs_of_nonpos hneg] at hacc'
      nlinarith
  · rcases lt_or_gt_of_ne hF with hneg | hpos
    · rw [abs_of_neg hneg] at hacc'
      have hsum : (q.fraction : ℝ) + η < 0 := by nlinarith
      rw [abs_of_neg hsum]
      nlinarith
    · rw [abs_of_pos hpos] at hacc'
      rw [abs_of_pos (by linarith)]
      nlinarith

/--
An accepted reduction gives the remainder `f` of `x * 2/π`, in units of `2 ^ -scale` quarter turns,
to a relative error of `2 ^ -bits` and with its sign.
-/
theorem QuarterTurns.Reduces.exists_remainder {q : QuarterTurns} {x : ℝ} (hq : q.Reduces x)
    {bits : ℕ} (h : q.accepts bits = true) :
    ∃ j : ℤ, ∃ f : ℝ, x * (2 / Real.pi) = 4 * j + q.quadrant.val + f / 2 ^ q.scale ∧
      |f - q.fraction| ≤ |f| / 2 ^ bits ∧ (0 < q.fraction ↔ 0 < f) ∧ q.fraction ≠ 0 := by
  obtain ⟨j, η, hη, hηlt, hx⟩ := hq
  obtain ⟨hF, hsign, hrel⟩ := QuarterTurns.accepts_spec h hη hηlt
  refine ⟨j, q.fraction + η, hx, ?_, hsign, hF⟩
  rw [add_sub_cancel_left, abs_of_nonneg hη, le_div_iff₀ (by positivity)]
  have : (2 : ℝ) ^ bits ≤ 2 ^ (bits + 1) - 1 := by
    rw [pow_succ]
    have : (1 : ℝ) ≤ 2 ^ bits := one_le_pow₀ (by norm_num)
    linarith
  nlinarith

/-! ## Quadrants -/

/-- The sine and cosine after whole quarter turns are the rotated sine and cosine. -/
theorem sin_cos_add_quarterTurns (r : ℝ) (j : ℤ) (quadrant : Fin 4) :
    (Real.sin (r + (4 * j + quadrant.val) * (Real.pi / 2)),
        Real.cos (r + (4 * j + quadrant.val) * (Real.pi / 2))) =
      rotate quadrant (Real.sin r) (Real.cos r) := by
  have hturns : r + (4 * j + quadrant.val) * (Real.pi / 2) =
      r + quadrant.val * (Real.pi / 2) + j * (2 * Real.pi) := by ring
  rw [hturns, Real.sin_add_int_mul_two_pi, Real.cos_add_int_mul_two_pi]
  have h2 : r + 2 * (Real.pi / 2) = r + Real.pi := by ring
  have h3 : r + 3 * (Real.pi / 2) = r + Real.pi / 2 + Real.pi := by ring
  match quadrant with
  | ⟨0, _⟩ => simp [rotate]
  | ⟨1, _⟩ => simp [rotate, Real.sin_add_pi_div_two, Real.cos_add_pi_div_two]
  | ⟨2, _⟩ => simp [rotate, h2, Real.sin_add_pi, Real.cos_add_pi]
  | ⟨3, _⟩ =>
      simp [rotate, h3, Real.sin_add_pi, Real.cos_add_pi, Real.sin_add_pi_div_two,
        Real.cos_add_pi_div_two]
  | ⟨n + 4, h⟩ => exact absurd h (by omega)

/--
With `r = (fraction + η) / 2 ^ scale * π/2` the reduced argument, the sine and cosine of `x` are
those of `r` rotated by the quadrant.
-/
theorem QuarterTurns.Reduces.exists_sin_cos_eq_rotate {q : QuarterTurns} {x : ℝ}
    (hq : q.Reduces x) :
    ∃ η : ℝ, 0 ≤ η ∧ η < q.error ∧
      (Real.sin x, Real.cos x) =
        rotate q.quadrant (Real.sin ((q.fraction + η) / 2 ^ q.scale * (Real.pi / 2)))
          (Real.cos ((q.fraction + η) / 2 ^ q.scale * (Real.pi / 2))) := by
  obtain ⟨j, η, hη, hηlt, hx⟩ := hq
  refine ⟨η, hη, hηlt, ?_⟩
  rw [← sin_cos_add_quarterTurns _ j]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hxeq : x = (q.fraction + η) / 2 ^ q.scale * (Real.pi / 2) +
      (4 * j + q.quadrant.val) * (Real.pi / 2) := by
    calc x = x * (2 / Real.pi) * (Real.pi / 2) := by field_simp
      _ = _ := by rw [hx]; ring
  rw [← hxeq]

/-- A quarter-turn rotation keeps the Lipschitz bound of sine. -/
theorem abs_rotate_fst_sub_le (quadrant : Fin 4) (a b : ℝ) :
    |(rotate quadrant (Real.sin a) (Real.cos a)).1 -
        (rotate quadrant (Real.sin b) (Real.cos b)).1| ≤ |a - b| := by
  fin_cases quadrant <;> simp only [rotate]
  · exact Real.abs_sin_sub_sin_le a b
  · exact Real.abs_cos_sub_cos_le a b
  · rw [neg_sub_neg, abs_sub_comm]
    exact Real.abs_sin_sub_sin_le a b
  · rw [neg_sub_neg, abs_sub_comm]
    exact Real.abs_cos_sub_cos_le a b

/-- A quarter-turn rotation keeps the Lipschitz bound of cosine. -/
theorem abs_rotate_snd_sub_le (quadrant : Fin 4) (a b : ℝ) :
    |(rotate quadrant (Real.sin a) (Real.cos a)).2 -
        (rotate quadrant (Real.sin b) (Real.cos b)).2| ≤ |a - b| := by
  fin_cases quadrant <;> simp only [rotate]
  · exact Real.abs_cos_sub_cos_le a b
  · rw [neg_sub_neg, abs_sub_comm]
    exact Real.abs_sin_sub_sin_le a b
  · rw [neg_sub_neg, abs_sub_comm]
    exact Real.abs_cos_sub_cos_le a b
  · exact Real.abs_sin_sub_sin_le a b

/-! ## Error of the computed argument -/

/--
The computed argument `q.argumentNumerator precision / 2 ^ (scale + precision)` is within
`error / 2 ^ scale * π/2 + |fraction| / 2 ^ scale * 2 / 2 ^ precision` of the reduced argument
`(fraction + η) / 2 ^ scale * π/2`, for `0 ≤ η < error`.
-/
theorem QuarterTurns.abs_argument_sub_le (q : QuarterTurns) (precision : ℕ) {η : ℝ}
    (hη : 0 ≤ η) (hηlt : η < q.error) :
    |(q.fraction + η) / 2 ^ q.scale * (Real.pi / 2) -
        q.argumentNumerator precision / 2 ^ (q.scale + precision)| ≤
      q.error / 2 ^ q.scale * (Real.pi / 2) +
        |(q.fraction : ℝ)| / 2 ^ q.scale * (2 / 2 ^ precision) := by
  obtain ⟨hlo, hhi⟩ := halfPiLower_spec precision
  set H := halfPiLower precision with hH
  have hnum : (q.argumentNumerator precision : ℝ) = q.fraction * H := by
    simp [QuarterTurns.argumentNumerator, hH]
  rw [hnum]
  have hs : (0 : ℝ) < 2 ^ q.scale := by positivity
  have hp : (0 : ℝ) < 2 ^ precision := by positivity
  have hsplit : (q.fraction + η) / 2 ^ q.scale * (Real.pi / 2) -
      q.fraction * H / 2 ^ (q.scale + precision) =
      q.fraction / 2 ^ q.scale * (Real.pi / 2 - H / 2 ^ precision) +
        η / 2 ^ q.scale * (Real.pi / 2) := by
    rw [pow_add]
    field_simp
    ring
  rw [hsplit]
  have hgap0 : 0 ≤ Real.pi / 2 - H / 2 ^ precision := by
    rw [sub_nonneg, div_le_iff₀ hp]
    linarith
  have hgap : Real.pi / 2 - H / 2 ^ precision ≤ 2 / 2 ^ precision := by
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hp]
    linarith
  have hηterm : 0 ≤ η / 2 ^ q.scale * (Real.pi / 2) :=
    mul_nonneg (div_nonneg hη hs.le) (by positivity)
  have h1 : |(q.fraction : ℝ)| / 2 ^ q.scale * (Real.pi / 2 - H / 2 ^ precision) ≤
      |(q.fraction : ℝ)| / 2 ^ q.scale * (2 / 2 ^ precision) :=
    mul_le_mul_of_nonneg_left hgap (by positivity)
  have h2 : η / 2 ^ q.scale * (Real.pi / 2) ≤ q.error / 2 ^ q.scale * (Real.pi / 2) := by
    gcongr
  calc _ ≤ |(q.fraction : ℝ) / 2 ^ q.scale * (Real.pi / 2 - H / 2 ^ precision)| +
        |η / 2 ^ q.scale * (Real.pi / 2)| := abs_add_le _ _
    _ = |(q.fraction : ℝ)| / 2 ^ q.scale * (Real.pi / 2 - H / 2 ^ precision) +
        η / 2 ^ q.scale * (Real.pi / 2) := by
      rw [abs_mul, abs_div, abs_of_pos hs, abs_of_nonneg hgap0, abs_of_nonneg hηterm]
    _ ≤ _ := by linarith

/--
The sine of a reduced `x` is within `error / 2 ^ scale * π/2 + |fraction| / 2 ^ scale * 2 / 2 ^
precision` of the rotated sine of the computed argument
`q.argumentNumerator precision / 2 ^ (scale + precision)`.
-/
theorem QuarterTurns.Reduces.abs_sin_sub_rotate_le {q : QuarterTurns} {x : ℝ} (hq : q.Reduces x)
    (precision : ℕ) :
    |Real.sin x - (rotate q.quadrant
        (Real.sin (q.argumentNumerator precision / 2 ^ (q.scale + precision)))
        (Real.cos (q.argumentNumerator precision / 2 ^ (q.scale + precision)))).1| ≤
      q.error / 2 ^ q.scale * (Real.pi / 2) +
        |(q.fraction : ℝ)| / 2 ^ q.scale * (2 / 2 ^ precision) := by
  obtain ⟨η, hη, hηlt, hsc⟩ := hq.exists_sin_cos_eq_rotate
  have hsin := congrArg Prod.fst hsc
  simp only at hsin
  rw [hsin]
  exact (abs_rotate_fst_sub_le _ _ _).trans (q.abs_argument_sub_le precision hη hηlt)

/-- The cosine form of `QuarterTurns.Reduces.abs_sin_sub_rotate_le`. -/
theorem QuarterTurns.Reduces.abs_cos_sub_rotate_le {q : QuarterTurns} {x : ℝ} (hq : q.Reduces x)
    (precision : ℕ) :
    |Real.cos x - (rotate q.quadrant
        (Real.sin (q.argumentNumerator precision / 2 ^ (q.scale + precision)))
        (Real.cos (q.argumentNumerator precision / 2 ^ (q.scale + precision)))).2| ≤
      q.error / 2 ^ q.scale * (Real.pi / 2) +
        |(q.fraction : ℝ)| / 2 ^ q.scale * (2 / 2 ^ precision) := by
  obtain ⟨η, hη, hηlt, hsc⟩ := hq.exists_sin_cos_eq_rotate
  have hcos := congrArg Prod.snd hsc
  simp only at hcos
  rw [hcos]
  exact (abs_rotate_snd_sub_le _ _ _).trans (q.abs_argument_sub_le precision hη hηlt)

/-! ## Attempts -/

/-- Every attempt window has at least twenty bits. -/
theorem twenty_le_attemptWindow (p bits attempt : ℕ) : 20 ≤ attemptWindow p bits attempt := by
  rw [attemptWindow, startWindow, Nat.shiftLeft_eq]
  have : 1 ≤ 2 ^ attempt := Nat.one_le_two_pow
  nlinarith

/-- Later attempts have wider windows. -/
theorem attemptWindow_mono (p bits : ℕ) {attempt attempt' : ℕ} (h : attempt ≤ attempt') :
    attemptWindow p bits attempt ≤ attemptWindow p bits attempt' := by
  rw [attemptWindow, attemptWindow, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) h)

/-- Wider windows read the same or a higher level. -/
theorem windowLevel_mono (e : ℤ) {window window' : ℕ} (h : window ≤ window') :
    windowLevel e window ≤ windowLevel e window' :=
  levelFor_mono (max_le_max (Int.toNat_le_toNat (by omega)) (by omega))

/-- The attempts from `attempt` on return the reduction of one of them. -/
private theorem exists_reduce_go_eq_reduceWindow (m : ℕ) (e : ℤ) (p bits : ℕ) :
    ∀ fuel attempt, ∃ last, attempt ≤ last ∧ last ≤ attempt + fuel ∧
      reduce.go m e p bits attempt fuel = reduceWindow m e (attemptWindow p bits last)
  | 0, attempt => ⟨attempt, le_rfl, by omega, rfl⟩
  | fuel + 1, attempt => by
      simp only [reduce.go]
      split
      · exact ⟨attempt, le_rfl, by omega, rfl⟩
      · obtain ⟨last, hlo, hhi, h⟩ :=
          exists_reduce_go_eq_reduceWindow m e p bits fuel (attempt + 1)
        exact ⟨last, by omega, by omega, h⟩

/-- `reduce` returns the reduction of one of its attempts. -/
theorem exists_reduce_eq_reduceWindow (m : ℕ) (e : ℤ) (p bits fuel : ℕ) :
    ∃ attempt ≤ fuel,
      reduce m e p bits fuel = reduceWindow m e (attemptWindow p bits attempt) := by
  obtain ⟨attempt, -, hle, h⟩ := exists_reduce_go_eq_reduceWindow m e p bits fuel 0
  exact ⟨attempt, by omega, h⟩

/-- `reduce` reduces `m * 2 ^ e`, whichever attempt it returns. -/
theorem reduce_spec {m : ℕ} (hm : 0 < m) (e : ℤ) (p bits fuel : ℕ) :
    (reduce m e p bits fuel).Reduces (m * 2 ^ e) := by
  obtain ⟨attempt, -, h⟩ := exists_reduce_eq_reduceWindow m e p bits fuel
  rw [h]
  exact reduceWindow_spec hm e ((by omega : 2 ≤ 20).trans (twenty_le_attemptWindow p bits attempt))

/-- The error of `reduce` is `2 m` units. -/
theorem error_reduce (m : ℕ) (e : ℤ) (p bits fuel : ℕ) :
    (reduce m e p bits fuel).error = 2 * m := by
  obtain ⟨attempt, -, h⟩ := exists_reduce_eq_reduceWindow m e p bits fuel
  rw [h]
  rfl

/-- The fraction of `reduce` is at most half a quarter turn. -/
theorem abs_fraction_reduce_le (m : ℕ) (e : ℤ) (p bits fuel : ℕ) :
    |(reduce m e p bits fuel).fraction| ≤
      2 ^ ((reduce m e p bits fuel).scale - 1) := by
  obtain ⟨attempt, -, h⟩ := exists_reduce_eq_reduceWindow m e p bits fuel
  rw [h]
  have hwindow := twenty_le_attemptWindow p bits attempt
  have hscale : (reduceWindow m e (attemptWindow p bits attempt)).scale - 1 =
      attemptWindow p bits attempt - 3 := by
    change attemptWindow p bits attempt - 2 - 1 = _
    omega
  rw [hscale]
  exact abs_fraction_reduceWindow_le m e (by omega)

/--
An accepted attempt within the fuel makes the attempts from `attempt` on return an accepted
reduction.
-/
private theorem accepts_reduce_go {m : ℕ} {e : ℤ} {p bits : ℕ} :
    ∀ fuel attempt accepted, attempt ≤ accepted → accepted ≤ attempt + fuel →
      (reduceWindow m e (attemptWindow p bits accepted)).accepts bits →
      (reduce.go m e p bits attempt fuel).accepts bits
  | 0, attempt, accepted, hlo, hhi, h => by
      obtain rfl : accepted = attempt := by omega
      simpa [reduce.go] using h
  | fuel + 1, attempt, accepted, hlo, hhi, h => by
      simp only [reduce.go]
      split
      · assumption
      · rename_i hrejected
        have hne : accepted ≠ attempt := by
          rintro rfl
          exact hrejected h
        exact accepts_reduce_go fuel (attempt + 1) accepted (by omega) (by omega) h

/-- `reduce` returns an accepted reduction when some attempt within the fuel is accepted. -/
theorem accepts_reduce {m : ℕ} {e : ℤ} {p bits fuel attempt : ℕ} (hattempt : attempt ≤ fuel)
    (h : (reduceWindow m e (attemptWindow p bits attempt)).accepts bits) :
    (reduce m e p bits fuel).accepts bits :=
  accepts_reduce_go fuel 0 attempt (Nat.zero_le _) (by omega) h

/--
`fuelWithin?` keeps every attempt within the level limit: a result `count` is at most `fuel`, and
every attempt up to it reads a level of at most `limit`.
-/
theorem fuelWithin?_spec {e : ℤ} {p bits limit fuel count : ℕ}
    (h : fuelWithin? e p bits limit fuel = some count) :
    count ≤ fuel ∧ ∀ attempt ≤ count, windowLevel e (attemptWindow p bits attempt) ≤ limit := by
  induction fuel generalizing count with
  | zero =>
      simp only [fuelWithin?] at h
      split at h
      · rename_i hfirst
        obtain rfl := Option.some.inj h
        exact ⟨le_rfl, fun attempt hattempt => by
          obtain rfl : attempt = 0 := by omega
          exact hfirst⟩
      · exact absurd h (by simp)
  | succ fuel ih =>
      simp only [fuelWithin?] at h
      split at h
      · rename_i hlast
        obtain rfl := Option.some.inj h
        exact ⟨le_rfl, fun attempt hattempt =>
          (windowLevel_mono e (attemptWindow_mono p bits hattempt)).trans hlast⟩
      · obtain ⟨hle, hall⟩ := ih h
        exact ⟨by omega, hall⟩

/-- `fuelWithin?` gives no fuel exactly when the first window reads a level above `limit`. -/
theorem fuelWithin?_eq_none_iff {e : ℤ} {p bits limit fuel : ℕ} :
    fuelWithin? e p bits limit fuel = none ↔ limit < windowLevel e (attemptWindow p bits 0) := by
  induction fuel with
  | zero =>
      simp only [fuelWithin?]
      split
      · rename_i hfirst
        simp only [reduceCtorEq, false_iff, not_lt]
        exact hfirst
      · rename_i hfirst
        simp only [true_iff]
        omega
  | succ fuel ih =>
      simp only [fuelWithin?]
      split
      · rename_i hlast
        simp only [reduceCtorEq, false_iff, not_lt]
        exact (windowLevel_mono e (attemptWindow_mono p bits (Nat.zero_le _))).trans hlast
      · exact ih

end FloatLib.Numerics.Enclosure.ArgumentReduction
