/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Trigonometric.ArgumentReduction.Proof
public import Mathlib.Analysis.Real.Pi.Irrational

/-!
# Every nonzero argument has an accepting window

For `m > 0`, `m * 2 ^ e * 2/π` is irrational because `π` is (`irrational_pi`), so it keeps a
positive distance `d` from every integer. A reduction of it satisfies
`|fraction + η| ≥ d * 2 ^ scale` with `0 ≤ η < error`, so `|fraction| > d * 2 ^ scale - error`.
The error of `reduceWindow` is `2 m` for every window while `2 ^ scale` doubles with each bit of
window, so every window with `2 m * (2 ^ (bits + 1) + 1) < d * 2 ^ scale` is accepted
(`exists_accepting_window`). The attempt windows of `reduce` double, so enough fuel
reaches an accepted reduction (`exists_accepts_reduce`).

The runtime bounds its attempts and checks the acceptance of the one it returns, so it needs
neither theorem. They show that the bound on attempts is a resource limit: the method itself always
succeeds.
-/

public section

namespace FloatLib.Numerics.Enclosure.ArgumentReduction

/-- An irrational number keeps a positive distance from every integer. -/
private theorem exists_pos_le_abs_sub_intCast {y : ℝ} (hy : Irrational y) :
    ∃ d : ℝ, 0 < d ∧ ∀ n : ℤ, d ≤ |y - n| := by
  refine ⟨min (Int.fract y) (1 - Int.fract y), ?_, ?_⟩
  · have hpos : 0 < Int.fract y := Int.fract_pos.mpr (hy.ne_int _)
    have hlt := Int.fract_lt_one y
    exact lt_min hpos (by linarith)
  · intro n
    rw [← Int.self_sub_floor]
    rcases le_or_gt n ⌊y⌋ with hn | hn
    · have hcast : (n : ℝ) ≤ ⌊y⌋ := by exact_mod_cast hn
      calc min (y - ⌊y⌋) (1 - (y - ⌊y⌋)) ≤ y - ⌊y⌋ := min_le_left _ _
        _ ≤ y - n := by linarith
        _ ≤ |y - n| := le_abs_self _
    · have hcast : (⌊y⌋ : ℝ) + 1 ≤ n := by exact_mod_cast hn
      calc min (y - ⌊y⌋) (1 - (y - ⌊y⌋)) ≤ 1 - (y - ⌊y⌋) := min_le_right _ _
        _ ≤ n - y := by linarith
        _ ≤ |y - n| := by rw [abs_sub_comm]; exact le_abs_self _

/-- `m * 2 ^ e * 2/π` is irrational for `m > 0`. -/
theorem irrational_mul_two_div_pi {m : ℕ} (hm : 0 < m) (e : ℤ) :
    Irrational ((m * 2 ^ e : ℝ) * (2 / Real.pi)) := by
  have hq : ((2 * m * 2 ^ e : ℚ)) ≠ 0 := by positivity
  have h := irrational_pi.ratCast_div hq
  have hcast : (((2 * m * 2 ^ e : ℚ)) : ℝ) / Real.pi = (m * 2 ^ e : ℝ) * (2 / Real.pi) := by
    push_cast
    ring
  rwa [hcast] at h

/--
For `m > 0`, every wide enough window reduces `m * 2 ^ e` with `bits` relative bits:
`QuarterTurns.accepts bits` holds for all windows from some `start` on.
-/
theorem exists_accepting_window {m : ℕ} (hm : 0 < m) (e : ℤ) (bits : ℕ) :
    ∃ start, ∀ window, start ≤ window → (reduceWindow m e window).accepts bits = true := by
  obtain ⟨d, hd, hdist⟩ := exists_pos_le_abs_sub_intCast (irrational_mul_two_div_pi hm e)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 * m * (2 ^ (bits + 1) + 1) / d : ℝ)
    (by norm_num : (1 : ℝ) < 2)
  refine ⟨n + 2, fun window hwindow => ?_⟩
  obtain ⟨j, η, hη, hηlt, hx⟩ := reduceWindow_spec hm e (by omega : 2 ≤ window)
  set q := reduceWindow m e window with hqdef
  have herror : q.error = 2 * m := rfl
  have hscale : q.scale = window - 2 := rfl
  have hs : (0 : ℝ) < 2 ^ q.scale := by positivity
  -- The remainder is at least `d` away from zero.
  have hclose : d ≤ |((q.fraction : ℝ) + η) / 2 ^ q.scale| := by
    have h := hdist (4 * j + q.quadrant.val)
    push_cast at h
    rwa [hx, show 4 * (j : ℝ) + q.quadrant.val + (q.fraction + η) / 2 ^ q.scale -
      (4 * j + q.quadrant.val) = (q.fraction + η) / 2 ^ q.scale by ring] at h
  rw [abs_div, abs_of_pos hs, le_div_iff₀ hs] at hclose
  -- The scale is large enough.
  have hgrow : 2 * m * (2 ^ (bits + 1) + 1) < d * 2 ^ q.scale := by
    have hpow : (2 : ℝ) ^ n ≤ 2 ^ q.scale :=
      pow_le_pow_right₀ (by norm_num) (by rw [hscale]; omega)
    rw [div_lt_iff₀ hd] at hn
    nlinarith
  have hfraction : (2 * m * 2 ^ (bits + 1) : ℝ) ≤ |(q.fraction : ℝ)| := by
    have := abs_add_le (q.fraction : ℝ) η
    rw [abs_of_nonneg hη] at this
    rw [herror] at hηlt
    push_cast at hηlt
    nlinarith
  have hnat : q.error * 2 ^ (bits + 1) ≤ q.fraction.natAbs := by
    have : ((q.error * 2 ^ (bits + 1) : ℕ) : ℝ) ≤ (q.fraction.natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs, herror]
      push_cast
      exact hfraction
    exact_mod_cast this
  simpa [QuarterTurns.accepts, Nat.shiftLeft_eq] using hnat

/-- For `m > 0`, enough fuel makes `reduce` return an accepted reduction. -/
theorem exists_accepts_reduce {m : ℕ} (hm : 0 < m) (e : ℤ) (p bits : ℕ) :
    ∃ fuel, (reduce m e p bits fuel).accepts bits = true := by
  obtain ⟨start, hstart⟩ := exists_accepting_window hm e bits
  refine ⟨start, accepts_reduce le_rfl (hstart _ ?_)⟩
  rw [attemptWindow, Nat.shiftLeft_eq]
  have hlt : start < 2 ^ start := Nat.lt_two_pow_self
  have hone : 1 ≤ startWindow p bits := by unfold startWindow; omega
  nlinarith

end FloatLib.Numerics.Enclosure.ArgumentReduction
