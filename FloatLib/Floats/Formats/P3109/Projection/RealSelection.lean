/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Projection.Rational.Selection
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Real stochastic rounding thresholds

The report's floor and nearest-even formulas can be tested by comparing the exact real
fraction with one rational threshold. These identities apply to irrational fractions as well.
They justify the integer square comparisons used when rounding a square root.

Reference: P3109 unapproved interim report 4.0.3, revision `34f5964`, §4.7.4.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.P3109.RealRounding

/-- Nearest integer to a nonnegative real, with ties sent to the even integer. -/
noncomputable def nearestEven (value : Real) : Nat :=
  let lower : Nat := ⌊value⌋₊
  if value < lower + 1 / 2 ∨ (value = lower + 1 / 2 ∧ lower % 2 = 0) then lower
  else lower + 1

/-- The real RNITE formula preserves natural numbers. -/
@[simp] theorem nearestEven_natCast (n : Nat) : nearestEven (n : Real) = n := by
  simp only [nearestEven, Nat.floor_natCast]
  simp

/--
Reaching a positive integer by nearest-even rounding is decided at its lower halfway point.
At that point it is the parity of the upper integer that decides the tie.
-/
theorem le_nearestEven_iff (value : Real) (boundary : Nat) (_hb : 0 < boundary)
    (hv : 0 ≤ value) :
    boundary ≤ nearestEven value ↔
      (boundary : Real) - 1 / 2 < value ∨
        (value = (boundary : Real) - 1 / 2 ∧ boundary % 2 = 0) := by
  have hlo := Nat.floor_le hv
  have hhi := Nat.lt_floor_add_one value
  have hfloor := Nat.mod_lt ⌊value⌋₊ (by decide : 0 < 2)
  have hbmod := Nat.mod_lt boundary (by decide : 0 < 2)
  dsimp only [nearestEven]
  split_ifs with h
  · constructor
    · intro hle
      have hc : (boundary : Real) ≤ ⌊value⌋₊ := by exact_mod_cast hle
      left
      linarith
    · intro ht
      by_contra hn
      have hn' : ⌊value⌋₊ + 1 ≤ boundary := by omega
      have hc : (⌊value⌋₊ : Real) + 1 ≤ boundary := by exact_mod_cast hn'
      rcases h with h | ⟨h, heven⟩
      · rcases ht with ht | ⟨ht, _⟩ <;> linarith
      · have heq : boundary = ⌊value⌋₊ + 1 := by
          rcases ht with ht | ⟨ht, _⟩
          · linarith
          · have : (boundary : Real) = (⌊value⌋₊ : Real) + 1 := by linarith
            exact_mod_cast this
        rcases ht with ht | ⟨ht, hbpar⟩
        · linarith
        · omega
  · push Not at h
    constructor
    · intro hle
      by_cases heq : boundary = ⌊value⌋₊ + 1
      · have hc : (boundary : Real) = (⌊value⌋₊ : Real) + 1 := by exact_mod_cast heq
        by_cases ht : value = (⌊value⌋₊ : Real) + 1 / 2
        · right
          constructor
          · linarith
          · have := h.2 ht
            omega
        · left
          have : (⌊value⌋₊ : Real) + 1 / 2 < value :=
            lt_of_le_of_ne h.1 (Ne.symm ht)
          linarith
      · have hc : (boundary : Real) ≤ ⌊value⌋₊ := by exact_mod_cast (by omega : boundary ≤ ⌊value⌋₊)
        left
        linarith
    · intro ht
      by_contra hn
      have hc : (⌊value⌋₊ : Real) + 2 ≤ boundary := by
        exact_mod_cast (by omega : ⌊value⌋₊ + 2 ≤ boundary)
      rcases ht with ht | ⟨ht, _⟩ <;> linarith

/-- Floor-based stochastic selection is a comparison against an exact rational threshold. -/
theorem floor_selection_iff (root : Real) (lower scale random : Nat)
    (hscale : 0 < scale) (hrandom : random < scale) (hroot : (lower : Real) ≤ root) :
    scale ≤ ⌊(root - lower) * scale⌋₊ + random ↔
      ((lower * scale + (scale - random) : Nat) : Real) / scale ≤ root := by
  have hnonneg : 0 ≤ (root - lower) * scale := by positivity
  have hsub : scale - random ≤ ⌊(root - lower) * scale⌋₊ ↔
      scale ≤ ⌊(root - lower) * scale⌋₊ + random := by omega
  rw [← hsub, Nat.le_floor_iff hnonneg]
  have hs : (0 : Real) < scale := by exact_mod_cast hscale
  rw [div_le_iff₀ hs]
  push_cast
  constructor <;> intro h <;> nlinarith

/-- Nearest-even stochastic selection includes its halfway point exactly for an even boundary. -/
theorem nearestEven_selection_iff (root : Real) (lower scale random : Nat)
    (hscale : 0 < scale) (hrandom : random < scale) (hroot : (lower : Real) ≤ root) :
    scale ≤ nearestEven ((root - lower) * scale) + random ↔
      ((lower * (2 * scale) + (2 * (scale - random) - 1) : Nat) : Real) / (2 * scale) < root ∨
        (root = ((lower * (2 * scale) + (2 * (scale - random) - 1) : Nat) : Real) /
          (2 * scale) ∧ (scale - random) % 2 = 0) := by
  have hb : 0 < scale - random := by omega
  have hnonneg : 0 ≤ (root - lower) * scale := by positivity
  have hsub : scale - random ≤ nearestEven ((root - lower) * scale) ↔
      scale ≤ nearestEven ((root - lower) * scale) + random := by omega
  rw [← hsub, le_nearestEven_iff _ _ hb hnonneg]
  have hs : (0 : Real) < scale := by exact_mod_cast hscale
  have ht :
      ((lower * (2 * scale) + (2 * (scale - random) - 1) : Nat) : Real) / (2 * scale) =
        (lower : Real) + ((scale - random : Nat) - 1 / 2) / scale := by
    rw [Nat.cast_add, Nat.cast_sub (by omega : 1 ≤ 2 * (scale - random))]
    push_cast
    field_simp
  rw [ht]
  have hlt : (lower : Real) + ((scale - random : Nat) - 1 / 2) / scale < root ↔
      ((scale - random : Nat) : Real) - 1 / 2 < (root - lower) * scale := by
    rw [add_comm, ← lt_sub_iff_add_lt, div_lt_iff₀ hs]
  have heq : root = (lower : Real) + ((scale - random : Nat) - 1 / 2) / scale ↔
      (root - lower) * scale = ((scale - random : Nat) : Real) - 1 / 2 := by
    rw [add_comm, ← sub_eq_iff_eq_add, eq_div_iff (ne_of_gt hs)]
  rw [hlt, heq]

end FloatLib.Floats.Formats.P3109.RealRounding
