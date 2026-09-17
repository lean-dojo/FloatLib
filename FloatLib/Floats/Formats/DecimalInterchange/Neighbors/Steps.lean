/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Neighbors.Grid

/-!
# Successor and predecessor on a normalized decimal grid

The downward step immediately below a radix power is expressed on the finer
grid. Its upward grid step recovers the original value, so the same grid-gap
theorem establishes adjacency in both directions.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange
namespace Arithmetic

theorem neighborAbove_valid (f : Format) (c : Nat) (q : Int)
    (hqmin : f.minQuantum ≤ q) (hqmax : q ≤ f.maxQuantum) :
    (neighborAbove f c q).Valid f := by
  unfold neighborAbove
  split
  · exact (Datum.valid_quantum_iff ..).mpr ⟨‹_›, hqmin, hqmax⟩
  · split
    · apply (Datum.valid_quantum_iff ..).mpr
      have hb := f.payloadBound_lt_coefficientBound
      exact ⟨hb, by omega, by omega⟩
    · trivial

theorem neighborAbove_finite (f : Format) (c d : Nat) (q r : Int) (s : Bool)
    (hc : c < f.coefficientBound)
    (hout : neighborAbove f c q = .finite s d r) :
    s = false ∧ (d : ℚ) * (10 : ℚ) ^ r =
      ((c + 1 : Nat) : ℚ) * (10 : ℚ) ^ q := by
  unfold neighborAbove at hout
  split at hout
  · cases hout
    exact ⟨rfl, rfl⟩
  · split at hout
    · cases hout
      have he : c + 1 = f.coefficientBound := by omega
      constructor
      · rfl
      · rw [he, zpow_add₀ (by norm_num), zpow_one, Format.coefficientBound]
        push_cast
        ring
    · contradiction

theorem neighborAbove_full (f : Format) (c d : Nat) (q r : Int) (s : Bool)
    (hfull : q = f.minQuantum ∨ f.payloadBound ≤ c)
    (hout : neighborAbove f c q = .finite s d r) :
    r = f.minQuantum ∨ f.payloadBound ≤ d := by
  unfold neighborAbove at hout
  split at hout
  · cases hout
    omega
  · split at hout
    · cases hout
      exact Or.inr le_rfl
    · contradiction

/-- The predecessor of a normalized positive input is valid, normalized, and one
upward grid step below the input. It may be zero. -/
theorem neighborBelow_spec (f : Format) (c : Nat) (q : Int)
    (hc : c < f.coefficientBound) (hcpos : 0 < c)
    (hqmin : f.minQuantum ≤ q) (hqmax : q ≤ f.maxQuantum)
    (hfull : q = f.minQuantum ∨ f.payloadBound ≤ c) :
    ∃ d r, neighborBelow f c q = .finite false d r ∧
      (Datum.finite false d r).Valid f ∧
      (r = f.minQuantum ∨ f.payloadBound ≤ d) ∧
      ((d + 1 : Nat) : ℚ) * (10 : ℚ) ^ r = (c : ℚ) * (10 : ℚ) ^ q := by
  have hb := f.coefficientBound_pos
  unfold neighborBelow
  split
  · rename_i h
    refine ⟨_, _, rfl, (Datum.valid_quantum_iff ..).mpr
      ⟨by omega, by omega, by omega⟩, ?_, ?_⟩
    · right
      exact f.payloadBound_le_coefficientBound_sub_one
    · have he : f.coefficientBound - 1 + 1 = f.coefficientBound := by omega
      have hq : q = (q - 1) + 1 := by omega
      rw [he, h.2]
      conv_rhs => rw [hq, zpow_add₀ (by norm_num), zpow_one]
      rw [Format.coefficientBound]
      push_cast
      ring
  · rename_i h
    refine ⟨_, _, rfl, (Datum.valid_quantum_iff ..).mpr
      ⟨by omega, hqmin, hqmax⟩, ?_, ?_⟩
    · omega
    · rw [Nat.sub_add_cancel hcpos]

/-- Upper bound on every finite magnitude, including all nonminimal cohorts. -/
theorem neighbor_le_max (f : Format) (d : Nat) (r : Int)
    (hd : d < f.coefficientBound) (hr : r ≤ f.maxQuantum) :
    (d : ℚ) * (10 : ℚ) ^ r ≤
      ((f.coefficientBound - 1 : Nat) : ℚ) * (10 : ℚ) ^ f.maxQuantum := by
  have hc : (d : ℚ) ≤ ((f.coefficientBound - 1 : Nat) : ℚ) := by
    exact_mod_cast (show d ≤ f.coefficientBound - 1 by omega)
  exact mul_le_mul hc (zpow_le_zpow_right₀ (by norm_num) hr)
    (zpow_pos (by norm_num) _).le (Nat.cast_nonneg _)

/-- An infinite successor requires the greatest finite magnitude. -/
theorem neighborAbove_infinity (f : Format) (c : Nat) (q : Int)
    (hc : c < f.coefficientBound) (hq : q ≤ f.maxQuantum)
    (hout : neighborAbove f c q = .infinity false) :
    c = f.coefficientBound - 1 ∧ q = f.maxQuantum := by
  unfold neighborAbove at hout
  split at hout
  · contradiction
  · split at hout
    · contradiction
    · omega

end Arithmetic
end FloatLib.Floats.Formats.DecimalInterchange
