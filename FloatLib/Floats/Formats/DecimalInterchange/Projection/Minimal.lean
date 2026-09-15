/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Cohort

/-!
# Least-quantum cohorts of inexact projections

IEEE 754-2019 §5.2 selects the smallest available quantum for inexact results.
The coefficient is either on the subnormal grid or has a full leading digit;
therefore no equal valid value can have a smaller quantum. This includes finite
results delivered on directed overflow.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

theorem roundedPair_minimum_or_full (f : Format) (mode : RoundingMode) (s : Bool)
    {x : ℚ} (hx : 0 ≤ x) :
    (roundedPair f mode s x).2 = f.minQuantum ∨
      f.payloadBound ≤ (roundedPair f mode s x).1 := by
  simp only [roundedPair, f.carry_eq]
  split
  · exact Or.inr le_rfl
  · by_cases hq : roundingQuantum f x = f.minQuantum
    · exact Or.inl hq
    · right
      have hl := payloadBound_le_div_roundingQuantum f hx
        (lt_of_le_of_ne (roundingQuantum_ge_min f x) (Ne.symm hq))
      exact (Nat.le_floor hl).trans (mode.floor_le_roundMagnitude s _)

theorem roundedPair_quantum_minimal (f : Format) (mode : RoundingMode) (s : Bool)
    {x : ℚ} (hx : 0 ≤ x) (d : Nat) (r : Int)
    (hd : d < f.coefficientBound) (hr : f.minQuantum ≤ r)
    (hvalue : ((roundedPair f mode s x).1 : ℚ) * (10 : ℚ) ^ (roundedPair f mode s x).2 =
      (d : ℚ) * (10 : ℚ) ^ r) : (roundedPair f mode s x).2 ≤ r := by
  rcases roundedPair_minimum_or_full f mode s hx with h | h
  · rwa [h]
  · exact quantum_le_of_full_coefficient f _ d _ r h hd hvalue

/-- Every finite inexact result uses the least quantum in its valid cohort. -/
theorem projectMagnitude_inexact_quantum_minimal (f : Format) (mode : RoundingMode)
    (s : Bool) {x : ℚ} (hx : 0 ≤ x) (preferred : Int)
    (hinexact : (projectMagnitude f mode s x preferred).status.inexact = true)
    (c : Nat) (q : Int) (hout : (projectMagnitude f mode s x preferred).value = .finite s c q)
    (d : Nat) (r : Int) (hv : (Datum.finite s d r).Valid f)
    (hvalue : (c : ℚ) * (10 : ℚ) ^ q = (d : ℚ) * (10 : ℚ) ^ r) : q ≤ r := by
  have hd := (Datum.valid_quantum_iff ..).mp hv
  simp only [projectMagnitude_eq] at hinexact hout
  split at hout
  · split at hout
    · contradiction
    · simp only [Format.maxFinite, Datum.finite.injEq] at hout
      obtain ⟨_, rfl, rfl⟩ := hout
      apply quantum_le_of_full_coefficient f _ d _ r _ hd.1 hvalue
      exact f.payloadBound_le_coefficientBound_sub_one
  · rename_i hq
    simp only [ite_eq_right hq] at hinexact
    simp only [hinexact, ite_true] at hout
    obtain ⟨_, rfl, rfl⟩ := Datum.finite.inj hout
    exact roundedPair_quantum_minimal f mode s hx d r hd.1 hd.2.1 hvalue

end FloatLib.Floats.Formats.DecimalInterchange
