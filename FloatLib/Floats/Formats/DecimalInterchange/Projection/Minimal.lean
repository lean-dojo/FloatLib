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

/-- A rounded pair is either at the least quantum or has a full coefficient of `precision` digits,
so no cohort member of its value has a smaller quantum. -/
theorem roundedPair_minimum_or_full (f : Format) (mode : RoundingMode) (s : Bool)
    (x : ℚ) :
    (roundedPair f mode s x).2 = f.minQuantum ∨
      f.payloadBound ≤ (roundedPair f mode s x).1 := by
  simp only [roundedPair, f.carry_eq]
  split
  · exact Or.inr le_rfl
  · by_cases hq : roundingQuantum f x = f.minQuantum
    · exact Or.inl hq
    · right
      have hl := payloadBound_le_div_roundingQuantum f
        (lt_of_le_of_ne (roundingQuantum_ge_min f x) (Ne.symm hq))
      exact (Nat.le_floor hl).trans (mode.floor_le_roundMagnitude s _)

/-- A rounded pair uses the least quantum among all representations of its value that fit the
precision and the least quantum. -/
theorem roundedPair_quantum_minimal (f : Format) (mode : RoundingMode) (s : Bool)
    (x : ℚ) (d : Nat) (r : Int)
    (hd : d < f.coefficientBound) (hr : f.minQuantum ≤ r)
    (hvalue : ((roundedPair f mode s x).1 : ℚ) * (10 : ℚ) ^ (roundedPair f mode s x).2 =
      (d : ℚ) * (10 : ℚ) ^ r) : (roundedPair f mode s x).2 ≤ r :=
  Arithmetic.quantum_le_of_minimum_or_full f _ d _ r (roundedPair_minimum_or_full f mode s x) hd hr
    hvalue

/-- The greatest finite datum has a full coefficient at the largest quantum, so it uses the least
quantum among all valid representations of its value. Directed overflow delivers it. -/
theorem Format.maxFinite_quantum_minimal (f : Format) (s : Bool) {c : Nat} {q : Int}
    (h : f.maxFinite s = .finite s c q) (d : Nat) (r : Int) (hd : d < f.coefficientBound)
    (hvalue : (c : ℚ) * (10 : ℚ) ^ q = (d : ℚ) * (10 : ℚ) ^ r) : q ≤ r := by
  simp only [Format.maxFinite, Datum.finite.injEq] at h
  obtain ⟨-, rfl, rfl⟩ := h
  exact quantum_le_of_full_coefficient f _ d _ r f.payloadBound_le_coefficientBound_sub_one hd
    hvalue

/-- Every finite inexact result uses the least quantum in its valid cohort. -/
theorem projectMagnitude_inexact_quantum_minimal (f : Format) (mode : RoundingMode)
    (s : Bool) (x : ℚ) (preferred : Int)
    (hinexact : (projectMagnitude f mode s x preferred).status.inexact = true)
    (c : Nat) (q : Int) (hout : (projectMagnitude f mode s x preferred).value = .finite s c q)
    (d : Nat) (r : Int) (hv : (Datum.finite s d r).Valid f)
    (hvalue : (c : ℚ) * (10 : ℚ) ^ q = (d : ℚ) * (10 : ℚ) ^ r) : q ≤ r := by
  have hd := (Datum.valid_quantum_iff ..).mp hv
  simp only [projectMagnitude_eq] at hinexact hout
  split at hout
  · split at hout
    · contradiction
    · exact f.maxFinite_quantum_minimal s hout d r hd.1 hvalue
  · rename_i hq
    simp only [ite_eq_right hq] at hinexact
    simp only [hinexact, ite_true] at hout
    obtain ⟨_, rfl, rfl⟩ := Datum.finite.inj hout
    exact roundedPair_quantum_minimal f mode s x d r hd.1 hd.2.1 hvalue

end FloatLib.Floats.Formats.DecimalInterchange
