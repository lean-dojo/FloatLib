/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Proof

/-!
# Exactness on every representable decimal

These theorems cover every valid coefficient and quantum in any `Format`,
in all five rounding directions. A change of representation within a cohort is not inexact:
only a change in numerical value can raise that exception.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

theorem roundingQuantum_le_of_valid (f : Format) (s : Bool) (c : Nat) (q : Int)
    (h : (Datum.finite s c q).Valid f) :
    roundingQuantum f ((c : ℚ) * (10 : ℚ) ^ q) ≤ q := by
  rw [Datum.valid_quantum_iff] at h
  have hu : 0 < (10 : ℚ) ^ q := zpow_pos (by norm_num) _
  apply roundingQuantum_le f (mul_nonneg (Nat.cast_nonneg c) hu.le) h.2.1
  exact mul_lt_mul_of_pos_right (by exact_mod_cast h.1) hu

/-- A valid decimal's exact value is fixed, even when another member of its cohort is selected. -/
theorem roundedPair_exact_value (f : Format) (mode : RoundingMode) (s : Bool)
    (c : Nat) (q : Int) (h : (Datum.finite s c q).Valid f) :
    ((roundedPair f mode s ((c : ℚ) * (10 : ℚ) ^ q)).1 : ℚ) *
        (10 : ℚ) ^ (roundedPair f mode s ((c : ℚ) * (10 : ℚ) ^ q)).2 =
      (c : ℚ) * (10 : ℚ) ^ q := by
  rw [roundedPair_value]
  exact mode.roundAt_exact_value s c (roundingQuantum_le_of_valid f s c q h)

/-- An exact representable input cannot cause an exponent carry beyond its original exponent. -/
theorem roundedPair_quantum_le_of_valid (f : Format) (mode : RoundingMode) (s : Bool)
    (c : Nat) (q : Int) (h : (Datum.finite s c q).Valid f) :
    (roundedPair f mode s ((c : ℚ) * (10 : ℚ) ^ q)).2 ≤ q := by
  let x := (c : ℚ) * (10 : ℚ) ^ q
  have hx : 0 ≤ x := mul_nonneg (Nat.cast_nonneg c) (zpow_pos (by norm_num) _).le
  have hq := roundingQuantum_le_of_valid f s c q h
  have he := mode.roundAt_exact_value s c hq
  have hu : 0 < (10 : ℚ) ^ roundingQuantum f x := zpow_pos (by norm_num) _
  have hf := (div_lt_iff₀ hu).mp (div_roundingQuantum_lt f hx)
  have hc : mode.roundAt s x (roundingQuantum f x) < f.coefficientBound := by
    have hv : (mode.roundAt s x (roundingQuantum f x) : ℚ) *
        (10 : ℚ) ^ roundingQuantum f x = x := he
    have hcmp := hv.trans_lt hf
    exact_mod_cast (mul_lt_mul_iff_left₀ hu).mp hcmp
  have hn : mode.roundAt s x (roundingQuantum f x) ≠ f.coefficientBound := Nat.ne_of_lt hc
  change (roundedPair f mode s x).2 ≤ q
  simp only [roundedPair, f.carry_eq, if_neg hn]
  exact hq

/-- Exact finite projection raises none of the five default exception flags. -/
theorem projectMagnitude_status_of_exact (f : Format) (mode : RoundingMode) (s : Bool)
    (x : ℚ) (preferred : Int)
    (hq : (roundedPair f mode s x).2 ≤ f.maxQuantum)
    (hx : ((roundedPair f mode s x).1 : ℚ) * (10 : ℚ) ^ (roundedPair f mode s x).2 = x) :
    (projectMagnitude f mode s x preferred).status = {} := by
  simp [projectMagnitude_eq, not_lt.mpr hq, hx]

/-- Every valid finite decimal projects with its exact numerical value. -/
theorem projectMagnitude_exact (f : Format) (mode : RoundingMode) (s : Bool)
    (c : Nat) (q preferred : Int) (h : (Datum.finite s c q).Valid f) :
    (projectMagnitude f mode s ((c : ℚ) * (10 : ℚ) ^ q) preferred).value.toRat? =
      (Datum.finite s c q).toRat? := by
  have hq := (roundedPair_quantum_le_of_valid f mode s c q h).trans
    ((Datum.valid_quantum_iff ..).mp h).2.2
  rw [projectMagnitude_value f mode s _ preferred hq]
  have hv := mode.roundAt_exact_value s c (roundingQuantum_le_of_valid f s c q h)
  simp only [Datum.toRat?_eq, mul_assoc, hv]

/-- Cohort selection, including zero, never raises inexact on a representable input. -/
theorem projectMagnitude_exact_status (f : Format) (mode : RoundingMode) (s : Bool)
    (c : Nat) (q preferred : Int) (h : (Datum.finite s c q).Valid f) :
    (projectMagnitude f mode s ((c : ℚ) * (10 : ℚ) ^ q) preferred).status = {} := by
  apply projectMagnitude_status_of_exact
  · exact (roundedPair_quantum_le_of_valid f mode s c q h).trans
      ((Datum.valid_quantum_iff ..).mp h).2.2
  · exact roundedPair_exact_value f mode s c q h

end FloatLib.Floats.Formats.DecimalInterchange
