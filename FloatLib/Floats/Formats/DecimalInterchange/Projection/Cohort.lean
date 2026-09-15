/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Cohort.Optimal
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Exact

/-!
# Preferred cohorts of exact decimal results

For every representable exact magnitude, projection selects the valid cohort
member whose quantum exponent is closest to the requested preferred exponent.
The conclusion compares the returned datum with every valid representation of
that magnitude, including representations with a different coefficient.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

/-- Every representation of an exact magnitude is at or above its initial projection grid. -/
theorem roundedPair_quantum_minimal_of_exact (f : Format) (mode : RoundingMode)
    (s : Bool) (x : ℚ) (d : Nat) (r : Int)
    (hd : d < f.coefficientBound) (hrmin : f.minQuantum ≤ r) (hrmax : r ≤ f.maxQuantum)
    (hvalue : x = (d : ℚ) * (10 : ℚ) ^ r) :
    (roundedPair f mode s x).2 ≤ r := by
  rw [hvalue]
  exact roundedPair_quantum_le_of_valid f mode s d r
    ((Datum.valid_quantum_iff ..).mpr ⟨hd, hrmin, hrmax⟩)

/-- Exact projection chooses the exponent closest to the preferred exponent over the whole cohort. -/
theorem projectMagnitude_quantum_closest (f : Format) (mode : RoundingMode) (s : Bool)
    (c : Nat) (q preferred : Int) (hvalid : (Datum.finite s c q).Valid f)
    (d : Nat) (r : Int)
    (hout : (projectMagnitude f mode s ((c : ℚ) * (10 : ℚ) ^ q) preferred).value =
      .finite s d r)
    (e : Nat) (t : Int) (he : (Datum.finite s e t).Valid f)
    (hvalue : (c : ℚ) * (10 : ℚ) ^ q = (e : ℚ) * (10 : ℚ) ^ t) :
    |preferred - r| ≤ |preferred - t| := by
  let x := (c : ℚ) * (10 : ℚ) ^ q
  let pair := roundedPair f mode s x
  have hq : pair.2 ≤ f.maxQuantum :=
    (roundedPair_quantum_le_of_valid f mode s c q hvalid).trans
      ((Datum.valid_quantum_iff ..).mp hvalid).2.2
  have hv : (pair.1 : ℚ) * (10 : ℚ) ^ pair.2 = x :=
    roundedPair_exact_value f mode s c q hvalid
  have hminimal : ∀ (a : Nat) (b : Int), a < f.coefficientBound →
      f.minQuantum ≤ b → b ≤ f.maxQuantum →
      (pair.1 : ℚ) * (10 : ℚ) ^ pair.2 = (a : ℚ) * (10 : ℚ) ^ b → pair.2 ≤ b := by
    intro a b ha hbmin hbmax hab
    exact roundedPair_quantum_minimal_of_exact f mode s x a b ha hbmin hbmax
      (hv.symm.trans hab)
  have he' := (Datum.valid_quantum_iff ..).mp he
  have hclosest := preferredCohort_quantum_closest f pair.1 pair.2 preferred hq hminimal
    e t he'.1 he'.2.1 he'.2.2 (hv.trans hvalue)
  change (projectMagnitude f mode s x preferred).value = .finite s d r at hout
  simp only [projectMagnitude_eq, show ¬f.maxQuantum < pair.2 from not_lt.mpr hq,
    pair, hv, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at hout
  change preferredCohort f s pair.1 pair.2 preferred = .finite s d r at hout
  have hr := (Datum.finite.inj hout).2.2
  rw [← hr]
  exact hclosest

end FloatLib.Floats.Formats.DecimalInterchange
