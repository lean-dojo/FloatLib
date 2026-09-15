/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Sqrt.Exact
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Cohort

/-!
# Preferred cohorts of exact square roots

An exact representable square root is returned at the valid exponent closest
to the preferred exponent. The public operation uses the floor of half the
operand exponent, as required by IEEE 754-2019 §5.4.1.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

/-- Exact square-root projection minimizes the distance to the preferred exponent. -/
theorem sqrtMagnitude_quantum_closest (f : Format) (mode : RoundingMode)
    (c : Nat) (q preferred : Int) (hvalid : (Datum.finite false c q).Valid f)
    (d : Nat) (r : Int)
    (hout : (sqrtMagnitude f mode (((c : ℚ) * (10 : ℚ) ^ q) ^ 2) preferred).value =
      .finite false d r)
    (e : Nat) (t : Int) (he : (Datum.finite false e t).Valid f)
    (hvalue : (c : ℚ) * (10 : ℚ) ^ q = (e : ℚ) * (10 : ℚ) ^ t) :
    |preferred - r| ≤ |preferred - t| := by
  let x := (c : ℚ) * (10 : ℚ) ^ q
  let pair := sqrtPair f mode (x ^ 2)
  have hq : pair.2 ≤ f.maxQuantum :=
    (sqrtPair_quantum_le_of_valid f mode false c q hvalid).trans
      ((Datum.valid_quantum_iff ..).mp hvalid).2.2
  have hv : (pair.1 : ℚ) * (10 : ℚ) ^ pair.2 = x :=
    sqrtPair_exact_value f mode false c q hvalid
  have hminimal : ∀ (a : Nat) (b : Int), a < f.coefficientBound →
      f.minQuantum ≤ b → b ≤ f.maxQuantum →
      (pair.1 : ℚ) * (10 : ℚ) ^ pair.2 = (a : ℚ) * (10 : ℚ) ^ b → pair.2 ≤ b := by
    intro a b ha hbmin hbmax hab
    have heq : x = (a : ℚ) * (10 : ℚ) ^ b := hv.symm.trans hab
    change (sqrtPair f mode (x ^ 2)).2 ≤ b
    rw [heq]
    exact sqrtPair_quantum_le_of_valid f mode false a b
      ((Datum.valid_quantum_iff ..).mpr ⟨ha, hbmin, hbmax⟩)
  have he' := (Datum.valid_quantum_iff ..).mp he
  have hclosest := preferredCohort_quantum_closest f pair.1 pair.2 preferred hq hminimal
    e t he'.1 he'.2.1 he'.2.2 (hv.trans hvalue)
  change (sqrtMagnitude f mode (x ^ 2) preferred).value = .finite false d r at hout
  simp only [sqrtMagnitude, show ¬f.maxQuantum < pair.2 from not_lt.mpr hq,
    pair, hv, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at hout
  change preferredCohort f false pair.1 pair.2 preferred = .finite false d r at hout
  have hr := (Datum.finite.inj hout).2.2
  rw [← hr]
  exact hclosest

/-- The public square root uses the closest valid exponent to the floor of half the input quantum.
The exact-root hypothesis ranges over every representable nonnegative root, including zero. -/
theorem Arithmetic.sqrt_quantum_closest (f : Format) (mode : RoundingMode)
    (a : Nat) (b : Int) (c : Nat) (q : Int)
    (hvalid : (Datum.finite false c q).Valid f)
    (hroot : (a : ℚ) * (10 : ℚ) ^ b = ((c : ℚ) * (10 : ℚ) ^ q) ^ 2)
    (d : Nat) (r : Int)
    (hout : (sqrt f mode (.finite false a b)).value = .finite false d r)
    (e : Nat) (t : Int) (he : (Datum.finite false e t).Valid f)
    (hvalue : (c : ℚ) * (10 : ℚ) ^ q = (e : ℚ) * (10 : ℚ) ^ t) :
    |b / 2 - r| ≤ |b / 2 - t| := by
  by_cases ha : a = 0
  · have hz : (c : ℚ) * (10 : ℚ) ^ q = 0 := by
      simp only [ha, Nat.cast_zero, zero_mul] at hroot
      nlinarith [sq_nonneg ((c : ℚ) * (10 : ℚ) ^ q)]
    have hout' : (projectMagnitude f mode false ((c : ℚ) * (10 : ℚ) ^ q)
        (b / 2)).value = .finite false d r := by
      simpa [sqrt, ha, hz] using hout
    exact projectMagnitude_quantum_closest f mode false c q (b / 2) hvalid
      d r hout' e t he hvalue
  · have hout' : (sqrtMagnitude f mode (((c : ℚ) * (10 : ℚ) ^ q) ^ 2)
        (b / 2)).value = .finite false d r := by
      simpa [sqrt, ha, hroot] using hout
    exact sqrtMagnitude_quantum_closest f mode c q (b / 2) hvalid d r hout' e t he hvalue

end FloatLib.Floats.Formats.DecimalInterchange
