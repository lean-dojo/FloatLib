/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Sqrt.Cohort
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Minimal
public import FloatLib.Floats.Formats.DecimalInterchange.Sqrt.Semantics

/-!
# Least-quantum cohorts of inexact square roots

An inexact root gets the least quantum in its cohort. The theorem compares the actual rounded root
with every valid representation of that rounded value, and it doesn't assume the mathematical
root is rational.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

/-- A rounded square root is either at the least quantum or has a full coefficient of `precision`
digits, so no cohort member of its value has a smaller quantum. -/
theorem sqrtPair_minimum_or_full (f : Format) (mode : RoundingMode) (x : ℚ) :
    (sqrtPair f mode x).2 = f.minQuantum ∨ f.payloadBound ≤ (sqrtPair f mode x).1 := by
  simp only [sqrtPair, f.carry_eq]
  split
  · exact Or.inr le_rfl
  · by_cases hq : sqrtQuantum f x = f.minQuantum
    · exact Or.inl hq
    · right
      have hl := payloadBound_sq_le_div_sqrtQuantum f
        (lt_of_le_of_ne (sqrtQuantum_ge_min f x) (Ne.symm hq))
      have hfloor : f.payloadBound ^ 2 ≤ ⌊x / (10 : ℚ) ^ (2 * sqrtQuantum f x)⌋₊ :=
        Nat.le_floor (by exact_mod_cast hl)
      have hs : f.payloadBound ≤ sqrtFloor (x / (10 : ℚ) ^ (2 * sqrtQuantum f x)) :=
        Nat.le_sqrt'.mpr hfloor
      rcases mode.sqrtRound_eq_floor_or_succ (x / (10 : ℚ) ^ (2 * sqrtQuantum f x))
        with h | h <;> omega

/-- The rounded square root uses the least quantum among all representations of its value that fit
the precision and the least quantum. -/
theorem sqrtPair_quantum_minimal (f : Format) (mode : RoundingMode)
    (x : ℚ) (d : Nat) (r : Int)
    (hd : d < f.coefficientBound) (hr : f.minQuantum ≤ r)
    (hvalue : ((sqrtPair f mode x).1 : ℚ) * (10 : ℚ) ^ (sqrtPair f mode x).2 =
      (d : ℚ) * (10 : ℚ) ^ r) : (sqrtPair f mode x).2 ≤ r :=
  Arithmetic.quantum_le_of_minimum_or_full f _ d _ r (sqrtPair_minimum_or_full f mode x) hd hr
    hvalue

/-- An inexact finite root has the least quantum in its valid cohort, even when the exact root is irrational. -/
theorem sqrtMagnitude_inexact_quantum_minimal (f : Format) (mode : RoundingMode)
    (x : ℚ) (preferred : Int)
    (hinexact : (sqrtMagnitude f mode x preferred).status.inexact = true)
    (c : Nat) (q : Int) (hout : (sqrtMagnitude f mode x preferred).value = .finite false c q)
    (d : Nat) (r : Int) (hv : (Datum.finite false d r).Valid f)
    (hvalue : (c : ℚ) * (10 : ℚ) ^ q = (d : ℚ) * (10 : ℚ) ^ r) : q ≤ r := by
  have hd := (Datum.valid_quantum_iff ..).mp hv
  dsimp only [sqrtMagnitude] at hinexact hout
  split at hout
  · split at hout
    · contradiction
    · exact f.maxFinite_quantum_minimal false hout d r hd.1 hvalue
  · rename_i hq
    simp only [ite_eq_right hq] at hinexact
    simp only [hinexact, ite_true] at hout
    obtain ⟨_, rfl, rfl⟩ := Datum.finite.inj hout
    exact sqrtPair_quantum_minimal f mode x d r hd.1 hd.2.1 hvalue

/-- Every inexact finite result of the public square root uses the least quantum in its cohort. -/
theorem Arithmetic.sqrt_inexact_quantum_minimal (f : Format) (mode : RoundingMode)
    (s : Bool) (a : Nat) (b : Int)
    (hinexact : (sqrt f mode (.finite s a b)).status.inexact = true)
    (c : Nat) (q : Int) (hout : (sqrt f mode (.finite s a b)).value = .finite false c q)
    (d : Nat) (r : Int) (hv : (Datum.finite false d r).Valid f)
    (hvalue : (c : ℚ) * (10 : ℚ) ^ q = (d : ℚ) * (10 : ℚ) ^ r) : q ≤ r := by
  by_cases ha : a = 0
  · simp [ha, sqrt_zero] at hinexact
  · cases s
    · simp only [sqrt, ite_eq_right ha, Bool.false_eq_true, ite_false] at hinexact hout
      exact sqrtMagnitude_inexact_quantum_minimal f mode _ (b / 2) hinexact c q hout d r hv
        hvalue
    · simp [sqrt, ha, invalidResult] at hinexact

end FloatLib.Floats.Formats.DecimalInterchange
