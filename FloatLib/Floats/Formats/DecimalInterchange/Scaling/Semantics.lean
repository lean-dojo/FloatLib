/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Scaling.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Direction
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Minimal

/-!
# Scaling accuracy and cohort independence of exponent queries

The accuracy bounds use the delivered rational value and the public overflow
flag. Exact cohort selection also applies when the original shifted quantum is
outside the format range but another member of its cohort is representable.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange
namespace Arithmetic

theorem scaleB_quantum_le_of_no_overflow (f : Format) (mode : RoundingMode)
    (s : Bool) (c : Nat) (q n : Int)
    (hfinite : (scaleB f mode (.finite s c q) n).status.overflow = false) :
    (roundedPair f mode s ((c : ℚ) * (10 : ℚ) ^ (q + n))).2 ≤ f.maxQuantum := by
  by_contra h
  have he := (projectMagnitude_overflow_iff f mode s
    ((c : ℚ) * (10 : ℚ) ^ (q + n)) (q + n)).mpr (by omega)
  change (scaleB f mode (.finite s c q) n).status.overflow = true at he
  simp [hfinite] at he

/-- Both nearest directions deliver at most half a unit of error on the selected grid. -/
theorem scaleB_error_le_half (f : Format) (mode : RoundingMode)
    (hm : mode = .nearestEven ∨ mode = .nearestAway)
    (s : Bool) (c : Nat) (q n : Int)
    (hfinite : (scaleB f mode (.finite s c q) n).status.overflow = false) :
    ∃ v, (scaleB f mode (.finite s c q) n).value.toRat? = some v ∧
      |v - Datum.finiteValue s c q * (10 : ℚ) ^ n| ≤
        (10 : ℚ) ^ roundingQuantum f ((c : ℚ) * (10 : ℚ) ^ (q + n)) / 2 := by
  have hx : 0 ≤ (c : ℚ) * (10 : ℚ) ^ (q + n) :=
    mul_nonneg (Nat.cast_nonneg _) (zpow_pos (by norm_num) _).le
  have h := projectMagnitude_error_le_half f mode hm s hx (q + n)
    (scaleB_quantum_le_of_no_overflow f mode s c q n hfinite)
  cases s <;> simpa [scaleB, Datum.finiteValue, scaleB_exact_magnitude, mul_assoc] using h

/-- Every rounding direction delivers an error smaller than one selected grid unit. -/
theorem scaleB_error_lt_one (f : Format) (mode : RoundingMode)
    (s : Bool) (c : Nat) (q n : Int)
    (hfinite : (scaleB f mode (.finite s c q) n).status.overflow = false) :
    ∃ v, (scaleB f mode (.finite s c q) n).value.toRat? = some v ∧
      |v - Datum.finiteValue s c q * (10 : ℚ) ^ n| <
        (10 : ℚ) ^ roundingQuantum f ((c : ℚ) * (10 : ℚ) ^ (q + n)) := by
  have hx : 0 ≤ (c : ℚ) * (10 : ℚ) ^ (q + n) :=
    mul_nonneg (Nat.cast_nonneg _) (zpow_pos (by norm_num) _).le
  have h := projectMagnitude_error_lt_one f mode s hx (q + n)
    (scaleB_quantum_le_of_no_overflow f mode s c q n hfinite)
  cases s <;> simpa [scaleB, Datum.finiteValue, scaleB_exact_magnitude, mul_assoc] using h

theorem scaleB_towardPositive_le (f : Format) (s : Bool) (c : Nat) (q n : Int)
    (hfinite : (scaleB f .towardPositive (.finite s c q) n).status.overflow = false) :
    ∃ v, (scaleB f .towardPositive (.finite s c q) n).value.toRat? = some v ∧
      Datum.finiteValue s c q * (10 : ℚ) ^ n ≤ v := by
  have hx : 0 ≤ (c : ℚ) * (10 : ℚ) ^ (q + n) :=
    mul_nonneg (Nat.cast_nonneg _) (zpow_pos (by norm_num) _).le
  have h := projectMagnitude_towardPositive_le f s hx (q + n)
    (scaleB_quantum_le_of_no_overflow f .towardPositive s c q n hfinite)
  cases s <;> simpa [scaleB, Datum.finiteValue, scaleB_exact_magnitude, mul_assoc] using h

theorem scaleB_towardNegative_le (f : Format) (s : Bool) (c : Nat) (q n : Int)
    (hfinite : (scaleB f .towardNegative (.finite s c q) n).status.overflow = false) :
    ∃ v, (scaleB f .towardNegative (.finite s c q) n).value.toRat? = some v ∧
      v ≤ Datum.finiteValue s c q * (10 : ℚ) ^ n := by
  have hx : 0 ≤ (c : ℚ) * (10 : ℚ) ^ (q + n) :=
    mul_nonneg (Nat.cast_nonneg _) (zpow_pos (by norm_num) _).le
  have h := projectMagnitude_towardNegative_le f s hx (q + n)
    (scaleB_quantum_le_of_no_overflow f .towardNegative s c q n hfinite)
  cases s <;> simpa [scaleB, Datum.finiteValue, scaleB_exact_magnitude, mul_assoc] using h

/-- Exactness does not require the source's shifted representation itself to be in range. -/
theorem scaleB_exact_status_of_representable (f : Format) (mode : RoundingMode)
    (s : Bool) (c e : Nat) (q n t : Int) (he : (Datum.finite s e t).Valid f)
    (hv : (c : ℚ) * (10 : ℚ) ^ (q + n) = (e : ℚ) * (10 : ℚ) ^ t) :
    (scaleB f mode (.finite s c q) n).status = {} := by
  simpa only [scaleB, hv] using projectMagnitude_exact_status f mode s e t (q + n) he

/-- Representable exact results choose the cohort member nearest the preferred shifted quantum. -/
theorem scaleB_quantum_closest_of_representable (f : Format) (mode : RoundingMode)
    (s : Bool) (c e : Nat) (q n t : Int) (he : (Datum.finite s e t).Valid f)
    (hv : (c : ℚ) * (10 : ℚ) ^ (q + n) = (e : ℚ) * (10 : ℚ) ^ t)
    (d : Nat) (r : Int) (hout : (scaleB f mode (.finite s c q) n).value = .finite s d r)
    (a : Nat) (b : Int) (ha : (Datum.finite s a b).Valid f)
    (hab : (c : ℚ) * (10 : ℚ) ^ (q + n) = (a : ℚ) * (10 : ℚ) ^ b) :
    |q + n - r| ≤ |q + n - b| := by
  simp only [scaleB, hv] at hout
  exact projectMagnitude_quantum_closest f mode s e t (q + n) he d r hout
    a b ha (hv.symm.trans hab)

/-- Inexact finite results, including directed overflow deliveries, use the least quantum. -/
theorem scaleB_inexact_quantum_minimal (f : Format) (mode : RoundingMode)
    (s : Bool) (c : Nat) (q n : Int)
    (hinexact : (scaleB f mode (.finite s c q) n).status.inexact = true)
    (d : Nat) (r : Int) (hout : (scaleB f mode (.finite s c q) n).value = .finite s d r)
    (a : Nat) (b : Int) (ha : (Datum.finite s a b).Valid f)
    (he : (d : ℚ) * (10 : ℚ) ^ r = (a : ℚ) * (10 : ℚ) ^ b) : r ≤ b :=
  projectMagnitude_inexact_quantum_minimal f mode s
    (mul_nonneg (Nat.cast_nonneg _) (zpow_pos (by norm_num) _).le)
    (q + n) hinexact d r hout a b ha he

/-- Equal nonzero magnitudes have the same radix exponent, irrespective of cohort or sign. -/
theorem logB_eq_of_equal_magnitude (f g : Format) (s t : Bool) (c d : Nat) (q r : Int)
    (hc : c ≠ 0) (hd : d ≠ 0)
    (he : (c : ℚ) * (10 : ℚ) ^ q = (d : ℚ) * (10 : ℚ) ^ r) :
    (logB f (.finite s c q)).value = (logB g (.finite t d r)).value := by
  have hx := logB_bounds f s c q hc
  have hy := logB_bounds g t d r hd
  apply le_antisymm
  · by_contra h
    have hp : (10 : ℚ) ^ ((logB g (.finite t d r)).value + 1) ≤
        (10 : ℚ) ^ (logB f (.finite s c q)).value :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    rw [he] at hx
    linarith
  · by_contra h
    have hp : (10 : ℚ) ^ ((logB f (.finite s c q)).value + 1) ≤
        (10 : ℚ) ^ (logB g (.finite t d r)).value :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    rw [he] at hx
    linarith

@[simp] theorem logB_zero (f : Format) (s : Bool) (q : Int) :
    logB f (.finite s 0 q) = { value := -logBSentinel f, status := { invalid := true } } :=
  rfl

@[simp] theorem logB_infinity (f : Format) (s : Bool) :
    logB f (.infinity s) = { value := logBSentinel f, status := { invalid := true } } := rfl

@[simp] theorem logB_nan (f : Format) (s t : Bool) (p : Nat) :
    logB f (.nan s t p) = { value := logBSentinel f, status := { invalid := true } } := rfl

end Arithmetic
end FloatLib.Floats.Formats.DecimalInterchange
