/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Scaling.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Arithmetic.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Cohort
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Zero
import Mathlib.Tactic.Ring

/-!
# Exponent-operation semantics

The bounds on `logB` characterize its answer by consecutive radix powers.
Scaling inherits the actual projection's value, range, rounding and cohort
guarantees, including signed zero and decimal tininess before rounding.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange
namespace Arithmetic

theorem scaleB_valid (f : Format) (mode : RoundingMode) (x : Datum) (n : Int) :
    (scaleB f mode x n).value.Valid f := by
  cases x with
  | finite s c q =>
      exact projectMagnitude_valid f mode s
        (mul_nonneg (Nat.cast_nonneg c) (zpow_pos (by norm_num) (q + n)).le) _
  | infinity s => trivial
  | nan s t p => exact nanResult_valid ..

/-- The intermediate magnitude is exactly the input magnitude times the radix power. -/
theorem scaleB_exact_magnitude (c : Nat) (q n : Int) :
    (c : ℚ) * (10 : ℚ) ^ (q + n) =
      ((c : ℚ) * (10 : ℚ) ^ q) * (10 : ℚ) ^ n := by
  rw [zpow_add₀ (by norm_num)]
  ring

/-- An in-range exact shifted representation incurs no exceptions. -/
theorem scaleB_exact_status (f : Format) (mode : RoundingMode)
    (s : Bool) (c : Nat) (q n : Int)
    (hvalid : (Datum.finite s c (q + n)).Valid f) :
    (scaleB f mode (.finite s c q) n).status = {} :=
  projectMagnitude_exact_status f mode s c (q + n) (q + n) hvalid

theorem scaleB_exact_value (f : Format) (mode : RoundingMode)
    (s : Bool) (c : Nat) (q n : Int)
    (hvalid : (Datum.finite s c (q + n)).Valid f) :
    (scaleB f mode (.finite s c q) n).value.toRat? =
      some (Datum.finiteValue s c q * (10 : ℚ) ^ n) := by
  have h := projectMagnitude_exact f mode s c (q + n) (q + n) hvalid
  simpa [scaleB, Datum.toRat?_eq, Datum.finiteValue,
    zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), mul_assoc] using h

/-- The selected quantum is closest to `q + n` among valid representations of the exact result. -/
theorem scaleB_quantum_closest (f : Format) (mode : RoundingMode)
    (s : Bool) (c : Nat) (q n : Int)
    (hvalid : (Datum.finite s c (q + n)).Valid f)
    (d : Nat) (r : Int)
    (hout : (scaleB f mode (.finite s c q) n).value = .finite s d r)
    (e : Nat) (t : Int) (he : (Datum.finite s e t).Valid f)
    (hvalue : (c : ℚ) * (10 : ℚ) ^ (q + n) = (e : ℚ) * (10 : ℚ) ^ t) :
    |q + n - r| ≤ |q + n - t| :=
  projectMagnitude_quantum_closest f mode s c (q + n) (q + n) hvalid
    d r hout e t he hvalue

/-- Scaling zero changes only its quantum, clamped at the format boundaries. -/
theorem scaleB_zero (f : Format) (mode : RoundingMode) (s : Bool) (q n : Int) :
    scaleB f mode (.finite s 0 q) n =
      { value := .finite s 0 (max f.minQuantum (min (q + n) f.maxQuantum)) } := by
  simpa [scaleB] using projectMagnitude_zero f mode s (q + n)

theorem scaleB_inexact_iff (f : Format) (mode : RoundingMode)
    (s : Bool) (c : Nat) (q n : Int) (v : ℚ)
    (hq : (roundedPair f mode s ((c : ℚ) * (10 : ℚ) ^ (q + n))).2 ≤ f.maxQuantum)
    (hv : (scaleB f mode (.finite s c q) n).value.toRat? = some v) :
    (scaleB f mode (.finite s c q) n).status.inexact = true ↔
      v ≠ Datum.finiteValue s c q * (10 : ℚ) ^ n := by
  have h := projectMagnitude_inexact_iff f mode s
    ((c : ℚ) * (10 : ℚ) ^ (q + n)) v (q + n) hq hv
  cases s <;> simpa [scaleB, Datum.finiteValue, scaleB_exact_magnitude, mul_assoc] using h

/-- Scaling uses the exact, unrounded magnitude in the decimal tininess test. -/
theorem scaleB_underflow_iff (f : Format) (mode : RoundingMode)
    (s : Bool) (c : Nat) (q n : Int)
    (hq : (roundedPair f mode s ((c : ℚ) * (10 : ℚ) ^ (q + n))).2 ≤ f.maxQuantum) :
    (scaleB f mode (.finite s c q) n).status.underflow = true ↔
      (c : ℚ) * (10 : ℚ) ^ (q + n) < f.minNormal ∧
        (scaleB f mode (.finite s c q) n).status.inexact = true := by
  simp [scaleB, projectMagnitude_eq, not_lt.mpr hq]

theorem logB_finite (f : Format) (s : Bool) (c : Nat) (q : Int) (hc : c ≠ 0) :
    logB f (.finite s c q) = { value := q + (Nat.log 10 c : Int) } := by
  cases c <;> simp_all [logB]

/-- The returned exponent is exactly the unique radix-power bracket for the magnitude. -/
theorem logB_bounds (f : Format) (s : Bool) (c : Nat) (q : Int) (hc : c ≠ 0) :
    (10 : ℚ) ^ (logB f (.finite s c q)).value ≤ (c : ℚ) * (10 : ℚ) ^ q ∧
      (c : ℚ) * (10 : ℚ) ^ q < (10 : ℚ) ^ ((logB f (.finite s c q)).value + 1) := by
  rw [logB_finite f s c q hc]
  have hl : (10 : ℚ) ^ Nat.log 10 c ≤ (c : ℚ) := by
    exact_mod_cast Nat.pow_log_le_self 10 hc
  have hu : (c : ℚ) < (10 : ℚ) ^ (Nat.log 10 c + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1 < 10) c
  have hp : 0 < (10 : ℚ) ^ q := zpow_pos (by norm_num) q
  constructor
  · simpa [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), mul_comm] using
      mul_le_mul_of_nonneg_right hl hp.le
  · simpa [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), pow_succ, mul_assoc, mul_comm,
      mul_left_comm] using mul_lt_mul_of_pos_right hu hp

theorem logB_valid_range (f : Format) (s : Bool) (c : Nat) (q : Int)
    (hc : c ≠ 0) (hvalid : (Datum.finite s c q).Valid f) :
    f.minQuantum ≤ (logB f (.finite s c q)).value ∧
      (logB f (.finite s c q)).value ≤ f.maxQuantum + (f.precision : Int) - 1 := by
  have hv := (Datum.valid_quantum_iff ..).mp hvalid
  have hl : Nat.log 10 c < f.precision := by
    apply (Nat.log_lt_iff_lt_pow (by decide : 1 < 10) hc).mpr
    simpa [← Format.coefficientBound_eq] using hv.1
  rw [logB_finite f s c q hc]
  simp only
  omega

/-- The exceptional integer exceeds twice either absolute endpoint of the exponent range. -/
theorem logBSentinel_twice_bound (f : Format) :
    2 * |f.minQuantum| < logBSentinel f ∧
      2 * |f.maxQuantum + (f.precision : Int) - 1| < logBSentinel f := by
  have hlo := le_max_left |f.minQuantum| |f.maxQuantum + (f.precision : Int) - 1|
  have hhi := le_max_right |f.minQuantum| |f.maxQuantum + (f.precision : Int) - 1|
  unfold logBSentinel
  omega

/-- Every valid finite exponent has absolute value less than half the exceptional sentinel. -/
theorem logB_sentinel_twice_abs (f : Format) (s : Bool) (c : Nat) (q : Int)
    (hc : c ≠ 0) (hvalid : (Datum.finite s c q).Valid f) :
    2 * |(logB f (.finite s c q)).value| < logBSentinel f := by
  have hr := logB_valid_range f s c q hc hvalid
  have hb := logBSentinel_twice_bound f
  have hlo := neg_abs_le f.minQuantum
  have hhi := le_abs_self (f.maxQuantum + (f.precision : Int) - 1)
  rcases le_total 0 (logB f (.finite s c q)).value with h | h
  · rw [abs_of_nonneg h]
    omega
  · rw [abs_of_nonpos h]
    omega

/-- The integer exceptional result cannot collide with a valid finite nonzero exponent. -/
theorem logB_sentinel_separated (f : Format) (s : Bool) (c : Nat) (q : Int)
    (hc : c ≠ 0) (hvalid : (Datum.finite s c q).Valid f) :
    -logBSentinel f < (logB f (.finite s c q)).value ∧
      (logB f (.finite s c q)).value < logBSentinel f := by
  have h := logB_sentinel_twice_abs f s c q hc hvalid
  have hp := abs_nonneg (logB f (.finite s c q)).value
  have hlo := neg_abs_le (logB f (.finite s c q)).value
  have hhi := le_abs_self (logB f (.finite s c q)).value
  omega

end Arithmetic
end FloatLib.Floats.Formats.DecimalInterchange
