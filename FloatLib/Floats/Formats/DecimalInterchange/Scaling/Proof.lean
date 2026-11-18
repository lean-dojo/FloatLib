/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Arithmetic.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Cohort
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Saturation
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Zero
public import FloatLib.Floats.Formats.DecimalInterchange.Scaling.Runtime

/-!
# Exponent-operation semantics

Bounds between consecutive powers of ten pin down `logB`, so for `314` the answer is
`2`. Scaling inherits the value, range, rounding and cohort guarantees of the projection it calls,
signed zero and decimal tininess before rounding included.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange
namespace Arithmetic

/-- Scaling a finite datum projects the exact product of its magnitude and the radix power. -/
theorem scale_finite (f : Format) (mode : RoundingMode) (s : Bool) (c : Nat) (q n : Int) :
    scale f mode (.finite s c q) n =
      projectMagnitude f mode s ((c : ℚ) * (10 : ℚ) ^ (q + n)) (q + n) :=
  projectScaled_eq f mode s c (q + n) (q + n)

/-- Scaling by a power of ten always delivers a valid datum, including NaN, infinite and overflowed
results. -/
theorem scale_valid (f : Format) (mode : RoundingMode) (x : Datum) (n : Int) :
    (scale f mode x n).value.Valid f := by
  cases x with
  | finite s c q =>
      rw [scale_finite]
      exact projectMagnitude_valid f mode s
        (mul_nonneg (Nat.cast_nonneg c) (zpow_pos (by norm_num) (q + n)).le) _
  | infinity s => trivial
  | nan s t p => exact nanResult_valid ..

/-- The intermediate magnitude is the input magnitude times the radix power, unrounded. -/
theorem scale_exact_magnitude (c : Nat) (q n : Int) :
    (c : ℚ) * (10 : ℚ) ^ (q + n) =
      ((c : ℚ) * (10 : ℚ) ^ q) * (10 : ℚ) ^ n := by
  rw [zpow_add₀ (by norm_num)]
  ring

/-- An in-range exact shifted representation incurs no exceptions. -/
theorem scale_exact_status (f : Format) (mode : RoundingMode)
    (s : Bool) (c : Nat) (q n : Int)
    (hvalid : (Datum.finite s c (q + n)).Valid f) :
    (scale f mode (.finite s c q) n).status = {} := by
  rw [scale_finite]
  exact projectMagnitude_exact_status f mode s c (q + n) (q + n) hvalid

/-- When the shifted representation is valid in the format, scaling delivers the input value times
`10 ^ n`, unrounded. -/
theorem scale_exact_value (f : Format) (mode : RoundingMode)
    (s : Bool) (c : Nat) (q n : Int)
    (hvalid : (Datum.finite s c (q + n)).Valid f) :
    (scale f mode (.finite s c q) n).value.toRat? =
      some (Datum.finiteValue s c q * (10 : ℚ) ^ n) := by
  have h := projectMagnitude_exact f mode s c (q + n) (q + n) hvalid
  simpa [scale_finite, Datum.toRat?_eq, Datum.finiteValue,
    zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), mul_assoc] using h

/-- The selected quantum is closest to `q + n` among valid representations of the exact result. The
shifted representation `(c, q + n)` need not be valid itself, and any valid representation
`(e, t)` of the exact result is at least as far from `q + n`. -/
theorem scale_quantum_closest (f : Format) (mode : RoundingMode)
    (s : Bool) (c : Nat) (q n : Int)
    (d : Nat) (r : Int)
    (hout : (scale f mode (.finite s c q) n).value = .finite s d r)
    (e : Nat) (t : Int) (he : (Datum.finite s e t).Valid f)
    (hvalue : (c : ℚ) * (10 : ℚ) ^ (q + n) = (e : ℚ) * (10 : ℚ) ^ t) :
    |q + n - r| ≤ |q + n - t| := by
  rw [scale_finite] at hout
  exact projectMagnitude_quantum_closest f mode s c (q + n) (q + n) d r hout e t he hvalue

/-- Scaling zero changes only its quantum, clamped at the format boundaries. -/
theorem scale_zero (f : Format) (mode : RoundingMode) (s : Bool) (q n : Int) :
    scale f mode (.finite s 0 q) n =
      { value := .finite s 0 (max f.minQuantum (min (q + n) f.maxQuantum)) } := by
  simpa [scale_finite] using projectMagnitude_zero f mode s (q + n)

/-- Scaling a finite datum raises inexact if and only if a finite delivered value differs from the
exact scaled value, an overflow to the greatest finite datum included. -/
theorem scale_inexact_iff (f : Format) (mode : RoundingMode)
    (s : Bool) (c : Nat) (q n : Int) (v : ℚ)
    (hv : (scale f mode (.finite s c q) n).value.toRat? = some v) :
    (scale f mode (.finite s c q) n).status.inexact = true ↔
      v ≠ Datum.finiteValue s c q * (10 : ℚ) ^ n := by
  rw [scale_finite] at hv ⊢
  have h := projectMagnitude_inexact_iff f mode s
    ((c : ℚ) * (10 : ℚ) ^ (q + n)) v (q + n) hv
  cases s <;>
    simpa [Datum.finiteValue, scale_exact_magnitude,
      mul_assoc] using h

/-- Scaling uses the exact, unrounded magnitude in the decimal tininess test, and an overflowing
magnitude is never tiny. -/
theorem scale_underflow_iff (f : Format) (mode : RoundingMode)
    (s : Bool) (c : Nat) (q n : Int) :
    (scale f mode (.finite s c q) n).status.underflow = true ↔
      (c : ℚ) * (10 : ℚ) ^ (q + n) < f.minNormal ∧
        (scale f mode (.finite s c q) n).status.inexact = true := by
  by_cases hq : (roundedPair f mode s ((c : ℚ) * (10 : ℚ) ^ (q + n))).2 ≤ f.maxQuantum
  · simp [scale_finite, projectMagnitude_eq, not_lt.mpr hq]
  · have hq' := lt_of_not_ge hq
    have hlt := maxFinite_lt_of_roundedPair_overflow f mode s
      (mul_nonneg (Nat.cast_nonneg c) (zpow_pos (by norm_num : (0 : ℚ) < 10) _).le) hq'
    have hmin := f.minNormal_le_maxFinite
    simp only [scale_finite, projectMagnitude_eq, hq', ↓reduceIte, Bool.false_eq_true, false_iff,
      not_and]
    exact fun h => absurd h (not_lt.mpr (hmin.trans hlt.le))

/-- For a nonzero finite datum, `logB` is the exponent of its leading digit, the quantum plus the
coefficient's digit count minus one, and raises no flags. -/
theorem logB_finite (f : Format) (s : Bool) (c : Nat) (q : Int) (hc : c ≠ 0) :
    logB f (.finite s c q) = { value := q + (Nat.log 10 c : Int) } := by
  cases c <;> simp_all [logB]

/-- The returned exponent is the unique radix-power bracket for the magnitude. -/
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

/-- For a valid nonzero finite datum, `logB` lies between the least quantum and `emax`, the exponent
of the largest finite value's leading digit. -/
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
  have hm := le_max_left (max |f.minQuantum| |f.maxQuantum + (f.precision : Int) - 1|)
    |logBBound f|
  unfold logBSentinel
  omega

/-- The exceptional sentinel exceeds twice the `logB` bound `emax + p - 1`. -/
theorem logBSentinel_outside_logBBound (f : Format) :
    2 * |logBBound f| < logBSentinel f := by
  have hm := le_max_right (max |f.minQuantum| |f.maxQuantum + (f.precision : Int) - 1|)
    |logBBound f|
  unfold logBSentinel
  omega

/--
Whenever `logB` raises invalid, for a zero, an infinity or a NaN, its integer lies outside
`±2 × (emax + p - 1)`, as IEEE 754-2019 §5.3.3 requires for an integer `logBFormat`: the negative
sentinel for a zero and the positive one otherwise.
-/
theorem logB_outside_logBBound (f : Format) (x : Datum)
    (hinvalid : (logB f x).status.invalid = true) :
    2 * |logBBound f| < |(logB f x).value| := by
  have h := logBSentinel_outside_logBBound f
  have hpos : 0 < logBSentinel f := lt_of_le_of_lt (by positivity) h
  rcases x with ⟨s, _ | c, q⟩ | s | ⟨s, t, p⟩
  · simp [logB, abs_neg, abs_of_pos hpos, h]
  · simp [logB] at hinvalid
  · simp [logB, abs_of_pos hpos, h]
  · simp [logB, abs_of_pos hpos, h]

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
  have hlo := neg_abs_le (logB f (.finite s c q)).value
  have hhi := le_abs_self (logB f (.finite s c q)).value
  omega

end Arithmetic
end FloatLib.Floats.Formats.DecimalInterchange
