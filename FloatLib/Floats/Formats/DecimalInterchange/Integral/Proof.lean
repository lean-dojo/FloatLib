/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Integral.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Quantize.Proof

/-!
# Integral result, preferred quantum, and status guarantees

When the format's maximum quantum is nonnegative, every valid finite input produces
a finite integer at the specified preferred quantum, with no intermediate precision
loss or range exception. This includes all three standard presets. The general
invalid characterization also covers custom layouts with a negative maximum quantum.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Arithmetic

/-- The coefficient of a rounded integral value never exceeds the input coefficient. -/
theorem integral_coefficient_le (mode : RoundingMode) (s : Bool) (c : Nat) (q : Int) :
    mode.roundAt s ((c : ℚ) * (10 : ℚ) ^ q) (max q 0) ≤ c := by
  by_cases hq : 0 ≤ q
  · rw [max_eq_left hq, mode.roundAt_exact s c le_rfl]
    simp
  · have hn : q ≤ 0 := by omega
    rw [max_eq_right hn]
    simp only [RoundingMode.roundAt, zpow_zero, div_one]
    apply mode.roundMagnitude_le_nat s
      (mul_nonneg (Nat.cast_nonneg c) (zpow_pos (by norm_num : (0 : ℚ) < 10) q).le) c
    simpa using mul_le_mul_of_nonneg_left
      (zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℚ) ≤ 10) hn) (Nat.cast_nonneg (α := ℚ) c)

/-- The successful output explicitly retains the sign and preferred quantum, including zero. -/
theorem roundToIntegralExact_finite (f : Format) (mode : RoundingMode)
    (s : Bool) (c : Nat) (q : Int) (hv : (Datum.finite s c q).Valid f)
    (hzero : 0 ≤ f.maxQuantum) :
    roundToIntegralExact f mode (.finite s c q) =
      { value := .finite s (mode.roundAt s ((c : ℚ) * (10 : ℚ) ^ q) (max q 0)) (max q 0)
        status := { inexact := decide (
          (mode.roundAt s ((c : ℚ) * (10 : ℚ) ^ q) (max q 0) : ℚ) * (10 : ℚ) ^ (max q 0) ≠
            (c : ℚ) * (10 : ℚ) ^ q) } } := by
  obtain ⟨hc, hmin, hmax⟩ := (Datum.valid_quantum_iff ..).mp hv
  have hq : f.minQuantum ≤ max q 0 ∧ max q 0 ≤ f.maxQuantum ∧
      mode.roundAt s ((c : ℚ) * (10 : ℚ) ^ q) (max q 0) < f.coefficientBound :=
    ⟨hmin.trans (le_max_left ..), max_le hmax hzero,
      (integral_coefficient_le mode s c q).trans_lt hc⟩
  simp only [roundToIntegralExact, quantizeMagnitude, ite_eq_left hq]

/-- For a valid finite input, invalid occurs exactly when the preferred integral quantum
cannot be represented. The coefficient bound never causes this failure. -/
theorem roundToIntegralExact_invalid_iff (f : Format) (mode : RoundingMode)
    (s : Bool) (c : Nat) (q : Int) (hv : (Datum.finite s c q).Valid f) :
    (roundToIntegralExact f mode (.finite s c q)).status.invalid = true ↔
      f.maxQuantum < 0 := by
  obtain ⟨hc, hmin, hmax⟩ := (Datum.valid_quantum_iff ..).mp hv
  change (quantizeMagnitude f mode s _ _).status.invalid = true ↔ _
  rw [quantizeMagnitude_invalid_iff]
  have hcoef := (integral_coefficient_le mode s c q).trans_lt hc
  have hlo := hmin.trans (le_max_left q 0)
  constructor
  · intro h
    by_contra hn
    exact h ⟨hlo, max_le hmax (by omega), hcoef⟩
  · intro h hn
    have hz := le_max_right q 0
    omega

theorem roundToIntegralExact_valid (f : Format) (mode : RoundingMode) (x : Datum) :
    (roundToIntegralExact f mode x).value.Valid f := by
  cases x
  · exact quantizeMagnitude_valid ..
  · trivial
  · exact nanResult_valid ..

theorem roundToIntegral_valid (f : Format) (mode : RoundingMode) (x : Datum) :
    (roundToIntegral f mode x).value.Valid f := roundToIntegralExact_valid ..

/-- A valid finite input rounds to an integer when the maximum quantum is nonnegative. -/
theorem roundToIntegralExact_integer (f : Format) (mode : RoundingMode)
    (s : Bool) (c : Nat) (q : Int) (hv : (Datum.finite s c q).Valid f)
    (hzero : 0 ≤ f.maxQuantum) :
    ∃ n : Int, (roundToIntegralExact f mode (.finite s c q)).value.toRat? = some (n : ℚ) := by
  rw [roundToIntegralExact_finite f mode s c q hv hzero]
  let d := mode.roundAt s ((c : ℚ) * (10 : ℚ) ^ q) (max q 0)
  let n : Int := (d : Int) * 10 ^ (max q 0).toNat
  refine ⟨if s then -n else n, ?_⟩
  have he : ((max q 0).toNat : Int) = max q 0 := Int.toNat_of_nonneg (le_max_right ..)
  have hp : (10 : ℚ) ^ (max q 0) = (10 : ℚ) ^ (max q 0).toNat := by
    rw [← zpow_natCast, he]
  cases s <;> simp [Datum.toRat?_eq, hp, n, d]

/-- A valid finite input raises no range, domain, or divide-by-zero exception
when the maximum quantum is nonnegative. -/
theorem roundToIntegralExact_finite_flags (f : Format) (mode : RoundingMode)
    (s : Bool) (c : Nat) (q : Int) (hv : (Datum.finite s c q).Valid f)
    (hzero : 0 ≤ f.maxQuantum) :
    (roundToIntegralExact f mode (.finite s c q)).status.invalid = false ∧
      (roundToIntegralExact f mode (.finite s c q)).status.overflow = false ∧
      (roundToIntegralExact f mode (.finite s c q)).status.underflow = false ∧
      (roundToIntegralExact f mode (.finite s c q)).status.divideByZero = false := by
  rw [roundToIntegralExact_finite f mode s c q hv hzero]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Explicit-direction integral rounding suppresses inexact, including for a nonintegral input. -/
@[simp] theorem roundToIntegral_inexact (f : Format) (mode : RoundingMode) (x : Datum) :
    (roundToIntegral f mode x).status.inexact = false := rfl

/-- Exact integral rounding signals inexact precisely for a numerical change. -/
theorem roundToIntegralExact_inexact_iff (f : Format) (mode : RoundingMode)
    (s : Bool) (c : Nat) (q : Int) (v : ℚ)
    (hv : (roundToIntegralExact f mode (.finite s c q)).value.toRat? = some v) :
    (roundToIntegralExact f mode (.finite s c q)).status.inexact = true ↔
      v ≠ Datum.finiteValue s c q :=
  quantize_inexact_iff f mode s false c 0 q (max q 0) v hv

/-- Already nonnegative quantum exponents are preserved, including trailing coefficient zeros. -/
theorem roundToIntegralExact_of_nonneg_quantum (f : Format) (mode : RoundingMode)
    (s : Bool) (c : Nat) (q : Int) (hv : (Datum.finite s c q).Valid f) (hq : 0 ≤ q) :
    roundToIntegralExact f mode (.finite s c q) = { value := .finite s c q } := by
  simpa only [roundToIntegralExact, max_eq_left hq, quantize] using
    quantize_same_quantum f mode s false c 0 q hv

/-- Both nearest integral modes differ from the input by at most one half,
independent of its cohort. -/
theorem roundToIntegralExact_error_le_half (f : Format) (mode : RoundingMode)
    (hm : mode = .nearestEven ∨ mode = .nearestAway)
    (s : Bool) (c : Nat) (q : Int) (hv : (Datum.finite s c q).Valid f)
    (hzero : 0 ≤ f.maxQuantum) :
    ∃ value, (roundToIntegralExact f mode (.finite s c q)).value.toRat? = some value ∧
      |value - Datum.finiteValue s c q| ≤ (1 : ℚ) / 2 := by
  by_cases hq : 0 ≤ q
  · rw [roundToIntegralExact_of_nonneg_quantum f mode s c q hv hq]
    refine ⟨Datum.finiteValue s c q, Datum.toRat?_eq _, ?_⟩
    norm_num
  · have hi := (roundToIntegralExact_finite_flags f mode s c q hv hzero).1
    have he := quantize_error_le_half f mode hm s false c 0 q (max q 0) hi
    simpa only [roundToIntegralExact, quantize, max_eq_right (by omega : q ≤ 0), zpow_zero]
      using he

/-- The two integral variants have exactly the same numerical datum. -/
@[simp] theorem roundToIntegral_value (f : Format) (mode : RoundingMode) (x : Datum) :
    (roundToIntegral f mode x).value = (roundToIntegralExact f mode x).value := rfl

end FloatLib.Floats.Formats.DecimalInterchange.Arithmetic
