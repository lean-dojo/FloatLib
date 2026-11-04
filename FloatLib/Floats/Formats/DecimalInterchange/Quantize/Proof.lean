/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Quantize.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Arithmetic.Proof

/-!
# Quantize: range, fixed quantum, and numerical error

When quantize succeeds, the result has the requested quantum, signed zero included, and its
coefficient comes from a single exact rational rounding on that grid. The range test is necessary
and sufficient for a finite result.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Arithmetic

/-- Rounding a magnitude to a fixed quantum always delivers a valid datum: the default invalid NaN
whenever the quantum or the rounded coefficient does not fit. -/
theorem quantizeMagnitude_valid (f : Format) (mode : RoundingMode)
    (s : Bool) (x : ℚ) (q : Int) :
    (quantizeMagnitude f mode s x q).value.Valid f := by
  dsimp only [quantizeMagnitude]
  split
  · rename_i h
    exact (Datum.valid_quantum_iff ..).mpr ⟨h.2.2, h.1, h.2.1⟩
  · exact invalidResult_valid f

/-- Quantize always delivers a valid datum, including NaN, invalid and infinite results. -/
theorem quantize_valid (f : Format) (mode : RoundingMode) (x y : Datum) :
    (quantize f mode x y).value.Valid f := by
  cases x <;> cases y <;> simp only [quantize]
  all_goals first
    | exact quantizeMagnitude_valid ..
    | exact nanResult_valid ..
    | exact invalidResult_valid f
    | trivial

/-- Invalid is raised if and only if the requested rounded representation does not fit. -/
theorem quantizeMagnitude_invalid_iff (f : Format) (mode : RoundingMode)
    (s : Bool) (x : ℚ) (q : Int) :
    (quantizeMagnitude f mode s x q).status.invalid = true ↔
      ¬(f.minQuantum ≤ q ∧ q ≤ f.maxQuantum ∧
        mode.roundAt s x q < f.coefficientBound) := by
  dsimp only [quantizeMagnitude]
  split <;> simp_all [invalidResult]

/-- A successful quantization has the specified sign, grid, and rounded coefficient. -/
theorem quantizeMagnitude_of_not_invalid (f : Format) (mode : RoundingMode)
    (s : Bool) (x : ℚ) (q : Int)
    (h : (quantizeMagnitude f mode s x q).status.invalid = false) :
    quantizeMagnitude f mode s x q =
      { value := .finite s (mode.roundAt s x q) q
        status := { inexact := decide ((mode.roundAt s x q : ℚ) * (10 : ℚ) ^ q ≠ x) } } := by
  dsimp only [quantizeMagnitude] at *
  split at h <;> simp_all [invalidResult]

/-- Quantize raises neither underflow nor overflow, even for inexact subnormal results. -/
theorem quantize_range_flags (f : Format) (mode : RoundingMode) (x y : Datum) :
    (quantize f mode x y).status.underflow = false ∧
      (quantize f mode x y).status.overflow = false ∧
      (quantize f mode x y).status.divideByZero = false := by
  cases x <;> cases y <;>
    simp [quantize, nanResult, invalidResult, quantizeMagnitude]
  split <;> simp

/-- Quantization to an already represented quantum preserves the entire finite datum. -/
theorem quantize_same_quantum (f : Format) (mode : RoundingMode)
    (s t : Bool) (c d : Nat) (q : Int) (hv : (Datum.finite s c q).Valid f) :
    quantize f mode (.finite s c q) (.finite t d q) =
      { value := .finite s c q } := by
  obtain ⟨hc, hmin, hmax⟩ := (Datum.valid_quantum_iff ..).mp hv
  have hr := mode.roundAt_exact s c (q := q) (r := q) le_rfl
  simp only [sub_self, Int.toNat_zero, pow_zero, mul_one] at hr
  simp [quantize, quantizeMagnitude, hr, hc, hmin, hmax]

/-- A finite input magnitude is nonnegative. -/
private theorem magnitude_nonneg (c : Nat) (q : Int) : 0 ≤ (c : ℚ) * (10 : ℚ) ^ q :=
  mul_nonneg (Nat.cast_nonneg c) (zpow_pos (by norm_num) q).le

/-- A quantization that does not raise invalid delivers the input sign applied to the magnitude
rounded on the requested grid. -/
private theorem quantize_toRat?_of_not_invalid (f : Format) (mode : RoundingMode)
    (s t : Bool) (c d : Nat) (q r : Int)
    (h : (quantize f mode (.finite s c q) (.finite t d r)).status.invalid = false) :
    (quantize f mode (.finite s c q) (.finite t d r)).value.toRat? =
      some ((if s then -1 else 1) * (mode.roundAt s ((c : ℚ) * (10 : ℚ) ^ q) r : ℚ) *
        (10 : ℚ) ^ r) := by
  simp only [quantize, quantizeMagnitude_of_not_invalid f mode s _ r h, Datum.toRat?_eq]

/-- A successful quantization's error is the error of rounding the magnitude on the requested grid,
for either sign. -/
private theorem quantize_abs_sub (f : Format) (mode : RoundingMode)
    (s t : Bool) (c d : Nat) (q r : Int)
    (h : (quantize f mode (.finite s c q) (.finite t d r)).status.invalid = false) :
    ∃ value, (quantize f mode (.finite s c q) (.finite t d r)).value.toRat? = some value ∧
      |value - Datum.finiteValue s c q| =
        |(mode.roundAt s ((c : ℚ) * (10 : ℚ) ^ q) r : ℚ) * (10 : ℚ) ^ r -
          (c : ℚ) * (10 : ℚ) ^ q| := by
  refine ⟨_, quantize_toRat?_of_not_invalid f mode s t c d q r h, ?_⟩
  cases s
  · simp [Datum.finiteValue]
  · simp only [Datum.finiteValue, ite_true, neg_mul, one_mul, neg_sub_neg]
    rw [abs_sub_comm]

/-- If nearest-mode quantization of a finite input does not raise invalid, its result decodes to a
value within half a unit of the requested quantum (not of a normalized precision grid). -/
theorem quantize_error_le_half (f : Format) (mode : RoundingMode)
    (hm : mode = .nearest ∨ mode = .nearestAway)
    (s t : Bool) (c d : Nat) (q r : Int)
    (h : (quantize f mode (.finite s c q) (.finite t d r)).status.invalid = false) :
    ∃ value, (quantize f mode (.finite s c q) (.finite t d r)).value.toRat? = some value ∧
      |value - Datum.finiteValue s c q| ≤ (10 : ℚ) ^ r / 2 := by
  obtain ⟨value, hv, he⟩ := quantize_abs_sub f mode s t c d q r h
  refine ⟨value, hv, ?_⟩
  rw [he]
  exact mode.roundAt_error_le_half hm s (magnitude_nonneg c q) r

/-- On success the inexact flag records a numerical change, independently of the sign. -/
theorem quantize_inexact_iff (f : Format) (mode : RoundingMode)
    (s t : Bool) (c d : Nat) (q r : Int) (v : ℚ)
    (hv : (quantize f mode (.finite s c q) (.finite t d r)).value.toRat? = some v) :
    (quantize f mode (.finite s c q) (.finite t d r)).status.inexact = true ↔
      v ≠ Datum.finiteValue s c q := by
  simp only [quantize] at *
  dsimp only [quantizeMagnitude] at *
  split at hv
  · rename_i h
    simp only [ite_eq_left h, Datum.toRat?_eq, Option.some.injEq] at *
    subst v
    cases s <;> simp [Datum.finiteValue]
  · simp [invalidResult, Datum.toRat?_eq] at hv

/-- If quantization of a finite input does not raise invalid, then in every rounding direction its
result decodes to a value less than one unit of the requested quantum from the input. -/
theorem quantize_error_lt_one (f : Format) (mode : RoundingMode)
    (s t : Bool) (c d : Nat) (q r : Int)
    (h : (quantize f mode (.finite s c q) (.finite t d r)).status.invalid = false) :
    ∃ value, (quantize f mode (.finite s c q) (.finite t d r)).value.toRat? = some value ∧
      |value - Datum.finiteValue s c q| < (10 : ℚ) ^ r := by
  obtain ⟨value, hv, he⟩ := quantize_abs_sub f mode s t c d q r h
  refine ⟨value, hv, ?_⟩
  rw [he]
  exact mode.roundAt_error_lt_one s (magnitude_nonneg c q) r

/-- If upward quantization of a finite input does not raise invalid, its result decodes to a value
at least the input, for either sign. -/
theorem le_quantize_up (f : Format)
    (s t : Bool) (c d : Nat) (q r : Int)
    (h : (quantize f .up (.finite s c q) (.finite t d r)).status.invalid = false) :
    ∃ value, (quantize f .up (.finite s c q) (.finite t d r)).value.toRat? = some value ∧
      Datum.finiteValue s c q ≤ value := by
  refine ⟨_, quantize_toRat?_of_not_invalid f _ s t c d q r h, ?_⟩
  have h := RoundingMode.le_roundAt_up s (magnitude_nonneg c q) r
  cases s <;> simpa [Datum.finiteValue] using h

/-- If downward quantization of a finite input does not raise invalid, its result decodes to a value
at most the input, for either sign. -/
theorem quantize_down_le (f : Format)
    (s t : Bool) (c d : Nat) (q r : Int)
    (h : (quantize f .down (.finite s c q) (.finite t d r)).status.invalid = false) :
    ∃ value, (quantize f .down (.finite s c q) (.finite t d r)).value.toRat? = some value ∧
      value ≤ Datum.finiteValue s c q := by
  refine ⟨_, quantize_toRat?_of_not_invalid f _ s t c d q r h, ?_⟩
  have h := RoundingMode.roundAt_down_le s (magnitude_nonneg c q) r
  cases s <;> simpa [Datum.finiteValue] using h

end FloatLib.Floats.Formats.DecimalInterchange.Arithmetic
