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

The successful result has exactly the requested quantum, including signed zero.
The coefficient is obtained by a single exact rational rounding on that grid.
The range test is necessary and sufficient for a finite result.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Arithmetic

theorem quantizeMagnitude_valid (f : Format) (mode : RoundingMode)
    (s : Bool) (x : ℚ) (q : Int) :
    (quantizeMagnitude f mode s x q).value.Valid f := by
  dsimp only [quantizeMagnitude]
  split
  · rename_i h
    exact (Datum.valid_quantum_iff ..).mpr ⟨h.2.2, h.1, h.2.1⟩
  · exact invalidResult_valid f

theorem quantize_valid (f : Format) (mode : RoundingMode) (x y : Datum) :
    (quantize f mode x y).value.Valid f := by
  cases x <;> cases y <;> simp only [quantize]
  all_goals first
    | exact quantizeMagnitude_valid ..
    | exact nanResult_valid ..
    | exact invalidResult_valid f
    | trivial

/-- Invalid is raised precisely when the requested rounded representation does not fit. -/
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

/-- The nearest-mode error uses the requested quantum, not a normalized precision grid. -/
theorem quantize_error_le_half (f : Format) (mode : RoundingMode)
    (hm : mode = .nearestEven ∨ mode = .nearestAway)
    (s t : Bool) (c d : Nat) (q r : Int)
    (h : (quantize f mode (.finite s c q) (.finite t d r)).status.invalid = false) :
    ∃ value, (quantize f mode (.finite s c q) (.finite t d r)).value.toRat? = some value ∧
      |value - Datum.finiteValue s c q| ≤ (10 : ℚ) ^ r / 2 := by
  have he := quantizeMagnitude_of_not_invalid f mode s _ r h
  simp only [quantize, he, Datum.toRat?_eq]
  refine ⟨_, rfl, ?_⟩
  have herr := mode.roundAt_error_le_half hm s
    (mul_nonneg (Nat.cast_nonneg c) (zpow_pos (by norm_num : (0 : ℚ) < 10) q).le) r
  cases s
  · simpa [Datum.finiteValue] using herr
  · simp only [Datum.finiteValue, ite_true, neg_mul, one_mul, neg_sub_neg]
    rw [abs_sub_comm]
    exact herr

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
    simp only [if_pos h, Datum.toRat?_eq, Option.some.injEq] at *
    subst v
    cases s <;> simp [Datum.finiteValue]
  · simp [invalidResult, Datum.toRat?_eq] at hv

/-- Every rounding direction changes the value by less than one requested grid unit. -/
theorem quantize_error_lt_one (f : Format) (mode : RoundingMode)
    (s t : Bool) (c d : Nat) (q r : Int)
    (h : (quantize f mode (.finite s c q) (.finite t d r)).status.invalid = false) :
    ∃ value, (quantize f mode (.finite s c q) (.finite t d r)).value.toRat? = some value ∧
      |value - Datum.finiteValue s c q| < (10 : ℚ) ^ r := by
  have he := quantizeMagnitude_of_not_invalid f mode s _ r h
  simp only [quantize, he, Datum.toRat?_eq]
  refine ⟨_, rfl, ?_⟩
  have herr := mode.roundAt_error_lt_one s
    (mul_nonneg (Nat.cast_nonneg c) (zpow_pos (by norm_num : (0 : ℚ) < 10) q).le) r
  cases s
  · simpa [Datum.finiteValue] using herr
  · simp only [Datum.finiteValue, ite_true, neg_mul, one_mul, neg_sub_neg]
    rw [abs_sub_comm]
    exact herr

/-- Upward quantization is an upper bound on the exact input value, for either sign. -/
theorem le_quantize_towardPositive (f : Format)
    (s t : Bool) (c d : Nat) (q r : Int)
    (h : (quantize f .towardPositive (.finite s c q) (.finite t d r)).status.invalid = false) :
    ∃ value, (quantize f .towardPositive (.finite s c q) (.finite t d r)).value.toRat? = some value ∧
      Datum.finiteValue s c q ≤ value := by
  have he := quantizeMagnitude_of_not_invalid f .towardPositive s _ r h
  simp only [quantize, he, Datum.toRat?_eq]
  refine ⟨_, rfl, ?_⟩
  have hu : 0 < (10 : ℚ) ^ r := zpow_pos (by norm_num) _
  have hx : 0 ≤ (c : ℚ) * (10 : ℚ) ^ q :=
    mul_nonneg (Nat.cast_nonneg c) (zpow_pos (by norm_num) q).le
  have hs := mul_le_mul_of_nonneg_right
    (RoundingMode.le_roundSigned_towardPositive s (div_nonneg hx hu.le)) hu.le
  cases s <;> simpa [Datum.finiteValue, RoundingMode.roundSigned,
    RoundingMode.roundAt, hu.ne'] using hs

/-- Downward quantization is a lower bound on the exact input value, for either sign. -/
theorem quantize_towardNegative_le (f : Format)
    (s t : Bool) (c d : Nat) (q r : Int)
    (h : (quantize f .towardNegative (.finite s c q) (.finite t d r)).status.invalid = false) :
    ∃ value, (quantize f .towardNegative (.finite s c q) (.finite t d r)).value.toRat? = some value ∧
      value ≤ Datum.finiteValue s c q := by
  have he := quantizeMagnitude_of_not_invalid f .towardNegative s _ r h
  simp only [quantize, he, Datum.toRat?_eq]
  refine ⟨_, rfl, ?_⟩
  have hu : 0 < (10 : ℚ) ^ r := zpow_pos (by norm_num) _
  have hx : 0 ≤ (c : ℚ) * (10 : ℚ) ^ q :=
    mul_nonneg (Nat.cast_nonneg c) (zpow_pos (by norm_num) q).le
  have hs := mul_le_mul_of_nonneg_right
    (RoundingMode.roundSigned_towardNegative_le s (div_nonneg hx hu.le)) hu.le
  cases s <;> simpa [Datum.finiteValue, RoundingMode.roundSigned,
    RoundingMode.roundAt, hu.ne'] using hs

end FloatLib.Floats.Formats.DecimalInterchange.Arithmetic
