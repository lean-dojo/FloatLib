/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Rounding.DirectedProof
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Finiteness
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Bounds
public import FloatLib.Floats.Formats.Flocq.Theory.Analysis.Neighbors

/-!
# Positive directed comparison rounding

The positive downward and upward interfaces use the shared all-direction magnitude rounder.
Their numerical contracts require an IEEE descriptor and an exact comparator for a positive
real target. Downward rounding additionally remains finite for arbitrary descriptors and
comparators, and both wrappers always have nonnegative real interpretation.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.AlgebraicRounding

open FloatLib.Floats.Formats.Flocq FloatLib.Numerics

/-! Positive comparison rounding through the shared all-direction contract. -/

/-- Round a positive target downward; arbitrary comparators still return a finite value. -/
def roundDown (fmt : FloatFormat) (compare : Rat → Ordering) : Model fmt :=
  let result := roundMagnitude fmt .down false compare
  if isFinite result then result else posMaxFinite fmt

/-- Round a positive target upward with the shared comparison engine. -/
def roundUp (fmt : FloatFormat) (compare : Rat → Ordering) : Model fmt :=
  roundMagnitude fmt .up false compare

/-- Every direction's positive overflow value has nonnegative real interpretation. -/
theorem toReal_directedOverflow_false_nonneg (fmt : FloatFormat) (away : Bool) :
    0 ≤ toReal (directedOverflow fmt false away) := by
  cases away
  · simpa [directedOverflow, posMaxFinite, maxFinite] using toReal_posMaxFinite_nonneg fmt
  · exact toReal_nativeOverflow_false_nonneg fmt

/-- Packing a positive grid value has nonnegative real interpretation for every descriptor. -/
theorem toReal_packGrid_false_nonneg (fmt : FloatFormat) (mode : IEEERoundingMode)
    (mantissa : Nat) (exponent : Int) :
    0 ≤ toReal (packGrid fmt mode false mantissa exponent) := by
  unfold packGrid
  split_ifs
  · simp
  · exact toReal_directedOverflow_false_nonneg fmt _
  · exact toReal_roundRatScaled_false_nonneg fmt mantissa 1 exponent one_ne_zero

/-- The magnitude engine has nonnegative real interpretation even for inconsistent oracles. -/
theorem toReal_roundMagnitude_false_nonneg (fmt : FloatFormat) (mode : IEEERoundingMode)
    (compare : Rat → Ordering) : 0 ≤ toReal (roundMagnitude fmt mode false compare) := by
  simp only [roundMagnitude]
  split_ifs
  · exact toReal_directedOverflow_false_nonneg fmt _
  · exact toReal_packGrid_false_nonneg fmt mode _ _
  · exact toReal_packGrid_false_nonneg fmt mode _ _

/-- Downward positive comparison rounding is finite without hypotheses on the oracle. -/
@[simp] theorem isFinite_roundDown (fmt : FloatFormat) (compare : Rat → Ordering) :
    isFinite (roundDown fmt compare) = true := by
  simp only [roundDown]
  split_ifs with hfinite
  · exact hfinite
  · exact isFinite_posMaxFinite fmt

/-- Downward positive comparison rounding has nonnegative real interpretation. -/
theorem toReal_roundDown_nonneg (fmt : FloatFormat) (compare : Rat → Ordering) :
    0 ≤ toReal (roundDown fmt compare) := by
  simp only [roundDown]
  split_ifs
  · exact toReal_roundMagnitude_false_nonneg fmt .down compare
  · exact toReal_posMaxFinite_nonneg fmt

/-- Upward positive comparison rounding has nonnegative real interpretation. -/
theorem toReal_roundUp_nonneg (fmt : FloatFormat) (compare : Rat → Ordering) :
    0 ≤ toReal (roundUp fmt compare) :=
  toReal_roundMagnitude_false_nonneg fmt .up compare

/-- The predecessor of the upper power of two is the largest finite IEEE value. -/
theorem pred_upperExponent (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    Flocq.pred (β := binaryRadix) (fexp := fexpOf fmt)
      (Flocq.bpow binaryRadix (upperExponent fmt)) = toReal (posMaxFinite fmt) := by
  have hspacing : fexpOf fmt (upperExponent fmt) =
      fmt.maxNormalExponent - (fmt.fracWidth : Int) := by
    have hfield := fmt.maxFiniteExpField_pos
    simp only [fexpOf, fltExp, upperExponent, FloatFormat.minSubnormalExponent,
      FloatFormat.minNormalExponent, FloatFormat.maxNormalExponent, Int.ofNat_eq_natCast]
    omega
  rw [Flocq.pred_bpow, hspacing, toReal_posMaxFinite_ieee fmt hfmt,
    ← FloatFormat.maxNormalExponent_eq_ieee fmt hfmt]
  have hexponent : upperExponent fmt = (Int.ofNat (fmt.fracWidth + 1)) +
      (fmt.maxNormalExponent - Int.ofNat fmt.fracWidth) := by
    simp only [upperExponent, Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_one]
    omega
  have hpower : Flocq.bpow binaryRadix (upperExponent fmt) =
      (pow2 (fmt.fracWidth + 1) : ℝ) *
        Model.bpow (fmt.maxNormalExponent - Int.ofNat fmt.fracWidth) := by
    change Model.bpow (upperExponent fmt) = _
    rw [hexponent, bpow_add, bpow_ofNat]
  rw [hpower]
  have hpositive : 1 ≤ pow2 (fmt.fracWidth + 1) := by
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (pow2_pos _))
  rw [Nat.cast_sub hpositive, Nat.cast_one]
  change _ - Model.bpow _ = _
  simp only [Int.ofNat_eq_natCast]
  ring

/-- A nonnegative grid point below the upper power of two is at most the largest finite value. -/
theorem roundAt_down_le_posMaxFinite (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    {target : ℝ} (hupper : target < Flocq.bpow binaryRadix (upperExponent fmt)) :
    roundAt fmt target .down ≤ toReal (posMaxFinite fmt) := by
  have hgrid := genericFormat_roundAt fmt target .down
  have hupperGrid : GenericRepresentable binaryRadix (fexpOf fmt)
      (Flocq.bpow binaryRadix (upperExponent fmt)) := by
    apply genericFormat_bpow
    have hfield := fmt.maxFiniteExpField_pos
    simp only [upperExponent, FloatFormat.minSubnormalExponent,
      FloatFormat.minNormalExponent, FloatFormat.maxNormalExponent, Int.ofNat_eq_natCast]
    omega
  have hfloor : roundAt fmt target .down ≤ target := Flocq.round_floor_le target
  have hlt := hfloor.trans_lt hupper
  have h := Flocq.succ_le_of_lt (genericRepresentable_neg _ hupperGrid)
    (genericRepresentable_neg _ hgrid) (neg_lt_neg hlt)
  rw [Flocq.succ_neg, pred_upperExponent fmt hfmt] at h
  exact neg_le_neg_iff.mp h

/-- An exact positive downward result is already finite, so the wrapper leaves it unchanged. -/
theorem roundDown_eq_roundMagnitude (fmt : FloatFormat)
    (compare : Rat → Ordering) {target : ℝ} (hpositive : 0 < target)
    (hcompare : ∀ candidate : Rat, compare candidate = cmp target (candidate : ℝ)) :
    roundDown fmt compare = roundMagnitude fmt .down false compare := by
  have hround := roundMagnitude_roundsTo (fmt := fmt) .down false compare hpositive hcompare
  simp only [Bool.false_eq_true, ↓reduceIte] at hround
  have hfinite : isFinite (roundMagnitude fmt .down false compare) = true := by
    by_cases hrange : |roundAt fmt target .down| ≤ toReal (posMaxFinite fmt)
    · exact (hround.finite hrange).1
    · rw [hround.overflow (not_le.mp hrange)]
      simp [directedOverflow, IEEERoundingMode.overflowRoundsMagnitudeUp,
        IEEERoundingMode.roundsAwayFromZero]
  simp [roundDown, hfinite]

/-- For an exact positive target below the upper power, downward comparison rounding is exact. -/
theorem toReal_roundDown_eq_roundAt (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (compare : Rat → Ordering) (target : ℝ) (hpositive : 0 < target)
    (hcompare : ∀ candidate : Rat, compare candidate = cmp target (candidate : ℝ))
    (hupper : target < Flocq.bpow binaryRadix (upperExponent fmt)) :
    toReal (roundDown fmt compare) = roundAt fmt target .down := by
  rw [roundDown_eq_roundMagnitude fmt compare hpositive hcompare]
  have hround := roundMagnitude_roundsTo (fmt := fmt) .down false compare hpositive hcompare
  simp only [Bool.false_eq_true, ↓reduceIte] at hround
  apply (hround.finite _).2
  have hnonneg : 0 ≤ roundAt fmt target .down := by
    simpa only [roundAt_zero] using roundAt_mono fmt hpositive.le .down
  rw [abs_of_nonneg hnonneg]
  exact roundAt_down_le_posMaxFinite fmt hfmt hupper

/-- Upward positive comparison rounding returns infinity or the finite upward grid rounding. -/
theorem roundUp_eq_posInf_or_finite_roundAt (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (compare : Rat → Ordering) (target : ℝ) (hpositive : 0 < target)
    (hcompare : ∀ candidate : Rat, compare candidate = cmp target (candidate : ℝ)) :
    roundUp fmt compare = posInf fmt ∨
      (isFinite (roundUp fmt compare) = true ∧
        toReal (roundUp fmt compare) = roundAt fmt target .up) := by
  have hround := roundMagnitude_roundsTo (fmt := fmt) .up false compare hpositive hcompare
  simp only [Bool.false_eq_true, ↓reduceIte] at hround
  by_cases hrange : |roundAt fmt target .up| ≤ toReal (posMaxFinite fmt)
  · exact Or.inr (hround.finite hrange)
  · left
    change roundMagnitude fmt .up false compare = _
    rw [hround.overflow (not_le.mp hrange)]
    simp [directedOverflow, IEEERoundingMode.overflowRoundsMagnitudeUp,
      IEEERoundingMode.roundsAwayFromZero, nativeOverflow_eq_signedInf_of_isIEEE fmt hfmt]

/-- A positive target at most the largest finite value has a finite upward comparison rounding. -/
theorem roundUp_finite_roundAt_of_le_posMaxFinite (fmt : FloatFormat)
    (compare : Rat → Ordering) (target : ℝ) (hpositive : 0 < target)
    (hcompare : ∀ candidate : Rat, compare candidate = cmp target (candidate : ℝ))
    (hbound : target ≤ toReal (posMaxFinite fmt)) :
    isFinite (roundUp fmt compare) = true ∧
      toReal (roundUp fmt compare) = roundAt fmt target .up := by
  have hround := roundMagnitude_roundsTo (fmt := fmt) .up false compare hpositive hcompare
  simp only [Bool.false_eq_true, ↓reduceIte] at hround
  apply hround.finite
  have hnonneg : 0 ≤ roundAt fmt target .up := by
    simpa only [roundAt_zero] using roundAt_mono fmt hpositive.le .up
  rw [abs_of_nonneg hnonneg]
  have h := roundAt_mono fmt hbound .up
  rwa [roundAt_of_genericFormat fmt
    (toReal_genericFormat_of_isFinite _ (isFinite_posMaxFinite fmt)) .up] at h

end FloatLib.Floats.Formats.BinaryInterchange.Model.AlgebraicRounding
