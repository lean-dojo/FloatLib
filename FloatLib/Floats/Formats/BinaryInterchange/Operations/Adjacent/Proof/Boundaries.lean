/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Adjacent.Proof.Core

/-!
# Boundary behavior of adjacent-value operations

These theorems describe `nextUp` and `nextDown` at NaNs, zeros, infinities, and saturating finite
endpoints. They also extend the exact rank-step results from `Adjacent.Proof.Core` to one-sided
rank inequalities that remain valid at fixed endpoints.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-! ## Exceptional values and boundaries -/

/-- On a NaN, `nextUp` returns the format's `quietNaN` result. -/
theorem nextUp_of_isNaN {fmt : FloatFormat} (x : Model fmt)
    (hx : isNaN x = true) :
  nextUp x = quietNaN x := by
  simp [nextUp, hx]

/-- On a NaN, `nextDown` returns the format's `quietNaN` result. -/
theorem nextDown_of_isNaN {fmt : FloatFormat} (x : Model fmt)
    (hx : isNaN x = true) :
  nextDown x = quietNaN x := by
  simp [nextDown, hx]

/-- Positive infinity is the fixed upper endpoint of `nextUp`. -/
theorem nextUp_of_isInf_of_signBit_eq_false
    {fmt : FloatFormat} (x : Model fmt)
    (hinf : isInf x = true) (hsign : signBit x = false) :
    nextUp x = x := by
  have hnan := isNaN_eq_false_of_isInf_eq_true x hinf
  simp [nextUp, hnan, hinf, hsign]

/-- Negative infinity is the fixed lower endpoint of `nextDown`. -/
theorem nextDown_of_isInf_of_signBit_eq_true
    {fmt : FloatFormat} (x : Model fmt)
    (hinf : isInf x = true) (hsign : signBit x = true) :
    nextDown x = x := by
  have hnan := isNaN_eq_false_of_isInf_eq_true x hinf
  simp [nextDown, hnan, hinf, hsign]

/-- Both signed zeros step upward to the least positive subnormal. -/
theorem nextUp_of_isZero {fmt : FloatFormat} (x : Model fmt)
    (hx : isZero x = true) :
    nextUp x = posMinSubnormal fmt := by
  have hfinite := isFinite_eq_true_of_isZero_eq_true x hx
  have hnan := isNaN_eq_false_of_isFinite_eq_true x hfinite
  have hinf := isInf_eq_false_of_isFinite_eq_true x hfinite
  simp [nextUp, hx, hnan, hinf]

/-- Both signed zeros step downward to the negative subnormal of least magnitude. -/
theorem nextDown_of_isZero {fmt : FloatFormat} (x : Model fmt)
    (hx : isZero x = true) :
    nextDown x = negMinSubnormal fmt := by
  have hfinite := isFinite_eq_true_of_isZero_eq_true x hx
  have hnan := isNaN_eq_false_of_isFinite_eq_true x hfinite
  have hinf := isInf_eq_false_of_isFinite_eq_true x hfinite
  simp [nextDown, hx, hnan, hinf]

/--
An unsigned-zero format steps directly from its negative subnormal of least magnitude to zero,
skipping the reserved sign-mask NaN word.
-/
theorem nextUp_negMinSubnormal_of_not_supportsSignedZero
    (fmt : FloatFormat) (hfmt : fmt.supportsSignedZero = false) :
    nextUp (negMinSubnormal fmt) = posZero fmt := by
  simp [nextUp, hfmt]

/-- A format without infinity saturates `nextUp` at its largest finite value. -/
theorem nextUp_posMaxFinite_of_not_supportsInfinity
    (fmt : FloatFormat) (hfmt : fmt.supportsInfinity = false) :
    nextUp (posMaxFinite fmt) = posMaxFinite fmt := by
  have hbits :
      (maxFinite fmt false).bits ≠ (negMinSubnormal fmt).bits := by
    intro hequal
    have hsign :=
      congrArg
        (fun bits => (bits &&& FloatFormat.signMask fmt) != 0)
        hequal
    change
      signBit (maxFinite fmt false) =
        signBit (negMinSubnormal fmt) at hsign
    simp at hsign
  by_cases hsigned : fmt.supportsSignedZero = true
  · simp [nextUp, hfmt, hsigned, posMaxFinite]
  · have hsignedFalse := Bool.eq_false_of_not_eq_true hsigned
    simp [nextUp, hfmt, hsignedFalse, hbits, posMaxFinite]

/-- A format without infinity saturates `nextDown` at its most negative finite value. -/
theorem nextDown_negMaxFinite_of_not_supportsInfinity
    (fmt : FloatFormat) (hfmt : fmt.supportsInfinity = false) :
    nextDown (negMaxFinite fmt) = negMaxFinite fmt := by
  simp [nextDown, hfmt, negMaxFinite]

/-- A represented positive infinity is fixed by `nextUp`. -/
theorem nextUp_posInf_of_supportsInfinity
    (fmt : FloatFormat) (hfmt : fmt.supportsInfinity = true) :
    nextUp (posInf fmt) = posInf fmt := by
  have hinf := isInf_posInf fmt hfmt
  have hnan := isNaN_posInf fmt hfmt
  simp [nextUp, hinf, hnan]

/-- A represented negative infinity is fixed by `nextDown`. -/
theorem nextDown_negInf_of_supportsInfinity
    (fmt : FloatFormat) (hfmt : fmt.supportsInfinity = true) :
    nextDown (negInf fmt) = negInf fmt := by
  have hinf := isInf_negInf fmt hfmt
  have hnan := isNaN_negInf fmt hfmt
  simp [nextDown, hinf, hnan]

/-! ## Rank inequalities including saturating endpoints -/

/--
For every non-NaN value, `nextUp` never decreases the adjacency rank.

Ordinary values advance exactly one rank. Positive infinity and the largest finite value of a
format without infinity are fixed points, so the inequality becomes equality at those endpoints.
-/
theorem adjacencyRank_le_nextUp
    {fmt : FloatFormat} (x : Model fmt)
    (hnan : isNaN x = false) :
    adjacencyRank x ≤ adjacencyRank (nextUp x) := by
  by_cases hpositiveInfinity :
      isInf x = true ∧ signBit x = false
  · rw [nextUp_of_isInf_of_signBit_eq_false
      x hpositiveInfinity.1 hpositiveInfinity.2]
  · by_cases hupperEndpoint :
        fmt.supportsInfinity = false ∧
          x = posMaxFinite fmt
    · rw [hupperEndpoint.2,
        nextUp_posMaxFinite_of_not_supportsInfinity
          fmt hupperEndpoint.1]
    · have hinfinity :
          isInf x = true → signBit x = true := by
        intro hinf
        cases hsign : signBit x
        · exact (hpositiveInfinity ⟨hinf, hsign⟩).elim
        · rfl
      have hmax :
          fmt.supportsInfinity = false →
            x ≠ posMaxFinite fmt := by
        intro hnoInfinity hvalue
        exact hupperEndpoint ⟨hnoInfinity, hvalue⟩
      have hstep :=
        adjacencyRank_nextUp x hnan hinfinity hmax
      omega

/--
For every non-NaN value, `nextDown` never increases the adjacency rank.

Ordinary values retreat exactly one rank. Negative infinity and the most negative finite value of
a format without infinity are fixed points, so the inequality becomes equality at those endpoints.
-/
theorem adjacencyRank_nextDown_le
    {fmt : FloatFormat} (x : Model fmt)
    (hnan : isNaN x = false) :
    adjacencyRank (nextDown x) ≤ adjacencyRank x := by
  by_cases hnegativeInfinity :
      isInf x = true ∧ signBit x = true
  · rw [nextDown_of_isInf_of_signBit_eq_true
      x hnegativeInfinity.1 hnegativeInfinity.2]
  · by_cases hlowerEndpoint :
        fmt.supportsInfinity = false ∧
          x = negMaxFinite fmt
    · rw [hlowerEndpoint.2,
        nextDown_negMaxFinite_of_not_supportsInfinity
          fmt hlowerEndpoint.1]
    · have hinfinity :
          isInf x = true → signBit x = false := by
        intro hinf
        cases hsign : signBit x
        · rfl
        · exact (hnegativeInfinity ⟨hinf, hsign⟩).elim
      have hmin :
          fmt.supportsInfinity = false →
            x ≠ negMaxFinite fmt := by
        intro hnoInfinity hvalue
        exact hlowerEndpoint ⟨hnoInfinity, hvalue⟩
      have hstep :=
        adjacencyRank_nextDown x hnan hinfinity hmin
      omega

end Model
end FloatLib.Floats.Formats.BinaryInterchange
