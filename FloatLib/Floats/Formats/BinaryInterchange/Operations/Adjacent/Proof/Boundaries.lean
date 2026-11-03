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
rank inequalities and to the absence of a rank strictly between a value and its neighbor, which
hold at the fixed endpoints too. Through the rank order of `adjacencyRank_lt_adjacencyRank_iff`
these become statements about values: away from its fixed points `nextUp` strictly increases a
number and `nextDown` strictly decreases it, and no non-NaN value lies strictly between a number
and either neighbor (`no_value_between_nextUp`, `no_value_between_nextDown`).
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-! ## Exceptional values and boundaries -/

/-- On a NaN, `nextUp` returns the format's `quietNaN` result. -/
theorem nextUp_of_isNaN {fmt : FloatFormat} (x : Model fmt)
    (hx : isNaN x = true) :
  nextUp x = quietNaN x := by
  simp [nextUp, Internal.Value.nextUp, hx]

/-- On a NaN, `nextDown` returns the format's `quietNaN` result. -/
theorem nextDown_of_isNaN {fmt : FloatFormat} (x : Model fmt)
    (hx : isNaN x = true) :
  nextDown x = quietNaN x := by
  simp [nextDown, Internal.Value.nextDown, hx]

/-- Positive infinity is the fixed upper endpoint of `nextUp`. -/
theorem nextUp_of_isInf_of_signBit_eq_false
    {fmt : FloatFormat} (x : Model fmt)
    (hinf : isInf x = true) (hsign : signBit x = false) :
    nextUp x = x := by
  have hnan := isNaN_eq_false_of_isInf_eq_true x hinf
  simp [nextUp, Internal.Value.nextUp, hnan, hinf, hsign]

/-- Negative infinity is the fixed lower endpoint of `nextDown`. -/
theorem nextDown_of_isInf_of_signBit_eq_true
    {fmt : FloatFormat} (x : Model fmt)
    (hinf : isInf x = true) (hsign : signBit x = true) :
    nextDown x = x := by
  have hnan := isNaN_eq_false_of_isInf_eq_true x hinf
  simp [nextDown, Internal.Value.nextDown, hnan, hinf, hsign]

/-- Both signed zeros step upward to the least positive subnormal. -/
theorem nextUp_of_isZero {fmt : FloatFormat} (x : Model fmt)
    (hx : isZero x = true) :
    nextUp x = posMinSubnormal fmt := by
  have hfinite := isFinite_eq_true_of_isZero_eq_true x hx
  have hnan := isNaN_eq_false_of_isFinite_eq_true x hfinite
  have hinf := isInf_eq_false_of_isFinite_eq_true x hfinite
  simp [nextUp, Internal.Value.nextUp, hx, hnan, hinf]

/-- Both signed zeros step downward to the negative subnormal of least magnitude. -/
theorem nextDown_of_isZero {fmt : FloatFormat} (x : Model fmt)
    (hx : isZero x = true) :
    nextDown x = negMinSubnormal fmt := by
  have hfinite := isFinite_eq_true_of_isZero_eq_true x hx
  have hnan := isNaN_eq_false_of_isFinite_eq_true x hfinite
  have hinf := isInf_eq_false_of_isFinite_eq_true x hfinite
  simp [nextDown, Internal.Value.nextDown, hx, hnan, hinf]

/--
An unsigned-zero format steps directly from its negative subnormal of least magnitude to zero,
skipping the reserved sign-mask NaN word.
-/
theorem nextUp_negMinSubnormal_of_not_supportsSignedZero
    (fmt : FloatFormat) (hfmt : fmt.supportsSignedZero = false) :
    nextUp (negMinSubnormal fmt) = posZero fmt := by
  simp [nextUp, Internal.Value.nextUp, hfmt]

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
  · simp [nextUp, Internal.Value.nextUp, hfmt, hsigned, posMaxFinite]
  · have hsignedFalse := Bool.eq_false_of_not_eq_true hsigned
    simp [nextUp, Internal.Value.nextUp, hfmt, hsignedFalse, hbits, posMaxFinite]

/-- A format without infinity saturates `nextDown` at its most negative finite value. -/
theorem nextDown_negMaxFinite_of_not_supportsInfinity
    (fmt : FloatFormat) (hfmt : fmt.supportsInfinity = false) :
    nextDown (negMaxFinite fmt) = negMaxFinite fmt := by
  simp [nextDown, Internal.Value.nextDown, hfmt, negMaxFinite]

/-- A represented positive infinity is fixed by `nextUp`. -/
theorem nextUp_posInf_of_supportsInfinity
    (fmt : FloatFormat) (hfmt : fmt.supportsInfinity = true) :
    nextUp (posInf fmt) = posInf fmt := by
  have hinf := isInf_posInf fmt hfmt
  have hnan := isNaN_posInf fmt
  simp [nextUp, Internal.Value.nextUp, hinf, hnan]

/-- A represented negative infinity is fixed by `nextDown`. -/
theorem nextDown_negInf_of_supportsInfinity
    (fmt : FloatFormat) (hfmt : fmt.supportsInfinity = true) :
    nextDown (negInf fmt) = negInf fmt := by
  have hinf := isInf_negInf fmt hfmt
  have hnan := isNaN_negInf fmt
  simp [nextDown, Internal.Value.nextDown, hinf, hnan]

/-! ## Rank inequalities including saturating endpoints -/

/--
For a non-NaN value, `nextUp` either fixes it or advances its adjacency rank by exactly one. The
fixed points are positive infinity and the largest finite value of a format without infinity.
-/
theorem nextUp_eq_self_or_adjacencyRank_nextUp
    {fmt : FloatFormat} (x : Model fmt)
    (hnan : isNaN x = false) :
    nextUp x = x ∨ adjacencyRank (nextUp x) = adjacencyRank x + 1 := by
  by_cases hpositiveInfinity :
      isInf x = true ∧ signBit x = false
  · exact Or.inl (nextUp_of_isInf_of_signBit_eq_false
      x hpositiveInfinity.1 hpositiveInfinity.2)
  · by_cases hupperEndpoint :
        fmt.supportsInfinity = false ∧
          x = posMaxFinite fmt
    · left
      rw [hupperEndpoint.2,
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
      exact Or.inr (adjacencyRank_nextUp x hnan hinfinity hmax)

/--
For every non-NaN value, `nextUp` never decreases the adjacency rank.

Ordinary values advance exactly one rank. Positive infinity and the largest finite value of a
format without infinity are fixed points, so the inequality becomes equality at those endpoints.
-/
theorem adjacencyRank_le_nextUp
    {fmt : FloatFormat} (x : Model fmt)
    (hnan : isNaN x = false) :
    adjacencyRank x ≤ adjacencyRank (nextUp x) := by
  rcases nextUp_eq_self_or_adjacencyRank_nextUp x hnan with hfixed | hstep
  · rw [hfixed]
  · omega

/--
No adjacency rank lies strictly between a non-NaN value and its `nextUp` result, including the
fixed endpoints. The statement is about ranks only; `no_value_between_nextUp` is its reading for
values.
-/
theorem no_rank_between_nextUp
    {fmt : FloatFormat} (x : Model fmt)
    (hnan : isNaN x = false) :
    ¬ ∃ y : Model fmt,
        adjacencyRank x < adjacencyRank y ∧
          adjacencyRank y < adjacencyRank (nextUp x) := by
  rcases nextUp_eq_self_or_adjacencyRank_nextUp x hnan with hfixed | hstep
  · rw [hfixed]
    omega
  · rw [hstep]
    omega

/--
For a non-NaN value, `nextDown` either fixes it or retreats its adjacency rank by exactly one. The
fixed points are negative infinity and the most negative finite value of a format without
infinity.
-/
theorem nextDown_eq_self_or_adjacencyRank_nextDown
    {fmt : FloatFormat} (x : Model fmt)
    (hnan : isNaN x = false) :
    nextDown x = x ∨ adjacencyRank (nextDown x) + 1 = adjacencyRank x := by
  by_cases hnegativeInfinity :
      isInf x = true ∧ signBit x = true
  · exact Or.inl (nextDown_of_isInf_of_signBit_eq_true
      x hnegativeInfinity.1 hnegativeInfinity.2)
  · by_cases hlowerEndpoint :
        fmt.supportsInfinity = false ∧
          x = negMaxFinite fmt
    · left
      rw [hlowerEndpoint.2,
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
      exact Or.inr (adjacencyRank_nextDown x hnan hinfinity hmin)

/--
For every non-NaN value, `nextDown` never increases the adjacency rank.

Ordinary values retreat exactly one rank. Negative infinity and the most negative finite value of
a format without infinity are fixed points, so the inequality becomes equality at those endpoints.
-/
theorem adjacencyRank_nextDown_le
    {fmt : FloatFormat} (x : Model fmt)
    (hnan : isNaN x = false) :
    adjacencyRank (nextDown x) ≤ adjacencyRank x := by
  rcases nextDown_eq_self_or_adjacencyRank_nextDown x hnan with hfixed | hstep
  · rw [hfixed]
  · omega

/--
No adjacency rank lies strictly between a `nextDown` result and its non-NaN input, including the
fixed endpoints. The statement is about ranks only; `no_value_between_nextDown` is its reading for
values.
-/
theorem no_rank_between_nextDown
    {fmt : FloatFormat} (x : Model fmt)
    (hnan : isNaN x = false) :
    ¬ ∃ y : Model fmt,
        adjacencyRank (nextDown x) < adjacencyRank y ∧
          adjacencyRank y < adjacencyRank x := by
  rcases nextDown_eq_self_or_adjacencyRank_nextDown x hnan with hfixed | hstep
  · rw [hfixed]
    omega
  · rw [← hstep]
    omega

/-! ## Numerical adjacency -/

/--
Away from NaNs and a saturating positive endpoint, `nextUp` returns a strictly greater value in
the extended reals. The premises are those of `adjacencyRank_nextUp`.
-/
theorem toEReal_lt_toEReal_nextUp
    {fmt : FloatFormat} (x : Model fmt)
    (hnan : isNaN x = false)
    (hinfinity : isInf x = true → signBit x = true)
    (hmax : fmt.supportsInfinity = false → x ≠ posMaxFinite fmt) :
    toEReal x < toEReal (nextUp x) := by
  have hnext : isNaN (nextUp x) = false := by rw [isNaN_nextUp, hnan]
  rw [← adjacencyRank_lt_adjacencyRank_iff hnan hnext, adjacencyRank_nextUp x hnan hinfinity hmax]
  omega

/-- For every non-NaN value, `nextUp` never decreases the value in the extended reals. -/
theorem toEReal_le_toEReal_nextUp
    {fmt : FloatFormat} (x : Model fmt) (hnan : isNaN x = false) :
    toEReal x ≤ toEReal (nextUp x) := by
  have hnext : isNaN (nextUp x) = false := by rw [isNaN_nextUp, hnan]
  rw [← adjacencyRank_le_adjacencyRank_iff hnan hnext]
  exact adjacencyRank_le_nextUp x hnan

/--
No non-NaN value lies strictly between a non-NaN value and its `nextUp` result in the extended
reals. With `toEReal_lt_toEReal_nextUp`, `nextUp x` is the least value above an ordinary `x`.
-/
theorem no_value_between_nextUp
    {fmt : FloatFormat} (x : Model fmt) (hnan : isNaN x = false) :
    ¬ ∃ y : Model fmt,
        isNaN y = false ∧ toEReal x < toEReal y ∧ toEReal y < toEReal (nextUp x) := by
  rintro ⟨y, hy, hxy, hyx⟩
  have hnext : isNaN (nextUp x) = false := by rw [isNaN_nextUp, hnan]
  exact no_rank_between_nextUp x hnan ⟨y, (adjacencyRank_lt_adjacencyRank_iff hnan hy).2 hxy,
    (adjacencyRank_lt_adjacencyRank_iff hy hnext).2 hyx⟩

/--
Away from NaNs and a saturating negative endpoint, `nextDown` returns a strictly smaller value in
the extended reals. The premises are those of `adjacencyRank_nextDown`.
-/
theorem toEReal_nextDown_lt_toEReal
    {fmt : FloatFormat} (x : Model fmt)
    (hnan : isNaN x = false)
    (hinfinity : isInf x = true → signBit x = false)
    (hmin : fmt.supportsInfinity = false → x ≠ negMaxFinite fmt) :
    toEReal (nextDown x) < toEReal x := by
  have hnext : isNaN (nextDown x) = false := by rw [isNaN_nextDown, hnan]
  rw [← adjacencyRank_lt_adjacencyRank_iff hnext hnan,
    ← adjacencyRank_nextDown x hnan hinfinity hmin]
  omega

/-- For every non-NaN value, `nextDown` never increases the value in the extended reals. -/
theorem toEReal_nextDown_le_toEReal
    {fmt : FloatFormat} (x : Model fmt) (hnan : isNaN x = false) :
    toEReal (nextDown x) ≤ toEReal x := by
  have hnext : isNaN (nextDown x) = false := by rw [isNaN_nextDown, hnan]
  rw [← adjacencyRank_le_adjacencyRank_iff hnext hnan]
  exact adjacencyRank_nextDown_le x hnan

/--
No non-NaN value lies strictly between a `nextDown` result and its non-NaN input in the extended
reals. With `toEReal_nextDown_lt_toEReal`, `nextDown x` is the greatest value below an ordinary
`x`.
-/
theorem no_value_between_nextDown
    {fmt : FloatFormat} (x : Model fmt) (hnan : isNaN x = false) :
    ¬ ∃ y : Model fmt,
        isNaN y = false ∧ toEReal (nextDown x) < toEReal y ∧ toEReal y < toEReal x := by
  rintro ⟨y, hy, hxy, hyx⟩
  have hnext : isNaN (nextDown x) = false := by rw [isNaN_nextDown, hnan]
  exact no_rank_between_nextDown x hnan ⟨y, (adjacencyRank_lt_adjacencyRank_iff hnext hy).2 hxy,
    (adjacencyRank_lt_adjacencyRank_iff hy hnan).2 hyx⟩

end Model
end FloatLib.Floats.Formats.BinaryInterchange
