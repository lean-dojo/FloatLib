/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Certified.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Contract
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Enclosure.Proof
public import FloatLib.Numerics.Exact.Elementary.Proof
public import FloatLib.Numerics.Enclosure.Elementary.BinaryGridProof
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Correct rounding of accepted binary exponential and logarithm results

Taylor enclosure bounds and exact decoding prove that each returned encoding is finite and equals
nearest-even rounding of the real function. The domain certificates instantiate the existing
finite-real contract on the executable success predicate.

These are partial-correctness theorems: they describe a result whenever the kernel returns
`some`, and no theorem says which inputs succeed. The one proved success is the signed-zero
passthrough of `expMinus1` and `logPlus1`; `exp` and `log` have no proved success case.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals.Certified

open FloatLib.Numerics

private theorem half_lt_log_two : (1 / 2 : ℝ) < Real.log 2 :=
  lt_trans (by norm_num) Real.log_two_gt_d9

private theorem underflow_lt_exp {fmt : FloatFormat} {argument : ℚ}
    (hargument : expUnderflowArgumentBound fmt ≤ argument) :
    ((expUnderflowInterval fmt).hi : ℝ) < Real.exp (argument : ℝ) := by
  have hscale : fmt.minSubnormalExponent - 1 < 0 := by
    have := fmt.exponentBias_pos
    have := fmt.fracWidth_pos
    simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
      Int.ofNat_eq_natCast]
    omega
  simp only [expUnderflowArgumentBound] at hargument
  simp only [expUnderflowInterval, Dyadic.cast_toRat, Dyadic.toReal_mk_false,
    Nat.cast_one, one_mul]
  rw [← Real.log_lt_iff_lt_exp (by positivity), Real.log_zpow]
  calc
    ((fmt.minSubnormalExponent - 1 : ℤ) : ℝ) * Real.log 2 <
        ((fmt.minSubnormalExponent - 1 : ℤ) : ℝ) * (1 / 2) :=
      mul_lt_mul_of_neg_left half_lt_log_two (by exact_mod_cast hscale)
    _ = ((fmt.minSubnormalExponent - 1 : ℤ) : ℝ) / 2 := by ring
    _ ≤ (argument : ℝ) := by exact_mod_cast hargument

private theorem exp_lt_upper {fmt : FloatFormat} {argument : ℚ}
    (hfmt : fmt.isIEEE = true) (hargument : argument ≤ expUpperArgumentBound fmt) :
    Real.exp (argument : ℝ) < (expUpperBound fmt : ℝ) := by
  have hscale : 0 < fmt.maxNormalExponent + 1 := by
    rw [FloatFormat.maxNormalExponent_eq_ieee fmt hfmt]
    simp only [FloatFormat.ieeeMaxNormalExponent, Int.ofNat_eq_natCast]
    omega
  simp only [expUpperArgumentBound] at hargument
  simp only [expUpperBound, Dyadic.cast_toRat, Dyadic.toReal_mk_false,
    Nat.cast_one, one_mul]
  rw [← Real.lt_log_iff_exp_lt (by positivity), Real.log_zpow]
  calc
    (argument : ℝ) ≤ ((fmt.maxNormalExponent + 1 : ℤ) : ℝ) / 2 := by exact_mod_cast hargument
    _ = ((fmt.maxNormalExponent + 1 : ℤ) : ℝ) * (1 / 2) := by ring
    _ < ((fmt.maxNormalExponent + 1 : ℤ) : ℝ) * Real.log 2 :=
      mul_lt_mul_of_pos_left half_lt_log_two (by exact_mod_cast hscale)

private theorem expUnderflow_guard_iff (fmt : FloatFormat) (argument : ℚ) :
    (argument < expUnderflowArgumentBound fmt ∧
      ElementaryComparison.compareExp argument (expUnderflowInterval fmt).hi ≠ .gt) ↔
      ElementaryComparison.compareExp argument (expUnderflowInterval fmt).hi ≠ .gt := by
  refine ⟨And.right, fun hcompare => ⟨?_, hcompare⟩⟩
  by_contra hargument
  apply hcompare
  rw [ElementaryComparison.compareExp_eq_real, cmp_eq_gt_iff]
  exact underflow_lt_exp (le_of_not_gt hargument)

private theorem expUpper_guard_iff {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (argument boundary : ℚ) (hboundary : expUpperBound fmt ≤ boundary) :
    (expUpperArgumentBound fmt < argument ∧
      ElementaryComparison.compareExp argument boundary ≠ .lt) ↔
      ElementaryComparison.compareExp argument boundary ≠ .lt := by
  refine ⟨And.right, fun hcompare => ⟨?_, hcompare⟩⟩
  by_contra hargument
  apply hcompare
  rw [ElementaryComparison.compareExp_eq_real, cmp_eq_lt_iff]
  exact (exp_lt_upper hfmt (le_of_not_gt hargument)).trans_le (by exact_mod_cast hboundary)

/--
The rational argument checks preserve the original guarded exponential for every attempt budget,
including zero attempts and formats outside the supported domain.
-/
theorem expRat_eq_guarded (fmt : FloatFormat) (argument : ℚ) (options : Options) :
    expRat fmt argument options =
      if !fmt.isIEEE then none
      else if argument = 0 then Enclosure.round? fmt (RationalInterval.point 1)
      else if ElementaryComparison.compareExp argument (expUnderflowInterval fmt).hi ≠ .gt then
        Enclosure.round? fmt (expUnderflowInterval fmt)
      else if ElementaryComparison.compareExp argument (expUpperBound fmt) ≠ .lt then none
      else
        refine fmt (FloatLib.Numerics.Enclosure.BinaryGrid.exp argument)
          (max 1 options.initialDegree)
          (FloatLib.Numerics.Enclosure.BinaryGrid.expPrecision
            (fmt.fracWidth + 1) argument (max 1 options.initialDegree))
          options.maxSteps := by
  by_cases hfmt : fmt.isIEEE = true
  · simp only [expRat, expUnderflow_guard_iff,
      expUpper_guard_iff hfmt argument (expUpperBound fmt) le_rfl]
  · simp [expRat, hfmt]

/-- Skipping impossible guards preserves both accepted encodings and `none` for `expMinus1Rat`. -/
theorem expMinus1Rat_eq_guarded (fmt : FloatFormat) (argument : ℚ) (options : Options) :
    expMinus1Rat fmt argument options =
      if !fmt.isIEEE then none
      else if argument = 0 then Enclosure.round? fmt (RationalInterval.point 0)
      else if ElementaryComparison.compareExp argument (expUnderflowInterval fmt).hi ≠ .gt then
        Enclosure.round? fmt ((expUnderflowInterval fmt).sub (RationalInterval.point 1))
      else if ElementaryComparison.compareExp argument (expUpperBound fmt + 1) ≠ .lt then none
      else
        refine fmt
          (fun degree precision => (FloatLib.Numerics.Enclosure.BinaryGrid.exp
            argument degree precision).sub
            (RationalInterval.point 1))
          (max 1 options.initialDegree)
          (FloatLib.Numerics.Enclosure.BinaryGrid.expPrecision
            (fmt.fracWidth + 1) argument (max 1 options.initialDegree) true)
          options.maxSteps := by
  by_cases hfmt : fmt.isIEEE = true
  · simp only [expMinus1Rat, expUnderflow_guard_iff,
      expUpper_guard_iff hfmt argument (expUpperBound fmt + 1) (le_add_of_nonneg_right (by decide))]
  · simp [expMinus1Rat, hfmt]

private theorem exists_enclosure_of_refine_eq_some {fmt : FloatFormat}
    {enclose : Nat → Nat → RationalInterval} {target : ℝ}
    (hcontains : ∀ degree precision, (enclose degree precision).Contains target)
    {degree precision steps : Nat} {result : Model fmt}
    (hresult : refine fmt enclose degree precision steps = some result) :
    ∃ interval : RationalInterval,
      interval.Contains target ∧ Enclosure.round? fmt interval = some result := by
  obtain ⟨degree, precision, haccept⟩ := RationalInterval.exists_of_refine_eq_some hresult
  exact ⟨enclose degree precision, hcontains degree precision, haccept⟩

private theorem exists_enclosure_of_expRat_eq_some {fmt : FloatFormat}
    {argument : ℚ} {options : Options} {result : Model fmt}
    (hresult : expRat fmt argument options = some result) :
    ∃ interval : RationalInterval, interval.Contains (Real.exp (argument : ℝ)) ∧
      Enclosure.round? fmt interval = some result := by
  rw [expRat_eq_guarded] at hresult
  split at hresult
  · simp at hresult
  · split at hresult
    · rename_i hzero
      exact ⟨RationalInterval.point 1,
        by simpa [hzero] using RationalInterval.contains_point (1 : ℚ), hresult⟩
    · split at hresult
      · rename_i hsmall
        simp only [ElementaryComparison.compareExp_eq_real, ne_eq, cmp_eq_gt_iff] at hsmall
        exact ⟨expUnderflowInterval fmt,
          ⟨by simpa [expUnderflowInterval] using (Real.exp_pos (argument : ℝ)).le,
            le_of_not_gt hsmall⟩, hresult⟩
      · split at hresult
        · simp at hresult
        · exact exists_enclosure_of_refine_eq_some
            (fun degree precision =>
              FloatLib.Numerics.Enclosure.BinaryGrid.contains_exp argument degree precision)
            hresult

private theorem exists_enclosure_of_logRat_eq_some {fmt : FloatFormat}
    {argument : ℚ} {options : Options} {result : Model fmt}
    (hresult : logRat fmt argument options = some result) :
    ∃ interval : RationalInterval, interval.Contains (Real.log (argument : ℝ)) ∧
      Enclosure.round? fmt interval = some result := by
  rw [logRat] at hresult
  split at hresult
  · simp at hresult
  · split at hresult
    · simp at hresult
    · rename_i hpositive
      split at hresult
      · rename_i hone
        exact ⟨RationalInterval.point 0,
          by simpa [hone] using RationalInterval.contains_point (0 : ℚ), hresult⟩
      · exact exists_enclosure_of_refine_eq_some
          (fun degree precision => FloatLib.Numerics.Enclosure.BinaryGrid.contains_log
            argument degree precision (lt_of_not_ge hpositive)) hresult

private theorem exists_enclosure_of_expMinus1Rat_eq_some {fmt : FloatFormat}
    {argument : ℚ} {options : Options} {result : Model fmt}
    (hresult : expMinus1Rat fmt argument options = some result) :
    ∃ interval : RationalInterval, interval.Contains (Real.exp (argument : ℝ) - 1) ∧
      Enclosure.round? fmt interval = some result := by
  rw [expMinus1Rat_eq_guarded] at hresult
  split at hresult
  · simp at hresult
  · split at hresult
    · rename_i hzero
      exact ⟨RationalInterval.point 0,
        by simpa [hzero] using RationalInterval.contains_point (0 : ℚ), hresult⟩
    · split at hresult
      · rename_i hsmall
        simp only [ElementaryComparison.compareExp_eq_real, ne_eq, cmp_eq_gt_iff] at hsmall
        have hexp : (expUnderflowInterval fmt).Contains (Real.exp (argument : ℝ)) :=
          ⟨by simpa [expUnderflowInterval] using (Real.exp_pos (argument : ℝ)).le,
            le_of_not_gt hsmall⟩
        exact ⟨_, by simpa using
          RationalInterval.contains_sub hexp (RationalInterval.contains_point 1), hresult⟩
      · split at hresult
        · simp at hresult
        · refine exists_enclosure_of_refine_eq_some ?_ hresult
          intro degree precision
          simpa using RationalInterval.contains_sub
            (FloatLib.Numerics.Enclosure.BinaryGrid.contains_exp argument degree _)
            (RationalInterval.contains_point 1)

/-- Successful rational-input exponentials are finite. -/
theorem isFinite_of_expRat_eq_some {fmt : FloatFormat}
    {argument : ℚ} {options : Options} {result : Model fmt}
    (hresult : expRat fmt argument options = some result) : isFinite result = true := by
  obtain ⟨_, _, haccept⟩ := exists_enclosure_of_expRat_eq_some hresult
  exact Enclosure.isFinite_of_round?_eq_some haccept

/-- An accepted rational exponential equals rounding of the exact real exponential. -/
theorem toReal_of_expRat_eq_some {fmt : FloatFormat}
    {argument : ℚ} {options : Options} {result : Model fmt}
    (hresult : expRat fmt argument options = some result) :
    toReal result = roundAt fmt (Real.exp (argument : ℝ)) := by
  obtain ⟨_, hcontains, haccept⟩ := exists_enclosure_of_expRat_eq_some hresult
  exact Enclosure.toReal_eq_roundAt_of_round?_eq_some hcontains haccept

/-- Successful rational-input logarithms are finite. -/
theorem isFinite_of_logRat_eq_some {fmt : FloatFormat}
    {argument : ℚ} {options : Options} {result : Model fmt}
    (hresult : logRat fmt argument options = some result) : isFinite result = true := by
  obtain ⟨_, _, haccept⟩ := exists_enclosure_of_logRat_eq_some hresult
  exact Enclosure.isFinite_of_round?_eq_some haccept

/-- An accepted rational logarithm equals rounding of the exact real logarithm. -/
theorem toReal_of_logRat_eq_some {fmt : FloatFormat}
    {argument : ℚ} {options : Options} {result : Model fmt}
    (hresult : logRat fmt argument options = some result) :
    toReal result = roundAt fmt (Real.log (argument : ℝ)) := by
  obtain ⟨_, hcontains, haccept⟩ := exists_enclosure_of_logRat_eq_some hresult
  exact Enclosure.toReal_eq_roundAt_of_round?_eq_some hcontains haccept

/-- Successful rational-input `expMinus1` results are finite. -/
theorem isFinite_of_expMinus1Rat_eq_some {fmt : FloatFormat}
    {argument : ℚ} {options : Options} {result : Model fmt}
    (hresult : expMinus1Rat fmt argument options = some result) : isFinite result = true := by
  obtain ⟨_, _, haccept⟩ := exists_enclosure_of_expMinus1Rat_eq_some hresult
  exact Enclosure.isFinite_of_round?_eq_some haccept

/-- The subtraction takes place in the exact real expression, before its only rounding. -/
theorem toReal_of_expMinus1Rat_eq_some {fmt : FloatFormat}
    {argument : ℚ} {options : Options} {result : Model fmt}
    (hresult : expMinus1Rat fmt argument options = some result) :
    toReal result = roundAt fmt (Real.exp (argument : ℝ) - 1) := by
  obtain ⟨_, hcontains, haccept⟩ := exists_enclosure_of_expMinus1Rat_eq_some hresult
  exact Enclosure.toReal_eq_roundAt_of_round?_eq_some hcontains haccept

/-- Successful rational-input `logPlus1` results are finite. -/
theorem isFinite_of_logPlus1Rat_eq_some {fmt : FloatFormat}
    {argument : ℚ} {options : Options} {result : Model fmt}
    (hresult : logPlus1Rat fmt argument options = some result) : isFinite result = true :=
  isFinite_of_logRat_eq_some hresult

/-- Forming `1 + argument` exactly avoids an intermediate floating-point rounding. -/
theorem toReal_of_logPlus1Rat_eq_some {fmt : FloatFormat}
    {argument : ℚ} {options : Options} {result : Model fmt}
    (hresult : logPlus1Rat fmt argument options = some result) :
    toReal result = roundAt fmt (Real.log (1 + (argument : ℝ))) := by
  simpa only [Rat.cast_add, Rat.cast_one] using toReal_of_logRat_eq_some hresult

private theorem toReal_of_toRat?_eq_some {fmt : FloatFormat}
    {input : Model fmt} {argument : ℚ} (hinput : toRat? input = some argument) :
    toReal input = (argument : ℝ) := by
  cases hdecode : toDyadic? input with
  | none => simp [toRat?, hdecode] at hinput
  | some exact =>
      have hvalue : exact.toRat = argument := by simpa [toRat?, hdecode] using hinput
      rw [toReal_eq, hdecode, ← hvalue, Numerics.Dyadic.cast_toRat]

/-- Every exponential result returned by the concrete refinement algorithm is finite. -/
theorem isFinite_of_exp_eq_some {fmt : FloatFormat}
    {input result : Model fmt} {options : Options}
    (hresult : exp input options = some result) : isFinite result = true := by
  unfold exp at hresult
  cases hinput : toRat? input with
  | none => simp [hinput] at hresult
  | some argument =>
      rw [hinput] at hresult
      exact isFinite_of_expRat_eq_some hresult

/-- The concrete exponential kernel certifies nearest-even rounding of the exact input's exp. -/
theorem toReal_of_exp_eq_some {fmt : FloatFormat}
    {input result : Model fmt} {options : Options}
    (hresult : exp input options = some result) :
    toReal result = roundAt fmt (Real.exp (toReal input)) := by
  unfold exp at hresult
  cases hinput : toRat? input with
  | none => simp [hinput] at hresult
  | some argument =>
      rw [hinput] at hresult
      rw [toReal_of_toRat?_eq_some hinput]
      exact toReal_of_expRat_eq_some hresult

/-- Every logarithm result returned by the concrete refinement algorithm is finite. -/
theorem isFinite_of_log_eq_some {fmt : FloatFormat}
    {input result : Model fmt} {options : Options}
    (hresult : log input options = some result) : isFinite result = true := by
  unfold log at hresult
  cases hinput : toRat? input with
  | none => simp [hinput] at hresult
  | some argument =>
      rw [hinput] at hresult
      exact isFinite_of_logRat_eq_some hresult

/-- The concrete logarithm kernel certifies nearest-even rounding of the exact input's log. -/
theorem toReal_of_log_eq_some {fmt : FloatFormat}
    {input result : Model fmt} {options : Options}
    (hresult : log input options = some result) :
    toReal result = roundAt fmt (Real.log (toReal input)) := by
  unfold log at hresult
  cases hinput : toRat? input with
  | none => simp [hinput] at hresult
  | some argument =>
      rw [hinput] at hresult
      rw [toReal_of_toRat?_eq_some hinput]
      exact toReal_of_logRat_eq_some hresult

private theorem toReal_eq_zero_of_isZero {fmt : FloatFormat} {input : Model fmt}
    (hzero : isZero input = true) : toReal input = 0 := by
  rw [toReal_eq, toDyadic?_eq_zero_of_isZero_eq_true input hzero]
  simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand]

/-- Each accepted `expMinus1` result is finite, including the signed-zero branch. -/
theorem isFinite_of_expMinus1_eq_some {fmt : FloatFormat}
    {input result : Model fmt} {options : Options}
    (hresult : expMinus1 input options = some result) : isFinite result = true := by
  unfold expMinus1 at hresult
  split at hresult
  · rename_i hzero
    cases Option.some.inj hresult
    simp only [Bool.and_eq_true] at hzero
    exact isFinite_eq_true_of_isZero_eq_true input hzero.2
  · cases hinput : toRat? input with
    | none => simp [hinput] at hresult
    | some argument =>
        rw [hinput] at hresult
        exact isFinite_of_expMinus1Rat_eq_some hresult

/-- An accepted `expMinus1` equals nearest-even rounding of `Real.exp x - 1`. -/
theorem toReal_of_expMinus1_eq_some {fmt : FloatFormat}
    {input result : Model fmt} {options : Options}
    (hresult : expMinus1 input options = some result) :
    toReal result = roundAt fmt (Real.exp (toReal input) - 1) := by
  unfold expMinus1 at hresult
  split at hresult
  · rename_i hzero
    cases Option.some.inj hresult
    simp only [Bool.and_eq_true] at hzero
    simp [toReal_eq_zero_of_isZero hzero.2]
  · cases hinput : toRat? input with
    | none => simp [hinput] at hresult
    | some argument =>
        rw [hinput] at hresult
        rw [toReal_of_toRat?_eq_some hinput]
        exact toReal_of_expMinus1Rat_eq_some hresult

/-- Each accepted `logPlus1` result is finite, including the signed-zero branch. -/
theorem isFinite_of_logPlus1_eq_some {fmt : FloatFormat}
    {input result : Model fmt} {options : Options}
    (hresult : logPlus1 input options = some result) : isFinite result = true := by
  unfold logPlus1 at hresult
  split at hresult
  · rename_i hzero
    cases Option.some.inj hresult
    simp only [Bool.and_eq_true] at hzero
    exact isFinite_eq_true_of_isZero_eq_true input hzero.2
  · cases hinput : toRat? input with
    | none => simp [hinput] at hresult
    | some argument =>
        rw [hinput] at hresult
        exact isFinite_of_logPlus1Rat_eq_some hresult

/-- An accepted `logPlus1` equals nearest-even rounding of `Real.log (1 + x)`. -/
theorem toReal_of_logPlus1_eq_some {fmt : FloatFormat}
    {input result : Model fmt} {options : Options}
    (hresult : logPlus1 input options = some result) :
    toReal result = roundAt fmt (Real.log (1 + toReal input)) := by
  unfold logPlus1 at hresult
  split at hresult
  · rename_i hzero
    cases Option.some.inj hresult
    simp only [Bool.and_eq_true] at hzero
    simp [toReal_eq_zero_of_isZero hzero.2]
  · cases hinput : toRat? input with
    | none => simp [hinput] at hresult
    | some argument =>
        rw [hinput] at hresult
        rw [toReal_of_toRat?_eq_some hinput]
        exact toReal_of_logPlus1Rat_eq_some hresult

/-- The IEEE input's zero encoding passes through `expMinus1` unchanged. -/
@[simp] theorem expMinus1_of_isZero {fmt : FloatFormat} {input : Model fmt}
    (hfmt : fmt.isIEEE = true) (hzero : isZero input = true) (options : Options) :
    expMinus1 input options = some input := by
  simp [expMinus1, hfmt, hzero]

/-- The IEEE input's zero encoding passes through `logPlus1` unchanged. -/
@[simp] theorem logPlus1_of_isZero {fmt : FloatFormat} {input : Model fmt}
    (hfmt : fmt.isIEEE = true) (hzero : isZero input = true) (options : Options) :
    logPlus1 input options = some input := by
  simp [logPlus1, hfmt, hzero]

/--
The finite-real contract holds on the exponential kernel's executable success domain.
The zero fallback adapts the optional result to the contract's total-function argument.
-/
theorem exp_correctlyRoundedCertificateOn (fmt : FloatFormat) (options : Options) :
    Contract.CorrectlyRoundedCertificateOn fmt Real.exp
      (fun input => (exp input options).getD (zero fmt false))
      (fun input => (exp input options).isSome = true) := by
  constructor
  · intro input _ hsuccess
    cases hresult : exp input options with
    | none => simp [hresult] at hsuccess
    | some result =>
        simpa [hresult] using isFinite_of_exp_eq_some hresult
  · intro input _ hsuccess
    cases hresult : exp input options with
    | none => simp [hresult] at hsuccess
    | some result =>
        simpa [hresult] using toReal_of_exp_eq_some hresult

/-- The existing finite-real contract holds on the inputs accepted by this concrete log kernel. -/
theorem log_correctlyRoundedCertificateOn (fmt : FloatFormat) (options : Options) :
    Contract.CorrectlyRoundedCertificateOn fmt Real.log
      (fun input => (log input options).getD (zero fmt false))
      (fun input => (log input options).isSome = true) := by
  constructor
  · intro input _ hsuccess
    cases hresult : log input options with
    | none => simp [hresult] at hsuccess
    | some result =>
        simpa [hresult] using isFinite_of_log_eq_some hresult
  · intro input _ hsuccess
    cases hresult : log input options with
    | none => simp [hresult] at hsuccess
    | some result =>
        simpa [hresult] using toReal_of_log_eq_some hresult

/-- Correct rounding of `exp x - 1` on the executable acceptance domain. -/
theorem expMinus1_correctlyRoundedCertificateOn (fmt : FloatFormat) (options : Options) :
    Contract.CorrectlyRoundedCertificateOn fmt (fun x => Real.exp x - 1)
      (fun input => (expMinus1 input options).getD (zero fmt false))
      (fun input => (expMinus1 input options).isSome = true) := by
  constructor <;> intro input _ hsuccess <;>
    cases hresult : expMinus1 input options with
    | none => simp [hresult] at hsuccess
    | some result =>
        first
        | simpa [hresult] using isFinite_of_expMinus1_eq_some hresult
        | simpa [hresult] using toReal_of_expMinus1_eq_some hresult

/-- Correct rounding of `log (1 + x)` on the executable acceptance domain. -/
theorem logPlus1_correctlyRoundedCertificateOn (fmt : FloatFormat) (options : Options) :
    Contract.CorrectlyRoundedCertificateOn fmt (fun x => Real.log (1 + x))
      (fun input => (logPlus1 input options).getD (zero fmt false))
      (fun input => (logPlus1 input options).isSome = true) := by
  constructor <;> intro input _ hsuccess <;>
    cases hresult : logPlus1 input options with
    | none => simp [hresult] at hsuccess
    | some result =>
        first
        | simpa [hresult] using isFinite_of_logPlus1_eq_some hresult
        | simpa [hresult] using toReal_of_logPlus1_eq_some hresult

end FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals.Certified
