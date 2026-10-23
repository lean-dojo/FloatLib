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
public import FloatLib.Numerics.Enclosure.Constants.Proof
public import FloatLib.Numerics.Enclosure.Elementary.BinaryGridProof
public import FloatLib.Numerics.Enclosure.Elementary.LogTable.Proof
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Correct rounding of accepted binary exponential, logarithm, and power results

Taylor enclosure bounds and exact decoding prove that each returned encoding is finite and equals
nearest-even rounding of the real function. The domain certificates instantiate the finite-real
contract on the executable success predicate.

For powers, `rpow_eq_exp_reduced` writes `(s * 2 ^ e) ^ b` as `exp (b * log s + (b * e - k) *
log 2) * 2 ^ k` for every integer `k`. The grid enclosures of `log s` and `log 2`, the exponential
enclosure, and the scaled endpoint check `Enclosure.roundScaled?` then give
`toReal_of_powRat_eq_ok` and `toReal_of_pow_eq_ok`.

These are partial-correctness theorems: they describe a result whenever the kernel returns
`.ok`, and no theorem says which inputs succeed. The one proved success is the signed-zero
passthrough of `expMinus1` and `logPlus1`. `exp`, `log`, and `pow` have no proved success case.
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

/-- `accept` succeeds exactly with the certified encoding it was given. -/
@[simp] theorem accept_eq_ok {fmt : FloatFormat} {result : Option (Model fmt)}
    {failure : Failure} {value : Model fmt} :
    accept result failure = .ok value ↔ result = some value := by
  cases result <;> simp [accept]

/--
The rational argument checks preserve the original guarded exponential for every attempt budget,
including zero attempts and formats outside the supported domain.
-/
theorem expRat_eq_guarded (fmt : FloatFormat) (argument : ℚ) (options : Options) :
    expRat fmt argument options =
      if !fmt.isIEEE then .error .unsupportedFormat
      else if argument = 0 then
        accept (Enclosure.round? fmt (RationalInterval.point 1)) .inconclusive
      else if ElementaryComparison.compareExp argument (expUnderflowInterval fmt).hi ≠ .gt then
        accept (Enclosure.round? fmt (expUnderflowInterval fmt)) .inconclusive
      else if ElementaryComparison.compareExp argument (expUpperBound fmt) ≠ .lt then .error .range
      else
        let search := refine fmt (FloatLib.Numerics.Enclosure.BinaryGrid.exp argument)
          (max 1 options.initialDegree)
          (FloatLib.Numerics.Enclosure.BinaryGrid.expPrecision
            (fmt.fracWidth + 1) argument (max 1 options.initialDegree))
          options.maxSteps
        accept search
          (if search.isSome then .inconclusive else expSearchFailure fmt argument 0) := by
  by_cases hfmt : fmt.isIEEE = true
  · simp only [expRat, expUnderflow_guard_iff,
      expUpper_guard_iff hfmt argument (expUpperBound fmt) le_rfl]
  · simp [expRat, hfmt]

/-- Skipping impossible guards preserves both accepted encodings and failures of `expMinus1Rat`. -/
theorem expMinus1Rat_eq_guarded (fmt : FloatFormat) (argument : ℚ) (options : Options) :
    expMinus1Rat fmt argument options =
      if !fmt.isIEEE then .error .unsupportedFormat
      else if argument = 0 then
        accept (Enclosure.round? fmt (RationalInterval.point 0)) .inconclusive
      else if ElementaryComparison.compareExp argument (expUnderflowInterval fmt).hi ≠ .gt then
        accept (Enclosure.round? fmt ((expUnderflowInterval fmt).sub (RationalInterval.point 1)))
          .inconclusive
      else if ElementaryComparison.compareExp argument (expUpperBound fmt + 1) ≠ .lt then
        .error .range
      else
        let search := refine fmt
          (fun degree precision => (FloatLib.Numerics.Enclosure.BinaryGrid.exp
            argument degree precision).sub
            (RationalInterval.point 1))
          (max 1 options.initialDegree)
          (FloatLib.Numerics.Enclosure.BinaryGrid.expPrecision
            (fmt.fracWidth + 1) argument (max 1 options.initialDegree) true)
          options.maxSteps
        accept search
          (if search.isSome then .inconclusive else expSearchFailure fmt argument 1) := by
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

private theorem exists_enclosure_of_expRat_eq_ok {fmt : FloatFormat}
    {argument : ℚ} {options : Options} {result : Model fmt}
    (hresult : expRat fmt argument options = .ok result) :
    ∃ interval : RationalInterval, interval.Contains (Real.exp (argument : ℝ)) ∧
      Enclosure.round? fmt interval = some result := by
  rw [expRat_eq_guarded] at hresult
  split at hresult
  · simp at hresult
  · split at hresult
    · rename_i hzero
      exact ⟨RationalInterval.point 1,
        by simpa [hzero] using RationalInterval.contains_point (1 : ℚ), accept_eq_ok.mp hresult⟩
    · split at hresult
      · rename_i hsmall
        simp only [ElementaryComparison.compareExp_eq_real, ne_eq, cmp_eq_gt_iff] at hsmall
        exact ⟨expUnderflowInterval fmt,
          ⟨by simpa [expUnderflowInterval] using (Real.exp_pos (argument : ℝ)).le,
            le_of_not_gt hsmall⟩, accept_eq_ok.mp hresult⟩
      · split at hresult
        · simp at hresult
        · exact exists_enclosure_of_refine_eq_some
            (fun degree precision =>
              FloatLib.Numerics.Enclosure.BinaryGrid.contains_exp argument degree precision)
            (accept_eq_ok.mp hresult)

private theorem exists_enclosure_of_logRat_eq_ok {fmt : FloatFormat}
    {argument : ℚ} {options : Options} {result : Model fmt}
    (hresult : logRat fmt argument options = .ok result) :
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
          by simpa [hone] using RationalInterval.contains_point (0 : ℚ), accept_eq_ok.mp hresult⟩
      · exact exists_enclosure_of_refine_eq_some
          (fun degree precision => FloatLib.Numerics.Enclosure.BinaryGrid.contains_log
            argument degree precision (lt_of_not_ge hpositive)) (accept_eq_ok.mp hresult)

private theorem exists_enclosure_of_expMinus1Rat_eq_ok {fmt : FloatFormat}
    {argument : ℚ} {options : Options} {result : Model fmt}
    (hresult : expMinus1Rat fmt argument options = .ok result) :
    ∃ interval : RationalInterval, interval.Contains (Real.exp (argument : ℝ) - 1) ∧
      Enclosure.round? fmt interval = some result := by
  rw [expMinus1Rat_eq_guarded] at hresult
  split at hresult
  · simp at hresult
  · split at hresult
    · rename_i hzero
      exact ⟨RationalInterval.point 0,
        by simpa [hzero] using RationalInterval.contains_point (0 : ℚ), accept_eq_ok.mp hresult⟩
    · split at hresult
      · rename_i hsmall
        simp only [ElementaryComparison.compareExp_eq_real, ne_eq, cmp_eq_gt_iff] at hsmall
        have hexp : (expUnderflowInterval fmt).Contains (Real.exp (argument : ℝ)) :=
          ⟨by simpa [expUnderflowInterval] using (Real.exp_pos (argument : ℝ)).le,
            le_of_not_gt hsmall⟩
        exact ⟨_, by simpa using
          RationalInterval.contains_sub hexp (RationalInterval.contains_point 1),
          accept_eq_ok.mp hresult⟩
      · split at hresult
        · simp at hresult
        · refine exists_enclosure_of_refine_eq_some ?_ (accept_eq_ok.mp hresult)
          intro degree precision
          simpa using RationalInterval.contains_sub
            (FloatLib.Numerics.Enclosure.BinaryGrid.contains_exp argument degree _)
            (RationalInterval.contains_point 1)

/-- Successful rational-input exponentials are finite. -/
theorem isFinite_of_expRat_eq_ok {fmt : FloatFormat}
    {argument : ℚ} {options : Options} {result : Model fmt}
    (hresult : expRat fmt argument options = .ok result) : isFinite result = true := by
  obtain ⟨_, _, haccept⟩ := exists_enclosure_of_expRat_eq_ok hresult
  exact Enclosure.isFinite_of_round?_eq_some haccept

/-- An accepted rational exponential equals rounding of the exact real exponential. -/
theorem toReal_of_expRat_eq_ok {fmt : FloatFormat}
    {argument : ℚ} {options : Options} {result : Model fmt}
    (hresult : expRat fmt argument options = .ok result) :
    toReal result = roundAt fmt (Real.exp (argument : ℝ)) := by
  obtain ⟨_, hcontains, haccept⟩ := exists_enclosure_of_expRat_eq_ok hresult
  exact Enclosure.toReal_eq_roundAt_of_round?_eq_some hcontains haccept

/-- Successful rational-input logarithms are finite. -/
theorem isFinite_of_logRat_eq_ok {fmt : FloatFormat}
    {argument : ℚ} {options : Options} {result : Model fmt}
    (hresult : logRat fmt argument options = .ok result) : isFinite result = true := by
  obtain ⟨_, _, haccept⟩ := exists_enclosure_of_logRat_eq_ok hresult
  exact Enclosure.isFinite_of_round?_eq_some haccept

/-- An accepted rational logarithm equals rounding of the exact real logarithm. -/
theorem toReal_of_logRat_eq_ok {fmt : FloatFormat}
    {argument : ℚ} {options : Options} {result : Model fmt}
    (hresult : logRat fmt argument options = .ok result) :
    toReal result = roundAt fmt (Real.log (argument : ℝ)) := by
  obtain ⟨_, hcontains, haccept⟩ := exists_enclosure_of_logRat_eq_ok hresult
  exact Enclosure.toReal_eq_roundAt_of_round?_eq_some hcontains haccept

/-- Successful rational-input `expMinus1` results are finite. -/
theorem isFinite_of_expMinus1Rat_eq_ok {fmt : FloatFormat}
    {argument : ℚ} {options : Options} {result : Model fmt}
    (hresult : expMinus1Rat fmt argument options = .ok result) : isFinite result = true := by
  obtain ⟨_, _, haccept⟩ := exists_enclosure_of_expMinus1Rat_eq_ok hresult
  exact Enclosure.isFinite_of_round?_eq_some haccept

/-- The subtraction takes place in the exact real expression, before its only rounding. -/
theorem toReal_of_expMinus1Rat_eq_ok {fmt : FloatFormat}
    {argument : ℚ} {options : Options} {result : Model fmt}
    (hresult : expMinus1Rat fmt argument options = .ok result) :
    toReal result = roundAt fmt (Real.exp (argument : ℝ) - 1) := by
  obtain ⟨_, hcontains, haccept⟩ := exists_enclosure_of_expMinus1Rat_eq_ok hresult
  exact Enclosure.toReal_eq_roundAt_of_round?_eq_some hcontains haccept

/-- Successful rational-input `logPlus1` results are finite. -/
theorem isFinite_of_logPlus1Rat_eq_ok {fmt : FloatFormat}
    {argument : ℚ} {options : Options} {result : Model fmt}
    (hresult : logPlus1Rat fmt argument options = .ok result) : isFinite result = true :=
  isFinite_of_logRat_eq_ok hresult

/-- Forming `1 + argument` exactly avoids an intermediate floating-point rounding. -/
theorem toReal_of_logPlus1Rat_eq_ok {fmt : FloatFormat}
    {argument : ℚ} {options : Options} {result : Model fmt}
    (hresult : logPlus1Rat fmt argument options = .ok result) :
    toReal result = roundAt fmt (Real.log (1 + (argument : ℝ))) := by
  simpa only [Rat.cast_add, Rat.cast_one] using toReal_of_logRat_eq_ok hresult

private theorem toReal_of_toRat?_eq_some {fmt : FloatFormat}
    {input : Model fmt} {argument : ℚ} (hinput : toRat? input = some argument) :
    toReal input = (argument : ℝ) := by
  cases hdecode : toDyadic? input with
  | none => simp [toRat?, hdecode] at hinput
  | some exact =>
      have hvalue : exact.toRat = argument := by simpa [toRat?, hdecode] using hinput
      rw [toReal_eq, hdecode, ← hvalue, Numerics.Dyadic.cast_toRat]

/-- Every exponential result returned by the concrete refinement algorithm is finite. -/
theorem isFinite_of_exp_eq_ok {fmt : FloatFormat}
    {input result : Model fmt} {options : Options}
    (hresult : exp input options = .ok result) : isFinite result = true := by
  unfold exp at hresult
  split at hresult
  · simp at hresult
  cases hinput : toRat? input with
  | none => simp [hinput] at hresult
  | some argument =>
      rw [hinput] at hresult
      exact isFinite_of_expRat_eq_ok hresult

/-- The concrete exponential kernel certifies nearest-even rounding of the exact input's exp. -/
theorem toReal_of_exp_eq_ok {fmt : FloatFormat}
    {input result : Model fmt} {options : Options}
    (hresult : exp input options = .ok result) :
    toReal result = roundAt fmt (Real.exp (toReal input)) := by
  unfold exp at hresult
  split at hresult
  · simp at hresult
  cases hinput : toRat? input with
  | none => simp [hinput] at hresult
  | some argument =>
      rw [hinput] at hresult
      rw [toReal_of_toRat?_eq_some hinput]
      exact toReal_of_expRat_eq_ok hresult

/-- Every logarithm result returned by the concrete refinement algorithm is finite. -/
theorem isFinite_of_log_eq_ok {fmt : FloatFormat}
    {input result : Model fmt} {options : Options}
    (hresult : log input options = .ok result) : isFinite result = true := by
  unfold log at hresult
  split at hresult
  · simp at hresult
  cases hinput : toRat? input with
  | none => simp [hinput] at hresult
  | some argument =>
      rw [hinput] at hresult
      exact isFinite_of_logRat_eq_ok hresult

/-- The concrete logarithm kernel certifies nearest-even rounding of the exact input's log. -/
theorem toReal_of_log_eq_ok {fmt : FloatFormat}
    {input result : Model fmt} {options : Options}
    (hresult : log input options = .ok result) :
    toReal result = roundAt fmt (Real.log (toReal input)) := by
  unfold log at hresult
  split at hresult
  · simp at hresult
  cases hinput : toRat? input with
  | none => simp [hinput] at hresult
  | some argument =>
      rw [hinput] at hresult
      rw [toReal_of_toRat?_eq_some hinput]
      exact toReal_of_logRat_eq_ok hresult

/-- Each accepted `expMinus1` result is finite, including the signed-zero branch. -/
theorem isFinite_of_expMinus1_eq_ok {fmt : FloatFormat}
    {input result : Model fmt} {options : Options}
    (hresult : expMinus1 input options = .ok result) : isFinite result = true := by
  unfold expMinus1 at hresult
  split at hresult
  · simp at hresult
  split at hresult
  · rename_i hzero
    cases Except.ok.inj hresult
    exact isFinite_eq_true_of_isZero_eq_true input hzero
  · cases hinput : toRat? input with
    | none => simp [hinput] at hresult
    | some argument =>
        rw [hinput] at hresult
        exact isFinite_of_expMinus1Rat_eq_ok hresult

/-- An accepted `expMinus1` equals nearest-even rounding of `Real.exp x - 1`. -/
theorem toReal_of_expMinus1_eq_ok {fmt : FloatFormat}
    {input result : Model fmt} {options : Options}
    (hresult : expMinus1 input options = .ok result) :
    toReal result = roundAt fmt (Real.exp (toReal input) - 1) := by
  unfold expMinus1 at hresult
  split at hresult
  · simp at hresult
  split at hresult
  · rename_i hzero
    cases Except.ok.inj hresult
    simp [toReal_eq_zero_of_isZero _ hzero]
  · cases hinput : toRat? input with
    | none => simp [hinput] at hresult
    | some argument =>
        rw [hinput] at hresult
        rw [toReal_of_toRat?_eq_some hinput]
        exact toReal_of_expMinus1Rat_eq_ok hresult

/-- Each accepted `logPlus1` result is finite, including the signed-zero branch. -/
theorem isFinite_of_logPlus1_eq_ok {fmt : FloatFormat}
    {input result : Model fmt} {options : Options}
    (hresult : logPlus1 input options = .ok result) : isFinite result = true := by
  unfold logPlus1 at hresult
  split at hresult
  · simp at hresult
  split at hresult
  · rename_i hzero
    cases Except.ok.inj hresult
    exact isFinite_eq_true_of_isZero_eq_true input hzero
  · cases hinput : toRat? input with
    | none => simp [hinput] at hresult
    | some argument =>
        rw [hinput] at hresult
        exact isFinite_of_logPlus1Rat_eq_ok hresult

/-- An accepted `logPlus1` equals nearest-even rounding of `Real.log (1 + x)`. -/
theorem toReal_of_logPlus1_eq_ok {fmt : FloatFormat}
    {input result : Model fmt} {options : Options}
    (hresult : logPlus1 input options = .ok result) :
    toReal result = roundAt fmt (Real.log (1 + toReal input)) := by
  unfold logPlus1 at hresult
  split at hresult
  · simp at hresult
  split at hresult
  · rename_i hzero
    cases Except.ok.inj hresult
    simp [toReal_eq_zero_of_isZero _ hzero]
  · cases hinput : toRat? input with
    | none => simp [hinput] at hresult
    | some argument =>
        rw [hinput] at hresult
        rw [toReal_of_toRat?_eq_some hinput]
        exact toReal_of_logPlus1Rat_eq_ok hresult

/-- The IEEE input's zero encoding passes through `expMinus1` unchanged. -/
@[simp] theorem expMinus1_of_isZero {fmt : FloatFormat} {input : Model fmt}
    (hfmt : fmt.isIEEE = true) (hzero : isZero input = true) (options : Options) :
    expMinus1 input options = .ok input := by
  simp [expMinus1, hfmt, hzero]

/-- The IEEE input's zero encoding passes through `logPlus1` unchanged. -/
@[simp] theorem logPlus1_of_isZero {fmt : FloatFormat} {input : Model fmt}
    (hfmt : fmt.isIEEE = true) (hzero : isZero input = true) (options : Options) :
    logPlus1 input options = .ok input := by
  simp [logPlus1, hfmt, hzero]

/--
The finite-real contract holds on the exponential kernel's executable success domain.
The zero fallback adapts the certified result to the contract's total-function argument.
-/
theorem exp_correctlyRoundedCertificateOn (fmt : FloatFormat) (options : Options) :
    Contract.CorrectlyRoundedCertificateOn fmt Real.exp
      (fun input => (exp input options).toOption.getD (zero fmt false))
      (fun input => (exp input options).isOk = true) := by
  constructor
  · intro input _ hsuccess
    cases hresult : exp input options with
    | error _ => simp [hresult, Except.isOk, Except.toBool] at hsuccess
    | ok result =>
        simpa [hresult, Except.toOption] using isFinite_of_exp_eq_ok hresult
  · intro input _ hsuccess
    cases hresult : exp input options with
    | error _ => simp [hresult, Except.isOk, Except.toBool] at hsuccess
    | ok result =>
        simpa [hresult, Except.toOption] using toReal_of_exp_eq_ok hresult

/-- The finite-real contract holds on the inputs accepted by the logarithm kernel. -/
theorem log_correctlyRoundedCertificateOn (fmt : FloatFormat) (options : Options) :
    Contract.CorrectlyRoundedCertificateOn fmt Real.log
      (fun input => (log input options).toOption.getD (zero fmt false))
      (fun input => (log input options).isOk = true) := by
  constructor
  · intro input _ hsuccess
    cases hresult : log input options with
    | error _ => simp [hresult, Except.isOk, Except.toBool] at hsuccess
    | ok result =>
        simpa [hresult, Except.toOption] using isFinite_of_log_eq_ok hresult
  · intro input _ hsuccess
    cases hresult : log input options with
    | error _ => simp [hresult, Except.isOk, Except.toBool] at hsuccess
    | ok result =>
        simpa [hresult, Except.toOption] using toReal_of_log_eq_ok hresult

/-- Correct rounding of `exp x - 1` on the executable acceptance domain. -/
theorem expMinus1_correctlyRoundedCertificateOn (fmt : FloatFormat) (options : Options) :
    Contract.CorrectlyRoundedCertificateOn fmt (fun x => Real.exp x - 1)
      (fun input => (expMinus1 input options).toOption.getD (zero fmt false))
      (fun input => (expMinus1 input options).isOk = true) := by
  constructor <;> intro input _ hsuccess <;>
    cases hresult : expMinus1 input options with
    | error _ => simp [hresult, Except.isOk, Except.toBool] at hsuccess
    | ok result =>
        first
        | simpa [hresult, Except.toOption] using isFinite_of_expMinus1_eq_ok hresult
        | simpa [hresult, Except.toOption] using toReal_of_expMinus1_eq_ok hresult

/-- Correct rounding of `log (1 + x)` on the executable acceptance domain. -/
theorem logPlus1_correctlyRoundedCertificateOn (fmt : FloatFormat) (options : Options) :
    Contract.CorrectlyRoundedCertificateOn fmt (fun x => Real.log (1 + x))
      (fun input => (logPlus1 input options).toOption.getD (zero fmt false))
      (fun input => (logPlus1 input options).isOk = true) := by
  constructor <;> intro input _ hsuccess <;>
    cases hresult : logPlus1 input options with
    | error _ => simp [hresult, Except.isOk, Except.toBool] at hsuccess
    | ok result =>
        first
        | simpa [hresult, Except.toOption] using isFinite_of_logPlus1_eq_ok hresult
        | simpa [hresult, Except.toOption] using toReal_of_logPlus1_eq_ok hresult

/-! ## Real powers -/

section Powers

open FloatLib.Numerics.Interval.BinaryGrid

private theorem log_reduction_split {value : ℚ} (hvalue : 0 < value) (j : Nat) (hj : 0 < j) :
    Real.log (((j : ℚ) / 32 : ℚ) : ℝ) +
        Real.log ((mkRat (32 * value.num.natAbs) (value.den * j) : ℚ) : ℝ) =
      Real.log (value : ℝ) := by
  have hden : (0 : ℚ) < value.den := by exact_mod_cast value.den_pos
  have hnum : |(value.num : ℚ)| = value.num :=
    abs_of_nonneg (by exact_mod_cast Rat.num_nonneg.mpr hvalue.le)
  have hreduced : (mkRat (32 * value.num.natAbs) (value.den * j) : ℚ) = 32 * value / j := by
    rw [Rat.mkRat_eq_div]
    push_cast
    rw [hnum]
    conv_rhs => rw [← Rat.num_div_den value]
    field_simp
  have hjq : (0 : ℚ) < j := by exact_mod_cast hj
  rw [← Real.log_mul (by positivity) (by rw [hreduced]; positivity), hreduced]
  congr 1
  push_cast
  field_simp

/-- Table reduction preserves logarithm containment for every positive rational. -/
theorem containsReal_logReduced {value : ℚ} (hvalue : 0 < value) (precision : Nat) :
    (logReduced value precision).ContainsReal (decode precision) (Real.log (value : ℝ)) := by
  unfold logReduced
  dsimp only
  split
  · rename_i entry hentry
    set index := (64 * value.num.natAbs + value.den) / (2 * value.den) - 24
    have hsum := containsReal_add precision
      (FloatLib.Numerics.Enclosure.BinaryGrid.containsReal_logTableAt? hentry)
      (FloatLib.Numerics.Enclosure.BinaryGrid.containsReal_logUnreduced
        (value := mkRat (32 * value.num.natAbs) (value.den * (index + 24))) (by
          rw [Rat.mkRat_eq_div]
          have : (0 : ℚ) < value.num.natAbs := by
            exact_mod_cast Int.natAbs_pos.mpr (Rat.num_pos.mpr hvalue).ne'
          positivity) precision)
    rwa [log_reduction_split hvalue (index + 24) (by omega)] at hsum
  · exact FloatLib.Numerics.Enclosure.BinaryGrid.containsReal_logUnreduced hvalue precision

/-- The grid combination encloses `exponent * log s + multiple * log 2`. -/
theorem containsReal_powArgument {logScaled logTwo : Interval Int} {precision : Nat}
    {logValue : ℝ} (hlog : logScaled.ContainsReal (decode precision) logValue)
    (hlogTwo : logTwo.ContainsReal (decode precision) (Real.log 2)) (exponent multiple : ℚ) :
    (powArgument logScaled logTwo exponent multiple).ContainsReal (decode precision)
      ((exponent : ℝ) * logValue + (multiple : ℝ) * Real.log 2) :=
  containsReal_add precision
    (FloatLib.Numerics.Enclosure.BinaryGrid.containsReal_scaleRat precision hlog exponent)
    (FloatLib.Numerics.Enclosure.BinaryGrid.containsReal_scaleRat precision hlogTwo multiple)

/-- One exponential at the lower end encloses `exp` over the whole argument interval. -/
theorem contains_expInterval {argument : RationalInterval} {x : ℝ} (hx : argument.Contains x)
    (degree precision : Nat) :
    (expInterval argument degree precision).Contains (Real.exp x) := by
  have hlower := FloatLib.Numerics.Enclosure.BinaryGrid.contains_exp argument.lo degree precision
  have hlo : Real.exp (argument.lo : ℝ) ≤ Real.exp x := Real.exp_le_exp.mpr hx.1
  unfold expInterval
  dsimp only
  split
  · rename_i hwidth
    have hw0 : (0 : ℝ) ≤ ((argument.hi - argument.lo : ℚ) : ℝ) := by
      push_cast
      linarith [hx.1, hx.2]
    have hw1 : ((argument.hi - argument.lo : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hwidth
    have hexpw : Real.exp ((argument.hi - argument.lo : ℚ) : ℝ) ≤
        1 + 2 * ((argument.hi - argument.lo : ℚ) : ℝ) := by
      have h := Real.abs_exp_sub_one_le (x := ((argument.hi - argument.lo : ℚ) : ℝ))
        (by rw [abs_of_nonneg hw0]; exact hw1)
      rw [abs_of_nonneg hw0] at h
      linarith [le_abs_self (Real.exp ((argument.hi - argument.lo : ℚ) : ℝ) - 1)]
    refine ⟨hlower.1.trans hlo, ?_⟩
    calc Real.exp x ≤ Real.exp (argument.hi : ℝ) := Real.exp_le_exp.mpr hx.2
      _ = Real.exp (argument.lo : ℝ) * Real.exp ((argument.hi - argument.lo : ℚ) : ℝ) := by
        rw [← Real.exp_add]
        push_cast
        ring_nf
      _ ≤ _ := mul_le_mul hlower.2 hexpw (Real.exp_pos _).le
          ((Real.exp_pos _).le.trans hlower.2)
      _ = _ := by push_cast; ring
  · exact ⟨hlower.1.trans hlo, (Real.exp_le_exp.mpr hx.2).trans
      (FloatLib.Numerics.Enclosure.BinaryGrid.contains_exp argument.hi degree precision).2⟩

/-- An argument enclosed on every grid gives an enclosure of its exponential. -/
theorem contains_expReduced {reduced : Nat → Interval Int} {r : ℝ}
    (hreduced : ∀ grid, (reduced grid).ContainsReal (decode grid) r)
    (extraBits degree precision : Nat) :
    (expReduced reduced extraBits degree precision).Contains (Real.exp r) := by
  unfold expReduced
  exact contains_expInterval
    ((FloatLib.Numerics.Enclosure.BinaryGrid.contains_toRationalInterval _ _ r).mpr
      (hreduced _)) degree precision

/--
The real power of a positive scaled rational is the exponential of the reduced argument times the
removed power of two, for every integer scale.
-/
theorem rpow_eq_exp_reduced {scaled : ℚ} (hscaled : 0 < scaled) (binaryExponent scale : ℤ)
    (exponent : ℚ) :
    ((scaled : ℝ) * 2 ^ binaryExponent) ^ (exponent : ℝ) =
      Real.exp ((exponent : ℝ) * Real.log scaled +
        ((exponent * binaryExponent - scale : ℚ) : ℝ) * Real.log 2) * 2 ^ scale := by
  have hs : (0 : ℝ) < scaled := by exact_mod_cast hscaled
  have hpow : (2 : ℝ) ^ scale = Real.exp (scale * Real.log 2) := by
    rw [← Real.log_zpow, Real.exp_log (zpow_pos (by norm_num) scale)]
  rw [Real.rpow_def_of_pos (by positivity), Real.log_mul hs.ne' (zpow_ne_zero _ (by norm_num)),
    Real.log_zpow, hpow, ← Real.exp_add]
  congr 1
  push_cast
  ring

/-- The format's least subnormal exponent minus one is negative. -/
private theorem minSubnormalExponent_sub_one_neg (fmt : FloatFormat) :
    fmt.minSubnormalExponent - 1 < 0 := by
  have := fmt.exponentBias_pos
  have := fmt.fracWidth_pos
  simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
    Int.ofNat_eq_natCast]
  omega

/--
An argument at most the screened bound has an exponential of at most half the least subnormal:
`[0, 1]` contains it times `2 ^ -(minSubnormalExponent - 1)`, so the screen never forms that
power.
-/
theorem contains_exp_underflow {fmt : FloatFormat} {t : ℝ} {bound : ℚ} (ht : t ≤ bound)
    (hbound : bound ≤ ((fmt.minSubnormalExponent - 1 : ℤ) : ℚ) * logTwoUpper) :
    (⟨0, 1⟩ : RationalInterval).Contains
      (Real.exp t * 2 ^ (-(fmt.minSubnormalExponent - 1))) := by
  have hscale : ((fmt.minSubnormalExponent - 1 : ℤ) : ℝ) < 0 := by
    exact_mod_cast minSubnormalExponent_sub_one_neg fmt
  have hupper : (logTwoUpper : ℝ) = 0.6931471808 := by norm_num [logTwoUpper]
  have hlog : ((fmt.minSubnormalExponent - 1 : ℤ) : ℝ) * (logTwoUpper : ℝ) ≤
      ((fmt.minSubnormalExponent - 1 : ℤ) : ℝ) * Real.log 2 := by
    rw [hupper]
    exact mul_le_mul_of_nonpos_left Real.log_two_lt_d9.le hscale.le
  have hreal : t ≤ ((fmt.minSubnormalExponent - 1 : ℤ) : ℝ) * Real.log 2 :=
    ht.trans ((by exact_mod_cast hbound : (bound : ℝ) ≤ _).trans hlog)
  have hexp : Real.exp t ≤ 2 ^ (fmt.minSubnormalExponent - 1) :=
    calc Real.exp t ≤ Real.exp (((fmt.minSubnormalExponent - 1 : ℤ) : ℝ) * Real.log 2) :=
          Real.exp_le_exp.mpr hreal
      _ = 2 ^ (fmt.minSubnormalExponent - 1) := by
        rw [← Real.log_zpow, Real.exp_log (zpow_pos (by norm_num) _)]
  have hpow : (0 : ℝ) < 2 ^ (-(fmt.minSubnormalExponent - 1)) := zpow_pos (by norm_num) _
  constructor
  · simpa using (mul_pos (Real.exp_pos t) hpow).le
  · calc Real.exp t * 2 ^ (-(fmt.minSubnormalExponent - 1))
        ≤ 2 ^ (fmt.minSubnormalExponent - 1) * 2 ^ (-(fmt.minSubnormalExponent - 1)) :=
          mul_le_mul_of_nonneg_right hexp hpow.le
      _ = ((1 : ℚ) : ℝ) := by
        rw [← zpow_add₀ (by norm_num), add_neg_cancel, zpow_zero, Rat.cast_one]

/--
The refinement stage of `powRatScaled` is sound for every integer scale: an accepted result is
finite and the correctly rounded real power.
-/
private theorem toReal_of_powSearch_eq_some {fmt : FloatFormat} {scaled : ℚ} (hs : 0 < scaled)
    {binaryExponent : ℤ} {exponent : ℚ} {firstGrid : Nat} {argument : Interval Int}
    (hargument : argument.ContainsReal (decode firstGrid)
      ((exponent : ℝ) * Real.log scaled +
        ((exponent * binaryExponent : ℚ) : ℝ) * Real.log 2))
    (scale : ℤ) (extraBits degree precision steps : Nat) {result : Model fmt}
    (hresult : RationalInterval.refine
      (expReduced (fun grid =>
        if grid = firstGrid then
          Interval.BinaryGrid.sub argument
            (FloatLib.Numerics.Enclosure.BinaryGrid.scaleRat
              (Numerics.Enclosure.Constants.ln2Grid firstGrid) scale)
        else powArgument (logReduced scaled grid) (Numerics.Enclosure.Constants.ln2Grid grid)
          exponent
          (exponent * binaryExponent - scale)) extraBits)
      (fun interval => Enclosure.roundScaled? fmt interval scale) degree precision steps =
        some result) :
    isFinite result = true ∧
      toReal result =
        roundAt fmt (((scaled : ℝ) * 2 ^ binaryExponent) ^ (exponent : ℝ)) := by
  obtain ⟨degree, precision, haccept⟩ := RationalInterval.exists_of_refine_eq_some hresult
  refine ⟨Enclosure.isFinite_of_roundScaled?_eq_some haccept, ?_⟩
  rw [Enclosure.toReal_eq_roundAt_of_roundScaled?_eq_some (contains_expReduced ?_ _ _ _)
    haccept, ← rpow_eq_exp_reduced hs]
  intro grid
  split
  · rename_i hgrid
    subst hgrid
    have hsub := containsReal_sub _ hargument
      (FloatLib.Numerics.Enclosure.BinaryGrid.containsReal_scaleRat _
        (Numerics.Enclosure.Constants.containsReal_ln2Grid _) (scale : ℚ))
    convert hsub using 1
    push_cast
    ring
  · exact containsReal_powArgument (containsReal_logReduced hs grid)
      (Numerics.Enclosure.Constants.containsReal_ln2Grid grid)
      exponent _

private theorem rounded_of_powRatScaled_eq_ok {fmt : FloatFormat} {scaled : ℚ}
    {binaryExponent : ℤ} {exponent : ℚ} {options : Options} {result : Model fmt}
    (hresult : powRatScaled fmt scaled binaryExponent exponent options = .ok result) :
    isFinite result = true ∧
      toReal result =
        roundAt fmt (((scaled : ℝ) * 2 ^ binaryExponent) ^ (exponent : ℝ)) := by
  unfold powRatScaled at hresult
  split at hresult
  · simp at hresult
  split at hresult
  · simp at hresult
  rename_i hpositive
  have hs : 0 < scaled := lt_of_not_ge hpositive
  split at hresult
  · rename_i hzero
    subst hzero
    replace hresult := accept_eq_ok.mp hresult
    refine ⟨Enclosure.isFinite_of_round?_eq_some hresult, ?_⟩
    rw [Enclosure.toReal_eq_roundAt_of_round?_eq_some (target := 1)
      (by simpa using RationalInterval.contains_point (1 : ℚ)) hresult]
    simp
  dsimp only at hresult
  split at hresult
  · simp at hresult
  -- The argument encloses `t = exponent * log scaled + exponent * binaryExponent * log 2`.
  have hargument := containsReal_powArgument
    (containsReal_logReduced hs
      (FloatLib.Numerics.Enclosure.BinaryGrid.workingPrecision (fmt.fracWidth + 1)
        (max 1 options.initialDegree) +
      (max (magnitudeBits exponent) (magnitudeBits (exponent * binaryExponent)) + 1)))
    (Numerics.Enclosure.Constants.containsReal_ln2Grid _) exponent (exponent * binaryExponent)
  have hpower := rpow_eq_exp_reduced hs binaryExponent 0 exponent
  simp only [Int.cast_zero, sub_zero, zpow_zero, mul_one] at hpower
  split at hresult
  · rename_i hscreen
    replace hresult := accept_eq_ok.mp hresult
    refine ⟨Enclosure.isFinite_of_roundScaled?_eq_some hresult, ?_⟩
    have hrounded := Enclosure.toReal_eq_roundAt_of_roundScaled?_eq_some
      (contains_exp_underflow (t := (exponent : ℝ) * Real.log scaled +
          ((exponent * binaryExponent : ℚ) : ℝ) * Real.log 2)
        (by simpa using ((containsReal_iff _ _ _).mp hargument).2) hscreen) hresult
    rw [hpower, hrounded, mul_assoc, ← zpow_add₀ (by norm_num), neg_add_cancel, zpow_zero,
      mul_one]
  split at hresult
  · simp at hresult
  exact toReal_of_powSearch_eq_some hs hargument _ _ _ _ _ (accept_eq_ok.mp hresult)

/-- Successful scaled powers are finite. -/
theorem isFinite_of_powRatScaled_eq_ok {fmt : FloatFormat} {scaled : ℚ}
    {binaryExponent : ℤ} {exponent : ℚ} {options : Options} {result : Model fmt}
    (hresult : powRatScaled fmt scaled binaryExponent exponent options = .ok result) :
    isFinite result = true :=
  (rounded_of_powRatScaled_eq_ok hresult).1

/-- An accepted scaled power equals rounding of the real power of `scaled * 2 ^ binaryExponent`. -/
theorem toReal_of_powRatScaled_eq_ok {fmt : FloatFormat} {scaled : ℚ}
    {binaryExponent : ℤ} {exponent : ℚ} {options : Options} {result : Model fmt}
    (hresult : powRatScaled fmt scaled binaryExponent exponent options = .ok result) :
    toReal result = roundAt fmt (((scaled : ℝ) * 2 ^ binaryExponent) ^ (exponent : ℝ)) :=
  (rounded_of_powRatScaled_eq_ok hresult).2

/-- The binary split of a positive rational is positive and recombines to its value. -/
theorem splitTwoPow_spec {value : ℚ} (hvalue : 0 < value) :
    0 < (splitTwoPow value).1 ∧
      ((splitTwoPow value).1 : ℝ) * 2 ^ (splitTwoPow value).2 = (value : ℝ) := by
  unfold splitTwoPow
  dsimp only
  have hpow (exponent : ℤ) : (0 : ℚ) < 2 ^ exponent := zpow_pos (by norm_num) exponent
  split
  · refine ⟨div_pos hvalue (hpow _), ?_⟩
    push_cast
    field_simp
  · refine ⟨div_pos (div_pos hvalue (hpow _)) (by norm_num), ?_⟩
    push_cast
    rw [zpow_add_one₀ (by norm_num)]
    field_simp

private theorem rounded_of_powRat_eq_ok {fmt : FloatFormat} {base exponent : ℚ}
    {options : Options} {result : Model fmt}
    (hresult : powRat fmt base exponent options = .ok result) :
    isFinite result = true ∧ toReal result = roundAt fmt ((base : ℝ) ^ (exponent : ℝ)) := by
  unfold powRat at hresult
  split at hresult
  · simp at hresult
  · rename_i hpositive
    have hsplit := splitTwoPow_spec (lt_of_not_ge hpositive)
    have h := rounded_of_powRatScaled_eq_ok hresult
    rwa [hsplit.2] at h

/-- Successful rational-input powers are finite. -/
theorem isFinite_of_powRat_eq_ok {fmt : FloatFormat} {base exponent : ℚ}
    {options : Options} {result : Model fmt}
    (hresult : powRat fmt base exponent options = .ok result) : isFinite result = true :=
  (rounded_of_powRat_eq_ok hresult).1

/--
An accepted rational power equals nearest-even rounding of the real power `base ^ exponent`
(`Real.rpow`, with `base > 0` whenever the result is accepted).
-/
theorem toReal_of_powRat_eq_ok {fmt : FloatFormat} {base exponent : ℚ}
    {options : Options} {result : Model fmt}
    (hresult : powRat fmt base exponent options = .ok result) :
    toReal result = roundAt fmt ((base : ℝ) ^ (exponent : ℝ)) :=
  (rounded_of_powRat_eq_ok hresult).2

/-- An accepted rational power has a positive base. -/
theorem base_pos_of_powRat_eq_ok {fmt : FloatFormat} {base exponent : ℚ}
    {options : Options} {result : Model fmt}
    (hresult : powRat fmt base exponent options = .ok result) : 0 < base := by
  unfold powRat at hresult
  split at hresult
  · simp at hresult
  · exact lt_of_not_ge ‹_›

/-- The stored-field bound `powArgumentExponent` bounds `|exponent * log base|`. -/
theorem abs_mul_log_lt_two_pow_powArgumentExponent {base exponent : Numerics.Dyadic}
    (hnegative : base.negative = false) (hsignificand : base.significand ≠ 0) :
    |exponent.toReal * Real.log base.toReal| < 2 ^ powArgumentExponent base exponent := by
  set m := base.significand
  set e := base.exponent
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hsignificand
  have hbase : base.toReal = (m : ℝ) * 2 ^ e := by
    simp [Dyadic.toReal, Dyadic.signedSignificand, hnegative, m, e]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2one : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  -- `|log base| ≤ (|e| + log₂ m + 1) * log 2 < |e| + log₂ m + 1 < 2 ^ (log₂ (…) + 1)`.
  set total : ℕ := e.natAbs + m.log2 + 1
  have htotal : (0 : ℝ) < total := by positivity
  have hlogm : Real.log m ≤ ((m.log2 + 1 : ℕ) : ℝ) * Real.log 2 := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.lt_log2_self.le)
  have hlogm0 : 0 ≤ Real.log m := Real.log_nonneg hm
  have hlogbase : |Real.log base.toReal| < 2 ^ ((total.log2 + 1 : ℕ) : ℤ) := by
    rw [hbase, Real.log_mul (by positivity) (zpow_ne_zero _ (by norm_num)), Real.log_zpow]
    calc |Real.log m + e * Real.log 2| ≤ |Real.log m| + |(e : ℝ) * Real.log 2| := abs_add_le _ _
      _ = Real.log m + (e.natAbs : ℝ) * Real.log 2 := by
        rw [abs_of_nonneg hlogm0, abs_mul, abs_of_pos hlog2, Nat.cast_natAbs, Int.cast_abs]
      _ ≤ (total : ℝ) * Real.log 2 := by
        simp only [total]
        push_cast at hlogm ⊢
        nlinarith
      _ < total := by nlinarith
      _ < 2 ^ ((total.log2 + 1 : ℕ) : ℤ) := by
        rw [zpow_natCast]
        exact_mod_cast Nat.lt_log2_self
  have hexponent : |exponent.toReal| ≤
      2 ^ (exponent.exponent + ((exponent.significand.log2 + 1 : ℕ) : ℤ)) := by
    have habs : |exponent.toReal| = (exponent.significand : ℝ) * 2 ^ exponent.exponent := by
      cases hsign : exponent.negative <;>
        simp [Dyadic.toReal, Dyadic.signedSignificand, hsign, abs_mul, abs_of_pos
          (zpow_pos (by norm_num : (0 : ℝ) < 2) _)]
    rw [habs, zpow_add₀ (by norm_num), mul_comm]
    gcongr
    rw [zpow_natCast]
    exact_mod_cast Nat.lt_log2_self.le
  rw [abs_mul, powArgumentExponent]
  calc |exponent.toReal| * |Real.log base.toReal|
      ≤ 2 ^ (exponent.exponent + ((exponent.significand.log2 + 1 : ℕ) : ℤ)) *
          |Real.log base.toReal| :=
        mul_le_mul_of_nonneg_right hexponent (abs_nonneg _)
    _ < 2 ^ (exponent.exponent + ((exponent.significand.log2 + 1 : ℕ) : ℤ)) *
          2 ^ ((total.log2 + 1 : ℕ) : ℤ) :=
        mul_lt_mul_of_pos_left hlogbase (zpow_pos (by norm_num) _)
    _ = _ := by rw [← zpow_add₀ (by norm_num)]

/-- Every exponential of an argument below `2 ^ -(fracWidth + 4)` lies in `powNearOne`. -/
theorem contains_exp_powNearOne (fmt : FloatFormat) {t : ℝ}
    (ht : |t| < 2 ^ (-((fmt.fracWidth : ℤ) + 4))) :
    (powNearOne fmt).Contains (Real.exp t) := by
  have hgap : (((Dyadic.mk false 1 (-((fmt.fracWidth : ℤ) + 3))).toRat : ℚ) : ℝ) =
      2 * 2 ^ (-((fmt.fracWidth : ℤ) + 4)) := by
    rw [Dyadic.cast_toRat, Dyadic.toReal_mk_false, Nat.cast_one, one_mul,
      show -((fmt.fracWidth : ℤ) + 3) = 1 + -((fmt.fracWidth : ℤ) + 4) by ring,
      zpow_add₀ (by norm_num), zpow_one]
  have hsmall : |t| ≤ 1 := by
    refine ht.le.trans (zpow_le_one_of_nonpos₀ (by norm_num) ?_)
    omega
  have h := Real.abs_exp_sub_one_le hsmall
  rcases abs_le.mp (h.trans (by linarith : 2 * |t| ≤ 2 * 2 ^ (-((fmt.fracWidth : ℤ) + 4))))
    with ⟨hlower, hupper⟩
  constructor <;> simp only [powNearOne, Rat.cast_sub, Rat.cast_add, Rat.cast_one, hgap] <;>
    linarith

private theorem rounded_of_pow_eq_ok {fmt : FloatFormat} {base exponent : Model fmt}
    {options : Options} {result : Model fmt} (hresult : pow base exponent options = .ok result) :
    isFinite result = true ∧
      toReal result = roundAt fmt (toReal base ^ toReal exponent) := by
  unfold pow at hresult
  split at hresult
  · simp at hresult
  split at hresult
  · rename_i a b ha hb
    have hbase : toReal base = a.toReal := by rw [toReal_eq, ha]
    have hexponent : toReal exponent = b.toReal := by rw [toReal_eq, hb]
    rw [hbase, hexponent]
    split at hresult
    · simp at hresult
    rename_i hpositive
    simp only [Bool.or_eq_true, beq_iff_eq, not_or, Bool.not_eq_true] at hpositive
    have hm : (0 : ℝ) < a.significand := by exact_mod_cast Nat.pos_of_ne_zero hpositive.2
    have hreal : a.toReal = (a.significand : ℝ) * 2 ^ a.exponent := by
      simp [Dyadic.toReal, Dyadic.signedSignificand, hpositive.1]
    have hapos : 0 < a.toReal := by rw [hreal]; positivity
    split at hresult
    · rename_i htiny
      replace hresult := accept_eq_ok.mp hresult
      refine ⟨Enclosure.isFinite_of_round?_eq_some hresult, ?_⟩
      rw [Real.rpow_def_of_pos hapos]
      refine Enclosure.toReal_eq_roundAt_of_round?_eq_some (contains_exp_powNearOne fmt ?_)
        hresult
      calc |Real.log a.toReal * b.toReal| = |b.toReal * Real.log a.toReal| := by rw [mul_comm]
        _ < 2 ^ powArgumentExponent a b :=
          abs_mul_log_lt_two_pow_powArgumentExponent hpositive.1 hpositive.2
        _ ≤ 2 ^ (-((fmt.fracWidth : ℤ) + 4)) := zpow_le_zpow_right₀ (by norm_num) htiny
    split at hresult
    · simp at hresult
    have h := rounded_of_powRatScaled_eq_ok hresult
    have hsplit := splitTwoPow_spec (value := (a.significand : ℚ)) (by exact_mod_cast hm)
    have hcombine : ((splitTwoPow (a.significand : ℚ)).1 : ℝ) *
        2 ^ ((splitTwoPow (a.significand : ℚ)).2 + a.exponent) = a.toReal := by
      rw [zpow_add₀ (by norm_num), ← mul_assoc, hsplit.2, hreal]
      push_cast
      ring
    rwa [hcombine, Dyadic.cast_toRat] at h
  · simp at hresult

/-- Every power returned by the certified search is finite. -/
theorem isFinite_of_pow_eq_ok {fmt : FloatFormat} {base exponent : Model fmt}
    {options : Options} {result : Model fmt} (hresult : pow base exponent options = .ok result) :
    isFinite result = true :=
  (rounded_of_pow_eq_ok hresult).1

/--
An accepted certified power equals nearest-even rounding of the real power
`toReal base ^ toReal exponent` (`Real.rpow`, since the base of an accepted result is positive).
-/
theorem toReal_of_pow_eq_ok {fmt : FloatFormat} {base exponent : Model fmt}
    {options : Options} {result : Model fmt} (hresult : pow base exponent options = .ok result) :
    toReal result = roundAt fmt (toReal base ^ toReal exponent) :=
  (rounded_of_pow_eq_ok hresult).2

end Powers

end FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals.Certified
