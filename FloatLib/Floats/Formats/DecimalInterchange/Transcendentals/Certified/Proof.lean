/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Certified.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Enclosure.Proof
public import FloatLib.Numerics.Exact.Elementary.Proof
public import FloatLib.Numerics.Enclosure.Elementary.BinaryGridProof
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Real rounding certificates for decimal exp-minus-one and log-plus-one

Every returned datum is valid and finite, and its real value equals radix-ten Flocq
nearest-even rounding of the exact real function. The theorems fix the real value only: they do
not say which member of the cohort is returned, nor the sign of a zero result, except for the
signed-zero passthrough below. These conclusions follow from rational enclosure bounds and the
decimal projection bridge, independently of whether refinement eventually succeeds.

These are partial-correctness theorems: they describe a result whenever the kernel returns
`some`, and no theorem says which inputs succeed. The one proved success is the signed-zero
passthrough, `expMinus1_of_isZero` and `logPlus1_of_isZero`.

The datum interfaces require a valid finite input, preserve signed zero and its quantum, and
reject the logarithm's excluded domain. None of these statements assumes quantum zero lies in
the destination range.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Certified

open FloatLib.Numerics
open FloatLib.Floats.Certified

private theorem log_ten_bounds : (2 : ℝ) < Real.log 10 ∧ Real.log 10 < 3 := by
  rw [Real.log_ten_eq]
  constructor
  · linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  · linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]

private theorem tail_lt_exp {f : Format} {argument : ℚ}
    (hargument : expMinus1TailArgumentBound f ≤ argument) :
    (expMinus1TailBound f : ℝ) < Real.exp (argument : ℝ) := by
  have hexponent : -(f.precision : ℝ) - 1 < 0 := by
    have : 0 ≤ (f.precision : ℝ) := Nat.cast_nonneg _
    linarith
  simp only [expMinus1TailArgumentBound] at hargument
  simp only [expMinus1TailBound, Rat.cast_zpow, Rat.cast_ofNat]
  rw [← Real.log_lt_iff_lt_exp (by positivity), Real.log_zpow]
  push_cast
  calc
    (-(f.precision : ℝ) - 1) * Real.log 10 <
        (-(f.precision : ℝ) - 1) * 2 :=
      mul_lt_mul_of_neg_left log_ten_bounds.1 hexponent
    _ = 2 * (-(f.precision : ℝ) - 1) := by ring
    _ ≤ (argument : ℝ) := by exact_mod_cast hargument

private theorem exp_lt_upper {f : Format} {argument : ℚ}
    (hargument : argument ≤ expMinus1UpperArgumentBound f) :
    Real.exp (argument : ℝ) < (expMinus1UpperBound f + 1 : ℚ) := by
  let exponent := f.maxQuantum + (f.precision : ℤ)
  change argument ≤ ((if 0 ≤ exponent then 2 * exponent else 3 * exponent : ℤ) : ℚ)
    at hargument
  have hbound : (argument : ℝ) ≤ (exponent : ℝ) * Real.log 10 := by
    by_cases hexponent : 0 ≤ exponent
    · have hnonneg : (0 : ℝ) ≤ (exponent : ℝ) := by exact_mod_cast hexponent
      have hargument' : (argument : ℝ) ≤ 2 * (exponent : ℝ) := by
        rw [ite_eq_left hexponent] at hargument
        exact_mod_cast hargument
      exact hargument'.trans (by nlinarith [log_ten_bounds.1])
    · have hneg : (exponent : ℝ) < 0 := by exact_mod_cast lt_of_not_ge hexponent
      have hargument' : (argument : ℝ) ≤ 3 * (exponent : ℝ) := by
        rw [ite_eq_right hexponent] at hargument
        exact_mod_cast hargument
      exact hargument'.trans (by nlinarith [log_ten_bounds.2])
  have hexp : Real.exp (argument : ℝ) ≤ (expMinus1UpperBound f : ℝ) := by
    simp only [expMinus1UpperBound, Rat.cast_zpow, Rat.cast_ofNat]
    rw [← Real.le_log_iff_exp_le (by positivity), Real.log_zpow]
    exact hbound
  push_cast
  linarith

/-- The cheap argument screen of the tail guard is implied by the exact exponential comparison. -/
private theorem expTail_guard_iff (f : Format) (argument : ℚ) :
    (argument < expMinus1TailArgumentBound f ∧
      ElementaryComparison.compareExp argument (expMinus1TailBound f) ≠ .gt) ↔
      ElementaryComparison.compareExp argument (expMinus1TailBound f) ≠ .gt :=
  and_iff_right_of_imp fun hcompare => by
    by_contra hargument
    apply hcompare
    rw [ElementaryComparison.compareExp_eq_real, cmp_eq_gt_iff]
    exact tail_lt_exp (le_of_not_gt hargument)

/-- The cheap argument screen of the overflow guard is implied by the exact exponential
comparison. -/
private theorem expUpper_guard_iff (f : Format) (argument : ℚ) :
    (expMinus1UpperArgumentBound f < argument ∧
      ElementaryComparison.compareExp argument (expMinus1UpperBound f + 1) ≠ .lt) ↔
      ElementaryComparison.compareExp argument (expMinus1UpperBound f + 1) ≠ .lt :=
  and_iff_right_of_imp fun hcompare => by
    by_contra hargument
    apply hcompare
    rw [ElementaryComparison.compareExp_eq_real, cmp_eq_lt_iff]
    exact exp_lt_upper (le_of_not_gt hargument)

private theorem expMinus1Rat_eq_guarded (f : Format) (argument : ℚ) (budget : Budget) :
    expMinus1Rat f argument budget =
      if argument = 0 then Enclosure.round? f (RationalInterval.point 0)
      else if ElementaryComparison.compareExp argument (expMinus1TailBound f) ≠ .gt then
        Enclosure.round? f (expMinus1TailInterval f)
      else if ElementaryComparison.compareExp argument (expMinus1UpperBound f + 1) ≠ .lt then
        none
      else
        refine f
          (fun degree precision => (FloatLib.Numerics.Enclosure.BinaryGrid.exp
            argument degree precision).sub
            (RationalInterval.point 1))
          (max 1 budget.initialDegree)
          (FloatLib.Numerics.Enclosure.BinaryGrid.expPrecision
            (f.coefficientBound.log2 + 1) argument (max 1 budget.initialDegree) true)
          budget.maxAttempts := by
  simp only [expMinus1Rat, expTail_guard_iff, expUpper_guard_iff]

private theorem exists_enclosure_of_refine_eq_some {f : Format}
    {enclose : Nat → Nat → RationalInterval} {target : ℝ}
    (hcontains : ∀ degree precision, (enclose degree precision).Contains target)
    {degree precision steps : Nat} {result : Datum}
    (hresult : refine f enclose degree precision steps = some result) :
    ∃ interval : RationalInterval,
      interval.Contains target ∧ Enclosure.round? f interval = some result := by
  obtain ⟨degree, precision, haccept⟩ := RationalInterval.exists_of_refine_eq_some hresult
  exact ⟨enclose degree precision, hcontains degree precision, haccept⟩

/-- A successful exponential-minus-one kernel took one of three paths, each with its real meaning:
the exact zero, the negative tail (where `exp argument` is at most the tail bound), or the refined
search below the overflow screen. The overflow screen itself never succeeds. -/
private theorem expMinus1Rat_cases_of_eq_some {f : Format}
    {argument : ℚ} {budget : Budget} {result : Datum}
    (hresult : expMinus1Rat f argument budget = some result) :
    (argument = 0 ∧ Enclosure.round? f (RationalInterval.point 0) = some result) ∨
      (Real.exp (argument : ℝ) ≤ expMinus1TailBound f ∧
        Enclosure.round? f (expMinus1TailInterval f) = some result) ∨
      (Real.exp (argument : ℝ) < (expMinus1UpperBound f + 1 : ℚ) ∧
        ∃ degree precision, refine f
          (fun degree precision => (FloatLib.Numerics.Enclosure.BinaryGrid.exp
            argument degree precision).sub (RationalInterval.point 1))
          degree precision budget.maxAttempts = some result) := by
  rw [expMinus1Rat_eq_guarded] at hresult
  split at hresult
  · exact Or.inl ⟨‹_›, hresult⟩
  · split at hresult
    · rename_i hsmall
      simp only [ElementaryComparison.compareExp_eq_real, ne_eq, cmp_eq_gt_iff] at hsmall
      exact Or.inr (Or.inl ⟨le_of_not_gt hsmall, hresult⟩)
    · split at hresult
      · simp at hresult
      · rename_i hlarge
        have hlt :
            ElementaryComparison.compareExp argument (expMinus1UpperBound f + 1) = .lt :=
          of_not_not hlarge
        rw [ElementaryComparison.compareExp_eq_real, cmp_eq_lt_iff] at hlt
        exact Or.inr (Or.inr ⟨hlt, _, _, hresult⟩)

private theorem exists_enclosure_of_expMinus1Rat_eq_some {f : Format}
    {argument : ℚ} {budget : Budget} {result : Datum}
    (hresult : expMinus1Rat f argument budget = some result) :
    ∃ interval : RationalInterval, interval.Contains (Real.exp (argument : ℝ) - 1) ∧
      Enclosure.round? f interval = some result := by
  rcases expMinus1Rat_cases_of_eq_some hresult with
    ⟨hzero, hround⟩ | ⟨hsmall, hround⟩ | ⟨-, _, _, hround⟩
  · exact ⟨RationalInterval.point 0,
      by simpa [hzero] using RationalInterval.contains_point (0 : ℚ), hround⟩
  · have hexp :
        (⟨0, expMinus1TailBound f⟩ : RationalInterval).Contains (Real.exp (argument : ℝ)) :=
      ⟨by simpa using (Real.exp_pos (argument : ℝ)).le, hsmall⟩
    exact ⟨expMinus1TailInterval f, by
      simpa [expMinus1TailInterval] using
        RationalInterval.contains_sub hexp (RationalInterval.contains_point 1), hround⟩
  · refine exists_enclosure_of_refine_eq_some ?_ hround
    intro degree precision
    simpa using RationalInterval.contains_sub
      (FloatLib.Numerics.Enclosure.BinaryGrid.contains_exp argument degree _)
      (RationalInterval.contains_point 1)

private theorem exists_enclosure_of_logPlus1Rat_eq_some {f : Format}
    {argument : ℚ} {budget : Budget} {result : Datum}
    (hresult : logPlus1Rat f argument budget = some result) :
    ∃ interval : RationalInterval, interval.Contains (Real.log (1 + (argument : ℝ))) ∧
      Enclosure.round? f interval = some result := by
  rw [logPlus1Rat] at hresult
  split at hresult
  · simp at hresult
  · rename_i hdomain
    split at hresult
    · rename_i hzero
      exact ⟨RationalInterval.point 0,
        by simpa [hzero] using RationalInterval.contains_point (0 : ℚ), hresult⟩
    · refine exists_enclosure_of_refine_eq_some ?_ hresult
      intro degree precision
      have hpositive : 0 < 1 + argument := by linarith [lt_of_not_ge hdomain]
      simpa only [Rat.cast_add, Rat.cast_one] using
        FloatLib.Numerics.Enclosure.BinaryGrid.contains_log (1 + argument) degree _ hpositive

/-- An accepted rational-input exponential-minus-one result is valid in the destination format. -/
theorem valid_of_expMinus1Rat_eq_some {f : Format}
    {argument : ℚ} {budget : Budget} {result : Datum}
    (hresult : expMinus1Rat f argument budget = some result) : result.Valid f := by
  obtain ⟨_, _, haccept⟩ := exists_enclosure_of_expMinus1Rat_eq_some hresult
  exact Enclosure.valid_of_round?_eq_some haccept

/-- An accepted rational-input exponential-minus-one result is finite. -/
theorem isFinite_of_expMinus1Rat_eq_some {f : Format}
    {argument : ℚ} {budget : Budget} {result : Datum}
    (hresult : expMinus1Rat f argument budget = some result) : result.isFinite = true := by
  obtain ⟨_, _, haccept⟩ := exists_enclosure_of_expMinus1Rat_eq_some hresult
  exact Enclosure.isFinite_of_round?_eq_some haccept

/-- Acceptance certifies the single real rounding of `exp argument - 1`. -/
theorem toReal_of_expMinus1Rat_eq_some {f : Format}
    {argument : ℚ} {budget : Budget} {result : Datum}
    (hresult : expMinus1Rat f argument budget = some result) :
    toReal result = roundAt f (Real.exp (argument : ℝ) - 1) := by
  obtain ⟨_, hcontains, haccept⟩ := exists_enclosure_of_expMinus1Rat_eq_some hresult
  exact Enclosure.toReal_eq_roundAt_of_round?_eq_some hcontains haccept

/-- An accepted rational-input logarithm-plus-one result is valid in the destination format. -/
theorem valid_of_logPlus1Rat_eq_some {f : Format}
    {argument : ℚ} {budget : Budget} {result : Datum}
    (hresult : logPlus1Rat f argument budget = some result) : result.Valid f := by
  obtain ⟨_, _, haccept⟩ := exists_enclosure_of_logPlus1Rat_eq_some hresult
  exact Enclosure.valid_of_round?_eq_some haccept

/-- An accepted rational-input logarithm-plus-one result is finite. -/
theorem isFinite_of_logPlus1Rat_eq_some {f : Format}
    {argument : ℚ} {budget : Budget} {result : Datum}
    (hresult : logPlus1Rat f argument budget = some result) : result.isFinite = true := by
  obtain ⟨_, _, haccept⟩ := exists_enclosure_of_logPlus1Rat_eq_some hresult
  exact Enclosure.isFinite_of_round?_eq_some haccept

/-- Acceptance certifies the single real rounding of `log (1 + argument)`. -/
theorem toReal_of_logPlus1Rat_eq_some {f : Format}
    {argument : ℚ} {budget : Budget} {result : Datum}
    (hresult : logPlus1Rat f argument budget = some result) :
    toReal result = roundAt f (Real.log (1 + (argument : ℝ))) := by
  obtain ⟨_, hcontains, haccept⟩ := exists_enclosure_of_logPlus1Rat_eq_some hresult
  exact Enclosure.toReal_eq_roundAt_of_round?_eq_some hcontains haccept

/-- The logarithm kernel rejects every rational argument at or below minus one. -/
theorem logPlus1Rat_eq_none_of_le_neg_one (f : Format) {argument : ℚ}
    (hdomain : argument ≤ -1) (budget : Budget) :
    logPlus1Rat f argument budget = none := by
  simp [logPlus1Rat, hdomain]

/-- Rational logarithm acceptance implies the true domain condition. -/
theorem neg_one_lt_of_logPlus1Rat_eq_some {f : Format}
    {argument : ℚ} {budget : Budget} {result : Datum}
    (hresult : logPlus1Rat f argument budget = some result) : -1 < argument := by
  by_contra h
  rw [logPlus1Rat_eq_none_of_le_neg_one f (le_of_not_gt h) budget] at hresult
  cases hresult

private theorem zero_facts {input : Datum} (hzero : input.isZero = true) :
    input.isFinite = true ∧ toReal input = 0 := by
  cases input with
  | finite s c q =>
      have hc : c = 0 := by simpa [Datum.isZero] using hzero
      simp [hc, Datum.isFinite, toReal, Datum.toRat?]
  | infinity s => simp [Datum.isZero] at hzero
  | nan s t p => simp [Datum.isZero] at hzero

private theorem isFinite_of_toRat?_eq_some {input : Datum} {argument : ℚ}
    (hinput : input.toRat? = some argument) : input.isFinite = true := by
  cases input <;> simp_all [Datum.isFinite, Datum.toRat?]

/-- A successful guarded call (an invalid input fails, a zero is returned unchanged, any other input
goes to the rational kernel) had a valid input that is either the returned zero or a finite
argument accepted by the kernel. -/
private theorem input_cases_of_guarded_eq_some {f : Format} {input result : Datum}
    {kernel : ℚ → Option Datum}
    (hresult : (if ¬input.Valid f then none
      else if input.isZero then some input
      else
        match input.toRat? with
        | none => none
        | some argument => kernel argument) = some result) :
    input.Valid f ∧ (input.isZero = true ∧ input = result ∨
      ∃ argument : ℚ, input.toRat? = some argument ∧ kernel argument = some result) := by
  split at hresult
  · simp at hresult
  · rename_i hvalid
    refine ⟨of_not_not hvalid, ?_⟩
    split at hresult
    · rename_i hzero
      exact Or.inl ⟨hzero, Option.some.inj hresult⟩
    · cases hinput : input.toRat? with
      | none => simp [hinput] at hresult
      | some argument =>
          rw [hinput] at hresult
          exact Or.inr ⟨argument, rfl, hresult⟩

private theorem input_cases_of_expMinus1_eq_some {f : Format}
    {input result : Datum} {budget : Budget}
    (hresult : expMinus1 f input budget = some result) :
    input.Valid f ∧ (input.isZero = true ∧ input = result ∨
      ∃ argument : ℚ, input.toRat? = some argument ∧
        expMinus1Rat f argument budget = some result) :=
  input_cases_of_guarded_eq_some hresult

private theorem input_cases_of_logPlus1_eq_some {f : Format}
    {input result : Datum} {budget : Budget}
    (hresult : logPlus1 f input budget = some result) :
    input.Valid f ∧ (input.isZero = true ∧ input = result ∨
      ∃ argument : ℚ, input.toRat? = some argument ∧
        logPlus1Rat f argument budget = some result) :=
  input_cases_of_guarded_eq_some hresult

/-- A successful datum-input exponential-minus-one call had a valid input. -/
theorem valid_input_of_expMinus1_eq_some {f : Format}
    {input result : Datum} {budget : Budget}
    (hresult : expMinus1 f input budget = some result) : input.Valid f :=
  (input_cases_of_expMinus1_eq_some hresult).1

/-- A successful datum-input logarithm-plus-one call had a valid input. -/
theorem valid_input_of_logPlus1_eq_some {f : Format}
    {input result : Datum} {budget : Budget}
    (hresult : logPlus1 f input budget = some result) : input.Valid f :=
  (input_cases_of_logPlus1_eq_some hresult).1

/-- Exponential-minus-one acceptance excludes infinities and NaNs as inputs. -/
theorem isFinite_input_of_expMinus1_eq_some {f : Format}
    {input result : Datum} {budget : Budget}
    (hresult : expMinus1 f input budget = some result) : input.isFinite = true := by
  rcases (input_cases_of_expMinus1_eq_some hresult).2 with
    ⟨hzero, _⟩ | ⟨_, hinput, _⟩
  · exact (zero_facts hzero).1
  · exact isFinite_of_toRat?_eq_some hinput

/-- Logarithm-plus-one acceptance excludes infinities and NaNs as inputs. -/
theorem isFinite_input_of_logPlus1_eq_some {f : Format}
    {input result : Datum} {budget : Budget}
    (hresult : logPlus1 f input budget = some result) : input.isFinite = true := by
  rcases (input_cases_of_logPlus1_eq_some hresult).2 with
    ⟨hzero, _⟩ | ⟨_, hinput, _⟩
  · exact (zero_facts hzero).1
  · exact isFinite_of_toRat?_eq_some hinput

/-- Every accepted exponential-minus-one datum is representable at the destination. -/
theorem valid_of_expMinus1_eq_some {f : Format}
    {input result : Datum} {budget : Budget}
    (hresult : expMinus1 f input budget = some result) : result.Valid f := by
  obtain ⟨hvalid, ⟨_, hsame⟩ | ⟨_, _, hvalue⟩⟩ :=
    input_cases_of_expMinus1_eq_some hresult
  · exact hsame ▸ hvalid
  · exact valid_of_expMinus1Rat_eq_some hvalue

/-- Every accepted logarithm-plus-one datum is representable at the destination. -/
theorem valid_of_logPlus1_eq_some {f : Format}
    {input result : Datum} {budget : Budget}
    (hresult : logPlus1 f input budget = some result) : result.Valid f := by
  obtain ⟨hvalid, ⟨_, hsame⟩ | ⟨_, _, hvalue⟩⟩ :=
    input_cases_of_logPlus1_eq_some hresult
  · exact hsame ▸ hvalid
  · exact valid_of_logPlus1Rat_eq_some hvalue

/-- Every accepted exponential-minus-one result is finite, including preserved signed zeros. -/
theorem isFinite_of_expMinus1_eq_some {f : Format}
    {input result : Datum} {budget : Budget}
    (hresult : expMinus1 f input budget = some result) : result.isFinite = true := by
  rcases (input_cases_of_expMinus1_eq_some hresult).2 with
    ⟨hzero, hsame⟩ | ⟨_, _, hvalue⟩
  · exact hsame ▸ (zero_facts hzero).1
  · exact isFinite_of_expMinus1Rat_eq_some hvalue

/-- Every accepted logarithm-plus-one result is finite, including preserved signed zeros. -/
theorem isFinite_of_logPlus1_eq_some {f : Format}
    {input result : Datum} {budget : Budget}
    (hresult : logPlus1 f input budget = some result) : result.isFinite = true := by
  rcases (input_cases_of_logPlus1_eq_some hresult).2 with
    ⟨hzero, hsame⟩ | ⟨_, _, hvalue⟩
  · exact hsame ▸ (zero_facts hzero).1
  · exact isFinite_of_logPlus1Rat_eq_some hvalue

/-- The real value of a returned exponential-minus-one datum is the nearest-even rounding of the
exact real target. -/
theorem toReal_of_expMinus1_eq_some {f : Format}
    {input result : Datum} {budget : Budget}
    (hresult : expMinus1 f input budget = some result) :
    toReal result = roundAt f (Real.exp (toReal input) - 1) := by
  rcases (input_cases_of_expMinus1_eq_some hresult).2 with
    ⟨hzero, hsame⟩ | ⟨_, hinput, hvalue⟩
  · rw [← hsame, (zero_facts hzero).2]
    simp
  · rw [toReal_of_toRat?_eq_some hinput]
    exact toReal_of_expMinus1Rat_eq_some hvalue

/-- The real value of a returned logarithm-plus-one datum is the nearest-even rounding of the exact
real target. -/
theorem toReal_of_logPlus1_eq_some {f : Format}
    {input result : Datum} {budget : Budget}
    (hresult : logPlus1 f input budget = some result) :
    toReal result = roundAt f (Real.log (1 + toReal input)) := by
  rcases (input_cases_of_logPlus1_eq_some hresult).2 with
    ⟨hzero, hsame⟩ | ⟨_, hinput, hvalue⟩
  · rw [← hsame, (zero_facts hzero).2]
    simp
  · rw [toReal_of_toRat?_eq_some hinput]
    exact toReal_of_logPlus1Rat_eq_some hvalue

/-- Every accepted logarithm-plus-one input lies strictly above the singularity at minus one. -/
theorem neg_one_lt_of_logPlus1_eq_some {f : Format}
    {input result : Datum} {budget : Budget}
    (hresult : logPlus1 f input budget = some result) : -1 < toReal input := by
  rcases (input_cases_of_logPlus1_eq_some hresult).2 with
    ⟨hzero, _⟩ | ⟨_, hinput, hvalue⟩
  · rw [(zero_facts hzero).2]
    norm_num
  · rw [toReal_of_toRat?_eq_some hinput]
    exact_mod_cast neg_one_lt_of_logPlus1Rat_eq_some hvalue

/-- The exponential-minus-one certificate includes a nearest-point property on the real grid. -/
theorem nearest_of_expMinus1_eq_some {f : Format}
    {input result : Datum} {budget : Budget}
    (hresult : expMinus1 f input budget = some result) :
    Flocq.RoundNearestPoint (Flocq.genericFormat decimalRadix (fexpOf f))
      (Real.exp (toReal input) - 1) (toReal result) := by
  rw [toReal_of_expMinus1_eq_some hresult]
  exact roundAt_nearest f _

/-- The logarithm-plus-one certificate includes a nearest-point property on the real grid. -/
theorem nearest_of_logPlus1_eq_some {f : Format}
    {input result : Datum} {budget : Budget}
    (hresult : logPlus1 f input budget = some result) :
    Flocq.RoundNearestPoint (Flocq.genericFormat decimalRadix (fexpOf f))
      (Real.log (1 + toReal input)) (toReal result) := by
  rw [toReal_of_logPlus1_eq_some hresult]
  exact roundAt_nearest f _

/-- The accepted exponential-minus-one result differs from its real target by at most half a ULP. -/
theorem error_le_half_ulp_of_expMinus1_eq_some {f : Format}
    {input result : Datum} {budget : Budget}
    (hresult : expMinus1 f input budget = some result) :
    |toReal result - (Real.exp (toReal input) - 1)| ≤
      Flocq.ulp decimalRadix (fexpOf f) (Real.exp (toReal input) - 1) / 2 := by
  rw [toReal_of_expMinus1_eq_some hresult]
  exact roundAt_error_le_half_ulp f _

/-- The accepted logarithm-plus-one result differs from its real target by at most half a ULP. -/
theorem error_le_half_ulp_of_logPlus1_eq_some {f : Format}
    {input result : Datum} {budget : Budget}
    (hresult : logPlus1 f input budget = some result) :
    |toReal result - Real.log (1 + toReal input)| ≤
      Flocq.ulp decimalRadix (fexpOf f) (Real.log (1 + toReal input)) / 2 := by
  rw [toReal_of_logPlus1_eq_some hresult]
  exact roundAt_error_le_half_ulp f _

/-- Either valid signed zero retains its entire datum, independently of the refinement budget. -/
theorem expMinus1_of_isZero {f : Format} {input : Datum}
    (hvalid : input.Valid f) (hzero : input.isZero = true) (budget : Budget) :
    expMinus1 f input budget = some input := by
  simp [expMinus1, hvalid, hzero]

/-- Either valid signed zero retains its sign and quantum under logarithm-plus-one. -/
theorem logPlus1_of_isZero {f : Format} {input : Datum}
    (hvalid : input.Valid f) (hzero : input.isZero = true) (budget : Budget) :
    logPlus1 f input budget = some input := by
  simp [logPlus1, hvalid, hzero]

/-- Invalid decimal representations are explicitly rejected by exponential-minus-one. -/
theorem expMinus1_eq_none_of_not_valid {f : Format} {input : Datum}
    (hvalid : ¬input.Valid f) (budget : Budget) : expMinus1 f input budget = none := by
  simp [expMinus1, hvalid]

/-- Invalid decimal representations are explicitly rejected by logarithm-plus-one. -/
theorem logPlus1_eq_none_of_not_valid {f : Format} {input : Datum}
    (hvalid : ¬input.Valid f) (budget : Budget) : logPlus1 f input budget = none := by
  simp [logPlus1, hvalid]

/-- Every infinity and NaN is explicitly rejected by exponential-minus-one. -/
theorem expMinus1_eq_none_of_not_isFinite {f : Format} {input : Datum}
    (hfinite : input.isFinite = false) (budget : Budget) :
    expMinus1 f input budget = none := by
  cases input <;> simp_all [Datum.isFinite, expMinus1, Datum.isZero, Datum.toRat?]

/-- Every infinity and NaN is explicitly rejected by logarithm-plus-one. -/
theorem logPlus1_eq_none_of_not_isFinite {f : Format} {input : Datum}
    (hfinite : input.isFinite = false) (budget : Budget) :
    logPlus1 f input budget = none := by
  cases input <;> simp_all [Datum.isFinite, logPlus1, Datum.isZero, Datum.toRat?]

/-- The datum logarithm interface rejects the real domain at and below minus one. -/
theorem logPlus1_eq_none_of_le_neg_one {f : Format} {input : Datum}
    (hdomain : toReal input ≤ -1) (budget : Budget) :
    logPlus1 f input budget = none := by
  cases hresult : logPlus1 f input budget with
  | none => rfl
  | some result =>
      exact (not_lt_of_ge hdomain (neg_one_lt_of_logPlus1_eq_some hresult)).elim

/-- No direct enclosure search is performed with a zero attempt budget. -/
@[simp] theorem refine_zero (f : Format) (enclose : Nat → Nat → RationalInterval)
    (degree precision : Nat) :
    refine f enclose degree precision 0 = none := rfl

/-- A nonzero logarithm argument with no refinement attempts returns `none`. -/
theorem logPlus1Rat_eq_none_of_no_steps (f : Format) {argument : ℚ}
    (hzero : argument ≠ 0) (degree : Nat) :
    logPlus1Rat f argument { initialDegree := degree, maxAttempts := 0 } = none := by
  simp [logPlus1Rat, hzero, refine]

/-- The exponential tail comparison uses a strictly positive rational bound. -/
theorem expMinus1TailBound_pos (f : Format) : 0 < expMinus1TailBound f :=
  zpow_pos (by norm_num) _

/-- The tail bound stays below one at every descriptor precision. -/
theorem expMinus1TailBound_lt_one (f : Format) : expMinus1TailBound f < 1 :=
  zpow_lt_one_of_neg₀ (by norm_num) (by omega)

/-- The explicit overflow cutoff is positive even when all allowed quanta are negative. -/
theorem expMinus1UpperBound_pos (f : Format) : 0 < expMinus1UpperBound f :=
  zpow_pos (by norm_num) _

/-- Exponential-minus-one acceptance implies the real target lies below the overflow cutoff. -/
theorem lt_upperBound_of_expMinus1Rat_eq_some {f : Format}
    {argument : ℚ} {budget : Budget} {result : Datum}
    (hresult : expMinus1Rat f argument budget = some result) :
    Real.exp (argument : ℝ) - 1 < (expMinus1UpperBound f : ℝ) := by
  have hupper : 0 < (expMinus1UpperBound f : ℝ) := by
    exact_mod_cast expMinus1UpperBound_pos f
  rcases expMinus1Rat_cases_of_eq_some hresult with
    ⟨hzero, -⟩ | ⟨hsmall, -⟩ | ⟨hlarge, -⟩
  · simpa [hzero] using hupper
  · have htail : (expMinus1TailBound f : ℝ) < 1 := by
      exact_mod_cast expMinus1TailBound_lt_one f
    linarith
  · simp only [Rat.cast_add, Rat.cast_one] at hlarge
    linarith

/-- Real results beyond the explicit finite-range cutoff are rejected for every search budget. -/
theorem expMinus1Rat_eq_none_of_upperBound_le {f : Format} {argument : ℚ}
    (hlarge : (expMinus1UpperBound f : ℝ) ≤ Real.exp (argument : ℝ) - 1)
    (budget : Budget) : expMinus1Rat f argument budget = none := by
  cases hresult : expMinus1Rat f argument budget with
  | none => rfl
  | some result =>
      exact (not_lt_of_ge hlarge (lt_upperBound_of_expMinus1Rat_eq_some hresult)).elim

/-- Outside the exact-zero and negative-tail shortcuts, a zero search budget returns `none`. -/
theorem expMinus1Rat_eq_none_of_no_steps (f : Format) {argument : ℚ}
    (hzero : argument ≠ 0)
    (htail : ElementaryComparison.compareExp argument (expMinus1TailBound f) = .gt)
    (degree : Nat) :
    expMinus1Rat f argument { initialDegree := degree, maxAttempts := 0 } = none := by
  simp [expMinus1Rat, hzero, htail, refine]

end FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Certified
