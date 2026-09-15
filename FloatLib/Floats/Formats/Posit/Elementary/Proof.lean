/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Elementary.Runtime
public import FloatLib.Floats.Formats.Posit.Rounding.Comparison.Proof
public import FloatLib.Floats.Formats.Posit.Semantics.Exact.Proof
public import FloatLib.Numerics.Exact.Elementary.Proof

/-!
# Correct rounding of natural posit elementary functions

The real-rounding theorems cover every finite input in the function's domain, including
extreme magnitudes, exact zero results, and the standard nonzero saturation rule.
Separate theorems record NaR propagation and invalid logarithm domains.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

namespace Elementary

/-- Exact exponential evaluation and output subtraction share one final rounding. -/
theorem expRat_eq_real (format : Format) (argument offset : Rat) :
    expRat format argument offset =
      RealRounding.round format (Real.exp (argument : ℝ) - (offset : ℝ)) := by
  unfold expRat
  apply ComparisonRounding.roundSigned_eq_real
  intro boundary
  rw [FloatLib.Numerics.ElementaryComparison.prepareExp_eq_real, Rat.cast_add]
  simp only [cmp, cmpUsing, sub_lt_iff_lt_add, lt_sub_iff_add_lt, add_comm]

/-- A positive rational logarithm argument is rounded according to its exact real value. -/
theorem logRat_eq_real (format : Format) (argument : Rat) (hpositive : 0 < argument) :
    logRat format argument = RealRounding.round format (Real.log (argument : ℝ)) := by
  rw [logRat, dite_eq_left hpositive]
  exact ComparisonRounding.roundSigned_eq_real format _ _
    (fun boundary => FloatLib.Numerics.ElementaryComparison.prepareLog_eq_real
      argument (format.bits.log2 + 2) hpositive boundary)

/-- Nonpositive arguments produce NaR before logarithm evaluation. -/
theorem logRat_eq_nar (format : Format) (argument : Rat) (hnonpositive : argument ≤ 0) :
    logRat format argument = nar format := by
  simp [logRat, not_lt_of_ge hnonpositive]

/-- Exponential evaluation propagates NaR for every exact output offset. -/
@[simp] theorem applyExp_nar {format : Format} (offset : Rat) :
    applyExp offset (nar format) = nar format := by
  simp [applyExp]

/-- Logarithm evaluation propagates NaR for every exact input offset. -/
@[simp] theorem applyLog_nar {format : Format} (offset : Rat) :
    applyLog offset (nar format) = nar format := by
  simp [applyLog]

/-- Finite exponential evaluation agrees with signed real rounding. -/
theorem applyExp_eq_real {format : Format} (offset : Rat) (value : Model format) {q : Rat}
    (hvalue : value.toRat? = some q) :
    applyExp offset value =
      RealRounding.round format (Real.exp (q : ℝ) - (offset : ℝ)) := by
  simp only [applyExp, hvalue]
  exact expRat_eq_real format q offset

/-- Finite logarithm evaluation forms its input offset exactly. -/
theorem applyLog_eq_real {format : Format} (offset : Rat) (value : Model format) {q : Rat}
    (hvalue : value.toRat? = some q) (hpositive : 0 < q + offset) :
    applyLog offset value =
      RealRounding.round format (Real.log ((q : ℝ) + (offset : ℝ))) := by
  simp only [applyLog, hvalue]
  simpa only [Rat.cast_add] using logRat_eq_real format (q + offset) hpositive

/-- Invalid exact-offset logarithm arguments produce NaR. -/
theorem applyLog_eq_nar {format : Format} (offset : Rat) (value : Model format) {q : Rat}
    (hvalue : value.toRat? = some q) (hnonpositive : q + offset ≤ 0) :
    applyLog offset value = nar format := by
  simp only [applyLog, hvalue]
  exact logRat_eq_nar format (q + offset) hnonpositive

end Elementary

variable {format : Format}

/-- Natural exponential has the exact signed real rounding required by the standard. -/
theorem exp_eq_real (value : Model format) {q : Rat} (hvalue : value.toRat? = some q) :
    exp value = RealRounding.round format (Real.exp (q : ℝ)) := by
  simpa [exp] using Elementary.applyExp_eq_real 0 value hvalue

/-- `expMinus1` rounds the exact exponential minus one, including near zero. -/
theorem expMinus1_eq_real (value : Model format) {q : Rat}
    (hvalue : value.toRat? = some q) :
    expMinus1 value = RealRounding.round format (Real.exp (q : ℝ) - 1) := by
  simpa [expMinus1] using Elementary.applyExp_eq_real 1 value hvalue

/-- Natural logarithm has the exact signed real rounding on its positive domain. -/
theorem log_eq_real (value : Model format) {q : Rat}
    (hvalue : value.toRat? = some q) (hq : 0 < q) :
    log value = RealRounding.round format (Real.log (q : ℝ)) := by
  simpa [log] using Elementary.applyLog_eq_real 0 value hvalue (by simpa using hq)

/-- `logPlus1` forms `1 + x` exactly before rounding the natural logarithm. -/
theorem logPlus1_eq_real (value : Model format) {q : Rat}
    (hvalue : value.toRat? = some q) (hq : -1 < q) :
    logPlus1 value = RealRounding.round format (Real.log (1 + (q : ℝ))) := by
  simpa [logPlus1, add_comm] using
    Elementary.applyLog_eq_real 1 value hvalue (by linarith)

/-- Natural exponential propagates NaR. -/
@[simp] theorem exp_nar : exp (nar format) = nar format := Elementary.applyExp_nar _
/-- Exponential minus one propagates NaR. -/
@[simp] theorem expMinus1_nar : expMinus1 (nar format) = nar format := Elementary.applyExp_nar _
/-- Natural logarithm propagates NaR. -/
@[simp] theorem log_nar : log (nar format) = nar format := Elementary.applyLog_nar _
/-- Natural logarithm of one plus the input propagates NaR. -/
@[simp] theorem logPlus1_nar : logPlus1 (nar format) = nar format := Elementary.applyLog_nar _

/-- Natural logarithm rejects zero and negative finite values. -/
theorem log_eq_nar_of_nonpos (value : Model format) {q : Rat}
    (hvalue : value.toRat? = some q) (hq : q ≤ 0) : log value = nar format :=
  Elementary.applyLog_eq_nar 0 value hvalue (by simpa using hq)

/-- Natural `Plus1` logarithm rejects finite values at or below `-1`. -/
theorem logPlus1_eq_nar_of_le_neg_one (value : Model format) {q : Rat}
    (hvalue : value.toRat? = some q) (hq : q ≤ -1) : logPlus1 value = nar format :=
  Elementary.applyLog_eq_nar 1 value hvalue (by linarith)

end FloatLib.Floats.Formats.Posit.Model
