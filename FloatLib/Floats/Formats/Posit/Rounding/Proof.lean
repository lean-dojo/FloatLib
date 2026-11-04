/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Runtime

/-!
# Correctness of exact rational-to-posit rounding

These are the laws of the rational-to-posit specification in `Rounding.Runtime`. Bisection finds
the cutoff whenever the accepted codes form a prefix, the threshold test sits at the standard's
appended-bit boundary, rounding the value of a finite code gives that code back, and rounding
commutes with negation (`roundRat_neg`). Import this module for the proofs alone, or the
`FloatLib.Floats.Formats.Posit` family entry point for the whole public interface.

## References

* Posit Working Group, *Standard for Posit Arithmetic (2022)*, March 2, 2022,
  Section 4, <https://posithub.org/docs/posit_standard-2.pdf>.
* John L. Gustafson, *Standard Posit Arithmetic*, Supercomputing Frontiers and Innovations 9(1),
  2022, <https://doi.org/10.14529/jsfi220102>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

variable {format : Format}

/--
A bisection step on a nontrivial interval tests the strictly interior midpoint and recurses on
the half that it selects.
-/
private theorem lowerCodeByBisection_succ_of_lt
    (accept : Nat → Bool) (fuel lower upper : Nat)
    (hnontrivial : lower + 1 < upper) :
    lower < (lower + upper) / 2 ∧ (lower + upper) / 2 < upper ∧
      lowerCodeByBisection accept (fuel + 1) lower upper =
        if accept ((lower + upper) / 2) then
          lowerCodeByBisection accept fuel ((lower + upper) / 2) upper
        else
          lowerCodeByBisection accept fuel lower ((lower + upper) / 2) :=
  ⟨by omega, by omega, by rw [lowerCodeByBisection, ite_eq_left hnontrivial]⟩

/--
Bounded bisection never reaches its exclusive upper endpoint.

This is a structural range fact and needs no monotonicity of `accept`. Every recursive branch
keeps a nonempty half-open interval and eventually returns one of its lower endpoints.
-/
theorem lowerCodeByBisection_lt_upper
    (accept : Nat → Bool) (fuel lower upper : Nat)
    (hlower : lower < upper) :
    lowerCodeByBisection accept fuel lower upper < upper := by
  induction fuel generalizing lower upper with
  | zero =>
      simpa [lowerCodeByBisection] using hlower
  | succ fuel inductionHypothesis =>
      by_cases hnontrivial : lower + 1 < upper
      · obtain ⟨hlowerMiddle, hmiddleUpper, hstep⟩ :=
          lowerCodeByBisection_succ_of_lt accept fuel lower upper hnontrivial
        rw [hstep]
        split
        · exact inductionHypothesis _ upper hmiddleUpper
        · exact (inductionHypothesis lower _ hlowerMiddle).trans hmiddleUpper
      · rw [lowerCodeByBisection, ite_eq_right hnontrivial]
        exact hlower

/-- Bounded bisection never returns below its initial lower endpoint. -/
theorem lower_le_lowerCodeByBisection
    (accept : Nat → Bool) (fuel lower upper : Nat) :
    lower ≤ lowerCodeByBisection accept fuel lower upper := by
  induction fuel generalizing lower upper with
  | zero =>
      rfl
  | succ fuel inductionHypothesis =>
      by_cases hnontrivial : lower + 1 < upper
      · obtain ⟨hlowerMiddle, -, hstep⟩ :=
          lowerCodeByBisection_succ_of_lt accept fuel lower upper hnontrivial
        rw [hstep]
        split
        · exact hlowerMiddle.le.trans (inductionHypothesis _ upper)
        · exact inductionHypothesis lower _
      · rw [lowerCodeByBisection, ite_eq_right hnontrivial]

/--
Bounded bisection is monotone under pointwise inclusion of accepted candidates.

The theorem is independent of monotonicity in the candidate index. It only uses that changing a
rejected midpoint to accepted moves the active interval upward.
-/
theorem lowerCodeByBisection_mono_accept
    (leftAccept rightAccept : Nat → Bool)
    (fuel lower upper : Nat)
    (haccept :
      ∀ code, leftAccept code = true → rightAccept code = true) :
    lowerCodeByBisection leftAccept fuel lower upper ≤
      lowerCodeByBisection rightAccept fuel lower upper := by
  induction fuel generalizing lower upper with
  | zero =>
      exact le_rfl
  | succ fuel inductionHypothesis =>
      by_cases hnontrivial : lower + 1 < upper
      · obtain ⟨hlowerMiddle, -, hleftStep⟩ :=
          lowerCodeByBisection_succ_of_lt leftAccept fuel lower upper hnontrivial
        obtain ⟨-, -, hrightStep⟩ :=
          lowerCodeByBisection_succ_of_lt rightAccept fuel lower upper hnontrivial
        rw [hleftStep, hrightStep]
        by_cases hleft : leftAccept ((lower + upper) / 2)
        · simp only [hleft, haccept _ hleft, ite_true]
          exact inductionHypothesis _ upper
        · simp only [Bool.eq_false_of_not_eq_true hleft, Bool.false_eq_true, ite_false]
          by_cases hright : rightAccept ((lower + upper) / 2)
          · simp only [hright, ite_true]
            exact
              (lowerCodeByBisection_lt_upper
                leftAccept fuel lower _ hlowerMiddle).le.trans
                (lower_le_lowerCodeByBisection
                  rightAccept fuel _ upper)
          · simp only [Bool.eq_false_of_not_eq_true hright, Bool.false_eq_true, ite_false]
            exact inductionHypothesis lower _
      · rw [lowerCodeByBisection, lowerCodeByBisection,
          ite_eq_right hnontrivial, ite_eq_right hnontrivial]

/--
Bounded bisection depends only on predicate values strictly inside its current interval.

This lets semantic monotonicity replace the exact-rational comparison predicate with a plain code
prefix without making any claim about out-of-range natural arguments.
-/
theorem lowerCodeByBisection_congr
    (leftAccept rightAccept : Nat → Bool)
    (fuel lower upper : Nat)
    (hagrees : ∀ code, lower < code → code < upper →
      leftAccept code = rightAccept code) :
    lowerCodeByBisection leftAccept fuel lower upper =
      lowerCodeByBisection rightAccept fuel lower upper := by
  induction fuel generalizing lower upper with
  | zero =>
      rfl
  | succ fuel inductionHypothesis =>
      by_cases hnontrivial : lower + 1 < upper
      · obtain ⟨hlowerMiddle, hmiddleUpper, hleftStep⟩ :=
          lowerCodeByBisection_succ_of_lt leftAccept fuel lower upper hnontrivial
        obtain ⟨-, -, hrightStep⟩ :=
          lowerCodeByBisection_succ_of_lt rightAccept fuel lower upper hnontrivial
        rw [hleftStep, hrightStep, hagrees _ hlowerMiddle hmiddleUpper]
        by_cases haccept : rightAccept ((lower + upper) / 2)
        · simp only [haccept, ite_true]
          exact inductionHypothesis _ upper fun code hmiddleCode hcodeUpper =>
            hagrees code (hlowerMiddle.trans hmiddleCode) hcodeUpper
        · simp only [Bool.eq_false_of_not_eq_true haccept, Bool.false_eq_true, ite_false]
          exact inductionHypothesis lower _ fun code hlowerCode hcodeMiddle =>
            hagrees code hlowerCode (hcodeMiddle.trans hmiddleUpper)
      · rw [lowerCodeByBisection, lowerCodeByBisection,
          ite_eq_right hnontrivial, ite_eq_right hnontrivial]

/--
Bounded bisection returns the cutoff when the accepted codes form a prefix of the naturals.

The interval invariant is `lower ≤ cutoff < upper`. The span bound says the remaining interval
holds at most `2 ^ fuel` unit steps, so every nontrivial midpoint leaves at most half the old span.
Nothing here depends on posit decoding, and every exact comparison domain that drives the same
search reuses this theorem.
-/
theorem lowerCodeByBisection_eq_cutoff
    (fuel lower upper cutoff : Nat)
    (hlower : lower ≤ cutoff)
    (hupper : cutoff < upper)
    (hspan : upper - lower ≤ 2 ^ fuel) :
    lowerCodeByBisection
        (fun code => decide (code ≤ cutoff)) fuel lower upper =
      cutoff := by
  induction fuel generalizing lower upper with
  | zero =>
      simp only [lowerCodeByBisection]
      norm_num at hspan
      omega
  | succ fuel inductionHypothesis =>
      by_cases hnontrivial : lower + 1 < upper
      · obtain ⟨hlowerMiddle, hmiddleUpper, hstep⟩ :=
          lowerCodeByBisection_succ_of_lt (fun code => decide (code ≤ cutoff))
            fuel lower upper hnontrivial
        rw [hstep]
        rw [Nat.pow_succ] at hspan
        by_cases hmiddle : (lower + upper) / 2 ≤ cutoff
        · rw [ite_eq_left (decide_eq_true hmiddle)]
          exact inductionHypothesis _ upper hmiddle hupper (by omega)
        · rw [ite_eq_right (fun h => hmiddle (of_decide_eq_true h))]
          exact inductionHypothesis lower _ hlower (by omega) (by omega)
      · rw [lowerCodeByBisection, ite_eq_right hnontrivial]
        omega

/--
The fuel and initial interval used by an `n`-bit posit search recover every nonnegative finite
code when the comparison predicate is the corresponding code prefix.
-/
theorem lowerCodeByBisection_eq_cutoff_for_format
    (format : Format) (cutoff : Nat)
    (hcutoff : cutoff < format.signMaskNat) :
    lowerCodeByBisection
        (fun code => decide (code ≤ cutoff))
        format.bits 0 format.signMaskNat =
      cutoff := by
  apply lowerCodeByBisection_eq_cutoff
  · exact Nat.zero_le cutoff
  · exact hcutoff
  · simp only [Nat.sub_zero]
    exact Nat.le_of_lt format.signMaskNat_lt_modulus

/--
A candidate bracketed by its exact value and successor is the reference lower code.

Direct arithmetic packers use this theorem to identify a constructed candidate with the search
result by proving bounds against the candidate and its successor.
-/
theorem lowerCodeForPositive_eq_of_bracket
    (format : Format) (target : Rat) (candidate : Nat)
    (hcandidate : candidate < format.signMaskNat)
    (hlower :
      nonnegativeRatAt format candidate ≤ target)
    (hupper :
      candidate + 1 < format.signMaskNat →
        target < nonnegativeRatAt format (candidate + 1)) :
    lowerCodeForPositive format target = candidate := by
  unfold lowerCodeForPositive
  rw [lowerCodeByBisection_congr
    (fun code => decide (nonnegativeRatAt format code ≤ target))
    (fun code => decide (code ≤ candidate))
    format.bits 0 format.signMaskNat]
  · exact lowerCodeByBisection_eq_cutoff_for_format
      format candidate hcandidate
  · intro code _hcodePos hcode
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro hvalue
      by_contra hnotCode
      have hsuccessorCode : candidate + 1 ≤ code := by
        omega
      have hsuccessorRange :
          candidate + 1 < format.signMaskNat :=
        lt_of_le_of_lt hsuccessorCode hcode
      have hsuccessorLe :
          nonnegativeRatAt format (candidate + 1) ≤
            nonnegativeRatAt format code :=
        (nonnegativeRatAt_le_iff format hsuccessorRange hcode).2
          hsuccessorCode
      exact (not_lt_of_ge hvalue)
        ((hupper hsuccessorRange).trans_le hsuccessorLe)
    · intro hcodeLe
      have hcandidateValue :
          nonnegativeRatAt format code ≤
            nonnegativeRatAt format candidate :=
        (nonnegativeRatAt_le_iff format hcode hcandidate).2 hcodeLe
      exact hcandidateValue.trans hlower

/--
Once the lower-code search reaches `maxPos`, positive rounding must return `maxPos`.

This endpoint fact is independent of how an execution kernel established the lower code. Direct
dyadic, quotient, and square-root packers can therefore share the final
reference-rounding argument.
-/
theorem roundPositiveCode_eq_maxPositive_of_lowerCode
    (format : Format) (target : Rat)
    (hminimum : minPositiveRat format ≤ target)
    (hlower :
      lowerCodeForPositive format target =
        format.signMaskNat - 1) :
    roundPositiveCode format target =
      format.signMaskNat - 1 := by
  have hpositive : 0 < target :=
    (nonnegativeRatAt_pos format (by decide) format.one_lt_signMaskNat).trans_le hminimum
  unfold roundPositiveCode
  rw [ite_eq_right (not_le_of_gt hpositive)]
  rw [ite_eq_right (not_lt_of_ge hminimum)]
  dsimp only
  rw [hlower]
  rw [ite_eq_right]
  have hsignMaskPositive := format.signMaskNat_pos
  omega

/--
Below `maxPos`, positive rounding is the appended-bit threshold decision at the lower code.

This is the interior counterpart of `roundPositiveCode_eq_maxPositive_of_lowerCode`: a kernel that
has identified the lower code and shown that its successor is still positive gets the
nearest-even choice between the two, with ties going to the even code.
-/
theorem roundPositiveCode_eq_midpointDecision_of_lowerCode
    (format : Format) (target : Rat) (lower : Nat)
    (hpositive : 0 < target)
    (hminimum : minPositiveRat format ≤ target)
    (hlower : lowerCodeForPositive format target = lower)
    (hsuccessor : lower + 1 < format.signMaskNat) :
    roundPositiveCode format target =
      let threshold := roundingThreshold format lower
      if target < threshold then
        lower
      else if threshold < target then
        lower + 1
      else if lower % 2 = 0 then
        lower
      else
        lower + 1 := by
  unfold roundPositiveCode
  rw [ite_eq_right (not_le_of_gt hpositive), ite_eq_right (not_lt_of_ge hminimum)]
  dsimp only
  rw [hlower, ite_eq_left hsuccessor]

/--
Searching for the exact value of a nonnegative finite code recovers that code at every width.
-/
theorem lowerCodeForPositive_nonnegativeRatAt
    (format : Format) (code : Nat)
    (hcode : code < format.signMaskNat) :
    lowerCodeForPositive format
        (nonnegativeRatAt format code) =
      code :=
  lowerCodeForPositive_eq_of_bracket format _ code hcode le_rfl
    (nonnegativeRatAt_lt_of_lt format (Nat.lt_succ_self code))

/--
The standard's appended-one rounding boundary is strictly above its retained lower code.

The proof embeds the lower `n`-bit code as the even `(n + 1)`-bit code `U0`, then applies the
global unsigned-code ordering theorem to the adjacent code `U1`.
-/
theorem nonnegativeRatAt_lt_roundingThreshold
    (format : Format) {code : Nat}
    (hcode : code < format.signMaskNat) :
    nonnegativeRatAt format code <
      roundingThreshold format code := by
  rw [roundingThreshold,
    ← nonnegativeRatAt_nextPrecision_two_mul
      format hcode]
  apply nonnegativeRatAt_lt_of_lt
    format.nextPrecision
  · omega
  · simp only [Format.nextPrecision_signMaskNat]
    omega

/--
Positive-code rounding is a left inverse of exact decoding on the complete nonnegative finite
interval.

This is the arbitrary-width encoder round-trip theorem. It combines global decoder monotonicity,
exact bisection recovery, and the standard's appended-bit boundary, with no enumeration of small
widths.
-/
theorem roundPositiveCode_nonnegativeRatAt
    (format : Format) {code : Nat}
    (hcode : code < format.signMaskNat) :
    roundPositiveCode format
        (nonnegativeRatAt format code) =
      code := by
  rcases Nat.eq_zero_or_pos code with rfl | hpos
  · simp [roundPositiveCode]
  have hminLe :
      minPositiveRat format ≤
        nonnegativeRatAt format code :=
    (nonnegativeRatAt_le_iff format format.one_lt_signMaskNat hcode).2 hpos
  have hlower := lowerCodeForPositive_nonnegativeRatAt format code hcode
  by_cases hupper : code + 1 < format.signMaskNat
  · rw [roundPositiveCode_eq_midpointDecision_of_lowerCode format _ code
      (nonnegativeRatAt_pos format hpos hcode) hminLe hlower hupper]
    exact ite_eq_left (nonnegativeRatAt_lt_roundingThreshold format hcode)
  · rw [roundPositiveCode_eq_maxPositive_of_lowerCode format _ hminLe
      (by rw [hlower]; omega)]
    omega

/-- Rounding the value of a nonnegative finite code with `roundPositiveRat` gives that code back. -/
theorem roundPositiveRat_nonnegativeRatAt
    (format : Format) {code : Nat}
    (hcode : code < format.signMaskNat) :
    roundPositiveRat format
        (nonnegativeRatAt format code) =
      ofNatBits code := by
  simp [roundPositiveRat,
    roundPositiveCode_nonnegativeRatAt
      format hcode]

/-- Rounding the rational zero gives the posit zero. -/
@[simp] theorem roundRat_zero (format : Format) :
    roundRat format 0 = zero format := by
  simp [roundRat]

/-- Rounding a nonnegative rational, zero included, is positive-magnitude rounding. -/
theorem roundRat_of_nonneg {value : Rat} (hvalue : 0 ≤ value) :
    roundRat format value = roundPositiveRat format value := by
  rcases hvalue.eq_or_lt with rfl | hpositive
  · simp [roundPositiveRat, roundPositiveCode, zero]
  · simp [roundRat, hpositive.ne', not_lt.mpr hpositive.le]

/-- Rounding a negative rational is encoding-level negation of rounding its magnitude. -/
theorem roundRat_of_neg {value : Rat} (hvalue : value < 0) :
    roundRat format value = neg (roundPositiveRat format (-value)) := by
  simp [roundRat, hvalue, ne_of_lt hvalue]

/--
Standard posit rounding is odd: rounding a negated rational gives the two's-complement negation of
the rounded value. Zero is fixed (`roundRat_zero`, `neg_zero`).
-/
theorem roundRat_neg (value : Rat) :
    roundRat format (-value) = neg (roundRat format value) := by
  rcases lt_or_ge value 0 with hvalue | hvalue
  · rw [roundRat_of_neg hvalue, Model.neg_neg, roundRat_of_nonneg (neg_nonneg.mpr hvalue.le)]
  · rcases hvalue.eq_or_lt with rfl | hpositive
    · simp
    · rw [roundRat_of_neg (neg_lt_zero.mpr hpositive), neg_neg, roundRat_of_nonneg hvalue]

/--
The public exact-rational rounding specification re-encodes every nonnegative finite posit.

Together with whole-word two's-complement symmetry, this supplies the canonical arbitrary-width
decode/encode round-trip used by optimized backends.
-/
theorem roundRat_nonnegativeRatAt
    (format : Format) {code : Nat}
    (hcode : code < format.signMaskNat) :
    roundRat format
        (nonnegativeRatAt format code) =
      ofNatBits code := by
  rw [roundRat_of_nonneg (nonnegativeRatAt_nonneg format hcode)]
  exact roundPositiveRat_nonnegativeRatAt format hcode

/-- The total positive-code helper preserves exact zero. -/
@[simp] theorem roundPositiveCode_zero (format : Format) :
    roundPositiveCode format 0 = 0 := by
  simp [roundPositiveCode]

/-- The square-root code of zero is the zero code. -/
@[simp] theorem roundSqrtCode_zero (format : Format) :
    roundSqrtCode format 0 = 0 := by
  simp [roundSqrtCode]

/-- The rounded square root of zero is the posit zero. -/
@[simp] theorem roundSqrtRat_zero (format : Format) :
    roundSqrtRat format 0 = zero format := by
  simp [roundSqrtRat, roundSqrtCode, zero]

end FloatLib.Floats.Formats.Posit.Model
