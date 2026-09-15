/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Runtime

/-!
# Correctness of exact rational-to-posit rounding

The executable rational-to-posit specification in `Rounding.Runtime` satisfies search,
threshold, round-trip, and sign laws. Import this module for these proofs, or import the
`FloatLib.Floats.Formats.Posit` family entry point for the complete public interface.

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
Bounded bisection never reaches its exclusive upper endpoint.

This structural range fact does not require monotonicity of `accept`; every recursive branch
retains a nonempty half-open interval and eventually returns one of its lower endpoints.
-/
theorem lowerCodeByBisection_lt_upper
    (accept : Nat → Bool) (fuel lower upper : Nat)
    (hlower : lower < upper) :
    lowerCodeByBisection accept fuel lower upper < upper := by
  induction fuel generalizing lower upper with
  | zero =>
      simpa [lowerCodeByBisection] using hlower
  | succ fuel inductionHypothesis =>
      rw [lowerCodeByBisection]
      by_cases hnontrivial : lower + 1 < upper
      · rw [if_pos hnontrivial]
        let middle := (lower + upper) / 2
        have hlowerMiddle : lower < middle := by
          dsimp [middle]
          omega
        have hmiddleUpper : middle < upper := by
          dsimp [middle]
          omega
        by_cases haccept : accept middle
        · rw [if_pos haccept]
          exact inductionHypothesis middle upper hmiddleUpper
        · rw [if_neg haccept]
          exact lt_trans
            (inductionHypothesis lower middle hlowerMiddle)
            hmiddleUpper
      · rw [if_neg hnontrivial]
        exact hlower

/-- Bounded bisection never returns below its initial lower endpoint. -/
theorem lower_le_lowerCodeByBisection
    (accept : Nat → Bool) (fuel lower upper : Nat) :
    lower ≤ lowerCodeByBisection accept fuel lower upper := by
  induction fuel generalizing lower upper with
  | zero =>
      rfl
  | succ fuel inductionHypothesis =>
      rw [lowerCodeByBisection]
      by_cases hnontrivial : lower + 1 < upper
      · rw [if_pos hnontrivial]
        let middle := (lower + upper) / 2
        have hlowerMiddle : lower < middle := by
          dsimp [middle]
          omega
        by_cases haccept : accept middle
        · rw [if_pos haccept]
          exact hlowerMiddle.le.trans
            (inductionHypothesis middle upper)
        · rw [if_neg haccept]
          exact inductionHypothesis lower middle
      · rw [if_neg hnontrivial]

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
      rw [lowerCodeByBisection, lowerCodeByBisection]
      by_cases hnontrivial : lower + 1 < upper
      · rw [if_pos hnontrivial, if_pos hnontrivial]
        let middle := (lower + upper) / 2
        have hlowerMiddle : lower < middle := by
          dsimp [middle]
          omega
        have hmiddleUpper : middle < upper := by
          dsimp [middle]
          omega
        change
          (if leftAccept middle then
              lowerCodeByBisection leftAccept fuel middle upper
            else
              lowerCodeByBisection leftAccept fuel lower middle) ≤
            if rightAccept middle then
              lowerCodeByBisection rightAccept fuel middle upper
            else
              lowerCodeByBisection rightAccept fuel lower middle
        by_cases hleft : leftAccept middle
        · have hright : rightAccept middle = true :=
            haccept middle hleft
          simp only [hleft, hright, if_true]
          exact inductionHypothesis middle upper
        · have hleftFalse : leftAccept middle = false :=
            Bool.eq_false_of_not_eq_true hleft
          simp only [hleftFalse, Bool.false_eq_true, if_false]
          by_cases hright : rightAccept middle
          · simp only [hright, if_true]
            exact
              (lowerCodeByBisection_lt_upper
                leftAccept fuel lower middle hlowerMiddle).le.trans
                (lower_le_lowerCodeByBisection
                  rightAccept fuel middle upper)
          · have hrightFalse : rightAccept middle = false :=
              Bool.eq_false_of_not_eq_true hright
            simp only [hrightFalse, Bool.false_eq_true, if_false]
            exact inductionHypothesis lower middle
      · rw [if_neg hnontrivial, if_neg hnontrivial]

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
      rw [lowerCodeByBisection, lowerCodeByBisection]
      by_cases hnontrivial : lower + 1 < upper
      · rw [if_pos hnontrivial, if_pos hnontrivial]
        let middle := (lower + upper) / 2
        have hlowerMiddle : lower < middle := by
          dsimp [middle]
          omega
        have hmiddleUpper : middle < upper := by
          dsimp [middle]
          omega
        have hmiddle :=
          hagrees middle hlowerMiddle hmiddleUpper
        change
          (if leftAccept middle then
              lowerCodeByBisection
                leftAccept fuel middle upper
            else
              lowerCodeByBisection
                leftAccept fuel lower middle) =
            if rightAccept middle then
              lowerCodeByBisection
                rightAccept fuel middle upper
            else
              lowerCodeByBisection
                rightAccept fuel lower middle
        rw [hmiddle]
        by_cases haccept : rightAccept middle
        · simp only [haccept, if_true]
          apply inductionHypothesis
          intro code hmiddleCode hcodeUpper
          exact hagrees code
            (hlowerMiddle.trans hmiddleCode) hcodeUpper
        · have hacceptFalse :=
            Bool.eq_false_of_not_eq_true haccept
          simp only [hacceptFalse,
            Bool.false_eq_true, if_false]
          apply inductionHypothesis
          intro code hlowerCode hcodeMiddle
          exact hagrees code hlowerCode
            (hcodeMiddle.trans hmiddleUpper)
      · rw [if_neg hnontrivial,
          if_neg hnontrivial]

/--
Bounded bisection exactly recovers a cutoff when the accepted codes form a natural-number prefix.

The interval invariant is `lower ≤ cutoff < upper`. The span bound states that the remaining
interval contains at most `2 ^ fuel` unit steps, so every nontrivial midpoint leaves at most half
the old span. This theorem is independent of posit decoding and can therefore be reused by every
exact comparison domain that drives the same search.
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
      rw [lowerCodeByBisection]
      by_cases hnontrivial : lower + 1 < upper
      · rw [if_pos hnontrivial]
        let middle := (lower + upper) / 2
        have hlowerMiddle : lower < middle := by
          dsimp [middle]
          omega
        have hmiddleUpper : middle < upper := by
          dsimp [middle]
          omega
        by_cases hmiddle : middle ≤ cutoff
        · have haccept :
              decide (middle ≤ cutoff) = true :=
            decide_eq_true hmiddle
          dsimp only
          rw [haccept]
          apply inductionHypothesis middle upper
          · exact hmiddle
          · exact hupper
          · rw [Nat.pow_succ] at hspan
            dsimp [middle]
            omega
        · have haccept :
              decide (middle ≤ cutoff) = false :=
            decide_eq_false hmiddle
          dsimp only
          rw [haccept]
          apply inductionHypothesis lower middle
          · exact hlower
          · omega
          · rw [Nat.pow_succ] at hspan
            dsimp [middle]
            omega
      · rw [if_neg hnontrivial]
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
    (hpositive : 0 < target)
    (hminimum : minPositiveRat format ≤ target)
    (hlower :
      lowerCodeForPositive format target =
        format.signMaskNat - 1) :
    roundPositiveCode format target =
      format.signMaskNat - 1 := by
  unfold roundPositiveCode
  rw [if_neg (not_le_of_gt hpositive)]
  rw [if_neg (not_lt_of_ge hminimum)]
  dsimp only
  rw [hlower]
  rw [if_neg]
  have hsignMaskPositive := format.signMaskNat_pos
  omega

/--
Searching for the exact value of a nonnegative finite code recovers that code at every width.
-/
theorem lowerCodeForPositive_nonnegativeRatAt
    (format : Format) (code : Nat)
    (hcode : code < format.signMaskNat) :
    lowerCodeForPositive format
        (nonnegativeRatAt format code) =
      code := by
  unfold lowerCodeForPositive
  rw [lowerCodeByBisection_congr
    (fun candidate =>
      decide
        (nonnegativeRatAt format candidate ≤
          nonnegativeRatAt format code))
    (fun candidate => decide (candidate ≤ code))
    format.bits 0 format.signMaskNat (by
      intro candidate _ hcand
      simp only [
        nonnegativeRatAt_le_iff
          format hcand hcode])]
  exact lowerCodeByBisection_eq_cutoff_for_format
    format code hcode

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
exact bisection recovery, and the standard's appended-bit boundary rather than relying on
small-width enumeration.
-/
theorem roundPositiveCode_nonnegativeRatAt
    (format : Format) {code : Nat}
    (hcode : code < format.signMaskNat) :
    roundPositiveCode format
        (nonnegativeRatAt format code) =
      code := by
  by_cases hzero : code = 0
  · subst code
    rw [nonnegativeRatAt_zero]
    simp [roundPositiveCode]
  have hpos : 0 < code :=
    Nat.pos_of_ne_zero hzero
  have htargetPos :
      0 < nonnegativeRatAt format code :=
    nonnegativeRatAt_pos format hpos hcode
  have hminLe :
      minPositiveRat format ≤
        nonnegativeRatAt format code := by
    unfold minPositiveRat
    exact
      (nonnegativeRatAt_le_iff
        format format.one_lt_signMaskNat hcode).2
        (by omega)
  unfold roundPositiveCode
  rw [if_neg (not_le_of_gt htargetPos)]
  rw [if_neg (not_lt_of_ge hminLe)]
  dsimp only
  rw [lowerCodeForPositive_nonnegativeRatAt
    format code hcode]
  by_cases hupper :
      code + 1 < format.signMaskNat
  · rw [if_pos hupper]
    rw [if_pos
      (nonnegativeRatAt_lt_roundingThreshold
        format hcode)]
  · rw [if_neg hupper]

/-- Model-valued positive rounding exactly re-encodes every nonnegative finite code. -/
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
  by_cases hzero : code = 0
  · subst code
    simp [zero]
  have hpos : 0 < code :=
    Nat.pos_of_ne_zero hzero
  have htargetPos :
      0 < nonnegativeRatAt format code :=
    nonnegativeRatAt_pos format hpos hcode
  unfold roundRat
  rw [if_neg (ne_of_gt htargetPos)]
  rw [if_neg (not_lt_of_ge htargetPos.le)]
  exact roundPositiveRat_nonnegativeRatAt
    format hcode

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

/-- Rounding a negative rational is encoding-level negation of rounding its magnitude. -/
theorem roundRat_of_neg {value : Rat} (hvalue : value < 0) :
    roundRat format value = neg (roundPositiveRat format (-value)) := by
  simp [roundRat, hvalue, ne_of_lt hvalue]

end FloatLib.Floats.Formats.Posit.Model
