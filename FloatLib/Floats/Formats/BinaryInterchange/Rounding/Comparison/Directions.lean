/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Comparison.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.CorrectlyRounded.Proof

/-!
# Rounding by exact comparisons is correct rounding in every direction

For every format descriptor and a comparator that orders a nonzero real number `r` against
every rational, `ComparisonRounding.round` in the direction `mode` meets the contract
`RoundsTo fmt mode r` (`round_roundsTo`), for each of the six members of `IEEERoundingMode`:
the five rounding-direction attributes of IEEE 754-2019 and rounding away from zero. The
descriptors are the conventional IEEE ones, the formats without an infinity such as OCP E4M3,
the formats with one zero such as ONNX E4M3FNUZ, and the formats in which every encoding is
finite. With `roundAt fmt r mode` the rounding of `r` in that direction on the grid of the
format with an unbounded exponent range, the result is finite and denotes that value when it is
at most the largest finite magnitude, and it is the overflow result of the direction otherwise
(IEEE 754-2019, clause 7.4; a format without an infinity delivers its NaN where an IEEE format
delivers an infinity, and a format without a NaN its largest finite value). In a format with
signed zeros it carries the sign of `r`, also when it is a zero. So the result toward negative
infinity is the largest value of the format that is at most `r`, the result toward positive
infinity the least value that is at least `r`, and the two results to nearest differ only at a
tie. A comparator of zero gives `+0` in every direction (`round_of_eq_zero`).

The directed directions are `AlgebraicRounding.roundMagnitude`, whose contract is
`AlgebraicRounding.roundMagnitude_roundsTo`. To nearest-even `ComparisonRounding.round` is
`AlgebraicRounding.round`, and `AlgebraicRounding.round_roundsTo` gives it the same contract.
For a conventional IEEE descriptor its result is finite below the overflow threshold, which
rounds to the first power of two past the range, and it keeps the sign it is given
(`AlgebraicRounding.signBit_round`). For every other descriptor the certificate of the
magnitude is rounded as a dyadic number that stands in the same place between the values of
the format (`roundCertificate_roundsTo`).

`deliver` may take its value to nearest-even from a hint. `Hint.Signed hint r` says that the
hint's value has the sign of `r`, which `Hint.Sound` leaves open for a result that is a zero.
With both, `deliver_roundsTo`, `Rule.deliver_roundsTo`, `unary_roundsTo` and `binary_roundsTo`
carry the contract through the flags, the rules and the operand tables.
`Rule.isZero_deliver` is the statement for a rule that locates zero.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Floats FloatLib.Numerics

variable {fmt : FloatFormat}

namespace AlgebraicRounding

open Transcendentals.CorrectlyRounded in
/--
For a conventional IEEE descriptor and an exact comparator of a nonnegative magnitude,
nearest-even rounding by comparisons keeps the sign bit it is given: on a zero, on a finite
nonzero result and on an infinity.
-/
theorem signBit_round (hfmt : fmt.isIEEE = true) (sign : Bool) {compare : ℚ → Ordering}
    {target : ℝ} (hnonneg : 0 ≤ target)
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp target (candidate : ℝ)) :
    signBit (round fmt sign compare) = sign := by
  cases hfinite : isFinite (round fmt sign compare) with
  | false =>
      rw [round_eq_nativeOverflow_of_isFinite_eq_false fmt hfmt sign compare hfinite,
        nativeOverflow_eq_signedInf_of_isIEEE fmt hfmt]
      cases sign <;> simp
  | true =>
      by_cases hzero : toReal (round fmt sign compare) = 0
      · exact signBit_round_of_toReal_eq_zero hfmt hnonneg hcompare hfinite hzero
      · have hvalue := toReal_round_eq_roundAt fmt hfmt sign compare target hnonneg hcompare
          hfinite
        cases sign with
        | false =>
            have hpos : 0 ≤ toReal (round fmt false compare) := by
              rw [hvalue]
              simpa using roundAt_mono fmt hnonneg
            rcases isZero_or_signBit_eq_false_of_toReal_nonneg _ hfinite hpos with h | h
            · exact absurd (toReal_eq_zero_of_isZero _ h) hzero
            · exact h
        | true =>
            have hneg : toReal (round fmt true compare) ≤ 0 := by
              rw [hvalue]
              simpa using roundAt_mono fmt (neg_nonpos.mpr hnonneg)
            cases hsign : signBit (round fmt true compare) with
            | true => rfl
            | false =>
                exact absurd (le_antisymm hneg (toReal_nonneg_of_signBit_eq_false hsign)) hzero

open Transcendentals.CorrectlyRounded in
/--
For a conventional IEEE descriptor and an exact comparator of the positive magnitude `t`,
`round` with the sign `sign` is finite and denotes `roundAt fmt (±t)` when that is at most the
largest finite magnitude, and is the infinity of that sign otherwise.
-/
private theorem round_roundsTo_of_isIEEE (hfmt : fmt.isIEEE = true) (sign : Bool)
    (compare : ℚ → Ordering)
    {t : ℝ} (ht : 0 < t)
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp t (candidate : ℝ)) :
    RoundsTo fmt .nearest (if sign then -t else t) sign (round fmt sign compare) := by
  have hround : 0 ≤ roundAt fmt t := by simpa using roundAt_mono fmt ht.le
  have habs : |roundAt fmt (if sign then -t else t)| = roundAt fmt t := by
    cases sign
    · simpa using abs_of_nonneg hround
    · simp only [↓reduceIte]
      rw [roundAt_neg, IEEERoundingMode.negate_nearest, abs_neg, abs_of_nonneg hround]
  refine ⟨fun hrange => ?_, fun hover => ?_, fun _ => signBit_round hfmt sign ht.le hcompare⟩
  · have hlt : t < (Transcendentals.Certified.overflowThreshold fmt : ℝ) := by
      by_contra hge
      have h := roundAt_mono fmt (not_lt.mp hge)
      rw [roundAt_overflowThreshold hfmt] at h
      rw [habs] at hrange
      exact absurd (h.trans hrange) (not_le.mpr (toReal_posMaxFinite_lt_bpow fmt))
    have hfinite := isFinite_round_of_lt_overflow fmt hfmt sign compare t hcompare
      (cast_overflowThreshold fmt ▸ hlt)
    exact ⟨hfinite, toReal_round_eq_roundAt fmt hfmt sign compare t ht.le hcompare hfinite⟩
  · have hnot : isFinite (round fmt sign compare) = false := by
      cases hfinite : isFinite (round fmt sign compare) with
      | false => rfl
      | true =>
          have hbound := abs_toReal_le_posMaxFinite_of_isFinite _ hfinite
          rw [toReal_round_eq_roundAt fmt hfmt sign compare t ht.le hcompare hfinite] at hbound
          exact absurd hover (not_lt.mpr hbound)
    rw [round_eq_nativeOverflow_of_isFinite_eq_false fmt hfmt sign compare hnot]
    rfl

/--
For a descriptor that is not a conventional IEEE one, the rounded certificate of a magnitude
strictly between half the least subnormal and `2 ^ (emax + 1)` meets the contract `RoundsTo`
to nearest-even. The certificate is rounded as the dyadic number with
two more bits that stands in the same place between the values of the format as the magnitude
(`located_of_quarter`), and `roundDyadic_spec` is the contract of that rounding.
-/
theorem roundCertificate_roundsTo (hfmt : ¬fmt.isIEEE = true) (sign : Bool)
    (compare : ℚ → Ordering) {t : ℝ}
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp t (candidate : ℝ))
    (hlower : Flocq.bpow binaryRadix (lowerExponent fmt) < t)
    (hupper : t < Flocq.bpow binaryRadix (upperExponent fmt)) :
    RoundsTo fmt .nearest (if sign then -t else t) sign
      (roundCertificate fmt sign (certificate fmt compare)) := by
  have ht : 0 < t := (Flocq.bpow.pos _ _).trans hlower
  obtain ⟨hblo, hbhi⟩ := binade_bounds fmt compare t hcompare hlower.le hupper
  obtain ⟨hvlo, hvhi⟩ := certificate_scaled_bounds fmt compare t hcompare hlower.le hupper
  have hfloor := truncatedMantissa_bounds fmt compare t (certificate fmt compare).exponent
    hcompare (by linarith) hvhi
  have hrep : AccuracyRepresents (certificate fmt compare).mantissa
      (certificate fmt compare).accuracy
      (t / Flocq.bpow binaryRadix (certificate fmt compare).exponent) :=
    accuracyAt_represents
      (fun candidate => compare (candidate * powerOfTwo (certificate fmt compare).exponent)) _ _
      (scaled_compare compare t _ hcompare) hfloor
  have hbinade := binade_ge_lowerExponent fmt compare
  have hsame : roundAt fmt (((4 * (certificate fmt compare).mantissa +
      accuracyQuarter (certificate fmt compare).accuracy : ℕ) : ℝ) *
        Flocq.bpow binaryRadix ((certificate fmt compare).exponent - 2)) = roundAt fmt t :=
    ((located_of_quarter fmt hbinade hblo hbhi hrep).roundAt_eq .nearest).trans
      ((located_of_truncated fmt ht hblo hbhi hfloor.1 hfloor.2
        (accuracyQuarter_eq_zero_iff hrep)).roundAt_eq .nearest).symm
  -- The rounded magnitude is positive: the magnitude is above half the least subnormal.
  have hpositive : 0 < roundAt fmt t := by
    have hgrid := genericFormat_bpow fmt (le_refl fmt.minSubnormalExponent)
    rcases le_or_gt (Flocq.bpow binaryRadix fmt.minSubnormalExponent) t with hge | hlt
    · have h := roundAt_mono fmt hge
      rw [roundAt_of_genericFormat fmt hgrid] at h
      exact (Flocq.bpow.pos _ _).trans_le h
    · have hnear := abs_roundAt_sub_le_abs_sub (fmt := fmt) hgrid (x := t)
      have hhalf : Flocq.bpow binaryRadix fmt.minSubnormalExponent =
          2 * Flocq.bpow binaryRadix (lowerExponent fmt) := by
        rw [Flocq.bpow_binaryRadix, Flocq.bpow_binaryRadix, lowerExponent,
          zpow_sub_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
        ring
      rw [abs_of_pos (sub_pos.mpr hlt)] at hnear
      have := (abs_le.mp hnear).1
      linarith
  have hreal : (Numerics.Dyadic.mk sign
      (4 * (certificate fmt compare).mantissa +
        accuracyQuarter (certificate fmt compare).accuracy)
      ((certificate fmt compare).exponent - 2)).toReal =
      if sign then -(((4 * (certificate fmt compare).mantissa +
          accuracyQuarter (certificate fmt compare).accuracy : ℕ) : ℝ) *
            Flocq.bpow binaryRadix ((certificate fmt compare).exponent - 2))
      else ((4 * (certificate fmt compare).mantissa +
          accuracyQuarter (certificate fmt compare).accuracy : ℕ) : ℝ) *
            Flocq.bpow binaryRadix ((certificate fmt compare).exponent - 2) := by
    cases sign
    · simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, Flocq.bpow_binaryRadix]
    · simp only [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand,
        Flocq.bpow_binaryRadix, ↓reduceIte, Int.cast_neg, Int.ofNat_eq_natCast,
        Int.cast_natCast, neg_mul]
  have hround : roundAt fmt (Numerics.Dyadic.mk sign
      (4 * (certificate fmt compare).mantissa +
        accuracyQuarter (certificate fmt compare).accuracy)
      ((certificate fmt compare).exponent - 2)).toReal = roundAt fmt (if sign then -t else t) := by
    rw [hreal]
    cases sign
    · exact hsame
    · simp only [↓reduceIte]
      rw [roundAt_neg, roundAt_neg, IEEERoundingMode.negate_nearest]
      exact congrArg Neg.neg hsame
  have hvalue : roundAt fmt (if sign then -t else t) =
      if sign then -roundAt fmt t else roundAt fmt t := by
    cases sign
    · rfl
    · simp only [↓reduceIte]
      rw [roundAt_neg, IEEERoundingMode.negate_nearest]
  obtain ⟨hin, hout⟩ := roundDyadic_spec fmt (Numerics.Dyadic.mk sign
    (4 * (certificate fmt compare).mantissa + accuracyQuarter (certificate fmt compare).accuracy)
    ((certificate fmt compare).exponent - 2))
  rw [hround] at hin hout
  have hcertificate : roundCertificate fmt sign (certificate fmt compare) =
      roundDyadic fmt (Numerics.Dyadic.mk sign
        (4 * (certificate fmt compare).mantissa +
          accuracyQuarter (certificate fmt compare).accuracy)
        ((certificate fmt compare).exponent - 2)) := by
    simp [roundCertificate, hfmt]
  rw [hcertificate]
  refine ⟨hin, fun hover => hout hover, fun hzero => ?_⟩
  by_cases hrange : |roundAt fmt (if sign then -t else t)| ≤ toReal (posMaxFinite fmt)
  · obtain ⟨hfinite, hdenotes⟩ := hin hrange
    rw [hvalue] at hdenotes
    cases sign
    · exact signBit_eq_false_of_toReal_pos hfinite (by simpa [hdenotes] using hpositive)
    · exact signBit_eq_true_of_toReal_neg (by simpa [hdenotes] using hpositive)
  · rw [hout (not_le.mp hrange)]
    exact signBit_directedOverflow hzero sign true

/--
**Nearest-even rounding by comparisons meets the rounding contract, for every format
descriptor.** For an exact comparator of the positive magnitude `t`, `round` with the sign
`sign` is finite and denotes `roundAt fmt (±t)` when that is at most the largest finite
magnitude, and is the overflow word of the format with that sign otherwise: an infinity, the
NaN of a format without one, or the largest finite value of a format in which every encoding is
finite.
-/
theorem round_roundsTo (sign : Bool)
    (compare : ℚ → Ordering) {t : ℝ} (ht : 0 < t)
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp t (candidate : ℝ)) :
    RoundsTo fmt .nearest (if sign then -t else t) sign (round fmt sign compare) := by
  by_cases hfmt : fmt.isIEEE = true
  · exact round_roundsTo_of_isIEEE hfmt sign compare ht hcompare
  have hvalue : roundAt fmt (if sign then -t else t) =
      if sign then -roundAt fmt t else roundAt fmt t := by
    cases sign
    · rfl
    · simp only [↓reduceIte]
      rw [roundAt_neg, IEEERoundingMode.negate_nearest]
  rw [round_eq fmt sign hcompare]
  by_cases hsmall : compare (powerOfTwo (lowerExponent fmt)) ≠ .gt
  · rw [ite_eq_left hsmall]
    have hle : t ≤ Flocq.bpow binaryRadix (lowerExponent fmt) := by
      simpa only [hcompare, cast_powerOfTwo, ne_eq, cmp_eq_gt_iff, not_lt] using hsmall
    have hround : roundAt fmt (if sign then -t else t) = 0 := by
      rw [hvalue, roundAt_eq_zero_of_le_halfMinSubnormal fmt t ht.le hle]
      cases sign <;> simp
    refine ⟨fun _ => ⟨isFinite_eq_true_of_isZero_eq_true _ (isZero_zero fmt sign), ?_⟩,
      fun hover => ?_, fun hzero => by simp [signBit_zero, hzero]⟩
    · rw [toReal_zero, hround]
    · rw [hround, abs_zero] at hover
      exact absurd hover (not_lt.mpr (toReal_posMaxFinite_pos fmt).le)
  rw [ite_eq_right hsmall]
  by_cases hlarge : compare (powerOfTwo (upperExponent fmt)) ≠ .lt
  · rw [ite_eq_left hlarge]
    have hge : Flocq.bpow binaryRadix (upperExponent fmt) ≤ t := by
      simpa only [hcompare, cast_powerOfTwo, ne_eq, cmp_eq_lt_iff, not_lt] using hlarge
    have hbeyond : toReal (posMaxFinite fmt) < |roundAt fmt (if sign then -t else t)| := by
      apply (toReal_posMaxFinite_lt_bpow fmt).trans_le
      apply bpow_le_abs_roundAt fmt .nearest
      · have := lowerExponent_lt_upperExponent fmt
        simp only [lowerExponent, upperExponent] at this ⊢
        omega
      · cases sign <;> simpa [abs_of_pos ht, upperExponent] using hge
    exact ⟨fun hin => absurd hbeyond (not_lt.mpr hin), fun _ => rfl,
      fun hzero => signBit_directedOverflow hzero sign true⟩
  · rw [ite_eq_right hlarge]
    exact roundCertificate_roundsTo hfmt sign compare hcompare
      (bpow_lowerExponent_lt_of_compare_eq_gt fmt hcompare (by simpa only [not_not] using hsmall))
      (lt_bpow_upperExponent_of_compare_eq_lt fmt hcompare (by simpa only [not_not] using hlarge))

end AlgebraicRounding

namespace ComparisonRounding

/--
For every format descriptor and an exact comparator of the positive magnitude `t`, the rounding
of the signed magnitude meets the contract `RoundsTo` in every direction.
-/
theorem roundMagnitude_roundsTo {mode : IEEERoundingMode}
    (sign : Bool) (compare : ℚ → Ordering) {t : ℝ} (ht : 0 < t)
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp t (candidate : ℝ)) :
    RoundsTo fmt mode (if sign then -t else t) sign (roundMagnitude fmt sign compare mode) := by
  cases mode
  case nearest =>
    exact AlgebraicRounding.round_roundsTo sign compare ht hcompare
  all_goals
    exact AlgebraicRounding.roundMagnitude_roundsTo _ sign compare ht hcompare

/--
**Rounding by exact comparisons is correct rounding in every direction.** For every format
descriptor (a conventional IEEE one, a format without an infinity such as OCP E4M3, a format
with one zero such as ONNX E4M3FNUZ, or a format in which every encoding is finite), a
comparator of the nonzero real number `target` and each direction `mode`, `round` is finite and
denotes `roundAt fmt target mode` when that value is at most the largest finite magnitude, and
is the overflow result of the direction otherwise. In a format with signed zeros it has the
sign of `target`.
-/
theorem round_roundsTo {mode : IEEERoundingMode}
    (compare : ℚ → Ordering) {target : ℝ} (hne : target ≠ 0)
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp target (candidate : ℝ)) :
    RoundsTo fmt mode target (decide (target < 0)) (round fmt compare mode) := by
  have hzero := hcompare 0
  rw [Rat.cast_zero] at hzero
  unfold round
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · rw [(cmp_eq_lt_iff _ _).mpr hneg] at hzero
    simp only [hzero, decide_eq_true hneg]
    simpa using roundMagnitude_roundsTo (fmt := fmt) true _ (neg_pos.mpr hneg)
      (magnitude_compare hcompare)
  · rw [(cmp_eq_gt_iff _ _).mpr hpos] at hzero
    simp only [hzero, decide_eq_false (not_lt.mpr hpos.le)]
    simpa using roundMagnitude_roundsTo (fmt := fmt) false compare hpos hcompare

/-- A comparator of zero is rounded to `+0` in every direction. -/
theorem round_of_eq_zero (compare : ℚ → Ordering) (mode : IEEERoundingMode)
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp (0 : ℝ) (candidate : ℝ)) :
    round fmt compare mode = zero fmt false := by
  have hzero : compare 0 = .eq := by
    rw [hcompare, Rat.cast_zero]
    exact (cmp_eq_eq_iff _ _).mpr rfl
  simp [round, hzero]

/--
That the value of a hint has the sign of `target`: negative exactly when `target` is, also for
a value that is a zero.
-/
def Hint.Signed (hint : Unit → Option (Hint fmt)) (target : ℝ) : Prop :=
  ∀ found, hint () = some found → signBit found.value = decide (target < 0)

/-- The hint without a result has the sign of every number. -/
theorem Hint.signed_none (target : ℝ) : Hint.Signed (fmt := fmt) (fun _ => none) target :=
  fun _ h => absurd h (by simp)

/--
For every format descriptor, a comparator of the nonzero real number `target` and a hint that
is right about `target` and has its sign, the value that `resolve` selects meets the contract
`RoundsTo` in every direction.
-/
theorem resolve_roundsTo {mode : IEEERoundingMode}
    (compare : ℚ → Ordering) {target : ℝ} (hne : target ≠ 0)
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp target (candidate : ℝ))
    {hint : Unit → Option (Hint fmt)} (hsound : Hint.Sound hint target)
    (hsigned : Hint.Signed hint target) :
    RoundsTo fmt mode target (decide (target < 0)) (resolve fmt compare mode hint).value := by
  cases mode
  case nearest =>
    unfold resolve
    dsimp only
    cases hfound : hint () with
    | none => exact round_roundsTo compare hne hcompare
    | some found =>
        obtain ⟨hfinite, hvalue, -⟩ := hsound found hfound
        refine ⟨fun _ => ⟨hfinite, hvalue⟩, fun hover => ?_, fun _ => hsigned found hfound⟩
        have hbound := abs_toReal_le_posMaxFinite_of_isFinite found.value hfinite
        rw [hvalue] at hbound
        exact absurd hover (not_lt.mpr hbound)
  all_goals exact round_roundsTo compare hne hcompare

/--
**A delivery is the correctly rounded value in every direction.** For every format descriptor,
a comparator of the nonzero real number `target` and a hint that is right about `target` and
has its sign, the value of `deliver` meets the contract `RoundsTo`: it is finite and denotes
`roundAt fmt target mode` in range, and is the overflow result of the direction beyond it.
-/
theorem deliver_roundsTo {mode : IEEERoundingMode}
    (compare : ℚ → Ordering) {target : ℝ} (hne : target ≠ 0)
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp target (candidate : ℝ))
    {hint : Unit → Option (Hint fmt)} (hsound : Hint.Sound hint target)
    (hsigned : Hint.Signed hint target) :
    RoundsTo fmt mode target (decide (target < 0)) (deliver fmt compare mode hint).value := by
  rw [deliver_value]
  exact resolve_roundsTo compare hne hcompare hsound hsigned

/--
For every format descriptor, a rule that locates the nonzero real number `target` delivers its
correctly rounded value in every direction, with any hint that is right about `target` and has
its sign.
-/
theorem Rule.deliver_roundsTo {mode : IEEERoundingMode} {rule : Rule}
    {target : ℝ} (hrule : rule.Locates target) (hne : target ≠ 0)
    {hint : Unit → Option (Hint fmt)} (hsound : Hint.Sound hint target)
    (hsigned : Hint.Signed hint target) :
    RoundsTo fmt mode target (decide (target < 0)) (rule.deliver fmt mode hint).value := by
  cases rule with
  | zero negative => exact absurd hrule hne
  | real compare =>
      exact ComparisonRounding.deliver_roundsTo compare hne hrule hsound hsigned
  | infinity negative => exact absurd hrule id
  | pole negative => exact absurd hrule id
  | invalid => exact absurd hrule id

/--
A rule that locates zero delivers a zero in every direction, with any hint that is right about
zero.
-/
theorem Rule.isZero_deliver {rule : Rule} (hrule : rule.Locates 0) (mode : IEEERoundingMode)
    {hint : Unit → Option (Hint fmt)} (hsound : Hint.Sound hint 0) :
    isZero (rule.deliver fmt mode hint).value = true := by
  cases rule with
  | zero negative => simp [Rule.deliver]
  | real compare =>
      have hround (mode : IEEERoundingMode) : isZero (round fmt compare mode) = true := by
        rw [round_of_eq_zero compare mode hrule]
        exact isZero_zero fmt false
      simp only [Rule.deliver, deliver_value]
      cases mode
      case nearest =>
        unfold resolve
        dsimp only
        cases hfound : hint () with
        | none => exact hround .nearest
        | some found =>
            obtain ⟨hfinite, hvalue, -⟩ := hsound found hfound
            exact (isZero_eq_true_iff_toReal_eq_zero _ hfinite).mpr (by simpa using hvalue)
      all_goals exact hround _
  | infinity negative => exact absurd hrule id
  | pole negative => exact absurd hrule id
  | invalid => exact absurd hrule id

/--
**A function of one operand is correctly rounded in every direction.** For every format
descriptor, a finite operand whose rule locates the nonzero real number `target` and a hint
that is right about `target` and has its sign at that operand, the result in the direction
`mode` meets the contract `RoundsTo fmt mode target`.
-/
theorem unary_roundsTo {mode : IEEERoundingMode}
    (rule : Operand → Rule) {x : Model fmt}
    {q : ℚ} (hq : toRat? x = some q) {target : ℝ}
    (hrule : (rule (.finite (signBit x) q)).Locates target) (hne : target ≠ 0)
    {hint : Operand → Unit → Option (Hint fmt)}
    (hsound : Hint.Sound (hint (.finite (signBit x) q)) target)
    (hsigned : Hint.Signed (hint (.finite (signBit x) q)) target) :
    RoundsTo fmt mode target (decide (target < 0)) (unary rule x mode hint).value := by
  rw [unary_of_toRat? rule hq]
  exact Rule.deliver_roundsTo hrule hne hsound hsigned

/--
**A function of two operands is correctly rounded in every direction.** For every format
descriptor, finite operands whose rule locates the nonzero real number `target` and a hint that
is right about `target` and has its sign at those operands, the result in the direction `mode`
meets the contract `RoundsTo fmt mode target`.
-/
theorem binary_roundsTo {mode : IEEERoundingMode}
    (rule : Operand → Operand → Rule)
    {x y : Model fmt} {p q : ℚ} (hp : toRat? x = some p) (hq : toRat? y = some q) {target : ℝ}
    (hrule : (rule (.finite (signBit x) p) (.finite (signBit y) q)).Locates target)
    (hne : target ≠ 0)
    {hint : Operand → Operand → Unit → Option (Hint fmt)}
    (hsound : Hint.Sound (hint (.finite (signBit x) p) (.finite (signBit y) q)) target)
    (hsigned : Hint.Signed (hint (.finite (signBit x) p) (.finite (signBit y) q)) target) :
    RoundsTo fmt mode target (decide (target < 0)) (binary rule x y mode hint).value := by
  rw [binary_of_toRat? rule hp hq]
  exact Rule.deliver_roundsTo hrule hne hsound hsigned

end ComparisonRounding

end FloatLib.Floats.Formats.BinaryInterchange.Model
