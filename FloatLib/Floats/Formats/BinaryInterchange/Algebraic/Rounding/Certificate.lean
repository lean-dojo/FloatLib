/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Rounding.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Accuracy.Proof
public import FloatLib.Numerics.Order.Bisection.Proof

/-!
# Exact certificates from bounded comparisons

Two bounded searches turn exact comparisons into a rounding certificate. The exponent search
keeps a bracket between powers of two, and the significand search keeps one between consecutive
integers. Exact comparison at the integer and its half-integer then supplies the accuracy
certificate that the rounding proof consumes.

`powerBounds_compare` shows that reading a comparison with a power of two off `powerBounds` gives
the comparator's own answer when the comparator is exact, and `round_eq` restates `round` with the
two direct comparisons at the ends of the exponent range, which is the form the proofs use.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.AlgebraicRounding

open Float.Model.UnpackedFloat
open FloatLib.Floats.Formats.Flocq

/-- The exact rational `powerOfTwo exponent` is the real power `2 ^ exponent`. -/
@[simp] theorem cast_powerOfTwo (exponent : Int) :
    (powerOfTwo exponent : ℝ) = bpow Numerics.binaryRadix exponent := by
  simp [powerOfTwo, Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand,
    bpow, Numerics.binaryRadix, Numerics.Radix.toReal]

/-- An exponent that `firstRung` returns was accepted. -/
theorem firstRung_hit (hit : Nat → Bool) (limit fuel step : Nat) {rung : Nat}
    (h : firstRung hit limit fuel step = some rung) : hit rung = true := by
  induction fuel generalizing step with
  | zero => simp [firstRung] at h
  | succ fuel ih =>
    rw [firstRung] at h
    split_ifs at h with hlimit hhit
    · cases h
      exact hhit
    · exact ih _ h

/-- The comparator answered `.lt` at the upper bound of `powerBounds`, whatever the comparator. -/
theorem powerBounds_above (fmt : FloatFormat) (compare : Rat → Ordering) {rung : Int}
    (h : (powerBounds fmt compare).above = some rung) : compare (powerOfTwo rung) = .lt := by
  simp only [powerBounds] at h
  split_ifs at h with hunit
  · cases h
    exact hunit
  · obtain ⟨step, hstep, rfl⟩ := Option.map_eq_some_iff.mp h
    simpa using firstRung_hit _ _ _ _ hstep

/-- The comparator answered `.gt` at the lower bound of `powerBounds`, whatever the comparator. -/
theorem powerBounds_below (fmt : FloatFormat) (compare : Rat → Ordering) {rung : Int}
    (h : (powerBounds fmt compare).below = some rung) : compare (powerOfTwo rung) = .gt := by
  simp only [powerBounds] at h
  split_ifs at h with hunit
  · cases h
    exact hunit
  · obtain ⟨step, hstep, rfl⟩ := Option.map_eq_some_iff.mp h
    simpa using firstRung_hit _ _ _ _ hstep

/--
For an exact comparator of a real target, the comparison through `powerBounds` is the comparison
with the power of two itself, at every exponent.
-/
theorem powerBounds_compare (fmt : FloatFormat) {compare : Rat → Ordering} {target : ℝ}
    (hcompare : ∀ candidate : Rat, compare candidate = cmp target (candidate : ℝ))
    (exponent : Int) :
    (powerBounds fmt compare).compare compare exponent = compare (powerOfTwo exponent) := by
  unfold PowerBounds.compare
  split_ifs with habove hbelow
  · cases hrung : (powerBounds fmt compare).above with
    | none => simp [hrung] at habove
    | some rung =>
      have hle : rung ≤ exponent := by simpa [hrung] using habove
      have hlt : target < bpow Numerics.binaryRadix rung :=
        (cmp_eq_lt_iff _ _).mp
          (by simpa only [hcompare, cast_powerOfTwo] using powerBounds_above fmt compare hrung)
      rw [hcompare, cast_powerOfTwo]
      exact ((cmp_eq_lt_iff _ _).mpr (hlt.trans_le ((bpow_le_bpow_iff _ _ _).mpr hle))).symm
  · cases hrung : (powerBounds fmt compare).below with
    | none => simp [hrung] at hbelow
    | some rung =>
      have hle : exponent ≤ rung := by simpa [hrung] using hbelow
      have hgt : bpow Numerics.binaryRadix rung < target :=
        (cmp_eq_gt_iff _ _).mp
          (by simpa only [hcompare, cast_powerOfTwo] using powerBounds_below fmt compare hrung)
      rw [hcompare, cast_powerOfTwo]
      exact ((cmp_eq_gt_iff _ _).mpr (((bpow_le_bpow_iff _ _ _).mpr hle).trans_lt hgt)).symm
  · rfl

/--
For an exact comparator of a real target, `round` is the rounding that compares with
`2 ^ lowerExponent` and `2 ^ upperExponent` directly: zero at or below the first, the overflow
value at or above the second, and the rounded certificate between them.
-/
theorem round_eq (fmt : FloatFormat) (sign : Bool) {compare : Rat → Ordering} {target : ℝ}
    (hcompare : ∀ candidate : Rat, compare candidate = cmp target (candidate : ℝ)) :
    round fmt sign compare =
      if compare (powerOfTwo (lowerExponent fmt)) ≠ .gt then zero fmt sign
      else if compare (powerOfTwo (upperExponent fmt)) ≠ .lt then nativeOverflow fmt sign
      else roundCertificate fmt sign (certificate fmt compare) := by
  simp only [round, powerBounds_compare fmt hcompare]

/-- The exponent search starts strictly below its exclusive upper bound. -/
theorem lowerExponent_lt_upperExponent (fmt : FloatFormat) :
    lowerExponent fmt < upperExponent fmt := by
  have := fmt.maxFiniteExpField_pos
  simp only [lowerExponent, upperExponent, FloatFormat.minSubnormalExponent,
    FloatFormat.minNormalExponent, FloatFormat.maxNormalExponent, Int.ofNat_eq_natCast]
  omega

/-- The exponent search always has at least one candidate binade. -/
theorem exponentSpan_pos (fmt : FloatFormat) : 0 < exponentSpan fmt := by
  have := lowerExponent_lt_upperExponent fmt
  simp only [exponentSpan]
  omega

/-- The located binade is never below the lowest searched exponent, whatever the comparator. -/
theorem binade_ge_lowerExponent (fmt : FloatFormat) (compare : Rat → Ordering) :
    lowerExponent fmt ≤ binade fmt compare := by
  simp only [binade]
  omega

/-- An exact comparator answering `.gt` at the lowest search power puts the target above it. -/
theorem bpow_lowerExponent_lt_of_compare_eq_gt (fmt : FloatFormat)
    {compare : Rat → Ordering} {target : ℝ}
    (hcompare : ∀ candidate : Rat, compare candidate = cmp target (candidate : ℝ))
    (hgt : compare (powerOfTwo (lowerExponent fmt)) = .gt) :
    bpow Numerics.binaryRadix (lowerExponent fmt) < target :=
  (cmp_eq_gt_iff _ _).mp (by simpa only [hcompare, cast_powerOfTwo] using hgt)

/-- An exact comparator answering `.lt` at the highest search power puts the target below it. -/
theorem lt_bpow_upperExponent_of_compare_eq_lt (fmt : FloatFormat)
    {compare : Rat → Ordering} {target : ℝ}
    (hcompare : ∀ candidate : Rat, compare candidate = cmp target (candidate : ℝ))
    (hlt : compare (powerOfTwo (upperExponent fmt)) = .lt) :
    target < bpow Numerics.binaryRadix (upperExponent fmt) :=
  (cmp_eq_lt_iff _ _).mp (by simpa only [hcompare, cast_powerOfTwo] using hlt)

/-- The first search locates consecutive powers of two around the exact target. -/
theorem binade_bounds (fmt : FloatFormat) (compare : Rat → Ordering) (target : ℝ)
    (hcompare : ∀ candidate : Rat, compare candidate = cmp target (candidate : ℝ))
    (hlower : bpow Numerics.binaryRadix (lowerExponent fmt) ≤ target)
    (hupper : target < bpow Numerics.binaryRadix (upperExponent fmt)) :
    bpow Numerics.binaryRadix (binade fmt compare) ≤ target ∧
      target < bpow Numerics.binaryRadix (binade fmt compare + 1) := by
  have hspanInt : (exponentSpan fmt : Int) = upperExponent fmt - lowerExponent fmt := by
    exact Int.toNat_of_nonneg (sub_nonneg.mpr (lowerExponent_lt_upperExponent fmt).le)
  have hspan : exponentSpan fmt ≤ 2 ^ ((exponentSpan fmt).log2 + 1) :=
    (by
      rw [Nat.log2_eq_log_two]
      exact (Nat.lt_pow_succ_log_self (by decide : 1 < (2 : Nat))
        (exponentSpan fmt)).le)
  have h := Numerics.bisect_bracket
    (fun index => decide
      ((powerBounds fmt compare).compare compare (lowerExponent fmt + index) ≠ .lt))
    (fun index => bpow Numerics.binaryRadix (lowerExponent fmt + index)) target
    (by
      intro index
      simp only [decide_eq_true_eq, powerBounds_compare fmt hcompare, hcompare, cast_powerOfTwo,
        ne_eq, cmp_eq_lt_iff, not_lt])
    ((exponentSpan fmt).log2 + 1) 0 (exponentSpan fmt)
    (exponentSpan_pos fmt) (by simpa using hspan)
    (by simpa using hlower)
    (by simpa [hspanInt] using hupper)
  simpa only [binade, Nat.cast_add, Nat.cast_one, add_assoc] using h

/--
Comparing `candidate * 2 ^ exponent` with an exact comparator for `target` compares `candidate`
with the scaled target `target / 2 ^ exponent`.
-/
theorem scaled_compare (compare : Rat → Ordering) (target : ℝ) (exponent : Int)
    (hcompare : ∀ candidate : Rat, compare candidate = cmp target (candidate : ℝ))
    (candidate : Rat) :
    compare (candidate * powerOfTwo exponent) =
      cmp (target / bpow Numerics.binaryRadix exponent) (candidate : ℝ) := by
  rw [hcompare, Rat.cast_mul, cast_powerOfTwo]
  simp only [cmp, cmpUsing, div_lt_iff₀ (bpow.pos _ _), lt_div_iff₀ (bpow.pos _ _)]

/-- Comparisons with the integer and half-integer determine a valid accuracy certificate. -/
theorem accuracyAt_represents (compare : Rat → Ordering) (target : ℝ) (mantissa : Nat)
    (hcompare : ∀ candidate : Rat, compare candidate = cmp target (candidate : ℝ))
    (hfloor : (mantissa : ℝ) ≤ target ∧ target < mantissa + 1) :
    AccuracyRepresents mantissa (accuracyAt compare mantissa) target := by
  unfold accuracyAt
  split
  · rename_i hexact
    have heq : target = (mantissa : ℝ) := by
      simpa only [hcompare, Rat.cast_natCast, cmp_eq_eq_iff] using hexact
    exact heq
  · rename_i hinexact
    have hne : target ≠ (mantissa : ℝ) := by
      simpa only [hcompare, Rat.cast_natCast, cmp_eq_eq_iff] using hinexact
    have hstrict := lt_of_le_of_ne hfloor.1 hne.symm
    have hhalf : compare ((mantissa : Rat) + 1 / 2) =
        cmp target ((mantissa : ℝ) + 1 / 2) := by
      simpa using hcompare ((mantissa : Rat) + 1 / 2)
    rw [hhalf]
    cases hcmp : cmp target ((mantissa : ℝ) + 1 / 2) with
    | lt => exact ⟨hstrict, (cmp_eq_lt_iff _ _).mp hcmp⟩
    | eq => exact (cmp_eq_eq_iff _ _).mp hcmp
    | gt => exact ⟨(cmp_eq_gt_iff _ _).mp hcmp, hfloor.2⟩

/-- The second search returns the exact integer part of the scaled magnitude. -/
theorem truncatedMantissa_bounds (fmt : FloatFormat) (compare : Rat → Ordering)
    (target : ℝ) (exponent : Int)
    (hcompare : ∀ candidate : Rat, compare candidate = cmp target (candidate : ℝ))
    (hlower : 0 ≤ target / bpow Numerics.binaryRadix exponent)
    (hupper : target / bpow Numerics.binaryRadix exponent < (2 : ℝ) ^ (fmt.fracWidth + 3)) :
    (truncatedMantissa fmt compare exponent : ℝ) ≤
        target / bpow Numerics.binaryRadix exponent ∧
      target / bpow Numerics.binaryRadix exponent <
        (truncatedMantissa fmt compare exponent : ℝ) + 1 := by
  have h := Numerics.bisect_bracket
    (fun candidate => decide (compare ((candidate : Rat) * powerOfTwo exponent) ≠ .lt))
    (fun candidate => (candidate : ℝ)) (target / bpow Numerics.binaryRadix exponent)
    (by
      intro index
      simp only [decide_eq_true_eq, scaled_compare compare target exponent hcompare,
        Rat.cast_natCast, ne_eq, cmp_eq_lt_iff, not_lt])
    (fmt.fracWidth + 3) 0 (2 ^ (fmt.fracWidth + 3)) (by positivity) (by simp)
    (by simpa using hlower) (by exact_mod_cast hupper)
  simpa only [truncatedMantissa, Nat.cast_add, Nat.cast_one] using h

/-- Two guard bits suffice for a positive truncated mantissa throughout the search interval. -/
theorem certificate_scaled_bounds (fmt : FloatFormat) (compare : Rat → Ordering)
    (target : ℝ)
    (hcompare : ∀ candidate : Rat, compare candidate = cmp target (candidate : ℝ))
    (hlower : bpow Numerics.binaryRadix (lowerExponent fmt) ≤ target)
    (hupper : target < bpow Numerics.binaryRadix (upperExponent fmt)) :
    1 ≤ target / bpow Numerics.binaryRadix (certificate fmt compare).exponent ∧
      target / bpow Numerics.binaryRadix (certificate fmt compare).exponent <
        (2 : ℝ) ^ (fmt.fracWidth + 3) := by
  obtain ⟨hblo, hbhi⟩ := binade_bounds fmt compare target hcompare hlower hupper
  have hbmin := binade_ge_lowerExponent fmt compare
  let b := binade fmt compare
  let e := certificateExponent fmt b
  change 1 ≤ target / bpow Numerics.binaryRadix e ∧
    target / bpow Numerics.binaryRadix e < (2 : ℝ) ^ (fmt.fracWidth + 3)
  have heb : e ≤ b := by
    dsimp [e, certificateExponent, b, lowerExponent] at *
    omega
  have hguard : b + 1 ≤ e + (fmt.fracWidth + 3 : Nat) := by
    dsimp [e, certificateExponent]
    omega
  constructor
  · rw [le_div_iff₀ (bpow.pos _ _), one_mul]
    exact (bpow_le_bpow_iff _ _ _).mpr heb |>.trans hblo
  · rw [div_lt_iff₀ (bpow.pos _ _)]
    have hpow :
        bpow Numerics.binaryRadix (e + (fmt.fracWidth + 3 : Nat)) =
          (2 : ℝ) ^ (fmt.fracWidth + 3) * bpow Numerics.binaryRadix e := by
      rw [bpow.add_exp, bpow_binaryRadix ((fmt.fracWidth + 3 : Nat) : Int), zpow_natCast, mul_comm]
    exact hbhi.trans_le (hpow ▸ (bpow_le_bpow_iff _ _ _).mpr hguard)

/--
Every interior oracle result supplies a valid nonzero accuracy certificate and satisfies the
normalizer's no-left-shift precondition. All bounds depend on the descriptor and assume no fixed
width.
-/
theorem certificate_spec (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (compare : Rat → Ordering) (target : ℝ)
    (hcompare : ∀ candidate : Rat, compare candidate = cmp target (candidate : ℝ))
    (hlower : bpow Numerics.binaryRadix (lowerExponent fmt) ≤ target)
    (hupper : target < bpow Numerics.binaryRadix (upperExponent fmt)) :
    let c := certificate fmt compare
    c.mantissa ≠ 0 ∧
      AccuracyRepresents c.mantissa c.accuracy
        (target / bpow Numerics.binaryRadix c.exponent) ∧
      c.exponent ≤ (FloatFormat.toModel fmt).targetExponent
        (Float.Model.totalExponent c.mantissa c.exponent) := by
  let c := certificate fmt compare
  let v := target / bpow Numerics.binaryRadix c.exponent
  obtain ⟨hvlo, hvhi⟩ := certificate_scaled_bounds fmt compare target hcompare hlower hupper
  have hfloor := truncatedMantissa_bounds fmt compare target c.exponent hcompare
    (by dsimp [c] at *; linarith) hvhi
  have hm : c.mantissa ≠ 0 := by
    intro hm
    change (c.mantissa : ℝ) ≤ v ∧ v < (c.mantissa : ℝ) + 1 at hfloor
    simp only [hm, Nat.cast_zero, zero_add] at hfloor
    exact (not_lt_of_ge hvlo) hfloor.2
  have ha : AccuracyRepresents c.mantissa c.accuracy v := by
    exact accuracyAt_represents
      (fun candidate => compare (candidate * powerOfTwo c.exponent)) v c.mantissa
      (scaled_compare compare target c.exponent hcompare) hfloor
  refine ⟨hm, ha, ?_⟩
  have htarget : 0 < target := (bpow.pos _ _).trans_le hlower
  obtain ⟨hblo, hbhi⟩ := binade_bounds fmt compare target hcompare hlower hupper
  have hmagnitude : magnitude Numerics.binaryRadix target = binade fmt compare + 1 := by
    apply magnitude_eq_of_bpow_bounds
    · simpa [abs_of_pos htarget] using hblo
    · simpa [abs_of_pos htarget] using hbhi
  have hv : v * bpow Numerics.binaryRadix c.exponent = target :=
    div_mul_cancel₀ _ (bpow.ne_zero _ _)
  rw [← cexp_accuracy_mul_bpow_eq_targetExponent fmt c.mantissa c.exponent c.accuracy
    v hfmt hm ha, hv, cexp, hmagnitude, fexpOf, fltExp]
  change certificateExponent fmt (binade fmt compare) ≤ _
  simp only [certificateExponent]
  omega

/--
Under a conventional IEEE descriptor, for an exact comparator of a target in
`[2 ^ lowerExponent, 2 ^ upperExponent)`, `roundCertificate` rounds the certificate once through
Lean's logical model: it packs `roundWithAccuracy` of the certificate, whose accuracy represents
the scaled magnitude `target / 2 ^ c.exponent` and whose exponent satisfies the normalizer's
no-left-shift precondition (`certificate_spec`).
-/
theorem roundCertificate_certificate_spec (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign : Bool) (compare : Rat → Ordering) (target : ℝ)
    (hcompare : ∀ candidate : Rat, compare candidate = cmp target (candidate : ℝ))
    (hlower : bpow Numerics.binaryRadix (lowerExponent fmt) ≤ target)
    (hupper : target < bpow Numerics.binaryRadix (upperExponent fmt)) :
    let c := certificate fmt compare
    roundCertificate fmt sign c =
        ofModel fmt (roundWithAccuracy (FloatFormat.toModel fmt) (modelSign sign)
          c.mantissa c.exponent c.accuracy) ∧
      AccuracyRepresents c.mantissa c.accuracy
        (target / bpow Numerics.binaryRadix c.exponent) ∧
      c.exponent ≤ (FloatFormat.toModel fmt).targetExponent
        (Float.Model.totalExponent c.mantissa c.exponent) := by
  obtain ⟨-, ha, he⟩ := certificate_spec fmt hfmt compare target hcompare hlower hupper
  exact ⟨by simp only [roundCertificate, hfmt, ite_true], ha, he⟩

end FloatLib.Floats.Formats.BinaryInterchange.Model.AlgebraicRounding
