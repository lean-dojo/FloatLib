/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Rounding.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Accuracy.Proof
public import FloatLib.Floats.Formats.Posit.Rounding.Proof

/-!
# Exact certificates from bounded comparisons

The exponent search preserves a bracket between powers of two. The significand search
preserves a bracket between consecutive integers. Exact comparison at the integer and its
half-integer supplies the accuracy certificate consumed by the existing rounding proof.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.AlgebraicRounding

open Float.Model.UnpackedFloat
open FloatLib.Floats.Formats.Flocq

@[simp] theorem cast_powerOfTwo (exponent : Int) :
    (powerOfTwo exponent : ℝ) = bpow Numerics.binaryRadix exponent := by
  simp [powerOfTwo, Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand,
    bpow, Numerics.binaryRadix, Numerics.Radix.toReal]

/--
A sufficiently deep bounded search ends at adjacent candidates enclosing the target.
Only exact comparison and an initial bracket are needed; the proof follows both search branches.
-/
theorem bisect_bracket (accept : Nat → Bool) (valueAt : Nat → ℝ) (target : ℝ)
    (haccept : ∀ index, accept index = true ↔ valueAt index ≤ target)
    (fuel lower upper : Nat) (horder : lower < upper)
    (hspan : upper - lower ≤ 2 ^ fuel)
    (hlower : valueAt lower ≤ target) (hupper : target < valueAt upper) :
    valueAt (bisect accept fuel lower upper) ≤ target ∧
      target < valueAt (bisect accept fuel lower upper + 1) := by
  induction fuel generalizing lower upper with
  | zero =>
    have hupperEq : upper = lower + 1 := by
      simp only [pow_zero] at hspan
      omega
    simpa [bisect, Posit.Model.lowerCodeByBisection, hupperEq] using And.intro hlower hupper
  | succ fuel ih =>
    rw [bisect, Posit.Model.lowerCodeByBisection]
    split
    · rename_i hnontrivial
      let middle := (lower + upper) / 2
      have hlo : lower < middle := by dsimp [middle]; omega
      have hhi : middle < upper := by dsimp [middle]; omega
      have hleft : middle - lower ≤ 2 ^ fuel := by
        dsimp [middle]
        rw [pow_succ] at hspan
        omega
      have hright : upper - middle ≤ 2 ^ fuel := by
        dsimp [middle]
        rw [pow_succ] at hspan
        omega
      dsimp only
      split
      · rename_i hmid
        exact ih middle upper hhi hright ((haccept middle).mp hmid) hupper
      · rename_i hmid
        exact ih lower middle hlo hleft hlower
          (lt_of_not_ge (fun h => hmid ((haccept middle).mpr h)))
    · have hupperEq : upper = lower + 1 := by omega
      simpa [hupperEq] using And.intro hlower hupper

theorem lowerExponent_lt_upperExponent (fmt : FloatFormat) :
    lowerExponent fmt < upperExponent fmt := by
  have := fmt.maxFiniteExpField_pos
  simp only [lowerExponent, upperExponent, FloatFormat.minSubnormalExponent,
    FloatFormat.minNormalExponent, FloatFormat.maxNormalExponent, Int.ofNat_eq_natCast]
  omega

theorem exponentSpan_pos (fmt : FloatFormat) : 0 < exponentSpan fmt := by
  have := lowerExponent_lt_upperExponent fmt
  simp only [exponentSpan]
  omega

theorem binade_ge_lowerExponent (fmt : FloatFormat) (compare : Rat → Ordering) :
    lowerExponent fmt ≤ binade fmt compare := by
  simp only [binade]
  omega

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
  have h := bisect_bracket
    (fun index => decide (compare (powerOfTwo (lowerExponent fmt + index)) ≠ .lt))
    (fun index => bpow Numerics.binaryRadix (lowerExponent fmt + index)) target
    (by
      intro index
      simp only [decide_eq_true_eq, hcompare, cast_powerOfTwo, ne_eq, cmp_eq_lt_iff,
        not_lt])
    ((exponentSpan fmt).log2 + 1) 0 (exponentSpan fmt)
    (exponentSpan_pos fmt) (by simpa using hspan)
    (by simpa using hlower)
    (by simpa [hspanInt] using hupper)
  simpa only [binade, Nat.cast_add, Nat.cast_one, add_assoc] using h

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
    accuracyRepresents mantissa (accuracyAt compare mantissa) target := by
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
  have h := bisect_bracket
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
      rw [bpow.add_exp]
      have hp : bpow Numerics.binaryRadix ((fmt.fracWidth + 3 : Nat) : Int) =
          (2 : ℝ) ^ (fmt.fracWidth + 3) := by
        change (2 : ℝ) ^ ((fmt.fracWidth + 3 : Nat) : Int) = _
        exact zpow_natCast _ _
      rw [hp, mul_comm]
    exact hbhi.trans_le (hpow ▸ (bpow_le_bpow_iff _ _ _).mpr hguard)

/--
Every interior oracle result supplies a valid nonzero accuracy certificate and satisfies the
normalizer's no-left-shift precondition. All bounds depend on the descriptor, not a fixed width.
-/
theorem certificate_spec (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (compare : Rat → Ordering) (target : ℝ)
    (hcompare : ∀ candidate : Rat, compare candidate = cmp target (candidate : ℝ))
    (hlower : bpow Numerics.binaryRadix (lowerExponent fmt) ≤ target)
    (hupper : target < bpow Numerics.binaryRadix (upperExponent fmt)) :
    let c := certificate fmt compare
    c.mantissa ≠ 0 ∧
      accuracyRepresents c.mantissa c.accuracy
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
  have ha : accuracyRepresents c.mantissa c.accuracy v := by
    exact accuracyAt_represents
      (fun candidate => compare (candidate * powerOfTwo c.exponent)) v c.mantissa
      (scaled_compare compare target c.exponent hcompare) hfloor
  refine ⟨hm, ha, ?_⟩
  have htarget : 0 < target := (bpow.pos _ _).trans_le hlower
  obtain ⟨hblo, hbhi⟩ := binade_bounds fmt compare target hcompare hlower hupper
  have hmagnitude : magnitude Numerics.binaryRadix target = binade fmt compare + 1 := by
    apply magnitude_eq_of_bpow_bounds _ _ _ htarget.ne'
    · simpa [abs_of_pos htarget] using hblo
    · simpa [abs_of_pos htarget] using hbhi
  have hv : v * bpow Numerics.binaryRadix c.exponent = target :=
    div_mul_cancel₀ _ (bpow.ne_zero _ _)
  rw [← cexp_accuracy_mul_bpow_eq_targetExponent fmt c.mantissa c.exponent c.accuracy
    v hfmt hm ha, hv, cexp, hmagnitude, fexpOf, fltExp]
  change certificateExponent fmt (binade fmt compare) ≤ _
  simp only [certificateExponent]
  omega

end FloatLib.Floats.Formats.BinaryInterchange.Model.AlgebraicRounding
