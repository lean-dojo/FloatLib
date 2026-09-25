/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Rounding.Certificate
public import FloatLib.Floats.Formats.BinaryInterchange.Model.Packing.Special
public import FloatLib.Floats.Formats.Posit.Algebraic.Root.Proof

/-!
# Correct rounding from exact algebraic comparisons

The certificate bridge proves nearest-even rounding for every interior target. Monotonicity
and the even tie at half the least subnormal cover the complete underflow interval. A finite
IEEE result excludes the explicit overflow branch. Thus the real theorem needs no search-budget
or distance-from-boundaries premise, and includes exact ties and subnormal results.

The real-refinement theorem uses a conventional IEEE descriptor, matching the existing logical
rounding bridge. Runtime handling of custom descriptors is separate from this theorem.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.AlgebraicRounding

open FloatLib.Floats.Formats.Flocq

/-- The midpoint between zero and the least subnormal rounds to the even endpoint, zero. -/
theorem roundAt_halfMinSubnormal (fmt : FloatFormat) :
    roundAt fmt (bpow Numerics.binaryRadix (lowerExponent fmt)) = 0 := by
  have hc : cexp Numerics.binaryRadix (fexpOf fmt)
      (bpow Numerics.binaryRadix (lowerExponent fmt)) = fmt.minSubnormalExponent := by
    rw [cexp, magnitude_bpow, fexpOf, fltExp]
    simp only [lowerExponent]
    omega
  have hs : scaledMantissa Numerics.binaryRadix (fexpOf fmt)
      (bpow Numerics.binaryRadix (lowerExponent fmt)) = (1 / 2 : ℝ) := by
    rw [scaledMantissa, hc, ← bpow.add_exp]
    have he : lowerExponent fmt + -fmt.minSubnormalExponent = -1 := by
      dsimp [lowerExponent]
      omega
    rw [he]
    norm_num [bpow, Numerics.binaryRadix, Numerics.Radix.toReal]
  unfold roundAt FloatLib.Floats.Formats.Flocq.round FloatLib.Floats.Formats.Flocq.toReal
  rw [hs]
  norm_num [nearestEven]

/-- Every nonnegative target at or below the first midpoint rounds to zero. -/
theorem roundAt_eq_zero_of_le_halfMinSubnormal (fmt : FloatFormat) (target : ℝ)
    (hnonneg : 0 ≤ target)
    (hsmall : target ≤ bpow Numerics.binaryRadix (lowerExponent fmt)) :
    roundAt fmt target = 0 := by
  apply le_antisymm
  · simpa [roundAt_halfMinSubnormal] using roundAt_mono fmt hsmall
  · simpa [roundAt_zero] using roundAt_mono fmt hnonneg

/--
An exact oracle produces one nearest-even rounding of its signed real target.

The sole numerical-domain premise is nonnegativity of the magnitude. Finiteness of the packed
IEEE result excludes overflow; underflow to signed zero and all midpoint ties are covered.
-/
theorem toReal_round_eq_roundAt (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign : Bool) (compare : Rat → Ordering) (target : ℝ) (hnonneg : 0 ≤ target)
    (hcompare : ∀ candidate : Rat, compare candidate = cmp target (candidate : ℝ))
    (hfinite : isFinite (round fmt sign compare) = true) :
    toReal (round fmt sign compare) = roundAt fmt (if sign then -target else target) := by
  unfold round at hfinite ⊢
  split
  · rename_i hsmall
    have hle : target ≤ bpow Numerics.binaryRadix (lowerExponent fmt) := by
      simpa only [hcompare, cast_powerOfTwo, ne_eq, cmp_eq_gt_iff, not_lt] using hsmall
    have hz := roundAt_eq_zero_of_le_halfMinSubnormal fmt target hnonneg hle
    cases sign <;> simp [hz]
  · rename_i hlarge
    rw [ite_eq_right hlarge] at hfinite
    split
    · rename_i habove
      rw [ite_eq_left habove] at hfinite
      have hs := FloatFormat.supportsInfinity_eq_true_of_isIEEE fmt hfmt
      cases sign <;> simp [nativeOverflow_eq_signedInf_of_isIEEE fmt hfmt,
        isFinite_posInf fmt hs, isFinite_negInf fmt hs] at hfinite
    · rename_i hbounded
      rw [ite_eq_right hbounded] at hfinite
      have hlo : bpow Numerics.binaryRadix (lowerExponent fmt) ≤ target := by
        have hgt : compare (powerOfTwo (lowerExponent fmt)) = .gt := by
          simpa only [not_not] using hlarge
        have := (cmp_eq_gt_iff _ _).mp
          (show cmp target (bpow Numerics.binaryRadix (lowerExponent fmt)) = .gt by
            simpa only [hcompare, cast_powerOfTwo] using hgt)
        exact this.le
      have hhi : target < bpow Numerics.binaryRadix (upperExponent fmt) := by
        have hlt : compare (powerOfTwo (upperExponent fmt)) = .lt := by
          simpa only [not_not] using hbounded
        simpa only [hcompare, cast_powerOfTwo, cmp_eq_lt_iff] using hlt
      obtain ⟨hm, ha, he⟩ := certificate_spec fmt hfmt compare target hcompare hlo hhi
      let c := certificate fmt compare
      have hc : target / bpow Numerics.binaryRadix c.exponent *
          bpow Numerics.binaryRadix c.exponent = target :=
        div_mul_cancel₀ _ (bpow.ne_zero _ _)
      simp only [roundCertificate, hfmt, ite_true] at hfinite ⊢
      rw [toReal_ofModel_roundWithAccuracy_eq_roundAt fmt hfmt (modelSign sign)
        c.mantissa c.exponent c.accuracy (target / bpow Numerics.binaryRadix c.exponent)
        hm ha he hfinite, hc]
      cases sign <;> simp [modelSign, modelSignBit]

/-- Exact integer-power comparisons correctly round any characterized nonnegative root. -/
theorem toReal_root_eq_roundAt (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign : Bool) (radicand : Rat) (degree : Nat) (target : ℝ)
    (hnonneg : 0 ≤ target) (hdegree : degree ≠ 0) (hroot : target ^ degree = (radicand : ℝ))
    (hfinite : isFinite (root fmt sign radicand degree) = true) :
    toReal (root fmt sign radicand degree) =
      roundAt fmt (if sign then -target else target) :=
  toReal_round_eq_roundAt fmt hfmt sign _ target hnonneg
    (Posit.Model.RootRounding.compareRoot_eq_real radicand degree target
      hnonneg hdegree hroot) hfinite

/-- The nonnegative real root exists for every nonnegative radicand and positive degree. -/
theorem toReal_root_eq_roundAt_rpow (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign : Bool) (radicand : Rat) (degree : Nat)
    (hrad : 0 ≤ radicand) (hdegree : degree ≠ 0)
    (hfinite : isFinite (root fmt sign radicand degree) = true) :
    toReal (root fmt sign radicand degree) =
      roundAt fmt (if sign then -((radicand : ℝ) ^ (degree : ℝ)⁻¹)
        else (radicand : ℝ) ^ (degree : ℝ)⁻¹) := by
  have hreal : 0 ≤ (radicand : ℝ) := by exact_mod_cast hrad
  exact toReal_root_eq_roundAt fmt hfmt sign radicand degree _
    (Real.rpow_nonneg hreal _) hdegree (Real.rpow_inv_natCast_pow hreal hdegree) hfinite

/-- Degree two rounds the exact square root, including zero. -/
theorem toReal_root_two_eq_roundAt_sqrt (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign : Bool) (radicand : Rat) (hrad : 0 ≤ radicand)
    (hfinite : isFinite (root fmt sign radicand 2) = true) :
    toReal (root fmt sign radicand 2) =
      roundAt fmt (if sign then -Real.sqrt (radicand : ℝ) else Real.sqrt (radicand : ℝ)) := by
  apply toReal_root_eq_roundAt fmt hfmt sign radicand 2 _ (Real.sqrt_nonneg _) (by decide)
    (Real.sq_sqrt (by exact_mod_cast hrad)) hfinite

end FloatLib.Floats.Formats.BinaryInterchange.Model.AlgebraicRounding
