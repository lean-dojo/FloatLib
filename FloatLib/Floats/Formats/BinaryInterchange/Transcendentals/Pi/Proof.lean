/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Pi.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Rounding.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.SqrtSemantics
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Enclosure.Proof
public import FloatLib.Numerics.Enclosure.Constants.Proof
public import FloatLib.Numerics.Exact.Trigonometric.Proof
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Correct rounding of pi

`toReal_pi` proves that `Model.pi` is the nearest-even rounding of `Real.pi` in every IEEE
descriptor, and `isFinite_pi` that it is finite. The cached enclosure contains `π * 2 ^ bits` by
`halfPiLower_spec`, so an accepted enclosure gives the rounding by
`toReal_eq_roundAt_of_roundScaled?_eq_some`. The comparator fallback compares `atan 1 = π / 4`
exactly, and its result is finite because `π < 3.15` lies below the overflow threshold of every
IEEE descriptor: the smallest, `ieee 2 1`, has largest finite value 3 and threshold 3.5.
`isFinite_round_of_lt_overflow` states that threshold argument for any exact comparator.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Numerics

namespace AlgebraicRounding

/--
An exact comparator for a target below the overflow threshold
`2 ^ (maxNormal + 1) - 2 ^ (maxNormal - fracWidth - 1)` gives a finite IEEE result.
-/
theorem isFinite_round_of_lt_overflow (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign : Bool) (compare : Rat → Ordering) (target : ℝ)
    (hcompare : ∀ candidate : Rat, compare candidate = cmp target (candidate : ℝ))
    (hbound : target <
      FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (fmt.maxNormalExponent + 1) -
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
          (fmt.maxNormalExponent - fmt.fracWidth - 1)) :
    isFinite (round fmt sign compare) = true := by
  have hemax := FloatFormat.maxNormalExponent_eq_ieee fmt hfmt
  unfold round
  split
  · have hs := FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt hfmt
    cases sign <;> simp [zero, hs, isFinite_posZero, isFinite_negZero fmt hs]
  · rename_i hlarge
    have hupper :
        target < FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (upperExponent fmt) := by
      have : 0 < FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
          (fmt.maxNormalExponent - fmt.fracWidth - 1) := FloatLib.Floats.Formats.Flocq.bpow.pos _ _
      simp only [upperExponent]
      linarith
    have hlt : compare (powerOfTwo (upperExponent fmt)) = .lt := by
      rw [hcompare, cast_powerOfTwo]
      exact (cmp_eq_lt_iff _ _).mpr hupper
    rw [ite_eq_right_iff.mpr (fun h => absurd hlt h)]
    have hlo :
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (lowerExponent fmt) ≤ target := by
      have hgt : compare (powerOfTwo (lowerExponent fmt)) = .gt := by
        simpa only [not_not] using hlarge
      have := (cmp_eq_gt_iff _ _).mp
        (show cmp target
            (FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (lowerExponent fmt)) = .gt by
          simpa only [hcompare, cast_powerOfTwo] using hgt)
      exact this.le
    obtain ⟨hm, ha, he⟩ := certificate_spec fmt hfmt compare target hcompare hlo hupper
    let c := certificate fmt compare
    have hc : target / FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix c.exponent *
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix c.exponent = target :=
      div_mul_cancel₀ _ (FloatLib.Floats.Formats.Flocq.bpow.ne_zero _ _)
    simp only [roundCertificate, hfmt, ite_true]
    apply isFinite_ofModel_roundWithAccuracy_of_lt_overflow fmt hfmt (modelSign sign)
      c.mantissa c.exponent c.accuracy
      (target / FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix c.exponent) hm ha he
    rw [hc]
    rw [hemax] at hbound
    simpa using hbound

end AlgebraicRounding

/-- The cached enclosure contains `π * 2 ^ bits`. -/
theorem Transcendentals.contains_piScaledEnclosure (bits : Nat) :
    (Transcendentals.piScaledEnclosure bits).Contains (Real.pi * 2 ^ bits) := by
  obtain ⟨hlo, hhi⟩ := Numerics.Enclosure.Constants.halfPiLower_spec bits
  simp only [Transcendentals.piScaledEnclosure, RationalInterval.Contains]
  push_cast
  constructor <;> linarith

/-- The exact fallback comparator orders `π` against every rational candidate. -/
private theorem prepareArctan_one_compare_div_four (levels : Nat) (candidate : ℚ) :
    (TrigonometricComparison.prepareArctan 1 levels).compare (candidate / 4) =
      cmp Real.pi (candidate : ℝ) := by
  rw [TrigonometricComparison.prepareArctan_eq_real, Rat.cast_one, Real.arctan_one]
  push_cast
  simp only [cmp, cmpUsing, div_lt_div_iff_of_pos_right (show (0 : ℝ) < 4 by norm_num)]

/-- `π` lies below the overflow threshold of every IEEE descriptor. -/
theorem pi_lt_overflowThreshold (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    Real.pi <
      FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (fmt.maxNormalExponent + 1) -
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
          (fmt.maxNormalExponent - fmt.fracWidth - 1) := by
  have hemax : 1 ≤ fmt.maxNormalExponent := by
    rw [FloatFormat.maxNormalExponent_eq_ieee fmt hfmt]
    have := FloatFormat.bias_pos fmt
    simp only [FloatFormat.ieeeMaxNormalExponent, Int.ofNat_eq_natCast]
    omega
  have hfrac := fmt.fracWidth_pos
  set m := fmt.maxNormalExponent
  have hbpow (e : ℤ) : FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix e = (2 : ℝ) ^ e := by
    simp [FloatLib.Floats.Formats.Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal]
  rw [hbpow, hbpow]
  have hlow : (2 : ℝ) ^ (m - fmt.fracWidth - 1) ≤ 2 ^ (m - 2) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hsplit : (2 : ℝ) ^ (m + 1) = 8 * 2 ^ (m - 2) := by
    rw [show m + 1 = (m - 2) + 3 by ring, zpow_add₀ (by norm_num)]
    norm_num
    ring
  have hbase : (1 / 2 : ℝ) ≤ 2 ^ (m - 2) := by
    calc (1 / 2 : ℝ) = 2 ^ (-1 : ℤ) := by norm_num
      _ ≤ 2 ^ (m - 2) := zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hpi := Real.pi_lt_d2
  rw [hsplit]
  nlinarith

/-- `Model.pi` is finite in every IEEE descriptor. -/
theorem isFinite_pi (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) : isFinite (pi fmt) = true := by
  unfold pi
  dsimp only
  split
  · rename_i result hresult
    exact Transcendentals.Enclosure.isFinite_of_roundScaled?_eq_some hresult
  · exact AlgebraicRounding.isFinite_round_of_lt_overflow fmt hfmt false _ Real.pi
      (prepareArctan_one_compare_div_four 16) (pi_lt_overflowThreshold fmt hfmt)

/-- `Model.pi` is the nearest-even rounding of `Real.pi` in every IEEE descriptor. -/
theorem toReal_pi (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    toReal (pi fmt) = roundAt fmt Real.pi := by
  have hfinite := isFinite_pi fmt hfmt
  unfold pi at hfinite ⊢
  dsimp only at hfinite ⊢
  split
  · rename_i result hresult
    rw [Transcendentals.Enclosure.toReal_eq_roundAt_of_roundScaled?_eq_some
      (Transcendentals.contains_piScaledEnclosure (Transcendentals.piBits fmt)) hresult]
    congr 1
    rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ (by norm_num)]
    simp
  · rename_i hnone
    rw [hnone] at hfinite
    rw [AlgebraicRounding.toReal_round_eq_roundAt fmt hfmt false _ Real.pi Real.pi_pos.le
      (prepareArctan_one_compare_div_four 16) hfinite]
    simp

end FloatLib.Floats.Formats.BinaryInterchange.Model
