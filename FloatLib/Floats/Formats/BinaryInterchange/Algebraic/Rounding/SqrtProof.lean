/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Rounding.SqrtRuntime
public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Rounding.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Logarithm
public import FloatLib.Kernels.IntegerRoot.Proof

/-!
# Correctness of rational integer-root certificates

Integer division followed by integer root brackets the real root of a nonnegative rational.
The shared Newton kernel supplies the exact floor root without repeated power checks.
Uniqueness of the integer part identifies its result with the comparison search.
The root's binade follows from the radicand's binary logarithm and Euclidean division.
These facts preserve the complete encoded result for every descriptor.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.AlgebraicRounding

open FloatLib.Floats.Formats.Flocq

private theorem positiveRat_cast (radicand : Rat) (hrad : 0 ≤ radicand) :
    (radicand.num.natAbs : ℝ) / radicand.den = (radicand : ℝ) := by
  calc
    _ = |(radicand : ℝ)| := by simp [Rat.cast_def, abs_div]
    _ = _ := abs_of_nonneg (by exact_mod_cast hrad)

/-- Dividing the radicand's floor binary logarithm locates every positive-degree root's binade. -/
theorem rootBinade_bounds (radicand : Rat) (degree : Nat) (target : ℝ)
    (hrad : 0 < radicand) (hdegree : degree ≠ 0) (htarget : 0 ≤ target)
    (hroot : target ^ degree = (radicand : ℝ)) :
    Flocq.bpow Numerics.binaryRadix (rootBinade radicand degree) ≤ target ∧
      target < Flocq.bpow Numerics.binaryRadix (rootBinade radicand degree + 1) := by
  let logarithm := Numerics.RationalBinary.floorLog2 radicand.num.natAbs radicand.den
  have hn : radicand.num.natAbs ≠ 0 := by
    simpa only [ne_eq, Int.natAbs_eq_zero, Rat.num_eq_zero] using hrad.ne'
  have hr := positiveRat_cast radicand hrad.le
  have hlog := floorLog2_bounds radicand.num.natAbs radicand.den hn radicand.den_nz
  rw [hr] at hlog
  have hnInt : (0 : Int) < degree := by exact_mod_cast Nat.pos_of_ne_zero hdegree
  have hlo : rootBinade radicand degree * degree ≤ logarithm :=
    Int.ediv_mul_le logarithm hnInt.ne'
  have hhi : logarithm + 1 ≤ (rootBinade radicand degree + 1) * degree := by
    have := Int.lt_mul_ediv_self_add (x := logarithm) hnInt
    change logarithm + 1 ≤ (logarithm / (degree : Int) + 1) * degree
    nlinarith
  have hp (exponent : Int) :
      Flocq.bpow Numerics.binaryRadix exponent ^ degree =
        Flocq.bpow Numerics.binaryRadix (exponent * degree) := by
    simp only [Flocq.bpow, zpow_mul, zpow_natCast]
  constructor
  · apply (pow_le_pow_iff_left₀ (bpow.pos _ _).le htarget hdegree).mp
    rw [hp, hroot]
    exact ((bpow_le_bpow_iff _ _ _).mpr hlo).trans hlog.1
  · apply (pow_lt_pow_iff_left₀ htarget (bpow.pos _ _).le hdegree).mp
    rw [hp, hroot]
    exact hlog.2.trans_le ((bpow_le_bpow_iff _ _ _).mpr hhi)

/-- The computed root binade agrees with the bounded search throughout the finite interval. -/
theorem rootBinade_eq_binade (fmt : FloatFormat) (radicand : Rat) (degree : Nat)
    (target : ℝ) (hrad : 0 < radicand) (hdegree : degree ≠ 0) (htarget : 0 ≤ target)
    (hroot : target ^ degree = (radicand : ℝ))
    (hlower : Flocq.bpow Numerics.binaryRadix (lowerExponent fmt) ≤ target)
    (hupper : target < Flocq.bpow Numerics.binaryRadix (upperExponent fmt)) :
    rootBinade radicand degree =
      binade fmt (Posit.Model.RootRounding.compareRoot radicand degree) := by
  have hfast := rootBinade_bounds radicand degree target hrad hdegree htarget hroot
  have hslow := binade_bounds fmt _ target
    (Posit.Model.RootRounding.compareRoot_eq_real radicand degree target htarget hdegree hroot)
    hlower hupper
  exact bpow_interval_exponent_unique target _ _ hfast.1 hfast.2 hslow.1 hslow.2

/-- Raw integer scaling preserves the exact radicand without rational normalization. -/
theorem rootScale_real (radicand : Rat) (degree : Nat) (exponent : Int)
    (hrad : 0 ≤ radicand) :
    ((rootScale radicand degree exponent).1 : ℝ) /
        (rootScale radicand degree exponent).2 =
      (radicand : ℝ) / Flocq.bpow Numerics.binaryRadix exponent ^ degree := by
  rw [rootScale, scaleByPowerOfTwo_real]
  simp only [scaledRatToReal, positiveRat_cast radicand hrad, Model.bpow,
    Flocq.bpow, zpow_neg, zpow_mul, zpow_natCast, div_eq_mul_inv]

/-- Scaling preserves the positive denominator required by integer root comparisons. -/
theorem rootScale_den_pos (radicand : Rat) (degree : Nat) (exponent : Int) :
    0 < (rootScale radicand degree exponent).2 :=
  Nat.pos_of_ne_zero (Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero
    _ _ _ radicand.den_nz)

/-- Integer cross-multiplication compares an exact nonnegative root with an integer. -/
theorem cmp_integerPower_eq_root (numerator denominator degree candidate : Nat) (target : ℝ)
    (hden : 0 < denominator) (hdegree : degree ≠ 0) (htarget : 0 ≤ target)
    (hroot : target ^ degree = (numerator : ℝ) / denominator) :
    cmp numerator (candidate ^ degree * denominator) = cmp target (candidate : ℝ) := by
  have hd : (0 : ℝ) < denominator := by exact_mod_cast hden
  have hlt : numerator < candidate ^ degree * denominator ↔ target < (candidate : ℝ) := by
    calc
      _ ↔ (numerator : ℝ) < (candidate : ℝ) ^ degree * denominator := by norm_cast
      _ ↔ target ^ degree < (candidate : ℝ) ^ degree := by
        rw [hroot, div_lt_iff₀ hd]
      _ ↔ _ := pow_lt_pow_iff_left₀ htarget (Nat.cast_nonneg _) hdegree
  have hgt : candidate ^ degree * denominator < numerator ↔ (candidate : ℝ) < target := by
    calc
      _ ↔ (candidate : ℝ) ^ degree * denominator < numerator := by norm_cast
      _ ↔ (candidate : ℝ) ^ degree < target ^ degree := by
        rw [hroot, lt_div_iff₀ hd]
      _ ↔ _ := pow_lt_pow_iff_left₀ (Nat.cast_nonneg _) htarget hdegree
  simp only [cmp, cmpUsing, hlt, hgt]

/-- Doubling the candidate compares the exact root with a half-integer using only integers. -/
theorem cmp_halfIntegerPower_eq_root
    (numerator denominator degree candidate : Nat) (target : ℝ)
    (hden : 0 < denominator) (hdegree : degree ≠ 0) (htarget : 0 ≤ target)
    (hroot : target ^ degree = (numerator : ℝ) / denominator) :
    cmp (numerator <<< degree) ((2 * candidate + 1) ^ degree * denominator) =
      cmp target ((candidate : ℝ) + 1 / 2) := by
  have hdouble : (2 * target) ^ degree = ((numerator <<< degree : Nat) : ℝ) / denominator := by
    rw [mul_pow, hroot]
    simp only [Nat.shiftLeft_eq, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    ring
  rw [cmp_integerPower_eq_root _ _ _ _ (2 * target) hden hdegree
    (by positivity) hdouble]
  have hlt : 2 * target < ((2 * candidate + 1 : Nat) : ℝ) ↔
      target < (candidate : ℝ) + 1 / 2 := by
    push_cast
    constructor <;> intro h <;> linarith
  have hgt : ((2 * candidate + 1 : Nat) : ℝ) < 2 * target ↔
      (candidate : ℝ) + 1 / 2 < target := by
    push_cast
    constructor <;> intro h <;> linarith
  simp only [cmp, cmpUsing, hlt, hgt]

/-- Integer square root of an integer quotient brackets the square root of the exact quotient. -/
theorem sqrtQuotient_bounds (numerator denominator : Nat) (hd : 0 < denominator) :
    (Nat.sqrt (numerator / denominator) : ℝ) ≤ Real.sqrt (numerator / denominator) ∧
      Real.sqrt (numerator / denominator) < Nat.sqrt (numerator / denominator) + 1 := by
  have hdReal : (0 : ℝ) < denominator := by exact_mod_cast hd
  have hn : (0 : ℝ) ≤ numerator / denominator := by positivity
  constructor
  · apply Real.le_sqrt_of_sq_le
    apply (le_div_iff₀ hdReal).mpr
    exact_mod_cast (Nat.le_div_iff_mul_le hd).mp (Nat.sqrt_le' (numerator / denominator))
  · apply (Real.sqrt_lt hn (by positivity)).mpr
    apply (div_lt_iff₀ hdReal).mpr
    exact_mod_cast (Nat.div_lt_iff_lt_mul hd).mp
      (Nat.lt_succ_sqrt' (numerator / denominator))

/-- Target scaling commutes with the nonnegative square root. -/
theorem sqrtMantissa_bounds (radicand : Rat) (exponent : Int) (hrad : 0 ≤ radicand) :
    (sqrtMantissa radicand exponent : ℝ) ≤
        Real.sqrt (radicand : ℝ) / Flocq.bpow Numerics.binaryRadix exponent ∧
      Real.sqrt (radicand : ℝ) / Flocq.bpow Numerics.binaryRadix exponent <
        sqrtMantissa radicand exponent + 1 := by
  let scaled := rootScale radicand 2 exponent
  have hreal : 0 ≤ (radicand : ℝ) := by exact_mod_cast hrad
  have hsqrt : Real.sqrt ((scaled.1 : ℝ) / scaled.2) =
      Real.sqrt (radicand : ℝ) / Flocq.bpow Numerics.binaryRadix exponent := by
    rw [rootScale_real radicand 2 exponent hrad, Real.sqrt_div hreal,
      Real.sqrt_sq (bpow.pos _ _).le]
  have h := sqrtQuotient_bounds scaled.1 scaled.2 (rootScale_den_pos radicand 2 exponent)
  rw [hsqrt] at h
  simpa only [sqrtMantissa, Numerics.FixedWord.IntegerSquareRoot.sqrtNat_eq_sqrt] using h

/-- The exact integer root agrees with the comparison search throughout its finite interval. -/
theorem rootMantissa_eq_truncatedMantissa (fmt : FloatFormat) (radicand : Rat) (degree : Nat)
    (target : ℝ) (exponent : Int) (hrad : 0 ≤ radicand) (hdegree : degree ≠ 0)
    (htarget : 0 ≤ target) (hroot : target ^ degree = (radicand : ℝ))
    (hupper : target / Flocq.bpow Numerics.binaryRadix exponent <
      (2 : ℝ) ^ (fmt.fracWidth + 3)) :
    rootMantissa fmt radicand degree exponent =
      truncatedMantissa fmt (Posit.Model.RootRounding.compareRoot radicand degree) exponent := by
  let compare := Posit.Model.RootRounding.compareRoot radicand degree
  have hcompare : ∀ candidate : Rat,
      compare candidate = cmp target (candidate : ℝ) :=
    Posit.Model.RootRounding.compareRoot_eq_real radicand degree target htarget hdegree hroot
  have hnonneg : 0 ≤ target / Flocq.bpow Numerics.binaryRadix exponent := by
    exact div_nonneg htarget (bpow.pos _ _).le
  have hbisect := truncatedMantissa_bounds fmt compare target exponent
    hcompare hnonneg hupper
  rw [rootMantissa, ite_eq_right hdegree, Numerics.IntegerRoot.root_eq_nthRoot]
  let scaled := rootScale radicand degree exponent
  let mantissa := Nat.nthRoot degree (scaled.1 / scaled.2)
  have hden := rootScale_den_pos radicand degree exponent
  have hdenReal : (0 : ℝ) < scaled.2 := by exact_mod_cast hden
  have hrootScaled : (target / Flocq.bpow Numerics.binaryRadix exponent) ^ degree =
      (scaled.1 : ℝ) / scaled.2 := by
    rw [rootScale_real radicand degree exponent hrad, div_pow, hroot]
  have hfloor : (mantissa : ℝ) ≤ target / Flocq.bpow Numerics.binaryRadix exponent ∧
      target / Flocq.bpow Numerics.binaryRadix exponent < (mantissa : ℝ) + 1 := by
    constructor
    · apply (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) hnonneg hdegree).mp
      rw [hrootScaled, le_div_iff₀ hdenReal]
      exact_mod_cast (Nat.le_div_iff_mul_le hden).mp
        (Nat.pow_nthRoot_le (n := degree) (a := scaled.1 / scaled.2) (Or.inl hdegree))
    · apply (pow_lt_pow_iff_left₀ hnonneg (by positivity) hdegree).mp
      rw [hrootScaled, div_lt_iff₀ hdenReal]
      exact_mod_cast (Nat.div_lt_iff_lt_mul hden).mp
        (Nat.lt_pow_nthRoot_add_one hdegree (scaled.1 / scaled.2))
  exact ((Nat.floor_eq_iff hnonneg).mpr hfloor).symm.trans
    ((Nat.floor_eq_iff hnonneg).mpr hbisect)

/-- Integer comparisons preserve the complete exactness and midpoint classification. -/
theorem rootAccuracy_eq_accuracyAt (radicand : Rat) (degree : Nat) (exponent : Int)
    (mantissa : Nat) (target : ℝ) (hrad : 0 ≤ radicand) (hdegree : degree ≠ 0)
    (htarget : 0 ≤ target) (hroot : target ^ degree = (radicand : ℝ)) :
    rootAccuracy radicand degree exponent mantissa =
      accuracyAt (fun candidate =>
        Posit.Model.RootRounding.compareRoot radicand degree
          (candidate * powerOfTwo exponent)) mantissa := by
  let scaled := rootScale radicand degree exponent
  let value := target / Flocq.bpow Numerics.binaryRadix exponent
  have hvalue : 0 ≤ value := div_nonneg htarget (bpow.pos _ _).le
  have hscaled : value ^ degree = (scaled.1 : ℝ) / scaled.2 := by
    rw [rootScale_real radicand degree exponent hrad, div_pow, hroot]
  have hinteger := cmp_integerPower_eq_root scaled.1 scaled.2 degree mantissa value
    (rootScale_den_pos radicand degree exponent) hdegree hvalue hscaled
  have hhalf := cmp_halfIntegerPower_eq_root scaled.1 scaled.2 degree mantissa value
    (rootScale_den_pos radicand degree exponent) hdegree hvalue hscaled
  have hexact : scaled.1 = mantissa ^ degree * scaled.2 ↔ value = (mantissa : ℝ) := by
    rw [← cmp_eq_eq_iff, hinteger, cmp_eq_eq_iff]
  have hcompare := scaled_compare (Posit.Model.RootRounding.compareRoot radicand degree)
    target exponent
    (Posit.Model.RootRounding.compareRoot_eq_real radicand degree target htarget hdegree hroot)
  dsimp only [scaled, value] at hexact hhalf
  simp only [rootAccuracy, scaledRootAccuracy, accuracyAt, hcompare, Rat.cast_natCast,
    Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, cmp_eq_eq_iff, hexact, hhalf]

/-- Sharing the scaled ratio preserves every field of the accuracy certificate. -/
theorem rootCertificateAt_eq (fmt : FloatFormat) (radicand : Rat) (degree : Nat)
    (exponent : Int) :
    rootCertificateAt fmt radicand degree exponent =
      ⟨rootMantissa fmt radicand degree exponent, exponent,
        rootAccuracy radicand degree exponent (rootMantissa fmt radicand degree exponent)⟩ := by
  rfl

/-- Integer-root construction preserves every field of the reference accuracy certificate. -/
theorem rootCertificate_eq_certificate (fmt : FloatFormat) (radicand : Rat) (degree : Nat)
    (target : ℝ) (hrad : 0 < radicand) (hdegree : degree ≠ 0) (htarget : 0 ≤ target)
    (hroot : target ^ degree = (radicand : ℝ))
    (hlower : Flocq.bpow Numerics.binaryRadix (lowerExponent fmt) ≤ target)
    (hupper : target < Flocq.bpow Numerics.binaryRadix (upperExponent fmt)) :
    rootCertificate fmt radicand degree =
      certificate fmt (Posit.Model.RootRounding.compareRoot radicand degree) := by
  let compare := Posit.Model.RootRounding.compareRoot radicand degree
  let exponent := certificateExponent fmt (binade fmt compare)
  have hcompare := Posit.Model.RootRounding.compareRoot_eq_real
    radicand degree target htarget hdegree hroot
  have hbinade := rootBinade_eq_binade fmt radicand degree target
    hrad hdegree htarget hroot hlower hupper
  obtain ⟨_, hupperScaled⟩ :=
    certificate_scaled_bounds fmt compare target hcompare hlower hupper
  have hm := rootMantissa_eq_truncatedMantissa fmt radicand degree target exponent
    hrad.le hdegree htarget hroot hupperScaled
  simpa only [rootCertificate, rootCertificateAt_eq, certificate, hbinade,
    rootAccuracy_eq_accuracyAt radicand degree _ _ target hrad.le hdegree htarget hroot] using
    congrArg (fun mantissa =>
      Certificate.mk mantissa exponent
        (accuracyAt (fun candidate => compare (candidate * powerOfTwo exponent)) mantissa)) hm

/-- The integer-square-root certificate equals the comparison certificate throughout its range. -/
theorem sqrtCertificate_eq_certificate (fmt : FloatFormat) (radicand : Rat)
    (hrad : 0 ≤ radicand)
    (hlower : Flocq.bpow Numerics.binaryRadix (lowerExponent fmt) ≤ Real.sqrt (radicand : ℝ))
    (hupper : Real.sqrt (radicand : ℝ) < Flocq.bpow Numerics.binaryRadix (upperExponent fmt)) :
    sqrtCertificate fmt radicand =
      certificate fmt (Posit.Model.RootRounding.compareRoot radicand 2) := by
  have hpositive : 0 < Real.sqrt (radicand : ℝ) := (bpow.pos _ _).trans_le hlower
  have hradPositive : 0 < radicand := by
    exact_mod_cast Real.sqrt_pos.mp hpositive
  exact rootCertificate_eq_certificate fmt radicand 2 (Real.sqrt (radicand : ℝ))
    hradPositive (by decide) (Real.sqrt_nonneg _) (Real.sq_sqrt (by exact_mod_cast hrad))
    hlower hupper

/-- Integer binade classification and exact roots preserve every reference result bit. -/
theorem rootRat_eq_root (fmt : FloatFormat) (sign : Bool) (radicand : Rat) (degree : Nat) :
    rootRat fmt sign radicand degree = root fmt sign radicand degree := by
  unfold rootRat
  split
  · rfl
  · rename_i hdomain
    have hdegree : degree ≠ 0 := (not_or.mp hdomain).1
    have hrad : 0 < radicand := lt_of_not_ge (not_or.mp hdomain).2
    let target := (radicand : ℝ) ^ (degree : ℝ)⁻¹
    have hreal : 0 ≤ (radicand : ℝ) := by exact_mod_cast hrad.le
    have htarget : 0 ≤ target := Real.rpow_nonneg hreal _
    have hroot : target ^ degree = (radicand : ℝ) :=
      Real.rpow_inv_natCast_pow hreal hdegree
    let compare := Posit.Model.RootRounding.compareRoot radicand degree
    let b := rootBinade radicand degree
    have hcompare := Posit.Model.RootRounding.compareRoot_eq_real
      radicand degree target htarget hdegree hroot
    have hb := rootBinade_bounds radicand degree target hrad hdegree htarget hroot
    change
      (if b < lowerExponent fmt then zero fmt sign
       else if upperExponent fmt ≤ b then nativeOverflow fmt sign
       else if b = lowerExponent fmt ∧ compare (powerOfTwo b) = .eq then zero fmt sign
       else roundCertificate fmt sign (rootCertificate fmt radicand degree)) =
        round fmt sign compare
    unfold round
    by_cases hsmall : compare (powerOfTwo (lowerExponent fmt)) ≠ .gt
    · rw [ite_eq_left hsmall]
      have hle : target ≤ Flocq.bpow Numerics.binaryRadix (lowerExponent fmt) := by
        simpa only [compare, hcompare, cast_powerOfTwo, ne_eq, cmp_eq_gt_iff, not_lt] using hsmall
      have hble : b ≤ lowerExponent fmt :=
        (bpow_le_bpow_iff _ _ _).mp (hb.1.trans hle)
      by_cases hbelow : b < lowerExponent fmt
      · rw [ite_eq_left hbelow]
      · have heqb : b = lowerExponent fmt := by omega
        have heq : compare (powerOfTwo b) = .eq := by
          have heqReal : target = Flocq.bpow Numerics.binaryRadix b :=
            le_antisymm (heqb ▸ hle) hb.1
          simpa only [compare, hcompare, cast_powerOfTwo, cmp_eq_eq_iff] using heqReal
        have hnabove : ¬ upperExponent fmt ≤ b := by
          have := lowerExponent_lt_upperExponent fmt
          omega
        rw [ite_eq_right hbelow, ite_eq_right hnabove, ite_eq_left ⟨heqb, heq⟩]
    · have hgt : Flocq.bpow Numerics.binaryRadix (lowerExponent fmt) < target := by
        simpa only [compare, hcompare, cast_powerOfTwo, ne_eq, cmp_eq_gt_iff, not_not]
          using hsmall
      have hbelow : ¬ b < lowerExponent fmt := by
        intro h
        have hnext : b + 1 ≤ lowerExponent fmt := by omega
        exact (hb.2.trans_le ((bpow_le_bpow_iff _ _ _).mpr hnext)).not_gt hgt
      rw [ite_eq_right hbelow, ite_eq_right hsmall]
      by_cases hlarge : compare (powerOfTwo (upperExponent fmt)) ≠ .lt
      · rw [ite_eq_left hlarge]
        have hle : Flocq.bpow Numerics.binaryRadix (upperExponent fmt) ≤ target := by
          simpa only [compare, hcompare, cast_powerOfTwo, ne_eq, cmp_eq_lt_iff, not_lt] using hlarge
        have hupper : upperExponent fmt < b + 1 :=
          (bpow_lt_bpow_iff _ _ _).mp (hle.trans_lt hb.2)
        rw [ite_eq_left (show upperExponent fmt ≤ b by omega)]
      · rw [ite_eq_right hlarge]
        have hlt : target < Flocq.bpow Numerics.binaryRadix (upperExponent fmt) := by
          simpa only [compare, hcompare, cast_powerOfTwo, ne_eq, cmp_eq_lt_iff, not_not]
            using hlarge
        have hupper : b < upperExponent fmt :=
          (bpow_lt_bpow_iff _ _ _).mp (hb.1.trans_lt hlt)
        have hmidpoint : ¬ (b = lowerExponent fmt ∧ compare (powerOfTwo b) = .eq) := by
          rintro ⟨heqb, heq⟩
          have heqReal : target = Flocq.bpow Numerics.binaryRadix b := by
            simpa only [compare, hcompare, cast_powerOfTwo, cmp_eq_eq_iff] using heq
          rw [heqb] at heqReal
          exact hgt.ne' heqReal
        rw [ite_eq_right (not_le.mpr hupper), ite_eq_right hmidpoint]
        exact congrArg (roundCertificate fmt sign)
          (rootCertificate_eq_certificate fmt radicand degree target hrad hdegree htarget
            hroot hgt.le hlt)

/-- The optimized square root preserves every result bit for any complete descriptor. -/
theorem sqrtRat_eq_root (fmt : FloatFormat) (sign : Bool) (radicand : Rat)
    (_hrad : 0 ≤ radicand) :
    sqrtRat fmt sign radicand = root fmt sign radicand 2 := by
  exact rootRat_eq_root fmt sign radicand 2

/-- The optimized rational square root rounds the exact real square root once. -/
theorem toReal_sqrtRat_eq_roundAt (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign : Bool) (radicand : Rat) (hrad : 0 ≤ radicand)
    (hfinite : isFinite (sqrtRat fmt sign radicand) = true) :
    toReal (sqrtRat fmt sign radicand) =
      roundAt fmt (if sign then -Real.sqrt (radicand : ℝ) else Real.sqrt (radicand : ℝ)) := by
  rw [sqrtRat_eq_root fmt sign radicand hrad] at hfinite ⊢
  exact toReal_root_two_eq_roundAt_sqrt fmt hfmt sign radicand hrad hfinite

/-- Selecting the square-root specialization preserves the complete general-root result. -/
theorem rootWithSqrt_eq_root (fmt : FloatFormat) (sign : Bool) (radicand : Rat)
    (degree : Nat) (_hrad : 0 ≤ radicand) :
    rootWithSqrt fmt sign radicand degree = root fmt sign radicand degree := by
  exact rootRat_eq_root fmt sign radicand degree

end FloatLib.Floats.Formats.BinaryInterchange.Model.AlgebraicRounding
