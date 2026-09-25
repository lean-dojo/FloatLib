/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Bounds
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Finiteness
public import FloatLib.Floats.Formats.BinaryInterchange.Status.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.TotalOrder.Encoding
import FloatLib.Floats.Formats.BinaryInterchange.Analysis.DyadicOrder
import FloatLib.Numerics.Bitwise

/-!
# Rounding an exactly representable dyadic is the identity

For a descriptor with `fmt.isIEEE = true`, a dyadic `m * 2^e` whose significand fits in the
precision, whose exponent is at least the minimum subnormal exponent, and whose magnitude is at
most the largest finite value is exactly representable. Rounding it in any of the four IEEE
directions therefore returns a finite value with exactly the same real denotation.

`roundDyadicWithRounding_of_representable` is the statement used by IEEE `remainder` (whose exact
result is always representable) and by `roundToIntegral` (whose rounded integer is always
representable for every IEEE interchange format). The finite decoded value of any word satisfies
the three hypotheses; see `toDyadic?_significand_lt` and `minSubnormalExponent_le_toDyadic?`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq

section

/-! ## Bounds satisfied by every decoded finite value -/

/--
The decoded dyadic of a word has a significand below `2^(fracWidth + 1)` and an exponent no smaller
than the minimum subnormal exponent. These bounds describe the format's precision and exponent grid.
-/
theorem toDyadic?_significand_lt_and_minSubnormalExponent_le
    {fmt : FloatFormat} (x : Model fmt) {d : Numerics.Dyadic}
    (hd : toDyadic? x = some d) :
    d.significand < 2 ^ (fmt.fracWidth + 1) ∧
      fmt.minSubnormalExponent ≤ d.exponent := by
  have hfin : isFinite x = true := isFinite_eq_true_of_toDyadic?_some hd
  have hdecode := toDyadic?_ofFields_of_isFinite fmt (signBit x) (expField x) (fracField x)
    (by simpa [← pow2_eq_two_pow] using expField_lt_pow2 x)
    (by simpa [← pow2_eq_two_pow] using fracField_lt_pow2 x)
    (by simpa only [ofFields_signBit_expField_fracField] using hfin)
  rw [ofFields_signBit_expField_fracField, hd] at hdecode
  have hfrac := fracField_lt_pow2 x
  have hmin : fmt.minSubnormalExponent ≤ 0 := by
    have := fmt.exponentBias_pos
    simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
      Int.ofNat_eq_natCast]
    omega
  have hfracSucc : fracField x < 2 ^ (fmt.fracWidth + 1) :=
    hfrac.trans (Nat.pow_lt_pow_right (by decide) (by omega))
  by_cases he : expField x = 0
  · by_cases hf : fracField x = 0
    · simp only [he, hf, ite_true, Option.some.injEq] at hdecode
      rw [hdecode]
      exact ⟨Nat.two_pow_pos _, hmin⟩
    · simp only [he, hf, ite_true, ite_false, Option.some.injEq] at hdecode
      rw [hdecode]
      exact ⟨hfracSucc, le_rfl⟩
  · simp only [he, ite_false, Option.some.injEq] at hdecode
    rw [hdecode]
    refine ⟨?_, ?_⟩
    · simp only [pow2_eq_two_pow, pow_succ]
      omega
    · simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
        Int.ofNat_eq_natCast]
      omega

/-- The decoded significand of a word fits in the format's precision. -/
theorem toDyadic?_significand_lt
    {fmt : FloatFormat} (x : Model fmt) {d : Numerics.Dyadic}
    (hd : toDyadic? x = some d) :
    d.significand < 2 ^ (fmt.fracWidth + 1) :=
  (toDyadic?_significand_lt_and_minSubnormalExponent_le x hd).1

/-- The decoded exponent of a word is at least the minimum subnormal exponent. -/
theorem minSubnormalExponent_le_toDyadic?
    {fmt : FloatFormat} (x : Model fmt) {d : Numerics.Dyadic}
    (hd : toDyadic? x = some d) :
    fmt.minSubnormalExponent ≤ d.exponent :=
  (toDyadic?_significand_lt_and_minSubnormalExponent_le x hd).2

/-! ## Membership in the format grid -/

/--
A dyadic belongs to the gradual-underflow grid when its significand is `m * 2^k` with `m` below
`2^(fracWidth + 1)` and its exponent is at least the minimum subnormal exponent. The scaled form
is what `roundToIntegral` produces when the input already has a nonnegative exponent, so the
trailing zero bits must be allowed here. `Dyadic.genericFormat_of_significand_lt` is the unscaled
special case.
-/
theorem Dyadic.genericFormat_of_eq_mul_pow2
    (fmt : FloatFormat) (d : Numerics.Dyadic) (m k : Nat)
    (hsig : d.significand = m * 2 ^ k)
    (hm : m < 2 ^ (fmt.fracWidth + 1))
    (hexp : fmt.minSubnormalExponent ≤ d.exponent) :
    genericFormat Numerics.binaryRadix (fexpOf fmt) d.toReal := by
  have hprec : (0 : ℤ) < fmt.fracWidth + 1 := by positivity
  apply (generic_format_FLT_iff fmt.minSubnormalExponent (fmt.fracWidth + 1) hprec _).2
  refine ⟨hprec, ⟨if d.negative then -(m : Int) else m, d.exponent + k⟩, ?_, ?_,
    show fmt.minSubnormalExponent ≤ d.exponent + (k : Int) by omega⟩
  · cases hneg : d.negative <;>
      simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, hneg, hsig,
        Flocq.toReal, Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)] <;> ring
  · cases d.negative <;> simpa [Numerics.binaryRadix] using hm

/--
A dyadic whose significand fits in the precision and whose exponent is at least the minimum
subnormal exponent belongs to the descriptor's Flocq grid. No magnitude bound is needed because
the grid has no upper exponent limit.
-/
theorem Dyadic.genericFormat_of_significand_lt
    (fmt : FloatFormat) (d : Numerics.Dyadic)
    (hsig : d.significand < 2 ^ (fmt.fracWidth + 1))
    (hexp : fmt.minSubnormalExponent ≤ d.exponent) :
    genericFormat Numerics.binaryRadix (fexpOf fmt) d.toReal :=
  Dyadic.genericFormat_of_eq_mul_pow2 fmt d d.significand 0 (by simp) hsig hexp

/-- The exact value of the largest finite word, as a dyadic, denotes the same real. -/
theorem Dyadic.toReal_maxFiniteDyadic (fmt : FloatFormat) :
    (maxFiniteDyadic fmt).toReal = toReal (posMaxFinite fmt) := by
  rw [toReal_posMaxFinite]
  simp [maxFiniteDyadic, Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand,
    bpow, Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal]

/--
The leading binary exponent of a nonzero dyadic within the largest finite magnitude does not
exceed the largest normal exponent.
-/
theorem Dyadic.leadingExponent_le_maxNormalExponent
    (fmt : FloatFormat) (d : Numerics.Dyadic) (hm : d.significand ≠ 0)
    (hbound : |d.toReal| ≤ toReal (posMaxFinite fmt)) :
    (d.significand.log2 : Int) + d.exponent ≤ fmt.maxNormalExponent := by
  have hleading : pow2 d.significand.log2 ≤ d.significand := pow2_log2_le hm
  have hleadingReal : (pow2 d.significand.log2 : ℝ) ≤ d.significand := by
    exact_mod_cast hleading
  have hlower :
      bpow ((d.significand.log2 : Int) + d.exponent) ≤ |d.toReal| := by
    rw [Dyadic.abs_toReal, bpow_add, ← Int.ofNat_eq_natCast, bpow_ofNat]
    exact mul_le_mul_of_nonneg_right hleadingReal (bpow_nonneg _)
  have hpow :
      bpow ((d.significand.log2 : Int) + d.exponent) <
        bpow (fmt.maxNormalExponent + 1) :=
    hlower.trans_lt (hbound.trans_lt (toReal_posMaxFinite_lt_bpow fmt))
  have := (bpow_lt_bpow_iff Numerics.binaryRadix _ _).mp hpow
  omega

/-- Ceiling division of a multiple of `2^shift` by `2^shift` is exact. -/
theorem shiftRightCeilPow2_mul_pow2_of_le (m shift k : Nat) (hshift : shift ≤ k) :
    shiftRightCeilPow2 (m * 2 ^ k) shift = m * 2 ^ (k - shift) := by
  have hsplit : 2 ^ k = 2 ^ (k - shift) * 2 ^ shift := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hquotient : m * 2 ^ k / 2 ^ shift = m * 2 ^ (k - shift) := by
    rw [hsplit, ← Nat.mul_assoc]
    exact Nat.mul_div_cancel _ (Nat.two_pow_pos shift)
  unfold shiftRightCeilPow2
  by_cases hzero : shift = 0
  · subst hzero
    simp
  · have hexact : m * 2 ^ k - m * 2 ^ (k - shift) * 2 ^ shift = 0 := by
      rw [Nat.mul_assoc, ← hsplit]
      exact Nat.sub_self _
    have hright : Nat.shiftRight (m * 2 ^ k) shift = m * 2 ^ (k - shift) := by
      rw [← hquotient]
      exact Nat.shiftRight_eq_div_pow _ _
    have hleft :
        Nat.shiftLeft (m * 2 ^ (k - shift)) shift = m * 2 ^ (k - shift) * 2 ^ shift :=
      Nat.shiftLeft_eq _ _
    simp only [beq_iff_eq, hzero, ite_false]
    rw [hright, hleft, hexact]
    simp

/--
Normalizing a significand of the form `m * 2^k` with `m` in precision never carries into the next
binade: the shift discards only zero bits or the value already fits.
-/
theorem roundMantissaToLeadingBitUp_ne_pow2_succ_of_eq_mul_pow2
    (m k fracWidth : Nat) (hm : m ≠ 0)
    (hsig : m < 2 ^ (fracWidth + 1)) :
    roundMantissaToLeadingBitUp (m * 2 ^ k) fracWidth ≠ pow2 (fracWidth + 1) := by
  have hlogm : m.log2 ≤ fracWidth := by
    have := (Nat.log2_lt hm).2 hsig
    omega
  have hlog : (m * 2 ^ k).log2 = m.log2 + k := by
    rw [← Nat.shiftLeft_eq]
    exact Nat.log2_shiftLeft_of_ne_zero m k hm
  have hne : m * 2 ^ k ≠ 0 := Nat.mul_ne_zero hm (Nat.two_pow_pos k).ne'
  unfold roundMantissaToLeadingBitUp
  rw [hlog]
  by_cases hle : fracWidth ≤ m.log2 + k
  · rw [ite_eq_left hle, shiftRightCeilPow2_mul_pow2_of_le m (m.log2 + k - fracWidth) k (by omega)]
    have hupper : m < 2 ^ (m.log2 + 1) := Nat.lt_log2_self
    have hmul :
        m * 2 ^ (k - (m.log2 + k - fracWidth)) <
          2 ^ (m.log2 + 1) * 2 ^ (k - (m.log2 + k - fracWidth)) :=
      Nat.mul_lt_mul_of_pos_right hupper (Nat.two_pow_pos _)
    rw [← Nat.pow_add] at hmul
    have hexp : m.log2 + 1 + (k - (m.log2 + k - fracWidth)) = fracWidth + 1 := by
      omega
    rw [hexp] at hmul
    rw [pow2_eq_two_pow]
    exact Nat.ne_of_lt hmul
  · rw [ite_eq_right hle, Nat.shiftLeft_eq', Nat.shiftLeft_eq, pow2_eq_two_pow]
    have hupper : m * 2 ^ k < 2 ^ (m.log2 + k + 1) := by
      rw [← hlog]
      exact Nat.lt_log2_self
    have hmul :
        m * 2 ^ k * 2 ^ (fracWidth - (m.log2 + k)) <
          2 ^ (m.log2 + k + 1) * 2 ^ (fracWidth - (m.log2 + k)) :=
      Nat.mul_lt_mul_of_pos_right hupper (Nat.two_pow_pos _)
    rw [← Nat.pow_add] at hmul
    have hexp : m.log2 + k + 1 + (fracWidth - (m.log2 + k)) = fracWidth + 1 := by
      omega
    rw [hexp] at hmul
    exact Nat.ne_of_lt hmul

/-- Normalizing a significand that already fits in the precision never carries. -/
theorem roundMantissaToLeadingBitUp_ne_pow2_succ_of_lt
    (mantissa fracWidth : Nat) (hm : mantissa ≠ 0)
    (hsig : mantissa < 2 ^ (fracWidth + 1)) :
    roundMantissaToLeadingBitUp mantissa fracWidth ≠ pow2 (fracWidth + 1) := by
  have := roundMantissaToLeadingBitUp_ne_pow2_succ_of_eq_mul_pow2 mantissa 0 fracWidth hm hsig
  simpa using this

/-! ## Exact rounding, one direction at a time -/

/--
Nearest-even rounding of a representable dyadic returns a finite word with the same real value.
-/
theorem roundDyadic_of_representable
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (d : Numerics.Dyadic) (m k : Nat)
    (hsig : d.significand = m * 2 ^ k)
    (hm : m < 2 ^ (fmt.fracWidth + 1))
    (hexp : fmt.minSubnormalExponent ≤ d.exponent)
    (hbound : |d.toReal| ≤ toReal (posMaxFinite fmt)) :
    isFinite (roundDyadic fmt d) = true ∧ toReal (roundDyadic fmt d) = d.toReal := by
  have hfinite := isFinite_roundDyadic_of_isIEEE_of_abs_toReal_le_posMaxFinite fmt hfmt d hbound
  refine ⟨hfinite, ?_⟩
  rw [toReal_roundDyadic_eq_roundAt fmt hfmt d hfinite]
  exact round_preserves_generic nearestEven d.toReal
    (Dyadic.genericFormat_of_eq_mul_pow2 fmt d m k hsig hm hexp)

/-- Downward rounding of a representable positive magnitude is exact and finite. -/
theorem roundDyadicPosDown_of_representable
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (m k : Nat) (exponent : Int)
    (hm0 : m ≠ 0)
    (hm : m < 2 ^ (fmt.fracWidth + 1))
    (hexp : fmt.minSubnormalExponent ≤ exponent)
    (hmax : ((m * 2 ^ k).log2 : Int) + exponent ≤ fmt.maxNormalExponent) :
    isFinite (roundDyadicPosDown fmt (m * 2 ^ k) exponent) = true ∧
      toReal (roundDyadicPosDown fmt (m * 2 ^ k) exponent) =
        ((m * 2 ^ k : Nat) : ℝ) * bpow exponent := by
  have hne : m * 2 ^ k ≠ 0 := Nat.mul_ne_zero hm0 (Nat.two_pow_pos k).ne'
  refine ⟨isFinite_roundDyadicPosDown fmt _ exponent hfmt, ?_⟩
  rw [toReal_roundDyadicPosDown_eq_roundAt_of_le_max fmt _ exponent hfmt hne hmax]
  have hgeneric :=
    Dyadic.genericFormat_of_eq_mul_pow2 fmt ⟨false, m * 2 ^ k, exponent⟩ m k rfl hm hexp
  simpa [roundAtDown, Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand,
    bpow, Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal] using
    round_preserves_generic floorRound _ hgeneric

/-- Upward rounding of a representable positive magnitude is exact and finite. -/
theorem roundDyadicPosUp_of_representable
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (m k : Nat) (exponent : Int)
    (hm0 : m ≠ 0)
    (hm : m < 2 ^ (fmt.fracWidth + 1))
    (hexp : fmt.minSubnormalExponent ≤ exponent)
    (hmax : ((m * 2 ^ k).log2 : Int) + exponent ≤ fmt.maxNormalExponent) :
    isFinite (roundDyadicPosUp fmt (m * 2 ^ k) exponent) = true ∧
      toReal (roundDyadicPosUp fmt (m * 2 ^ k) exponent) =
        ((m * 2 ^ k : Nat) : ℝ) * bpow exponent := by
  have hne : m * 2 ^ k ≠ 0 := Nat.mul_ne_zero hm0 (Nat.two_pow_pos k).ne'
  obtain ⟨hfinite, hround⟩ :=
    roundDyadicPosUp_finite_roundAt_of_le_max_of_no_carry fmt _ exponent hfmt hne hmax
      (roundMantissaToLeadingBitUp_ne_pow2_succ_of_eq_mul_pow2 m k fmt.fracWidth hm0 hm)
  refine ⟨hfinite, ?_⟩
  rw [hround]
  have hgeneric :=
    Dyadic.genericFormat_of_eq_mul_pow2 fmt ⟨false, m * 2 ^ k, exponent⟩ m k rfl hm hexp
  simpa [roundAtUp, Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand,
    bpow, Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal] using
    round_preserves_generic ceilRound _ hgeneric

/-- Real value of a dyadic in terms of its sign and magnitude. -/
private theorem Dyadic.toReal_eq_signed_magnitude (d : Numerics.Dyadic) :
    d.toReal =
      if d.negative then -((d.significand : ℝ) * bpow d.exponent)
      else (d.significand : ℝ) * bpow d.exponent := by
  cases hneg : d.negative <;>
    simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, hneg,
      bpow, Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal]

/--
Every IEEE rounding direction fixes an exactly representable dyadic: the result is finite and its
real value is the dyadic's own value. The significand may carry trailing zero bits beyond the
precision, as `m * 2^k`.
-/
theorem roundDyadicWithRounding_of_eq_mul_pow2
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (mode : IEEERoundingMode)
    (d : Numerics.Dyadic) (m k : Nat)
    (hsig : d.significand = m * 2 ^ k)
    (hm : m < 2 ^ (fmt.fracWidth + 1))
    (hexp : fmt.minSubnormalExponent ≤ d.exponent)
    (hbound : |d.toReal| ≤ toReal (posMaxFinite fmt)) :
    isFinite (roundDyadicWithRounding fmt mode d) = true ∧
      toReal (roundDyadicWithRounding fmt mode d) = d.toReal := by
  cases mode with
  | nearestEven =>
      exact roundDyadic_of_representable fmt hfmt d m k hsig hm hexp hbound
  | towardZero =>
      by_cases hzero : d.significand = 0
      · have hreal : d.toReal = 0 := by
          simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, hzero]
        simp only [roundDyadicWithRounding, roundDyadicTowardZero, hzero, beq_self_eq_true,
          ite_true]
        exact ⟨isFinite_eq_true_of_isZero_eq_true _ (isZero_zero fmt d.negative),
          by rw [toReal_zero, hreal]⟩
      · have hm0 : m ≠ 0 := by
          intro hm0
          exact hzero (by simp [hsig, hm0])
        have hmax := Dyadic.leadingExponent_le_maxNormalExponent fmt d hzero hbound
        rw [hsig] at hmax
        have hpos := roundDyadicPosDown_of_representable fmt hfmt m k d.exponent hm0 hm hexp hmax
        simp only [roundDyadicWithRounding, roundDyadicTowardZero, hzero, beq_iff_eq, ite_false]
        rw [Dyadic.toReal_eq_signed_magnitude, hsig]
        cases hneg : d.negative
        · simpa [roundDyadicPosDown] using hpos
        · simp only [ite_true]
          rw [roundDyadicMagnitudeDown_true_eq_neg_false fmt _ _ (by simp [hfmt])]
          refine ⟨by simpa [roundDyadicPosDown] using hpos.1, ?_⟩
          rw [toReal_neg _ (by simpa [roundDyadicPosDown] using hpos.1)]
          simpa [roundDyadicPosDown] using congrArg Neg.neg hpos.2
  | towardPositiveInfinity =>
      by_cases hzero : d.significand = 0
      · have hreal : d.toReal = 0 := by
          simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, hzero]
        simp only [roundDyadicWithRounding, roundDyadicUp, hzero, beq_self_eq_true, ite_true]
        exact ⟨isFinite_eq_true_of_isZero_eq_true _ (isZero_zero fmt d.negative),
          by rw [toReal_zero, hreal]⟩
      · have hm0 : m ≠ 0 := by
          intro hm0
          exact hzero (by simp [hsig, hm0])
        have hmax := Dyadic.leadingExponent_le_maxNormalExponent fmt d hzero hbound
        rw [hsig] at hmax
        simp only [roundDyadicWithRounding, roundDyadicUp, hzero, beq_iff_eq, ite_false]
        rw [Dyadic.toReal_eq_signed_magnitude, hsig]
        cases hneg : d.negative
        · have hpos := roundDyadicPosUp_of_representable fmt hfmt m k d.exponent hm0 hm hexp hmax
          simpa [roundDyadicPosUp] using hpos
        · have hpos :=
            roundDyadicPosDown_of_representable fmt hfmt m k d.exponent hm0 hm hexp hmax
          simp only [ite_true]
          rw [roundDyadicMagnitudeDown_true_eq_neg_false fmt _ _ (by simp [hfmt])]
          refine ⟨by simpa [roundDyadicPosDown] using hpos.1, ?_⟩
          rw [toReal_neg _ (by simpa [roundDyadicPosDown] using hpos.1)]
          simpa [roundDyadicPosDown] using congrArg Neg.neg hpos.2
  | towardNegativeInfinity =>
      by_cases hzero : d.significand = 0
      · have hreal : d.toReal = 0 := by
          simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, hzero]
        simp only [roundDyadicWithRounding, roundDyadicDown, hzero, beq_self_eq_true, ite_true]
        exact ⟨isFinite_eq_true_of_isZero_eq_true _ (isZero_zero fmt d.negative),
          by rw [toReal_zero, hreal]⟩
      · have hm0 : m ≠ 0 := by
          intro hm0
          exact hzero (by simp [hsig, hm0])
        have hmax := Dyadic.leadingExponent_le_maxNormalExponent fmt d hzero hbound
        rw [hsig] at hmax
        simp only [roundDyadicWithRounding, roundDyadicDown, hzero, beq_iff_eq, ite_false]
        rw [Dyadic.toReal_eq_signed_magnitude, hsig]
        cases hneg : d.negative
        · have hpos :=
            roundDyadicPosDown_of_representable fmt hfmt m k d.exponent hm0 hm hexp hmax
          simpa [roundDyadicPosDown] using hpos
        · have hpos := roundDyadicPosUp_of_representable fmt hfmt m k d.exponent hm0 hm hexp hmax
          simp only [ite_true]
          rw [roundDyadicMagnitudeUp_true_eq_neg_false fmt _ _ (by simp [hfmt])
            (nativeOverflow_true_eq_neg_false_of_isIEEE fmt hfmt)]
          refine ⟨by simpa [roundDyadicPosUp] using hpos.1, ?_⟩
          rw [toReal_neg _ (by simpa [roundDyadicPosUp] using hpos.1)]
          simpa [roundDyadicPosUp] using congrArg Neg.neg hpos.2

/--
Every IEEE rounding direction fixes an exactly representable dyadic whose significand fits in the
precision: the result is finite and its real value is the dyadic's own value.
-/
theorem roundDyadicWithRounding_of_representable
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (mode : IEEERoundingMode)
    (d : Numerics.Dyadic)
    (hsig : d.significand < 2 ^ (fmt.fracWidth + 1))
    (hexp : fmt.minSubnormalExponent ≤ d.exponent)
    (hbound : |d.toReal| ≤ toReal (posMaxFinite fmt)) :
    isFinite (roundDyadicWithRounding fmt mode d) = true ∧
      toReal (roundDyadicWithRounding fmt mode d) = d.toReal :=
  roundDyadicWithRounding_of_eq_mul_pow2 fmt hfmt mode d d.significand 0 (by simp) hsig hexp
    hbound

/-! ## Overflow classification of representable dyadics -/

/-- The overflow midpoint lies strictly above the largest finite value. -/
private theorem toReal_posMaxFinite_lt_overflowMidpoint (fmt : FloatFormat) :
    toReal (posMaxFinite fmt) < (overflowMidpoint fmt).toReal := by
  rw [← Dyadic.toReal_maxFiniteDyadic]
  simp only [overflowMidpoint, maxFiniteDyadic, Numerics.Dyadic.toReal_mk_false]
  set M : ℝ := ((pow2 fmt.fracWidth + fmt.maxFiniteFracField : Nat) : ℝ) with hM
  set E : Int := fmt.maxNormalExponent - Int.ofNat fmt.fracWidth with hE
  have hsplit : bpow E = 2 * bpow (E - 1) := by
    rw [show E = 1 + (E - 1) by ring, bpow_add, bpow_one]
    ring_nf
  have hpos : 0 < bpow (E - 1) := bpow_pos _
  have hcast :
      ((2 * (pow2 fmt.fracWidth + fmt.maxFiniteFracField) + 1 : Nat) : ℝ) = 2 * M + 1 := by
    rw [hM]
    push_cast
    ring
  change M * bpow E < ((2 * (pow2 fmt.fracWidth + fmt.maxFiniteFracField) + 1 : Nat) : ℝ) *
    bpow (E - 1)
  rw [hcast, hsplit]
  nlinarith

/-- The overflow limit lies strictly above the largest finite value. -/
private theorem toReal_posMaxFinite_lt_overflowLimit (fmt : FloatFormat) :
    toReal (posMaxFinite fmt) < (overflowLimit fmt).toReal := by
  rw [← Dyadic.toReal_maxFiniteDyadic]
  simp only [overflowLimit, maxFiniteDyadic, Numerics.Dyadic.toReal_mk_false]
  set M : ℝ := ((pow2 fmt.fracWidth + fmt.maxFiniteFracField : Nat) : ℝ) with hM
  set E : Int := fmt.maxNormalExponent - Int.ofNat fmt.fracWidth with hE
  have hpos : 0 < bpow E := bpow_pos _
  have hcast :
      ((pow2 fmt.fracWidth + fmt.maxFiniteFracField + 1 : Nat) : ℝ) = M + 1 := by
    rw [hM]
    push_cast
    ring
  change M * bpow E < ((pow2 fmt.fracWidth + fmt.maxFiniteFracField + 1 : Nat) : ℝ) * bpow E
  rw [hcast]
  nlinarith

/-- The magnitude of a dyadic denotes the absolute value of its real value. -/
private theorem Dyadic.toReal_magnitude (d : Numerics.Dyadic) :
    ({ d with negative := false } : Numerics.Dyadic).toReal = |d.toReal| := by
  rw [Dyadic.abs_toReal]
  simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand,
    Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal]

/--
No rounding direction classifies a dyadic within the largest finite magnitude as overflowing.
Together with `roundDyadicWithRounding_of_representable`, this clears the `overflow` indicator of
`dyadicRoundingStatus` for exactly representable results.
-/
theorem dyadicRoundingOverflows_eq_false_of_abs_toReal_le_posMaxFinite
    (fmt : FloatFormat) (mode : IEEERoundingMode) (d : Numerics.Dyadic)
    (hbound : |d.toReal| ≤ toReal (posMaxFinite fmt)) :
    dyadicRoundingOverflows fmt mode d = false := by
  have hmagnitude :
      dyadicMagnitudeOverflows fmt d = false := by
    simp only [dyadicMagnitudeOverflows, beq_eq_false_iff_ne, ne_eq]
    rw [cmpDyadic_gt_iff, Dyadic.toReal_magnitude, Dyadic.toReal_maxFiniteDyadic]
    exact not_lt.mpr hbound
  have htruncation :
      dyadicTruncationOverflows fmt d = false := by
    simp only [dyadicTruncationOverflows, bne_eq_false_iff_eq]
    rw [cmpDyadic_lt_iff, Dyadic.toReal_magnitude]
    exact hbound.trans_lt (toReal_posMaxFinite_lt_overflowLimit fmt)
  have hnearest :
      dyadicNearestEvenOverflows fmt d = false := by
    have hlt :
        cmpDyadic { d with negative := false } (overflowMidpoint fmt) = .lt := by
      rw [cmpDyadic_lt_iff, Dyadic.toReal_magnitude]
      exact hbound.trans_lt (toReal_posMaxFinite_lt_overflowMidpoint fmt)
    simp [dyadicNearestEvenOverflows, hlt]
  cases mode <;>
    simp [dyadicRoundingOverflows, hmagnitude, htruncation, hnearest]

end

/-! ## Exact reconstruction of finite representations -/

/-- A nonzero decoded dyadic already uses the format's canonical exponent. -/
theorem cexp_toDyadic? {fmt : FloatFormat} {x : Model fmt} {d : Numerics.Dyadic}
    (hd : toDyadic? x = some d) (hm : d.significand ≠ 0) :
    cexp Numerics.binaryRadix (fexpOf fmt) d.toReal = d.exponent := by
  rw [cexp, Dyadic.magnitude_toReal d hm]
  have hfin := isFinite_eq_true_of_toDyadic?_some hd
  have hshape := toDyadic?_ofFields_of_isFinite fmt (signBit x) (expField x) (fracField x)
    (expField_lt_pow2 x) (fracField_lt_pow2 x)
    (by simpa only [ofFields_signBit_expField_fracField] using hfin)
  rw [ofFields_signBit_expField_fracField, hd] at hshape
  have hf := fracField_lt_pow2 x
  by_cases he : expField x = 0
  · by_cases hz : fracField x = 0
    · simp only [he, hz, ite_true, Option.some.injEq] at hshape
      simp [hshape] at hm
    · simp only [he, hz, ite_true, ite_false, Option.some.injEq] at hshape
      rw [hshape]
      have hl : (fracField x).log2 < fmt.fracWidth := by
        rw [Nat.log2_eq_log_two]
        exact (Nat.log_lt_iff_lt_pow (by decide) hz).mpr hf
      simp only [fexpOf, fltExp, Int.ofNat_eq_natCast]
      exact max_eq_right (by omega)
  · simp only [he, ite_false, Option.some.injEq] at hshape
    rw [hshape]
    have hm' : pow2 fmt.fracWidth + fracField x ≠ 0 := by
      have hp : 0 < pow2 fmt.fracWidth := by simp [pow2_eq_two_pow]
      omega
    have hl : (pow2 fmt.fracWidth + fracField x).log2 = fmt.fracWidth := by
      rw [Nat.log2_eq_log_two]
      apply (Nat.log_eq_iff (Or.inr ⟨by decide, hm'⟩)).mpr
      simp only [pow2_eq_two_pow, pow_succ]
      omega
    simp only [hl, fexpOf, fltExp, FloatFormat.minSubnormalExponent,
      FloatFormat.minNormalExponent, Int.ofNat_eq_natCast]
    rw [max_eq_left (by omega)]
    omega

/-- Equal nonzero numerical values have the same canonical decoded exponent. -/
theorem toDyadic?_exponent_eq_of_toReal_eq {fmt : FloatFormat} {x y : Model fmt}
    {dx dy : Numerics.Dyadic} (hx : toDyadic? x = some dx) (hy : toDyadic? y = some dy)
    (hx0 : dx.significand ≠ 0) (hy0 : dy.significand ≠ 0)
    (hvalue : toReal x = toReal y) : dx.exponent = dy.exponent := by
  rw [← cexp_toDyadic? hx hx0, ← cexp_toDyadic? hy hy0]
  congr 1
  simpa only [toReal_eq, hx, hy] using hvalue

/-- A dyadic denotes zero exactly when its unsigned coefficient is zero. -/
theorem Dyadic.toReal_eq_zero_iff (d : Numerics.Dyadic) :
    d.toReal = 0 ↔ d.significand = 0 := by
  have hp := zpow_ne_zero d.exponent (by norm_num : (2 : ℝ) ≠ 0)
  cases hs : d.negative <;>
    simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, hs, hp]

/-- Equal nonzero finite real values determine the complete binary word. -/
theorem eq_of_toReal_eq_of_nonzero {fmt : FloatFormat} {x y : Model fmt}
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hvalue : toReal x = toReal y) (hzero : toReal x ≠ 0) : x = y := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  have hv : dx.toReal = dy.toReal := by simpa [toReal_eq, hdx, hdy] using hvalue
  have hx0 : dx.significand ≠ 0 := by
    apply (Dyadic.toReal_eq_zero_iff dx).not.mp
    simpa [toReal_eq, hdx] using hzero
  have hy0 : dy.significand ≠ 0 := by
    apply (Dyadic.toReal_eq_zero_iff dy).not.mp
    rw [← hv]
    exact (Dyadic.toReal_eq_zero_iff dx).not.mpr hx0
  have he := toDyadic?_exponent_eq_of_toReal_eq hdx hdy hx0 hy0 hvalue
  have hm : dx.signedSignificand = dy.signedSignificand := by
    have hmReal : (dx.signedSignificand : ℝ) = (dy.signedSignificand : ℝ) := by
      apply mul_right_cancel₀ (zpow_ne_zero dy.exponent (by norm_num : (2 : ℝ) ≠ 0))
      simpa [Numerics.Dyadic.toReal, he] using hv
    exact_mod_cast hmReal
  have hcoeff : dx.significand = dy.significand := by
    have hn := congrArg Int.natAbs hm
    cases hs : dx.negative <;> cases ht : dy.negative <;>
      simpa [Numerics.Dyadic.signedSignificand, hs, ht] using hn
  have hsign : dx.negative = dy.negative := by
    cases hs : dx.negative <;> cases ht : dy.negative <;>
      simp_all [Numerics.Dyadic.signedSignificand]
  have hd : dx = dy := by
    cases dx
    cases dy
    simp_all
  exact eq_of_toDyadic?_eq_some hdx (hdy.trans (congrArg some hd.symm))

/-- In a conventional IEEE format, rounding a decoded nonzero value restores its word. -/
theorem roundDyadicWithRounding_toDyadic?_of_nonzero {fmt : FloatFormat}
    (hfmt : fmt.isIEEE = true) (mode : IEEERoundingMode) {x : Model fmt}
    {d : Numerics.Dyadic} (hd : toDyadic? x = some d) (hm : d.significand ≠ 0) :
    roundDyadicWithRounding fmt mode d = x := by
  have hfin := isFinite_eq_true_of_toDyadic?_some hd
  have hv : toReal x = d.toReal := by simp [toReal_eq, hd]
  have hb : |d.toReal| ≤ toReal (posMaxFinite fmt) := by
    rw [← hv]
    exact abs_toReal_le_posMaxFinite_of_isIEEE_of_isFinite x hfmt hfin
  have hr := roundDyadicWithRounding_of_representable fmt hfmt mode d
    (toDyadic?_significand_lt x hd) (minSubnormalExponent_le_toDyadic? x hd) hb
  exact eq_of_toReal_eq_of_nonzero hr.1 hfin (hr.2.trans hv.symm)
    (by rw [hr.2]; exact (Dyadic.toReal_eq_zero_iff d).not.mpr hm)

/-- In a conventional IEEE format, rounding an exact zero preserves its sign. -/
theorem roundDyadicWithRounding_zero (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (mode : IEEERoundingMode) (negative : Bool) (exponent : Int) :
    roundDyadicWithRounding fmt mode ⟨negative, 0, exponent⟩ = zero fmt negative := by
  cases negative <;> cases mode <;>
    simp [roundDyadicWithRounding, roundDyadicTowardZero, roundDyadicUp, roundDyadicDown,
      roundDyadic, hfmt, ieeeRoundDyadic, zero, modelSign,
      posZero_eq_ofModel_zero, negZero_eq_ofModel_zero]

/-- In a conventional IEEE format, rounding a decoded finite dyadic restores its complete word. -/
theorem roundDyadicWithRounding_toDyadic? {fmt : FloatFormat}
    (hfmt : fmt.isIEEE = true) (mode : IEEERoundingMode) {x : Model fmt}
    {d : Numerics.Dyadic} (hd : toDyadic? x = some d) :
    roundDyadicWithRounding fmt mode d = x := by
  by_cases hm : d.significand = 0
  · have hz := isZero_eq_true_of_toDyadic?_some_of_mant_eq_zero hd hm
    have hdx := toDyadic?_eq_zero_of_isZero_eq_true x hz
    have hd' := Option.some.inj (hd.symm.trans hdx)
    rw [hd', roundDyadicWithRounding_zero fmt hfmt]
    apply eq_of_toDyadic?_eq_some (d := ⟨signBit x, 0, 0⟩) _ hdx
    simp [toDyadic?_zero, signBit_zero,
      FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt hfmt]
  · exact roundDyadicWithRounding_toDyadic?_of_nonzero hfmt mode hd hm


end Model
end FloatLib.Floats.Formats.BinaryInterchange
