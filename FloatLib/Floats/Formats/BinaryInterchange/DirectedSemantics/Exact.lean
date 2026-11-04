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

Take a descriptor with `fmt.isIEEE = true` and a dyadic `m * 2^e` whose significand fits in the
precision, whose exponent is at least the minimum subnormal exponent and whose magnitude is at
most the largest finite value. That dyadic is exactly representable, so rounding it in any of the
six directions returns a finite value with the same real denotation. Such a value is never a grid
tie either (`dyadicIsGridTie_eq_false_of_eq_mul_pow2`).

IEEE `remainder` and `roundToIntegral` both use `Internal.Directed.roundDyadic_of_representable`.
The exact result of `remainder` is always representable, and so is the rounded integer of
`roundToIntegral` in every IEEE interchange format. Any finite decoded value of a word meets all
three hypotheses. Its precision and exponent bounds come from `toDyadic?_significand_lt` and
`minSubnormalExponent_le_toDyadic?`, and its magnitude bound from
`abs_toReal_le_posMaxFinite_of_toDyadic?_some`, which holds in every encoding.
`Internal.Directed.roundDyadic_toDyadic?` puts them together: in an IEEE format, rounding a
decoded word in any direction returns that word.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq

section

/-! ## Bounds satisfied by every decoded finite value -/

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

/-- A finite nonzero value is at least the least subnormal `2 ^ minSubnormalExponent` in size. -/
theorem bpow_minSubnormalExponent_le_abs_toReal {fmt : FloatFormat} {x : Model fmt}
    (hfinite : isFinite x = true) (hzero : toReal x ≠ 0) :
    bpow fmt.minSubnormalExponent ≤ |toReal x| := by
  obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite hfinite
  have hreal : toReal x = d.toReal := by rw [toReal_eq, hd]
  rw [hreal] at hzero ⊢
  have hsignificand : d.significand ≠ 0 := fun hsignificand => hzero (by
    simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, hsignificand])
  have hone : (1 : ℝ) ≤ d.significand := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hsignificand
  rw [Dyadic.abs_toReal]
  calc bpow fmt.minSubnormalExponent
      ≤ bpow d.exponent := bpow_le_bpow_of_le (minSubnormalExponent_le_toDyadic? x hd)
    _ = 1 * bpow d.exponent := (one_mul _).symm
    _ ≤ d.significand * bpow d.exponent := mul_le_mul_of_nonneg_right hone (bpow_nonneg _)

/--
Every decoded finite value lies strictly below `2^(maxNormalExponent + 1)` in magnitude, whatever
the descriptor's encoding.
-/
theorem abs_toReal_lt_bpow_of_toDyadic?_some
    {fmt : FloatFormat} (x : Model fmt) {d : Numerics.Dyadic}
    (hd : toDyadic? x = some d) :
    |d.toReal| < bpow (fmt.maxNormalExponent + 1) := by
  have hfin : isFinite x = true := isFinite_eq_true_of_toDyadic?_some hd
  have hexponentLe := expField_le_maxFiniteExpField_of_isFinite x hfin
  have hfractionLt := fracField_lt_pow2 x
  have hmaxPositive := fmt.maxFiniteExpField_pos
  -- A significand below `2^k` scaled by `2^e` stays below `2^(k + e)`.
  have hbound : ∀ (k : Nat), d.significand < 2 ^ k →
      (k : Int) + d.exponent ≤ fmt.maxNormalExponent + 1 →
      |d.toReal| < bpow (fmt.maxNormalExponent + 1) := by
    intro k hsignificand hexponent
    rw [Dyadic.abs_toReal]
    exact natCast_mul_bpow_lt_bpow hsignificand hexponent
  rcases toDyadic?_some_cases hd with ⟨hs, _⟩ | ⟨_, _, hs, he⟩ | ⟨_, hs, he⟩
  · rw [Dyadic.abs_toReal, hs]
    simpa using bpow_pos (fmt.maxNormalExponent + 1)
  · apply hbound fmt.fracWidth (hs ▸ hfractionLt)
    rw [he]
    simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
      FloatFormat.maxNormalExponent, Int.ofNat_eq_natCast]
    omega
  · apply hbound (fmt.fracWidth + 1)
    · rw [hs]
      simp only [pow2_eq_two_pow, pow_succ]
      omega
    · rw [he]
      simp only [FloatFormat.maxNormalExponent, Int.ofNat_eq_natCast]
      omega

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

/-- Ceiling division of a multiple of `2^shift` by `2^shift` is exact. -/
theorem shiftRightCeil_mul_pow2_of_le (m shift k : Nat) (hshift : shift ≤ k) :
    Numerics.shiftRightCeil (m * 2 ^ k) shift = m * 2 ^ (k - shift) := by
  have hsplit : 2 ^ k = 2 ^ (k - shift) * 2 ^ shift := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hquotient : m * 2 ^ k / 2 ^ shift = m * 2 ^ (k - shift) := by
    rw [hsplit, ← Nat.mul_assoc]
    exact Nat.mul_div_cancel _ (Nat.two_pow_pos shift)
  unfold Numerics.shiftRightCeil
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
    (m k fracWidth : Nat)
    (hsig : m < 2 ^ (fracWidth + 1)) :
    roundMantissaToLeadingBitUp (m * 2 ^ k) fracWidth ≠ pow2 (fracWidth + 1) := by
  by_cases hm : m = 0
  · subst m
    simp [roundMantissaToLeadingBitUp, Numerics.shiftRightCeil, pow2_eq_two_pow,
      Nat.ne_of_lt (Nat.two_pow_pos (fracWidth + 1))]
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
  · rw [ite_eq_left hle, shiftRightCeil_mul_pow2_of_le m (m.log2 + k - fracWidth) k (by omega)]
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
    (mantissa fracWidth : Nat)
    (hsig : mantissa < 2 ^ (fracWidth + 1)) :
    roundMantissaToLeadingBitUp mantissa fracWidth ≠ pow2 (fracWidth + 1) := by
  have := roundMantissaToLeadingBitUp_ne_pow2_succ_of_eq_mul_pow2 mantissa 0 fracWidth hsig
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

/--
A representable dyadic is never a grid tie: every bit below its grid spacing is clear, so the
discarded bits are never one half of a unit.
-/
theorem dyadicIsGridTie_eq_false_of_eq_mul_pow2
    (fmt : FloatFormat) (d : Numerics.Dyadic) (m k : Nat)
    (hsig : d.significand = m * 2 ^ k)
    (hm : m < 2 ^ (fmt.fracWidth + 1))
    (hexp : fmt.minSubnormalExponent ≤ d.exponent) :
    dyadicIsGridTie fmt d = false := by
  by_cases hzero : d.significand = 0
  · rcases d with ⟨negative, significand, exponent⟩
    simp only at hzero
    subst hzero
    exact dyadicIsGridTie_zero fmt negative exponent
  have hlog : d.significand.log2 < fmt.fracWidth + 1 + k := by
    rw [Nat.log2_lt hzero, hsig, pow_add]
    exact Nat.mul_lt_mul_of_pos_right hm (Nat.two_pow_pos k)
  have hgrid : max fmt.minSubnormalExponent
      ((d.significand.log2 : Int) + d.exponent - fmt.fracWidth) ≤ d.exponent + k :=
    max_le (by omega) (by omega)
  unfold dyadicIsGridTie
  split
  · rfl
  · rename_i shift hshift
    rw [Int.negSucc_eq] at hshift
    have hle : shift + 1 ≤ k := by omega
    have hdvd : 2 ^ (shift + 1) ∣ d.significand := by
      rw [hsig]
      exact Dvd.dvd.mul_left (Nat.pow_dvd_pow 2 hle) m
    apply Bool.eq_false_of_not_eq_true
    intro htie
    rw [Numerics.shiftRightIsTie_eq_true_iff, Nat.mod_eq_zero_of_dvd hdvd] at htie
    have hpos := Nat.two_pow_pos (shift + 1 - 1)
    omega

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
  refine ⟨isFinite_roundDyadicPosDown fmt _ exponent, ?_⟩
  rw [toReal_roundDyadicPosDown_eq_roundAt_of_le_max fmt _ exponent hfmt hne hmax]
  have hgeneric :=
    Dyadic.genericFormat_of_eq_mul_pow2 fmt ⟨false, m * 2 ^ k, exponent⟩ m k rfl hm hexp
  simpa [roundAt, Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand,
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
      (roundMantissaToLeadingBitUp_ne_pow2_succ_of_eq_mul_pow2 m k fmt.fracWidth hm)
  refine ⟨hfinite, ?_⟩
  rw [hround]
  have hgeneric :=
    Dyadic.genericFormat_of_eq_mul_pow2 fmt ⟨false, m * 2 ^ k, exponent⟩ m k rfl hm hexp
  simpa [roundAt, Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand,
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
Downward magnitude rounding of a representable magnitude is exact and finite for either attached
sign. The negative case is the negation of the positive one.
-/
private theorem roundDyadicMagnitudeDown_of_representable
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (sign : Bool) (m k : Nat) (exponent : Int)
    (hm0 : m ≠ 0)
    (hm : m < 2 ^ (fmt.fracWidth + 1))
    (hexp : fmt.minSubnormalExponent ≤ exponent)
    (hmax : ((m * 2 ^ k).log2 : Int) + exponent ≤ fmt.maxNormalExponent) :
    isFinite (roundDyadicMagnitudeDown fmt sign (m * 2 ^ k) exponent) = true ∧
      toReal (roundDyadicMagnitudeDown fmt sign (m * 2 ^ k) exponent) =
        if sign then -(((m * 2 ^ k : Nat) : ℝ) * bpow exponent)
        else ((m * 2 ^ k : Nat) : ℝ) * bpow exponent := by
  have hpos := roundDyadicPosDown_of_representable fmt hfmt m k exponent hm0 hm hexp hmax
  cases sign
  · simpa [roundDyadicPosDown] using hpos
  · rw [roundDyadicMagnitudeDown_true_eq_neg_false fmt _ _]
    refine ⟨by simpa [roundDyadicPosDown] using hpos.1, ?_⟩
    rw [toReal_neg _ (by simpa [roundDyadicPosDown] using hpos.1)]
    simpa [roundDyadicPosDown] using congrArg Neg.neg hpos.2

/--
Upward magnitude rounding of a representable magnitude is exact and finite for either attached
sign. The negative case is the negation of the positive one.
-/
private theorem roundDyadicMagnitudeUp_of_representable
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (sign : Bool) (m k : Nat) (exponent : Int)
    (hm0 : m ≠ 0)
    (hm : m < 2 ^ (fmt.fracWidth + 1))
    (hexp : fmt.minSubnormalExponent ≤ exponent)
    (hmax : ((m * 2 ^ k).log2 : Int) + exponent ≤ fmt.maxNormalExponent) :
    isFinite (roundDyadicMagnitudeUp fmt sign (m * 2 ^ k) exponent) = true ∧
      toReal (roundDyadicMagnitudeUp fmt sign (m * 2 ^ k) exponent) =
        if sign then -(((m * 2 ^ k : Nat) : ℝ) * bpow exponent)
        else ((m * 2 ^ k : Nat) : ℝ) * bpow exponent := by
  have hpos := roundDyadicPosUp_of_representable fmt hfmt m k exponent hm0 hm hexp hmax
  cases sign
  · simpa [roundDyadicPosUp] using hpos
  · rw [roundDyadicMagnitudeUp_true_eq_neg_false fmt _ _ (by simp [hfmt])]
    refine ⟨by simpa [roundDyadicPosUp] using hpos.1, ?_⟩
    rw [toReal_neg _ (by simpa [roundDyadicPosUp] using hpos.1)]
    simpa [roundDyadicPosUp] using congrArg Neg.neg hpos.2

/--
Every rounding direction fixes a representable dyadic. The result is finite and has the dyadic's
own real value. The significand may carry trailing zero bits beyond the precision, as `m * 2^k`.
-/
theorem Internal.Directed.roundDyadic_of_eq_mul_pow2
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (mode : IEEERoundingMode)
    (d : Numerics.Dyadic) (m k : Nat)
    (hsig : d.significand = m * 2 ^ k)
    (hm : m < 2 ^ (fmt.fracWidth + 1))
    (hexp : fmt.minSubnormalExponent ≤ d.exponent)
    (hbound : |d.toReal| ≤ toReal (posMaxFinite fmt)) :
    isFinite (Internal.Directed.roundDyadic fmt mode d) = true ∧
      toReal (Internal.Directed.roundDyadic fmt mode d) = d.toReal := by
  -- The directed modes deliver the zero of the dyadic's own sign for a zero significand.
  have hzeroCase (hzero : d.significand = 0) :
      isFinite (zero fmt d.negative) = true ∧ toReal (zero fmt d.negative) = d.toReal :=
    ⟨isFinite_eq_true_of_isZero_eq_true _ (isZero_zero fmt d.negative), by
      rw [toReal_zero]
      simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, hzero]⟩
  -- A nonzero significand is a nonzero multiple `m * 2^k` within the overflow bound.
  have hnonzero (hzero : d.significand ≠ 0) :
      m ≠ 0 ∧ ((m * 2 ^ k).log2 : Int) + d.exponent ≤ fmt.maxNormalExponent :=
    ⟨fun hm0 => hzero (by simp [hsig, hm0]),
      hsig ▸ Dyadic.leadingExponent_le_maxNormalExponent fmt d hzero hbound⟩
  cases mode with
  | nearest =>
      exact roundDyadic_of_representable fmt hfmt d m k hsig hm hexp hbound
  | nearestAway =>
      have htie := dyadicIsGridTie_eq_false_of_eq_mul_pow2 fmt d m k hsig hm hexp
      simp only [Internal.Directed.roundDyadic, roundDyadicNearestAway, htie, Bool.false_eq_true,
        ite_false]
      exact roundDyadic_of_representable fmt hfmt d m k hsig hm hexp hbound
  | away =>
      by_cases hzero : d.significand = 0
      · simpa [Internal.Directed.roundDyadic, roundDyadicAway, hzero] using hzeroCase hzero
      · obtain ⟨hm0, hmax⟩ := hnonzero hzero
        simp only [Internal.Directed.roundDyadic, roundDyadicAway, hzero, beq_iff_eq, ite_false]
        rw [Dyadic.toReal_eq_signed_magnitude, hsig]
        exact roundDyadicMagnitudeUp_of_representable fmt hfmt _ m k _ hm0 hm hexp hmax
  | towardZero =>
      by_cases hzero : d.significand = 0
      · simpa [Internal.Directed.roundDyadic, roundDyadicTowardZero, hzero] using hzeroCase hzero
      · obtain ⟨hm0, hmax⟩ := hnonzero hzero
        simp only [Internal.Directed.roundDyadic, roundDyadicTowardZero, hzero, beq_iff_eq,
          ite_false]
        rw [Dyadic.toReal_eq_signed_magnitude, hsig]
        exact roundDyadicMagnitudeDown_of_representable fmt hfmt _ m k _ hm0 hm hexp hmax
  | up =>
      by_cases hzero : d.significand = 0
      · simpa [Internal.Directed.roundDyadic, roundDyadicUp, hzero] using hzeroCase hzero
      · obtain ⟨hm0, hmax⟩ := hnonzero hzero
        simp only [Internal.Directed.roundDyadic, roundDyadicUp, hzero, beq_iff_eq, ite_false]
        rw [Dyadic.toReal_eq_signed_magnitude, hsig]
        cases d.negative
        · exact roundDyadicMagnitudeUp_of_representable fmt hfmt false m k _ hm0 hm hexp hmax
        · exact roundDyadicMagnitudeDown_of_representable fmt hfmt true m k _ hm0 hm hexp hmax
  | down =>
      by_cases hzero : d.significand = 0
      · simpa [Internal.Directed.roundDyadic, roundDyadicDown, hzero] using hzeroCase hzero
      · obtain ⟨hm0, hmax⟩ := hnonzero hzero
        simp only [Internal.Directed.roundDyadic, roundDyadicDown, hzero, beq_iff_eq, ite_false]
        rw [Dyadic.toReal_eq_signed_magnitude, hsig]
        cases d.negative
        · exact roundDyadicMagnitudeDown_of_representable fmt hfmt false m k _ hm0 hm hexp hmax
        · exact roundDyadicMagnitudeUp_of_representable fmt hfmt true m k _ hm0 hm hexp hmax

/--
Every rounding direction fixes a representable dyadic whose significand fits in the precision.
The result is finite and has the dyadic's own real value.
-/
theorem Internal.Directed.roundDyadic_of_representable
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (mode : IEEERoundingMode)
    (d : Numerics.Dyadic)
    (hsig : d.significand < 2 ^ (fmt.fracWidth + 1))
    (hexp : fmt.minSubnormalExponent ≤ d.exponent)
    (hbound : |d.toReal| ≤ toReal (posMaxFinite fmt)) :
    isFinite (Internal.Directed.roundDyadic fmt mode d) = true ∧
      toReal (Internal.Directed.roundDyadic fmt mode d) = d.toReal :=
  Internal.Directed.roundDyadic_of_eq_mul_pow2 fmt hfmt mode d d.significand 0 (by simp) hsig hexp
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
Together with `Internal.Directed.roundDyadic_of_representable`, this clears the `overflow`
indicator of `dyadicRoundingStatus` for representable results.
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
  have hlt :
      cmpDyadic { d with negative := false } (overflowMidpoint fmt) = .lt := by
    rw [cmpDyadic_lt_iff, Dyadic.toReal_magnitude]
    exact hbound.trans_lt (toReal_posMaxFinite_lt_overflowMidpoint fmt)
  have hnearest :
      dyadicNearestEvenOverflows fmt d = false := by
    simp [dyadicNearestEvenOverflows, hlt]
  have hnearestAway :
      dyadicNearestAwayOverflows fmt d = false := by
    simp [dyadicNearestAwayOverflows, hlt]
  cases mode <;>
    simp [dyadicRoundingOverflows, hmagnitude, htruncation, hnearest, hnearestAway]

end

/-! ## Exact reconstruction of finite representations -/

/-- A nonzero decoded dyadic already uses the format's canonical exponent. -/
theorem cexp_toDyadic? {fmt : FloatFormat} {x : Model fmt} {d : Numerics.Dyadic}
    (hd : toDyadic? x = some d) (hm : d.significand ≠ 0) :
    cexp Numerics.binaryRadix (fexpOf fmt) d.toReal = d.exponent := by
  rw [cexp, Dyadic.magnitude_toReal d hm]
  rcases log2_significand_of_toDyadic?_some hd hm with ⟨-, hl, he⟩ | ⟨hfield, hl, he⟩
  · rw [he]
    simp only [fexpOf, fltExp, Int.ofNat_eq_natCast]
    exact max_eq_right (by omega)
  · rw [he]
    simp only [hl, fexpOf, fltExp, FloatFormat.minSubnormalExponent,
      FloatFormat.minNormalExponent, Int.ofNat_eq_natCast]
    rw [max_eq_left (by omega)]
    omega

/--
Equal nonzero numerical values have the same canonical decoded exponent. The second significand is
nonzero because it denotes the same nonzero value.
-/
theorem toDyadic?_exponent_eq_of_toReal_eq {fmt : FloatFormat} {x y : Model fmt}
    {dx dy : Numerics.Dyadic} (hx : toDyadic? x = some dx) (hy : toDyadic? y = some dy)
    (hx0 : dx.significand ≠ 0)
    (hvalue : toReal x = toReal y) : dx.exponent = dy.exponent := by
  have hy0 : dy.significand ≠ 0 := by
    apply (Dyadic.toReal_eq_zero_iff dy).not.mp
    have hv : dx.toReal = dy.toReal := by simpa [toReal_eq, hx, hy] using hvalue
    rw [← hv]
    exact (Dyadic.toReal_eq_zero_iff dx).not.mpr hx0
  rw [← cexp_toDyadic? hx hx0, ← cexp_toDyadic? hy hy0]
  congr 1
  simpa only [toReal_eq, hx, hy] using hvalue

/--
Equal nonzero real values determine the complete binary word. Both words are finite, because NaN
and the infinities denote zero.
-/
theorem eq_of_toReal_eq_of_nonzero {fmt : FloatFormat} {x y : Model fmt}
    (hvalue : toReal x = toReal y) (hzero : toReal x ≠ 0) : x = y := by
  obtain ⟨dx, hdx⟩ : ∃ d, toDyadic? x = some d := by
    cases hdecode : toDyadic? x with
    | none => exact absurd (by simp [toReal_eq, hdecode]) hzero
    | some d => exact ⟨d, rfl⟩
  obtain ⟨dy, hdy⟩ : ∃ d, toDyadic? y = some d := by
    cases hdecode : toDyadic? y with
    | none => exact absurd (hvalue.trans (by simp [toReal_eq, hdecode])) hzero
    | some d => exact ⟨d, rfl⟩
  have hv : dx.toReal = dy.toReal := by simpa [toReal_eq, hdx, hdy] using hvalue
  have hx0 : dx.significand ≠ 0 := by
    apply (Dyadic.toReal_eq_zero_iff dx).not.mp
    simpa [toReal_eq, hdx] using hzero
  have he := toDyadic?_exponent_eq_of_toReal_eq hdx hdy hx0 hvalue
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

/-- Rounding an exact zero preserves its sign in every direction and every encoding. -/
theorem Internal.Directed.roundDyadic_zero (fmt : FloatFormat)
    (mode : IEEERoundingMode) (negative : Bool) (exponent : Int) :
    Internal.Directed.roundDyadic fmt mode ⟨negative, 0, exponent⟩ = zero fmt negative := by
  cases hfmt : fmt.isIEEE <;> cases negative <;> cases mode <;>
    simp [Internal.Directed.roundDyadic, roundDyadicTowardZero, roundDyadicUp, roundDyadicDown,
      roundDyadicNearestAway, roundDyadicAway, Model.roundDyadic, hfmt, Model.ieeeRoundDyadic,
      roundDyadicGeneral, zero, modelSign, posZero_eq_ofModel_zero, negZero_eq_ofModel_zero]

/-- In a conventional IEEE format, rounding a decoded finite dyadic restores its complete word. -/
theorem Internal.Directed.roundDyadic_toDyadic? {fmt : FloatFormat}
    (hfmt : fmt.isIEEE = true) (mode : IEEERoundingMode) {x : Model fmt}
    {d : Numerics.Dyadic} (hd : toDyadic? x = some d) :
    Internal.Directed.roundDyadic fmt mode d = x := by
  by_cases hm : d.significand = 0
  · have hz := isZero_eq_true_of_toDyadic?_some_of_mant_eq_zero hd hm
    have hdx := toDyadic?_eq_zero_of_isZero_eq_true x hz
    have hd' := Option.some.inj (hd.symm.trans hdx)
    rw [hd', Internal.Directed.roundDyadic_zero fmt]
    apply eq_of_toDyadic?_eq_some (d := ⟨Model.signBit x, 0, 0⟩) _ hdx
    simp [toDyadic?_zero, signBit_zero,
      FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt hfmt]
  · have hv : toReal x = d.toReal := by simp [toReal_eq, hd]
    have hr := Internal.Directed.roundDyadic_of_representable fmt hfmt mode d
      (toDyadic?_significand_lt x hd) (minSubnormalExponent_le_toDyadic? x hd)
      (abs_toReal_le_posMaxFinite_of_toDyadic?_some x hd)
    exact eq_of_toReal_eq_of_nonzero (hr.2.trans hv.symm)
      (by rw [hr.2]; exact (Dyadic.toReal_eq_zero_iff d).not.mpr hm)


end Model
end FloatLib.Floats.Formats.BinaryInterchange
