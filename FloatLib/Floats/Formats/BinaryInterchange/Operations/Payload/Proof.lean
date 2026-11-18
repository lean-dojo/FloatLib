/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Payload.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Proof.RoundToIntegral.Real
public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Cast.Proof
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Exact

/-!
# Contracts of the NaN payload operations

For every format descriptor:

* `nanPayload_lt_payloadBound`: the payload of a NaN is below `payloadBound fmt`, and
  `nanPayload_propagatedNaN`: a quiet NaN built from a payload below the bound carries it.
* `admissiblePayload?_eq_some`: a value names the payload `n` only if it is the encoding of `n`
  and `n` is below the bound.
* `getPayload_setPayload`: reading the payload of `setPayload x` gives `x` back whenever `x` is
  admissible, and `setPayload_of_admissiblePayload?_eq_none`, `getPayload_of_isNaN_eq_false`:
  the two results for operands outside the domain, `+0` and `-1`.
* `isNaN_setPayload` and `signBit_setPayload`: the result of `setPayload` is a NaN exactly for an
  admissible operand, and its sign bit is clear in a format with signed zero.
* `isSignaling_setPayloadSignaling` and `getPayload_setPayloadSignaling`: in the IEEE encoding a
  nonzero admissible payload gives a signaling NaN whose payload reads back as the operand, and
  `setPayloadSignaling_of_admissiblePayload?_eq_none` gives `+0` outside the domain.

For a conventional IEEE descriptor whose exponent range reaches `2 ^ fracWidth`
(`fmt.fracWidth ≤ fmt.maxNormalExponent`, which every interchange format satisfies):

* `toReal_natCast_of_le`: a natural number up to `2 ^ fracWidth` is encoded exactly.
* `admissiblePayload?_natCast`: the encoding of a natural number below the bound is admissible.
* `toReal_getPayload`: `getPayload` of a NaN denotes its payload exactly.
* `setPayload_getPayload`: writing back the payload read from a NaN gives the quiet NaN with
  that payload and a clear sign bit.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats.Formats.Flocq

variable {fmt : FloatFormat}

/-- In the IEEE encoding the payload of a NaN is its fraction field without the quiet bit. -/
theorem nanPayload_eq_mod (x : Model fmt) (henc : fmt.encoding = .ieee)
    (hnan : isNaN x = true) :
    nanPayload x = fracField x % 2 ^ (fmt.fracWidth - 1) := by
  have hfw := fmt.fracWidth_pos
  have hieee : IEEE.isNaN x = true := by simpa [isNaN, henc] using hnan
  have hqq : 2 ^ fmt.fracWidth = 2 * 2 ^ (fmt.fracWidth - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have hflt : fracField x < 2 * 2 ^ (fmt.fracWidth - 1) := hqq ▸ fracField_lt_pow2 x
  have hqpos : 0 < 2 ^ (fmt.fracWidth - 1) := Nat.two_pow_pos _
  have htb : (fracField x).testBit (fmt.fracWidth - 1) =
      decide (2 ^ (fmt.fracWidth - 1) ≤ fracField x) := by
    rw [Nat.testBit_eq_decide_div_mod_eq]
    by_cases hle : 2 ^ (fmt.fracWidth - 1) ≤ fracField x
    · have hdiv : fracField x / 2 ^ (fmt.fracWidth - 1) = 1 := by
        apply Nat.div_eq_of_lt_le <;> omega
      simp [hdiv, hle]
    · have hdiv : fracField x / 2 ^ (fmt.fracWidth - 1) = 0 :=
        Nat.div_eq_of_lt (by omega)
      simp [hdiv, hle]
  unfold nanPayload isSignaling
  simp only [henc, IEEE.isSignaling, hieee, Bool.true_and, and_quietBit_eq_zero_iff, htb,
    payloadOfNaNField]
  by_cases hle : 2 ^ (fmt.fracWidth - 1) ≤ fracField x
  · have hlog : Nat.log2 (fracField x) = fmt.fracWidth - 1 := by
      rw [Nat.log2_eq_iff (by omega)]
      refine ⟨hle, ?_⟩
      rw [← Nat.pow_succ'] at hflt
      exact hflt
    simp only [hle, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, hlog]
    rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt (by omega)]
  · simp only [hle, decide_false, Bool.not_false, ite_true]
    exact (Nat.mod_eq_of_lt (by omega)).symm

/-- The payload of a NaN is below the payload bound of its format. -/
theorem nanPayload_lt_payloadBound (x : Model fmt) (hnan : isNaN x = true) :
    nanPayload x < payloadBound fmt := by
  cases henc : fmt.encoding with
  | ieee =>
      rw [nanPayload_eq_mod x henc hnan]
      simpa [payloadBound, henc] using Nat.mod_lt (fracField x) (Nat.two_pow_pos _)
  | finiteMaxNaN => simp [nanPayload, payloadOfNaNField, payloadBound, henc]
  | finiteUnsignedZero => simp [nanPayload, payloadOfNaNField, payloadBound, henc]
  | finite => simp [isNaN, henc] at hnan

/-- A positive payload bound means that the format has a NaN encoding. -/
theorem encoding_ne_finite_of_lt_payloadBound {n : Nat} (hn : n < payloadBound fmt) :
    fmt.encoding ≠ .finite := by
  intro henc
  simp [payloadBound, henc] at hn

/-- A quiet NaN built from a payload below the bound carries that payload. -/
theorem nanPayload_propagatedNaN (negative : Bool) {n : Nat} (hn : n < payloadBound fmt) :
    nanPayload (propagatedNaN fmt negative n) = n := by
  have hnan := isNaN_propagatedNaN fmt negative n (encoding_ne_finite_of_lt_payloadBound hn)
  cases henc : fmt.encoding with
  | ieee =>
      have hfw := fmt.fracWidth_pos
      have hn' : n < 2 ^ (fmt.fracWidth - 1) := by simpa [payloadBound, henc] using hn
      have hqq : 2 ^ fmt.fracWidth = 2 * 2 ^ (fmt.fracWidth - 1) := by
        rw [← Nat.pow_succ']; congr 1; omega
      have hfield : (2 ^ (fmt.fracWidth - 1) + n) % 2 ^ fmt.fracWidth =
          2 ^ (fmt.fracWidth - 1) + n := Nat.mod_eq_of_lt (by omega)
      rw [nanPayload_eq_mod _ henc hnan]
      simp only [propagatedNaN, henc, fracField_ofFields, hn', ite_true]
      rw [hfield, Nat.add_mod_left, Nat.mod_eq_of_lt hn']
  | finiteMaxNaN =>
      have : n = 0 := by simpa [payloadBound, henc] using hn
      simp [nanPayload, payloadOfNaNField, henc, this]
  | finiteUnsignedZero =>
      have : n = 0 := by simpa [payloadBound, henc] using hn
      simp [nanPayload, payloadOfNaNField, henc, this]
  | finite => exact absurd henc (encoding_ne_finite_of_lt_payloadBound hn)

/-- A value names the payload `n` only if it is the encoding of `n` and `n` is below the bound. -/
theorem admissiblePayload?_eq_some {x : Model fmt} {n : Nat}
    (h : admissiblePayload? x = some n) :
    n < payloadBound fmt ∧ ((n : Nat) : Model fmt) = x := by
  unfold admissiblePayload? at h
  split at h
  · rename_i value _
    by_cases hguard : (value.negative || decide ((fmt.fracWidth : Int) < value.exponent)) = true
    · simp [hguard] at h
    · by_cases hpayload : (roundDyadicToInt .towardZero value).toNat < payloadBound fmt ∧
          (((roundDyadicToInt .towardZero value).toNat : Nat) : Model fmt) = x
      · simp only [hguard, hpayload, and_self, ite_true, Bool.false_eq_true, ite_false,
          Option.some.injEq] at h
        subst h
        exact hpayload
      · simp [hguard, hpayload] at h
  all_goals cases h

/-- `getPayload` of an operand that is not a NaN is `-1`. -/
theorem getPayload_of_isNaN_eq_false {x : Model fmt} (h : isNaN x = false) :
    getPayload x = negOne fmt := by
  simp [getPayload, h]

/-- `setPayload` of an operand that names no admissible payload is `+0`. -/
theorem setPayload_of_admissiblePayload?_eq_none {x : Model fmt}
    (h : admissiblePayload? x = none) : setPayload x = posZero fmt := by
  simp [setPayload, h]

/-- The result of `setPayload` is a NaN exactly when the operand is admissible. -/
theorem isNaN_setPayload (x : Model fmt) :
    isNaN (setPayload x) = (admissiblePayload? x).isSome := by
  unfold setPayload
  cases h : admissiblePayload? x with
  | none =>
      simp [isNaN_eq_false_of_isFinite_eq_true (posZero fmt)
        (isFinite_eq_true_of_isZero_eq_true _ (isZero_posZero fmt))]
  | some n =>
      simpa using isNaN_propagatedNaN fmt false n
        (encoding_ne_finite_of_lt_payloadBound (admissiblePayload?_eq_some h).1)

/-- Reading the payload of `setPayload x` gives back an admissible `x`, as the same word. -/
theorem getPayload_setPayload {x : Model fmt} {n : Nat}
    (h : admissiblePayload? x = some n) : getPayload (setPayload x) = x := by
  obtain ⟨hn, hx⟩ := admissiblePayload?_eq_some h
  have hnan := isNaN_propagatedNaN fmt false n (encoding_ne_finite_of_lt_payloadBound hn)
  simp only [setPayload, h, getPayload, hnan, ite_true, nanPayload_propagatedNaN false hn]
  exact hx

/-- In a format with signed zero, the result of `setPayload` has a clear sign bit. -/
theorem signBit_setPayload (hfmt : fmt.supportsSignedZero = true) (x : Model fmt) :
    signBit (setPayload x) = false := by
  unfold setPayload
  cases h : admissiblePayload? x with
  | none => simp
  | some n =>
      cases henc : fmt.encoding <;>
        simp_all [propagatedNaN, FloatFormat.supportsSignedZero]

/-- `setPayloadSignaling` of an operand that names no admissible payload is `+0`. -/
theorem setPayloadSignaling_of_admissiblePayload?_eq_none {x : Model fmt}
    (h : admissiblePayload? x = none) : setPayloadSignaling x = posZero fmt := by
  unfold setPayloadSignaling
  cases fmt.encoding <;> simp [h]

/--
In the IEEE encoding, the word with an all-ones exponent and a nonzero fraction below the quiet
bit is a signaling NaN that carries the fraction as its payload.
-/
theorem isSignaling_ofFields_payload (henc : fmt.encoding = .ieee) (negative : Bool) {n : Nat}
    (hpos : n ≠ 0) (hn : n < 2 ^ (fmt.fracWidth - 1)) :
    isSignaling (ofFields fmt negative fmt.expAllOnesNat n) = true ∧
      nanPayload (ofFields fmt negative fmt.expAllOnesNat n) = n := by
  have hfw := fmt.fracWidth_pos
  have hqq : 2 ^ fmt.fracWidth = 2 * 2 ^ (fmt.fracWidth - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have hexp : fmt.expAllOnesNat % 2 ^ fmt.expWidth = fmt.expAllOnesNat :=
    Nat.mod_eq_of_lt (by
      unfold FloatFormat.expAllOnesNat
      have := Nat.one_le_two_pow (n := fmt.expWidth)
      omega)
  have hfrac : n % 2 ^ fmt.fracWidth = n := Nat.mod_eq_of_lt (by omega)
  have hsignaling : isSignaling (ofFields fmt negative fmt.expAllOnesNat n) = true := by
    simp only [isSignaling, henc, IEEE.isSignaling, IEEE.isNaN,
      and_quietBit_eq_zero_iff, expField_ofFields,
      fracField_ofFields, hexp, hfrac, Nat.testBit_lt_two_pow hn]
    simp [hpos]
  have hnan : isNaN (ofFields fmt negative fmt.expAllOnesNat n) = true := by
    by_contra hnot
    rw [isSignaling_eq_false_of_isNaN_eq_false _ (Bool.eq_false_of_not_eq_true hnot)] at hsignaling
    exact Bool.false_ne_true hsignaling
  refine ⟨hsignaling, ?_⟩
  rw [nanPayload_eq_mod _ henc hnan, fracField_ofFields, hfrac, Nat.mod_eq_of_lt hn]

/-- `setPayloadSignaling` of a nonzero admissible payload is a signaling NaN, in the IEEE
encoding. -/
theorem isSignaling_setPayloadSignaling (henc : fmt.encoding = .ieee) {x : Model fmt} {n : Nat}
    (h : admissiblePayload? x = some n) (hpos : n ≠ 0) :
    isSignaling (setPayloadSignaling x) = true := by
  have hn : n < 2 ^ (fmt.fracWidth - 1) := by
    simpa [payloadBound, henc] using (admissiblePayload?_eq_some h).1
  simp only [setPayloadSignaling, henc, h, hpos, ite_false]
  exact (isSignaling_ofFields_payload henc false hpos hn).1

/-- Reading the payload of `setPayloadSignaling x` gives back a nonzero admissible `x`, as the
same word, in the IEEE encoding. -/
theorem getPayload_setPayloadSignaling (henc : fmt.encoding = .ieee) {x : Model fmt} {n : Nat}
    (h : admissiblePayload? x = some n) (hpos : n ≠ 0) :
    getPayload (setPayloadSignaling x) = x := by
  obtain ⟨hbound, hx⟩ := admissiblePayload?_eq_some h
  have hn : n < 2 ^ (fmt.fracWidth - 1) := by simpa [payloadBound, henc] using hbound
  obtain ⟨hsignaling, hpayload⟩ := isSignaling_ofFields_payload henc false hpos hn
  have hnan : isNaN (ofFields fmt false fmt.expAllOnesNat n) = true := by
    by_contra hnot
    rw [isSignaling_eq_false_of_isNaN_eq_false _ (Bool.eq_false_of_not_eq_true hnot)] at hsignaling
    exact Bool.false_ne_true hsignaling
  simp only [setPayloadSignaling, henc, h, hpos, ite_false, getPayload, hnan, ite_true, hpayload]
  exact hx

/-! ## Conventional IEEE descriptors whose range reaches `2 ^ fracWidth` -/

/--
A natural number up to `2 ^ fracWidth` is encoded exactly by the natural-number cast, in a
conventional IEEE descriptor whose exponent range reaches `2 ^ fracWidth`.
-/
theorem toReal_natCast_of_le (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent) {n : Nat}
    (hn : n ≤ 2 ^ fmt.fracWidth) :
    isFinite ((n : Nat) : Model fmt) = true ∧ toReal ((n : Nat) : Model fmt) = n := by
  have hvalue : (Numerics.Dyadic.mk false n 0).toReal = n := by simp
  have hbound : |(Numerics.Dyadic.mk false n 0).toReal| ≤ toReal (posMaxFinite fmt) := by
    rw [hvalue, abs_of_nonneg (Nat.cast_nonneg n)]
    refine le_trans ?_ (two_pow_fracWidth_le_toReal_posMaxFinite fmt hrange)
    exact_mod_cast hn
  have hexponent : fmt.minSubnormalExponent ≤ (Numerics.Dyadic.mk false n 0).exponent := by
    have := fmt.exponentBias_pos
    simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
      Int.ofNat_eq_natCast]
    omega
  have h := roundDyadic_of_representable fmt hfmt (Numerics.Dyadic.mk false n 0) n 0 (by simp)
    (lt_of_le_of_lt hn (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))) hexponent hbound
  rw [natCast_def]
  exact ⟨h.1, h.2.trans hvalue⟩

/-- The payload bound of a conventional IEEE descriptor is at most `2 ^ fracWidth`. -/
theorem payloadBound_le_two_pow (fmt : FloatFormat) : payloadBound fmt ≤ 2 ^ fmt.fracWidth := by
  have hone := Nat.one_le_two_pow (n := fmt.fracWidth)
  cases henc : fmt.encoding <;> simp only [payloadBound, henc]
  · exact Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  · exact hone
  · exact hone
  · exact Nat.zero_le _

/--
The encoding of a natural number below the payload bound names that payload, in a conventional
IEEE descriptor whose exponent range reaches `2 ^ fracWidth`.
-/
theorem admissiblePayload?_natCast (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent) {n : Nat}
    (hn : n < payloadBound fmt) :
    admissiblePayload? ((n : Nat) : Model fmt) = some n := by
  obtain ⟨hfinite, hreal⟩ :=
    toReal_natCast_of_le hfmt hrange (hn.le.trans (payloadBound_le_two_pow fmt))
  obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite hfinite
  have hdreal : d.toReal = n := by simpa [toReal_eq, hd] using hreal
  have hsign : d.negative = false := by
    cases hneg : d.negative with
    | false => rfl
    | true =>
        by_cases hsig : d.significand = 0
        · have hzero : n = 0 := by
            have := (Dyadic.toReal_eq_zero_iff d).2 hsig
            rw [hdreal] at this
            exact_mod_cast this
          have hbit := sign_eq_signBit_of_toDyadic?_some hd
          rw [hneg, hzero] at hbit
          simp at hbit
        · have := Dyadic.toReal_lt_zero_of_negative_eq_true hneg hsig
          rw [hdreal] at this
          exact absurd this (not_lt.mpr (Nat.cast_nonneg n))
  have hexponent : ¬ (fmt.fracWidth : Int) < d.exponent := by
    intro hlt
    by_cases hsig : d.significand = 0
    · have hzero := toDyadic?_eq_zero_of_isZero_eq_true _
        (isZero_eq_true_of_toDyadic?_some_of_mant_eq_zero hd hsig)
      rw [hd] at hzero
      have := congrArg Numerics.Dyadic.exponent (Option.some.inj hzero)
      simp only at this
      omega
    · have hone : (1 : ℝ) ≤ d.significand := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hsig
      have hpow : (2 : ℝ) ^ (fmt.fracWidth : Int) ≤ (2 : ℝ) ^ d.exponent :=
        zpow_le_zpow_right₀ (by norm_num) hlt.le
      have hvalue : d.toReal = (d.significand : ℝ) * (2 : ℝ) ^ d.exponent := by
        simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, hsign]
      have hlarge : (2 : ℝ) ^ (fmt.fracWidth : Int) ≤ d.toReal := by
        rw [hvalue]
        calc (2 : ℝ) ^ (fmt.fracWidth : Int) = 1 * (2 : ℝ) ^ (fmt.fracWidth : Int) := by ring
          _ ≤ (d.significand : ℝ) * (2 : ℝ) ^ d.exponent :=
            mul_le_mul hone hpow (by positivity) (by positivity)
      have hsmall : (n : ℝ) < (2 : ℝ) ^ (fmt.fracWidth : Int) := by
        rw [zpow_natCast]
        exact_mod_cast lt_of_lt_of_le hn (payloadBound_le_two_pow fmt)
      rw [hdreal] at hlarge
      exact absurd hlarge (not_le.mpr hsmall)
  have hpayload : (roundDyadicToInt .towardZero d).toNat = n := by
    rw [roundDyadicToInt_towardZero, hdreal, ite_eq_left (Nat.cast_nonneg n)]
    simp
  simp [admissiblePayload?, exactValue_eq_finite_of_toDyadic?_eq_some hd, hsign, hexponent,
    hpayload, hn]

/--
`getPayload` of a NaN denotes its payload exactly, in a conventional IEEE descriptor whose
exponent range reaches `2 ^ fracWidth`.
-/
theorem toReal_getPayload (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent) {x : Model fmt}
    (hnan : isNaN x = true) : toReal (getPayload x) = nanPayload x := by
  have hle := (nanPayload_lt_payloadBound x hnan).le.trans (payloadBound_le_two_pow fmt)
  simp only [getPayload, hnan, ite_true]
  exact (toReal_natCast_of_le hfmt hrange hle).2

/--
Writing back the payload read from a NaN gives the quiet NaN with that payload and a clear sign
bit, in a conventional IEEE descriptor whose exponent range reaches `2 ^ fracWidth`.
-/
theorem setPayload_getPayload (hfmt : fmt.isIEEE = true)
    (hrange : (fmt.fracWidth : Int) ≤ fmt.maxNormalExponent) {x : Model fmt}
    (hnan : isNaN x = true) :
    setPayload (getPayload x) = propagatedNaN fmt false (nanPayload x) := by
  simp [setPayload, getPayload, hnan,
    admissiblePayload?_natCast hfmt hrange (nanPayload_lt_payloadBound x hnan)]

end Model
end FloatLib.Floats.Formats.BinaryInterchange
