/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Finite
import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Bounds

/-!
# Directed square-root bounds

The integer square-root bracket used by `sqrtDown` and `sqrtUp` encloses the exact real square
root after restoring its dyadic scale. For descriptors with `fmt.isIEEE = true`, directed dyadic
rounding yields extended-real lower and upper bounds on finite nonnegative inputs, including
negative zero.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq

section

private theorem natCast_sqrt_bounds (n : Nat) :
    (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) ∧
      Real.sqrt (n : ℝ) ≤ (Nat.sqrt n + 1 : Nat) := by
  constructor
  · apply (Real.le_sqrt (by positivity) (by positivity)).2
    have h := Nat.sqrt_le n
    simpa [pow_two] using
      (show ((Nat.sqrt n * Nat.sqrt n : Nat) : ℝ) ≤ (n : ℝ) by exact_mod_cast h)
  · apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have h := (Nat.lt_succ_sqrt n).le
      simpa [pow_two, Nat.succ_eq_add_one] using
        (show (n : ℝ) ≤ (((Nat.sqrt n + 1) * (Nat.sqrt n + 1) : Nat) : ℝ) by
          exact_mod_cast h)

private theorem sqrtScale_cancel (exponent : Int) (precision : Nat) :
    (2 : ℝ) ^ (2 * precision) *
        bpow (exponent - Int.ofNat precision) ^ 2 =
      bpow (exponent + exponent) := by
  have hprecision :
      (2 : ℝ) ^ (2 * precision) = bpow (Int.ofNat (2 * precision)) := by
    simpa [pow2_eq_two_pow, Nat.cast_pow] using
      (bpow_ofNat (2 * precision)).symm
  have hscale :
      bpow (exponent - Int.ofNat precision) ^ 2 =
        bpow ((exponent - Int.ofNat precision) +
          (exponent - Int.ofNat precision)) := by
    simpa [pow_two] using
      (bpow_add (exponent - Int.ofNat precision)
        (exponent - Int.ofNat precision)).symm
  rw [hprecision, hscale, ← bpow_add]
  congr 1
  have hcast : Int.ofNat (2 * precision) = 2 * Int.ofNat precision := by
    simp
  rw [hcast]
  ring

private theorem sqrt_source_scaled (fmt : FloatFormat) (d : Numerics.Dyadic)
    (hsign : d.negative = false) :
    let exponentOdd : Bool := (d.exponent % 2) != 0
    let mantissa : Nat := if exponentOdd then d.significand * 2 else d.significand
    let evenExponent : Int := if exponentOdd then d.exponent - 1 else d.exponent
    let halfExponent : Int := evenExponent / 2
    let leading : Nat := Nat.log2 mantissa
    let rootLeading : Nat := leading / 2
    let extraPrecision : Nat := fmt.fracWidth - rootLeading
    let scaled : Nat := Nat.shiftLeft mantissa (2 * extraPrecision)
    d.toReal =
      (scaled : ℝ) * bpow (halfExponent - Int.ofNat extraPrecision) ^ 2 := by
  dsimp only
  let exponentOdd : Bool := (d.exponent % 2) != 0
  let mantissa : Nat := if exponentOdd then d.significand * 2 else d.significand
  let evenExponent : Int := if exponentOdd then d.exponent - 1 else d.exponent
  let halfExponent : Int := evenExponent / 2
  let leading : Nat := Nat.log2 mantissa
  let rootLeading : Nat := leading / 2
  let extraPrecision : Nat := fmt.fracWidth - rootLeading
  let scaled : Nat := Nat.shiftLeft mantissa (2 * extraPrecision)
  change d.toReal =
    (scaled : ℝ) * bpow (halfExponent - Int.ofNat extraPrecision) ^ 2
  have heven : evenExponent = halfExponent + halfExponent := by
    have hmod : evenExponent % 2 = 0 := by
      cases hOdd : exponentOdd with
      | false =>
          have h : d.exponent % 2 = 0 := by
            have hb : (d.exponent % 2 != 0) = false := by
              simpa [exponentOdd] using hOdd
            exact (bne_eq_false_iff_eq).1 hb
          simp [evenExponent, hOdd, h]
      | true =>
          have hne : d.exponent % 2 ≠ 0 := by
            intro hEq
            have ht : (d.exponent % 2 != 0) = true := by
              simpa [exponentOdd] using hOdd
            simp [hEq] at ht
          have h1 : d.exponent % 2 = 1 :=
            (Int.emod_two_eq_zero_or_one d.exponent).resolve_left hne
          simp [evenExponent, hOdd, Int.sub_emod, h1]
    have hmul : evenExponent / 2 * 2 = evenExponent :=
      Int.ediv_mul_cancel (Int.dvd_iff_emod_eq_zero.2 hmod)
    simpa [halfExponent, mul_two] using hmul.symm
  have hsource : d.toReal = (mantissa : ℝ) * bpow evenExponent := by
    cases hOdd : exponentOdd with
    | false =>
        simp [Numerics.Dyadic.toReal, hsign, mantissa, evenExponent, hOdd,
          bpow, FloatLib.Floats.Formats.Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal]
    | true =>
        have hb :
            FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix d.exponent =
              FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (d.exponent - 1) *
                FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix 1 := by
          simpa [Int.sub_add_cancel] using bpow_add (d.exponent - 1) 1
        change (2 : ℝ) ^ d.exponent =
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (d.exponent - 1) *
            FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix 1 at hb
        rw [Numerics.Dyadic.toReal]
        simp only [Numerics.Dyadic.cast_signedSignificand, hsign,
          Bool.false_eq_true, ite_false, one_mul]
        rw [hb]
        rw [show
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix 1 = (2 : ℝ) by
            exact bpow_one]
        simp [mantissa, evenExponent, hOdd]
        ring
  have hscaled :
      (scaled : ℝ) = (mantissa : ℝ) * (2 : ℝ) ^ (2 * extraPrecision) := by
    simp [scaled, Nat.shiftLeft_eq]
  rw [hsource, hscaled, mul_assoc, sqrtScale_cancel]
  rw [heven]

/-- The dyadic endpoints computed by `sqrtDyadicBracket` enclose the exact square root. -/
theorem sqrtDyadicBracket_sound (fmt : FloatFormat) (d : Numerics.Dyadic)
    (hsign : d.negative = false) :
    (sqrtDyadicBracket fmt d).lower.toReal ≤ Real.sqrt d.toReal ∧
      Real.sqrt d.toReal ≤ (sqrtDyadicBracket fmt d).upper.toReal := by
  let exponentOdd : Bool := (d.exponent % 2) != 0
  let mantissa : Nat := if exponentOdd then d.significand * 2 else d.significand
  let evenExponent : Int := if exponentOdd then d.exponent - 1 else d.exponent
  let halfExponent : Int := evenExponent / 2
  let leading : Nat := Nat.log2 mantissa
  let rootLeading : Nat := leading / 2
  let extraPrecision : Nat := fmt.fracWidth - rootLeading
  let scaled : Nat := Nat.shiftLeft mantissa (2 * extraPrecision)
  let lowerMantissa : Nat := Nat.sqrt scaled
  let remainder : Nat := scaled - lowerMantissa * lowerMantissa
  let upperMantissa : Nat :=
    if remainder == 0 then lowerMantissa else lowerMantissa + 1
  let scale : ℝ := bpow (halfExponent - Int.ofNat extraPrecision)
  simp only [sqrtDyadicBracket, Numerics.Dyadic.toReal_mk_false]
  change (lowerMantissa : ℝ) * scale ≤ Real.sqrt d.toReal ∧
    Real.sqrt d.toReal ≤ (upperMantissa : ℝ) * scale
  have hsource : d.toReal = (scaled : ℝ) * scale ^ 2 := by
    simpa [exponentOdd, mantissa, evenExponent, halfExponent, leading, rootLeading,
      extraPrecision, scaled, scale] using sqrt_source_scaled fmt d hsign
  have hscalePos : 0 < scale := bpow_pos _
  have hsqrtSource : Real.sqrt d.toReal = Real.sqrt (scaled : ℝ) * scale := by
    rw [hsource, Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs,
      abs_of_pos hscalePos]
  have hnat := natCast_sqrt_bounds scaled
  have hlower : (lowerMantissa : ℝ) ≤ Real.sqrt (scaled : ℝ) := by
    simpa [lowerMantissa] using hnat.1
  have hupper : Real.sqrt (scaled : ℝ) ≤ (upperMantissa : ℝ) := by
    by_cases hzero : remainder = 0
    · have hlowerSq : lowerMantissa * lowerMantissa ≤ scaled := by
        simpa [lowerMantissa] using Nat.sqrt_le scaled
      have hscaledLe : scaled ≤ lowerMantissa * lowerMantissa :=
        (Nat.sub_eq_zero_iff_le).mp (by simpa [remainder] using hzero)
      have hscaledEq : scaled = lowerMantissa * lowerMantissa :=
        le_antisymm hscaledLe hlowerSq
      have hsqrt : Real.sqrt (scaled : ℝ) = (lowerMantissa : ℝ) := by
        rw [hscaledEq]
        norm_num [Nat.cast_mul, Real.sqrt_sq_eq_abs]
      simp [upperMantissa, hzero, hsqrt]
    · simpa [upperMantissa, hzero, lowerMantissa] using hnat.2
  rw [hsqrtSource]
  exact
    ⟨mul_le_mul_of_nonneg_right hlower hscalePos.le,
      mul_le_mul_of_nonneg_right hupper hscalePos.le⟩

private theorem signBit_eq_false_of_nonnegative_of_not_isZero
    {fmt : FloatFormat} (x : Model fmt) {d : Numerics.Dyadic}
    (hd : toDyadic? x = some d) (hnonnegative : 0 ≤ toReal x)
    (hzero : isZero x = false) :
    signBit x = false := by
  have hmant := significand_ne_zero_of_toDyadic?_some_of_isZero_eq_false hd hzero
  rw [← sign_eq_signBit_of_toDyadic?_some hd]
  cases hsign : d.negative with
  | false => rfl
  | true =>
      have hmantPos : (0 : ℝ) < d.significand := by
        exact_mod_cast Nat.pos_of_ne_zero hmant
      have hdNegative : d.toReal < 0 := by
        simpa [Numerics.Dyadic.toReal, hsign] using
          neg_neg_of_pos (mul_pos hmantPos (zpow_pos (by norm_num : (0 : ℝ) < 2) d.exponent))
      have hxReal : toReal x = d.toReal := by
        simp [toReal_eq, hd]
      rw [hxReal] at hnonnegative
      exact (not_lt_of_ge hnonnegative hdNegative).elim

/-- A finite value with clear sign bit has nonnegative real value. -/
theorem toReal_nonneg_of_isFinite_of_signBit_eq_false
    {fmt : FloatFormat} (x : Model fmt)
    (hfinite : isFinite x = true) (hxsign : signBit x = false) :
    0 ≤ toReal x := by
  obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite hfinite
  have hsign : d.negative = false := (sign_eq_signBit_of_toDyadic?_some hd).trans hxsign
  have hxReal : toReal x = d.toReal := by
    simp [toReal_eq, hd]
  rw [hxReal, Numerics.Dyadic.toReal]
  simp only [Numerics.Dyadic.cast_signedSignificand, hsign, Bool.false_eq_true, ite_false, one_mul]
  exact mul_nonneg (Nat.cast_nonneg _) (bpow_nonneg _)

/-- Downward square root is non-NaN on finite nonnegative inputs. -/
theorem isNaN_sqrtDown_eq_false_of_isFinite_of_nonnegative
    {fmt : FloatFormat} (x : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hfinite : isFinite x = true) (hnonnegative : 0 ≤ toReal x) :
    isNaN (sqrtDown x) = false := by
  by_cases hzero : isZero x = true
  · rw [sqrtDown, sqrtWithRounding_eq_self_of_isZero .towardNegativeInfinity nofun hfinite hzero]
    exact isNaN_eq_false_of_isFinite_eq_true x hfinite
  · obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite hfinite
    have hzeroFalse : isZero x = false := Bool.eq_false_iff.mpr hzero
    rw [sqrtDown_eq_roundDyadicDown_of_toDyadic?_some hd
      (signBit_eq_false_of_nonnegative_of_not_isZero x hd hnonnegative hzeroFalse) hzeroFalse]
    exact isNaN_roundDyadicDown_eq_false fmt _ hfmt

/-- Upward square root is non-NaN on finite nonnegative inputs. -/
theorem isNaN_sqrtUp_eq_false_of_isFinite_of_nonnegative
    {fmt : FloatFormat} (x : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hfinite : isFinite x = true) (hnonnegative : 0 ≤ toReal x) :
    isNaN (sqrtUp x) = false := by
  by_cases hzero : isZero x = true
  · rw [sqrtUp, sqrtWithRounding_eq_self_of_isZero .towardPositiveInfinity nofun hfinite hzero]
    exact isNaN_eq_false_of_isFinite_eq_true x hfinite
  · obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite hfinite
    have hzeroFalse : isZero x = false := Bool.eq_false_iff.mpr hzero
    rw [sqrtUp_eq_roundDyadicUp_of_toDyadic?_some hd
      (signBit_eq_false_of_nonnegative_of_not_isZero x hd hnonnegative hzeroFalse) hzeroFalse]
    exact isNaN_roundDyadicUp_eq_false fmt _ hfmt

/--
`sqrtDown` encloses the exact square root from below for every finite value with nonnegative real
semantics, including negative zero.
-/
theorem toEReal_sqrtDown_le_of_nonnegative
    {fmt : FloatFormat} (x : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hfinite : isFinite x = true) (hnonnegative : 0 ≤ toReal x) :
    toEReal (sqrtDown x) ≤ ((Real.sqrt (toReal x) : ℝ) : EReal) := by
  by_cases hzero : isZero x = true
  · rw [sqrtDown, sqrtWithRounding_eq_self_of_isZero .towardNegativeInfinity nofun hfinite hzero,
      toEReal_eq_coe_toReal_of_isFinite x hfinite, toReal_eq_zero_of_isZero x hzero]
    simp
  · obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite hfinite
    have hzeroFalse : isZero x = false := Bool.eq_false_iff.mpr hzero
    have hsign := signBit_eq_false_of_nonnegative_of_not_isZero x hd hnonnegative hzeroFalse
    have hxReal : toReal x = d.toReal := by
      simp [toReal_eq, hd]
    rw [sqrtDown_eq_roundDyadicDown_of_toDyadic?_some hd hsign hzeroFalse, hxReal]
    calc
      toEReal (roundDyadicDown fmt (sqrtDyadicBracket fmt d).lower) ≤
          ((sqrtDyadicBracket fmt d).lower.toReal : EReal) :=
        toEReal_roundDyadicDown_le fmt _ hfmt
      _ ≤ (Real.sqrt d.toReal : EReal) :=
        EReal.coe_le_coe_iff.2
          (sqrtDyadicBracket_sound fmt d ((sign_eq_signBit_of_toDyadic?_some hd).trans hsign)).1

/--
The exact square root is bounded above by `sqrtUp` for every finite value with nonnegative real
semantics, including negative zero.
-/
theorem le_toEReal_sqrtUp_of_nonnegative
    {fmt : FloatFormat} (x : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hfinite : isFinite x = true) (hnonnegative : 0 ≤ toReal x) :
    ((Real.sqrt (toReal x) : ℝ) : EReal) ≤ toEReal (sqrtUp x) := by
  by_cases hzero : isZero x = true
  · rw [sqrtUp, sqrtWithRounding_eq_self_of_isZero .towardPositiveInfinity nofun hfinite hzero,
      toEReal_eq_coe_toReal_of_isFinite x hfinite, toReal_eq_zero_of_isZero x hzero]
    simp
  · obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite hfinite
    have hzeroFalse : isZero x = false := Bool.eq_false_iff.mpr hzero
    have hsign := signBit_eq_false_of_nonnegative_of_not_isZero x hd hnonnegative hzeroFalse
    have hxReal : toReal x = d.toReal := by
      simp [toReal_eq, hd]
    rw [sqrtUp_eq_roundDyadicUp_of_toDyadic?_some hd hsign hzeroFalse, hxReal]
    calc
      (Real.sqrt d.toReal : EReal) ≤ ((sqrtDyadicBracket fmt d).upper.toReal : EReal) :=
        EReal.coe_le_coe_iff.2
          (sqrtDyadicBracket_sound fmt d ((sign_eq_signBit_of_toDyadic?_some hd).trans hsign)).2
      _ ≤ toEReal (roundDyadicUp fmt (sqrtDyadicBracket fmt d).upper) :=
        le_toEReal_roundDyadicUp fmt _ hfmt

/-- `sqrtDown` bounds the exact square root from below on finite inputs with a clear sign bit. -/
theorem toEReal_sqrtDown_le
    {fmt : FloatFormat} (x : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hfinite : isFinite x = true) (hxsign : signBit x = false) :
    toEReal (sqrtDown x) ≤ ((Real.sqrt (toReal x) : ℝ) : EReal) :=
  toEReal_sqrtDown_le_of_nonnegative x hfmt hfinite
    (toReal_nonneg_of_isFinite_of_signBit_eq_false x hfinite hxsign)

/-- `sqrtUp` bounds the exact square root from above on finite inputs with a clear sign bit. -/
theorem le_toEReal_sqrtUp
    {fmt : FloatFormat} (x : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hfinite : isFinite x = true) (hxsign : signBit x = false) :
    ((Real.sqrt (toReal x) : ℝ) : EReal) ≤ toEReal (sqrtUp x) :=
  le_toEReal_sqrtUp_of_nonnegative x hfmt hfinite
    (toReal_nonneg_of_isFinite_of_signBit_eq_false x hfinite hxsign)

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
