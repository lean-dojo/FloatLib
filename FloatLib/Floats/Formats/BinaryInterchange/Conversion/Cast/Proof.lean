/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module
public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Cast.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Model.ERealSemantics
public import FloatLib.Floats.Formats.BinaryInterchange.Model.Fields.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Proof

import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Basic

/-!
# Correctness of binary format casts

A finite cast decodes a finite source exactly and applies nearest-even rounding on the
destination grid. Fully finite encodings then clip to their signed finite endpoints; every
other encoding preserves the grid result when the delivered result is finite. This policy
theorem covers arbitrary widths and biases. The IEEE refinement and exact grid-extension
statements follow from it. An IEEE destination keeps NaNs and infinities, so its finite result
also forces a finite source.

## References

- IEEE Standard for Floating-Point Arithmetic, IEEE 754-2019, Section 5.4.2.
  https://doi.org/10.1109/IEEESTD.2019.8766229
- S. Boldo and G. Melquiond, "Flocq: A Unified Library for Proving Floating-Point Algorithms in
  Coq," 2011. https://doi.org/10.1109/ARITH.2011.40
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-- The directed cast kernel computes `cast` in every rounding direction. -/
theorem Internal.Directed.cast_eq
    (src dst : FloatFormat) (x : Model src) (mode : IEEERoundingMode) :
    Internal.Directed.cast src dst x mode = Model.cast src dst x mode := by
  cases mode <;> rfl

/-- The status cast kernel is `cast` with `status := true`. -/
theorem Internal.Status.cast_eq
    (src dst : FloatFormat) (x : Model src) (mode : IEEERoundingMode) :
    Internal.Status.cast src dst x mode = Model.cast src dst x mode (status := true) :=
  rfl

/-- A cast with `status := true` delivers the value of the cast in the same direction. -/
@[simp] theorem value_cast
    (src dst : FloatFormat) (x : Model src) (mode : IEEERoundingMode) :
    (cast src dst x mode (status := true)).value =
      cast src dst x mode := by
  rw [← Internal.Directed.cast_eq, ← Internal.Status.cast_eq]
  unfold Internal.Status.cast
  split
  · simp [outcomeWithInvalid]
  · split
    · by_cases hvalue :
          isInfinite (Internal.Directed.cast src dst x mode) = true <;>
        simp [hvalue]
    · rfl

/-- Casting a finite value to its own format is the identity, signed zero included. -/
@[simp] theorem cast_self_of_finite {fmt : FloatFormat} (x : Model fmt)
    (hx : isFinite x = true) :
    cast fmt fmt x = x := by
  have hnan := isNaN_eq_false_of_isFinite_eq_true x hx
  have hinf := isInfinite_eq_false_of_isFinite_eq_true x hx
  simp [cast, Internal.Nearest.cast, hnan, hinf]

/-! ## NaN propagation -/

/-- Setting the quiet bit of a word leaves its sign bit unchanged. -/
theorem signBit_or_quietBit {fmt : FloatFormat} (b : FloatFormat.ExecWord fmt) :
    signBit (ofBits (fmt := fmt) (b ||| FloatFormat.quietBit fmt)) = signBit (ofBits (fmt := fmt)
      b) := by
  have hfw := fmt.fracWidth_pos
  rw [signBit_eq_msb, signBit_eq_msb]
  unfold ofBits FloatFormat.quietBit FloatFormat.ofWordNat FloatFormat.quietBitNat
  simp only [BitVec.msb_or]
  have hq : (BitVec.ofNat fmt.bitWidth (2 ^ (fmt.fracWidth - 1))).msb = false := by
    rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_ofNat, Nat.testBit_two_pow]
    simp only [FloatFormat.bitWidth]
    have : ¬ fmt.fracWidth - 1 = 1 + fmt.expWidth + fmt.fracWidth - 1 := by omega
    simp [this]
  simp [hq]

/-- Quieting a value keeps its exponent field, so it does not change finiteness. -/
theorem isFinite_quietNaN {fmt : FloatFormat} (x : Model fmt) :
    isFinite (quietNaN x) = isFinite x := by
  unfold quietNaN
  split
  · rename_i hencoding
    split
    · simp only [isFinite, hencoding, IEEE.isFinite]
      rw [expField_or_quietBit]
      rfl
    · rfl
  all_goals rfl

/-- The canonical NaN of an IEEE encoding is not finite. -/
theorem isFinite_canonicalNaN {fmt : FloatFormat} (hencoding : fmt.encoding = .ieee) :
    isFinite (canonicalNaN fmt) = false := by
  have h := isFinite_posInf fmt (by simp [FloatFormat.supportsInfinity, hencoding])
  simp only [isFinite, hencoding, IEEE.isFinite, canonicalNaN, posInf] at h ⊢
  rw [expField_or_quietBit]
  exact h

/--
The quiet bit of a word is clear if and only if bit `fracWidth - 1` of its fraction is clear.
-/
theorem and_quietBit_eq_zero_iff {fmt : FloatFormat} (x : Model fmt) :
    ((x.bits &&& FloatFormat.quietBit fmt) == 0) = !(fracField x).testBit (fmt.fracWidth - 1) := by
  have hfw := fmt.fracWidth_pos
  have hlt : fmt.fracWidth - 1 < fmt.bitWidth := by unfold FloatFormat.bitWidth; omega
  have hq : (2 : Nat) ^ (fmt.fracWidth - 1) < 2 ^ fmt.bitWidth := Nat.pow_lt_pow_right (by omega)
    hlt
  have key : (x.bits &&& FloatFormat.quietBit fmt).toNat =
      if (fracField x).testBit (fmt.fracWidth - 1) then 2 ^ (fmt.fracWidth - 1) else 0 := by
    unfold fracField FloatFormat.quietBit FloatFormat.fracMask FloatFormat.ofWordNat
      FloatFormat.quietBitNat FloatFormat.fracMaskNat
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq, Nat.testBit_and,
      Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one]
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i = fmt.fracWidth - 1
    · subst hi; split <;> simp_all
    · have : ¬ fmt.fracWidth - 1 = i := fun h => hi h.symm
      split <;> simp [Nat.testBit_and, this]
  cases ht : (fracField x).testBit (fmt.fracWidth - 1)
  · simp only [ht] at key
    have : x.bits &&& FloatFormat.quietBit fmt = 0 := BitVec.eq_of_toNat_eq (by simpa using key)
    simp [this]
  · simp only [ht, ite_true] at key
    have hne : x.bits &&& FloatFormat.quietBit fmt ≠ 0 := by
      intro h; rw [h] at key; have := Nat.two_pow_pos (fmt.fracWidth - 1);
        simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.zero_mod] at key; omega
    simpa using hne

/--
Rebuilding a NaN from its sign and IEEE payload gives the quieted NaN.

This is the same-descriptor case of IEEE 754-2019 §6.2.3, so `cast` could use `propagatedNaN` on
every NaN. It keeps `quietNaN` on the same descriptor because that path avoids field packing.
-/
theorem propagatedNaN_eq_quietNaN {fmt : FloatFormat} (x : Model fmt) (hnan : isNaN x = true) :
    propagatedNaN fmt (signBit x) (nanPayload x) = quietNaN x := by
  have hfw := fmt.fracWidth_pos
  unfold isNaN at hnan
  unfold propagatedNaN quietNaN nanPayload isSignaling
  cases henc : fmt.encoding with
  | finite => simp [henc] at hnan
  | finiteUnsignedZero =>
      simp only [henc, beq_iff_eq] at hnan
      simp [negZero, ofBits, ← hnan]
  | finiteMaxNaN =>
      simp only [henc, Bool.and_eq_true, beq_iff_eq] at hnan
      simp only
      rw [← hnan.1, ← hnan.2]
      exact ofFields_signBit_expField_fracField x
  | ieee =>
      simp only [henc] at hnan
      simp only [hnan, ite_true]
      have hx : IEEE.isNaN x = true := hnan
      simp only [IEEE.isNaN, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hx
      obtain ⟨he, hf0⟩ := hx
      set f := fracField x with hfdef
      set q := 2 ^ (fmt.fracWidth - 1) with hqdef
      have hqq : 2 ^ fmt.fracWidth = 2 * q := by
        rw [hqdef, ← Nat.pow_succ']; congr 1; omega
      have hflt : f < 2 * q := hqq ▸ fracField_lt_pow2 x
      have hqpos : 0 < q := Nat.two_pow_pos _
      -- the quieted word as fields
      have hq : ofBits (fmt := fmt) (x.bits ||| FloatFormat.quietBit fmt) =
          ofFields fmt (signBit x) (FloatFormat.expAllOnesNat fmt) (f ||| q) := by
        rw [← ofFields_signBit_expField_fracField (ofBits (fmt := fmt) (x.bits |||
          FloatFormat.quietBit fmt)),
          signBit_or_quietBit, expField_or_quietBit, fracField_or_quietBit]
        change ofFields fmt (signBit x) (expField x) (fracField x ||| _) = _
        rw [he]
      rw [hq, IEEE.isSignaling, hnan, Bool.true_and, and_quietBit_eq_zero_iff, ← hfdef]
      congr 1
      have hdiv : f = q * (f / q) + f % q := (Nat.div_add_mod f q).symm
      have hmod : f % q < q := Nat.mod_lt _ hqpos
      have hd : f / q < 2 := Nat.div_lt_of_lt_mul (by omega)
      have htb : f.testBit (fmt.fracWidth - 1) = decide (f / q % 2 = 1) := by
        rw [Nat.testBit_eq_decide_div_mod_eq, hqdef]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp hd) with hdq | hdq <;>
        simp only [hdq, Nat.mul_zero, Nat.mul_one, Nat.zero_add] at hdiv
      · -- f < q: signaling
        have hfq : f < q := by omega
        have hor : q + f = f ||| q := by
          have := Nat.two_pow_add_eq_or_of_lt (a := 1) (i := fmt.fracWidth - 1) hfq
          rw [Nat.mul_one, ← hqdef] at this
          rw [this, Nat.or_comm]
        simp only [htb, hdq, payloadOfNaNField]
        simp [hfq, hor]
      · -- q ≤ f: quiet
        have hlog : Nat.log2 f = fmt.fracWidth - 1 := by
          rw [Nat.log2_eq_iff (by omega)]
          constructor
          · rw [← hqdef]; omega
          · rw [show fmt.fracWidth - 1 + 1 = fmt.fracWidth by omega, hqq]; omega
        simp only [htb, hdq, payloadOfNaNField, hlog, ← hqdef]
        have hr : f - q < q := by omega
        simp only [decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hr]
        have h1 := Nat.two_pow_add_eq_or_of_lt (a := 1) (i := fmt.fracWidth - 1) hmod
        rw [← hqdef, Nat.mul_one] at h1
        have hfeq : f = q ||| f % q := by omega
        have : (f ||| q) = f := by
          rw [hfeq, Nat.or_comm (q ||| f % q) q, ← Nat.or_assoc, Nat.or_self]
        omega

/--
On a NaN source, `cast` in any rounding direction is `propagatedNaN` on the source sign and IEEE
payload, for equal and unequal descriptors alike (IEEE 754-2019 §6.2.3).
-/
theorem cast_of_isNaN {src dst : FloatFormat} (x : Model src) (hnan : isNaN x = true)
    (mode : IEEERoundingMode := .nearest) :
    cast src dst x mode = propagatedNaN dst (signBit x) (nanPayload x) := by
  have hnearest : Internal.Nearest.cast src dst x =
      propagatedNaN dst (signBit x) (nanPayload x) := by
    by_cases h : src = dst
    · subst h
      simp [Internal.Nearest.cast, hnan, propagatedNaN_eq_quietNaN x hnan]
    · simp [Internal.Nearest.cast, hnan, h]
  cases mode <;> simp [cast, Internal.Directed.cast, hnan, hnearest]

/--
Casting into a conventional IEEE destination maps NaNs to NaNs and infinities to infinities in every
rounding direction, so a finite result has a finite source.
-/
theorem isFinite_of_isFinite_cast {src dst : FloatFormat} (hdst : dst.isIEEE = true)
    {x : Model src} {mode : IEEERoundingMode}
    (h : isFinite (cast src dst x mode) = true) : isFinite x = true := by
  by_cases hnan : isNaN x = true
  · rw [cast_of_isNaN x hnan mode] at h
    have hresult := isNaN_propagatedNaN dst (signBit x) (nanPayload x)
      (by simp [FloatFormat.encoding_eq_ieee_of_isIEEE dst hdst])
    simp [isFinite_eq_false_of_isNaN hresult] at h
  by_cases hinf : isInfinite x = true
  · have hcast : cast src dst x mode = nativeOverflow dst (signBit x) := by
      cases mode <;> simp [cast, Internal.Directed.cast, Internal.Nearest.cast, hnan, hinf]
    simp [hcast, isFinite_nativeOverflow hdst] at h
  exact isFinite_eq_true_of_isNaN_eq_false_of_isInfinite_eq_false x
    (Bool.eq_false_of_not_eq_true hnan) (Bool.eq_false_of_not_eq_true hinf)

/--
Casting a NaN into a destination with no NaN encoding raises invalid in every rounding mode.

Such a destination has no NaN to deliver, so `cast` returns positive zero and reports the lost
NaN through the invalid flag.
-/
theorem cast_invalid_of_isNaN_of_encoding_finite {src dst : FloatFormat}
    (x : Model src) (mode : IEEERoundingMode) (hnan : isNaN x = true)
    (hdst : dst.encoding = .finite) :
    (cast src dst x mode (status := true)).status.invalid = true := by
  simp [cast, Internal.Status.cast, Internal.Directed.cast, Internal.Nearest.cast, hnan,
    isNaN_eq_false_of_encoding_finite hdst, outcomeWithInvalid]

/-- Exact widening preserves the sign bit. -/
theorem signBit_widenExact {src dst : FloatFormat} (x : Model src)
    (hexp : src.expWidth = dst.expWidth)
    (hbias : src.exponentBias = dst.exponentBias)
    (hencoding : src.encoding = dst.encoding)
    (hfrac : src.fracWidth ≤ dst.fracWidth) :
    signBit (widenExact x hexp hbias hencoding hfrac) = signBit x := by
  simp [widenExact]

/-- A source exponent field fits a destination field of the same width. -/
private theorem expField_lt_pow2_of_expWidth_eq {src dst : FloatFormat} (x : Model src)
    (hexp : src.expWidth = dst.expWidth) : expField x < 2 ^ dst.expWidth := by
  simpa [← hexp] using expField_lt_pow2 x

/-- A source fraction shifted to the top of a wider destination field still fits that field. -/
private theorem shiftLeft_fracField_lt_pow2 {src dst : FloatFormat} (x : Model src)
    (hfrac : src.fracWidth ≤ dst.fracWidth) :
    Nat.shiftLeft (fracField x) (dst.fracWidth - src.fracWidth) < 2 ^ dst.fracWidth := by
  have hwidth : src.fracWidth + (dst.fracWidth - src.fracWidth) = dst.fracWidth := by
    omega
  simpa [Nat.shiftLeft_eq, ← pow_add, hwidth] using
    Nat.mul_lt_mul_of_pos_right (fracField_lt_pow2 x)
      (Nat.two_pow_pos (dst.fracWidth - src.fracWidth))

/-- Exact widening preserves the biased exponent field. -/
theorem expField_widenExact {src dst : FloatFormat} (x : Model src)
    (hexp : src.expWidth = dst.expWidth)
    (hbias : src.exponentBias = dst.exponentBias)
    (hencoding : src.encoding = dst.encoding)
    (hfrac : src.fracWidth ≤ dst.fracWidth) :
    expField (widenExact x hexp hbias hencoding hfrac) = expField x := by
  simp [widenExact, Nat.mod_eq_of_lt (expField_lt_pow2_of_expWidth_eq x hexp)]

/-- Exact widening shifts the stored fraction into the high end of the destination field. -/
theorem fracField_widenExact {src dst : FloatFormat} (x : Model src)
    (hexp : src.expWidth = dst.expWidth)
    (hbias : src.exponentBias = dst.exponentBias)
    (hencoding : src.encoding = dst.encoding)
    (hfrac : src.fracWidth ≤ dst.fracWidth) :
    fracField (widenExact x hexp hbias hencoding hfrac) =
      Nat.shiftLeft (fracField x) (dst.fracWidth - src.fracWidth) := by
  rw [widenExact, fracField_ofFields, Nat.mod_eq_of_lt (shiftLeft_fracField_lt_pow2 x hfrac)]

/-- A finite value stays finite under exact widening. -/
theorem isFinite_widenExact {src dst : FloatFormat} (x : Model src)
    (hexp : src.expWidth = dst.expWidth)
    (hbias : src.exponentBias = dst.exponentBias)
    (hencoding : src.encoding = dst.encoding)
    (hfrac : src.fracWidth ≤ dst.fracWidth)
    (hx : isFinite x = true) :
    isFinite (widenExact x hexp hbias hencoding hfrac) = true := by
  let shift := dst.fracWidth - src.fracWidth
  have hexpDst := expField_lt_pow2_of_expWidth_eq x hexp
  have hfracDst : Nat.shiftLeft (fracField x) shift < 2 ^ dst.fracWidth :=
    shiftLeft_fracField_lt_pow2 x hfrac
  have hxFields :
      isFinite (ofFields src (signBit x) (expField x) (fracField x)) = true := by
    simpa only [ofFields_signBit_expField_fracField] using hx
  rw [isFinite_ofFields src (signBit x) (expField x) (fracField x)
    (expField_lt_pow2 x) (fracField_lt_pow2 x)] at hxFields
  change isFinite
    (ofFields dst (signBit x) (expField x) (Nat.shiftLeft (fracField x) shift)) = true
  rw [isFinite_ofFields dst (signBit x) (expField x)
    (Nat.shiftLeft (fracField x) shift) hexpDst hfracDst]
  cases hsrc : src.encoding with
  | ieee =>
      have hdst : dst.encoding = .ieee := by simpa [hsrc] using hencoding.symm
      simp only [hsrc] at hxFields
      simp only [hdst]
      simpa [FloatFormat.expAllOnesNat, hexp] using hxFields
  | finiteMaxNaN =>
      have hdst : dst.encoding = .finiteMaxNaN := by
        simpa [hsrc] using hencoding.symm
      simp only [hsrc] at hxFields
      simp only [hdst]
      rw [Bool.not_eq_true'] at hxFields ⊢
      apply Bool.eq_false_iff.mpr
      intro htarget
      apply (Bool.eq_false_iff.mp hxFields)
      obtain ⟨hexponentBool, hfractionBool⟩ :=
        (Bool.and_eq_true _ _).mp htarget
      apply (Bool.and_eq_true _ _).mpr
      refine ⟨?_, ?_⟩
      · apply beq_iff_eq.mpr
        simpa [FloatFormat.expAllOnesNat, hexp] using
          (beq_iff_eq.mp hexponentBool)
      · apply beq_iff_eq.mpr
        have hfraction := beq_iff_eq.mp hfractionBool
        let widthShift := dst.fracWidth - src.fracWidth
        by_cases hshift : widthShift = 0
        · have hwidth : dst.fracWidth = src.fracWidth := by
            dsimp [widthShift] at hshift
            omega
          simpa [shift, widthShift, hshift, FloatFormat.fracMaskNat, hwidth] using hfraction
        · have hshiftPos : 0 < widthShift := Nat.pos_of_ne_zero hshift
          have hpowShift : 2 ≤ 2 ^ widthShift := by
            simpa using Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) hshiftPos
          have hwidth : src.fracWidth + widthShift = dst.fracWidth := by
            dsimp [widthShift]
            omega
          have hmul :
              Nat.shiftLeft (fracField x) widthShift ≤
                (2 ^ src.fracWidth - 1) * 2 ^ widthShift := by
            simpa [Nat.shiftLeft_eq] using Nat.mul_le_mul_right (2 ^ widthShift)
              (Nat.le_pred_of_lt (fracField_lt_pow2 x))
          have hstrictBase :
              (2 ^ src.fracWidth - 1) * 2 ^ widthShift <
                2 ^ src.fracWidth * 2 ^ widthShift - 1 := by
            have hpowSrcPos : 0 < 2 ^ src.fracWidth := Nat.two_pow_pos _
            have hpowShiftLe :
                2 ^ widthShift ≤ 2 ^ src.fracWidth * 2 ^ widthShift := by
              simpa only [one_mul] using Nat.mul_le_mul_right (2 ^ widthShift)
                (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpowSrcPos))
            apply Nat.lt_sub_of_add_lt
            rw [Nat.sub_mul]
            simp only [one_mul]
            omega
          have hpow :
              2 ^ dst.fracWidth = 2 ^ src.fracWidth * 2 ^ widthShift := by
            rw [← pow_add, hwidth]
          have hstrict :
              Nat.shiftLeft (fracField x) widthShift <
                FloatFormat.fracMaskNat dst := by
            unfold FloatFormat.fracMaskNat
            rw [hpow]
            exact lt_of_le_of_lt hmul hstrictBase
          exact False.elim (hstrict.ne hfraction)
  | finiteUnsignedZero =>
      have hdst : dst.encoding = .finiteUnsignedZero := by
        simpa [hsrc] using hencoding.symm
      simp only [hsrc] at hxFields
      simp only [hdst]
      simpa [Nat.shiftLeft_eq] using hxFields
  | finite =>
      have hdst : dst.encoding = .finite := by
        simpa [hsrc] using hencoding.symm
      simp [hdst]

/--
Exact same-exponent widening preserves the decoded real value.

For a nonzero finite value, widening left-shifts the integer significand by
`dst.fracWidth - src.fracWidth` and the destination scale loses the same number of powers of two,
so the represented real number is unchanged.
-/
theorem toReal_widenExact {src dst : FloatFormat} (x : Model src)
    (hexp : src.expWidth = dst.expWidth)
    (hbias : src.exponentBias = dst.exponentBias)
    (hencoding : src.encoding = dst.encoding)
    (hfrac : src.fracWidth ≤ dst.fracWidth)
    (hx : isFinite x = true) :
    toReal (widenExact x hexp hbias hencoding hfrac) = toReal x := by
  let shift := dst.fracWidth - src.fracWidth
  have hwidth : src.fracWidth + shift = dst.fracWidth := by
    dsimp [shift]
    omega
  have hwidthInt : Int.ofNat dst.fracWidth =
      Int.ofNat src.fracWidth + Int.ofNat shift := by
    simpa only [Int.ofNat_eq_natCast, Nat.cast_add] using
      congrArg (fun n : Nat ↦ (n : Int)) hwidth.symm
  have hmin : dst.minSubnormalExponent + Int.ofNat shift =
      src.minSubnormalExponent := by
    unfold FloatFormat.minSubnormalExponent FloatFormat.minNormalExponent
    rw [← hbias, hwidthInt]
    ring
  have hyfin : isFinite (widenExact x hexp hbias hencoding hfrac) = true :=
    isFinite_widenExact x hexp hbias hencoding hfrac hx
  have hexpDst := expField_lt_pow2_of_expWidth_eq x hexp
  have hfracDst : Nat.shiftLeft (fracField x) shift < 2 ^ dst.fracWidth :=
    shiftLeft_fracField_lt_pow2 x hfrac
  have hxdecode := toDyadic?_ofFields_of_isFinite
    src (signBit x) (expField x) (fracField x)
    (expField_lt_pow2 x) (fracField_lt_pow2 x) (by
      simpa only [ofFields_signBit_expField_fracField] using hx)
  rw [ofFields_signBit_expField_fracField] at hxdecode
  have hydecode :
      toDyadic? (widenExact x hexp hbias hencoding hfrac) =
        if expField x = 0 then
          if Nat.shiftLeft (fracField x) shift = 0 then
            some { negative := signBit x, significand := 0, exponent := 0 }
          else
            some {
              negative := signBit x
              significand := Nat.shiftLeft (fracField x) shift
              exponent := dst.minSubnormalExponent }
        else
          some {
            negative := signBit x
            significand := pow2 dst.fracWidth + Nat.shiftLeft (fracField x) shift
            exponent := Int.ofNat (expField x) - Int.ofNat dst.exponentBias -
              Int.ofNat dst.fracWidth } := by
    simpa [widenExact, shift] using
      toDyadic?_ofFields_of_isFinite
        dst (signBit x) (expField x) (Nat.shiftLeft (fracField x) shift)
        hexpDst hfracDst (by
          simpa [widenExact, shift] using hyfin)
  by_cases hexponent : expField x = 0
  · by_cases hfraction : fracField x = 0
    · simp only [hexponent, ↓reduceIte, hfraction, Nat.shiftLeft_eq', Nat.shiftLeft_eq, zero_mul]
      at hxdecode hydecode
      rw [toReal_eq, hydecode, toReal_eq, hxdecode]
    · simp only [hexponent, ↓reduceIte, hfraction, Nat.shiftLeft_eq', Nat.shiftLeft_eq, mul_eq_zero,
      Nat.pow_eq_zero, OfNat.ofNat_ne_zero, ne_eq, false_and, or_self] at hxdecode hydecode
      rw [toReal_eq, hydecode, toReal_eq, hxdecode]
      simp only [Numerics.Dyadic.toReal, Numerics.Dyadic.cast_signedSignificand]
      have hmantissa :
          ((fracField x * 2 ^ shift : Nat) : ℝ) =
            (fracField x : ℝ) *
              FloatLib.Floats.Formats.Flocq.bpow FloatLib.Numerics.binaryRadix
                (Int.ofNat shift) := by
        simp [FloatLib.Floats.Formats.Flocq.bpow,
          FloatLib.Numerics.binaryRadix, FloatLib.Numerics.Radix.toReal]
      rw [hmantissa, ← hmin, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      dsimp [FloatLib.Floats.Formats.Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal]
      ring
  · rw [ite_eq_right hexponent] at hxdecode hydecode
    rw [toReal_eq, hydecode, toReal_eq, hxdecode]
    simp only [Numerics.Dyadic.toReal, Numerics.Dyadic.cast_signedSignificand]
    have hpow :
        pow2 dst.fracWidth = pow2 src.fracWidth * 2 ^ shift := by
      simp [pow2, ← pow_add, hwidth, Nat.shiftLeft_eq]
    have hmantissa :
        pow2 dst.fracWidth + Nat.shiftLeft (fracField x) shift =
          (pow2 src.fracWidth + fracField x) * 2 ^ shift := by
      rw [hpow]
      simp [Nat.shiftLeft_eq, Nat.add_mul]
    have hcastMantissa :
        ((pow2 dst.fracWidth + Nat.shiftLeft (fracField x) shift : Nat) : ℝ) =
          (pow2 src.fracWidth + fracField x : ℝ) *
            FloatLib.Floats.Formats.Flocq.bpow FloatLib.Numerics.binaryRadix
              (Int.ofNat shift) := by
      rw [hmantissa]
      simp [FloatLib.Floats.Formats.Flocq.bpow, FloatLib.Numerics.binaryRadix,
        FloatLib.Numerics.Radix.toReal]
    rw [hcastMantissa]
    have hexponentScale :
        Int.ofNat shift + (Int.ofNat (expField x) - Int.ofNat dst.exponentBias -
            Int.ofNat dst.fracWidth) =
          Int.ofNat (expField x) - Int.ofNat src.exponentBias -
            Int.ofNat src.fracWidth := by
      rw [← hbias, hwidthInt]
      ring
    have hbpowScale :
        FloatLib.Floats.Formats.Flocq.bpow FloatLib.Numerics.binaryRadix
            (Int.ofNat shift) *
          FloatLib.Floats.Formats.Flocq.bpow FloatLib.Numerics.binaryRadix
            (Int.ofNat (expField x) - Int.ofNat dst.exponentBias -
              Int.ofNat dst.fracWidth) =
          FloatLib.Floats.Formats.Flocq.bpow FloatLib.Numerics.binaryRadix
            (Int.ofNat (expField x) - Int.ofNat src.exponentBias -
              Int.ofNat src.fracWidth) := by
      rw [← FloatLib.Floats.Formats.Flocq.bpow.add_exp, hexponentScale]
    calc
      _ = (if signBit x = true then -1 else 1) *
          (pow2 src.fracWidth + fracField x : ℝ) *
          (FloatLib.Floats.Formats.Flocq.bpow FloatLib.Numerics.binaryRadix
              (Int.ofNat shift) *
            FloatLib.Floats.Formats.Flocq.bpow FloatLib.Numerics.binaryRadix
              (Int.ofNat (expField x) - Int.ofNat dst.exponentBias -
                Int.ofNat dst.fracWidth)) := by
                  dsimp [FloatLib.Floats.Formats.Flocq.bpow,
                    Numerics.binaryRadix, Numerics.Radix.toReal]
                  ring
      _ = (if signBit x = true then -1 else 1) *
          (pow2 src.fracWidth + fracField x : ℝ) *
          FloatLib.Floats.Formats.Flocq.bpow FloatLib.Numerics.binaryRadix
            (Int.ofNat (expField x) - Int.ofNat src.exponentBias -
              Int.ofNat src.fracWidth) := by rw [hbpowScale]
      _ = _ := by norm_cast

/--
A destination with at least as many fraction bits and no larger minimum subnormal exponent has
a finer dyadic grid. This grid has no upper exponent bound.
-/
theorem fexpOf_le_of_gridExtension {src dst : FloatFormat}
    (hfrac : src.fracWidth ≤ dst.fracWidth)
    (hmin : dst.minSubnormalExponent ≤ src.minSubnormalExponent) :
    ∀ e, fexpOf dst e ≤ fexpOf src e := by
  intro e
  simp only [fexpOf, FloatLib.Floats.Formats.Flocq.fltExp]
  apply max_le_max
  · apply sub_le_sub_left
    simpa [add_comm] using add_le_add_right (Int.ofNat_le.mpr hfrac) 1
  · exact hmin

/-- Representability is preserved by extension to a finer dyadic grid. -/
theorem genericFormat_of_gridExtension {src dst : FloatFormat} {r : ℝ}
    (hfrac : src.fracWidth ≤ dst.fracWidth)
    (hmin : dst.minSubnormalExponent ≤ src.minSubnormalExponent)
    (hr : FloatLib.Floats.Formats.Flocq.GenericRepresentable FloatLib.Numerics.binaryRadix
      (fexpOf src) r) :
    FloatLib.Floats.Formats.Flocq.GenericRepresentable FloatLib.Numerics.binaryRadix
      (fexpOf dst) r := by
  exact FloatLib.Floats.Formats.Flocq.generic_inclusion
    (fexpOf_le_of_gridExtension hfrac hmin) hr

/-- Equal biases and increased precision preserve the entire rounded-real grid. -/
theorem genericFormat_of_compatibleWidening {src dst : FloatFormat}
    (hbias : src.exponentBias = dst.exponentBias)
    (hfrac : src.fracWidth ≤ dst.fracWidth) {r : ℝ}
    (hr : FloatLib.Floats.Formats.Flocq.GenericRepresentable FloatLib.Numerics.binaryRadix
      (fexpOf src) r) :
    FloatLib.Floats.Formats.Flocq.GenericRepresentable FloatLib.Numerics.binaryRadix
      (fexpOf dst) r := by
  apply genericFormat_of_gridExtension hfrac ?_ hr
  simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
    Int.ofNat_eq_natCast, hbias]
  omega

/--
Compatible finite widening preserves the complete field encoding, including signed zero, in
every rounding mode.
-/
theorem cast_eq_widenExact_of_compatibleWidening {src dst : FloatFormat} (x : Model src)
    (hexp : src.expWidth = dst.expWidth)
    (hbias : src.exponentBias = dst.exponentBias)
    (hencoding : src.encoding = dst.encoding)
    (hfrac : src.fracWidth ≤ dst.fracWidth)
    (hx : isFinite x = true) (mode : IEEERoundingMode := .nearest) :
    cast src dst x mode = widenExact x hexp hbias hencoding hfrac := by
  have hnan := isNaN_eq_false_of_isFinite_eq_true x hx
  have hinf := isInfinite_eq_false_of_isFinite_eq_true x hx
  have hcast : Internal.Nearest.cast src dst x = widenExact x hexp hbias hencoding hfrac := by
    by_cases hformat : src = dst
    · subst dst
      simp [Internal.Nearest.cast, hnan, hinf, widenExact, ofFields_signBit_expField_fracField]
    · simp [Internal.Nearest.cast, hnan, hinf, hformat, hexp, hbias, hencoding, hfrac]
  by_cases hformat : src = dst
  · subst dst
    cases mode <;>
      simp [cast, Internal.Directed.cast, hnan, hinf, hcast, widenExact,
        ofFields_signBit_expField_fracField]
  · cases mode <;>
      simp [cast, Internal.Directed.cast, hnan, hinf, hcast, hformat, hexp, hbias, hencoding,
        hfrac]

/-- Casting across compatible exponent semantics with at least as much precision is exact. -/
theorem cast_exact_of_compatibleWidening {src dst : FloatFormat} (x : Model src)
    (hexp : src.expWidth = dst.expWidth)
    (hbias : src.exponentBias = dst.exponentBias)
    (hencoding : src.encoding = dst.encoding)
    (hfrac : src.fracWidth ≤ dst.fracWidth)
    (hx : isFinite x = true) :
    toReal (cast src dst x) = toReal x := by
  rw [cast_eq_widenExact_of_compatibleWidening x hexp hbias hencoding hfrac hx,
    toReal_widenExact x hexp hbias hencoding hfrac hx]

/-- Every finite cast follows real nearest-even rounding and the destination's saturation policy. -/
theorem cast_policy {src dst : FloatFormat} (x : Model src)
    (hx : isFinite x = true) (hout : isFinite (cast src dst x) = true) :
    toReal (cast src dst x) =
      if dst.encoding = .finite then clampAt dst (roundAt dst (toReal x))
      else roundAt dst (toReal x) := by
  by_cases hw : src.expWidth = dst.expWidth ∧ src.exponentBias = dst.exponentBias ∧
      src.encoding = dst.encoding ∧ src.fracWidth ≤ dst.fracWidth
  · rcases hw with ⟨he, hb, hc, hf⟩
    have hv := cast_exact_of_compatibleWidening x he hb hc hf hx
    have hround : roundAt dst (toReal x) = toReal x :=
      Flocq.round_preserves_generic Flocq.nearestEven _ <|
        genericFormat_of_compatibleWidening hb hf (toReal_genericFormat_of_isFinite x hx)
    have hbound := abs_toReal_le_posMaxFinite_of_isFinite _ hout
    rw [hv] at hbound
    rw [hv, hround, clampAt_eq_self dst hbound]
    simp
  · have hnan := isNaN_eq_false_of_isFinite_eq_true x hx
    have hinf := isInfinite_eq_false_of_isFinite_eq_true x hx
    have hne : src ≠ dst := by
      intro h
      subst dst
      exact hw ⟨rfl, rfl, rfl, le_rfl⟩
    obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite hx
    have hc : cast src dst x = roundDyadic dst d := by
      simp only [cast, Internal.Nearest.cast, hnan, hinf, Bool.false_eq_true, dite_false, hne]
      split
      · next he =>
        split
        · next hb =>
          split
          · next henc =>
            split
            · next hf => exact (hw ⟨he, hb, henc, hf⟩).elim
            · simp [finiteDyadic, hd]
          · simp [finiteDyadic, hd]
        · simp [finiteDyadic, hd]
      · simp [finiteDyadic, hd]
    rw [hc] at hout ⊢
    rw [toReal_roundDyadic_policy dst d hout]
    have hv : d.toReal = toReal x := by rw [toReal_eq, hd]
    rw [hv]

/--
Casting any binary descriptor to an IEEE destination performs one nearest-even real rounding,
provided the delivered result is finite. A finite result forces a finite source
(`isFinite_of_isFinite_cast`), and the source may use a custom bias or a finite-only encoding.
-/
theorem cast_eq_roundAt {src dst : FloatFormat}
    (hdst : dst.isIEEE = true) (x : Model src)
    (hxy : isFinite (cast src dst x) = true) :
    toReal (cast src dst x) = roundAt dst (toReal x) := by
  simpa [((FloatFormat.isIEEE_eq_true_iff dst).mp hdst).1] using
    cast_policy x (isFinite_of_isFinite_cast hdst hxy) hxy

/-- Grid inclusion gives exact casting for every encoding, with clipping excluded where needed. -/
theorem cast_exact_of_gridExtension_policy {src dst : FloatFormat} (x : Model src)
    (hfrac : src.fracWidth ≤ dst.fracWidth)
    (hmin : dst.minSubnormalExponent ≤ src.minSubnormalExponent)
    (hx : isFinite x = true) (hout : isFinite (cast src dst x) = true)
    (hrange : dst.encoding = .finite → |toReal x| ≤ toReal (posMaxFinite dst)) :
    toReal (cast src dst x) = toReal x := by
  have hr : roundAt dst (toReal x) = toReal x :=
    Flocq.round_preserves_generic Flocq.nearestEven _
      (genericFormat_of_gridExtension hfrac hmin (toReal_genericFormat_of_isFinite x hx))
  rw [cast_policy x hx hout, hr]
  split
  · next h => exact clampAt_eq_self dst (hrange h)
  · rfl

/--
Casting into an IEEE destination with a finer dyadic grid preserves the real value of every source
descriptor, including finite-only encodings, whenever the executable result is finite. This
permits a wider exponent field and covers the usual exact standard-format widening conversions.
The finite result is needed because grid inclusion does not bound the destination's upper
exponent range.
-/
theorem cast_exact_of_gridExtension {src dst : FloatFormat} (x : Model src)
    (hdst : dst.isIEEE = true)
    (hfrac : src.fracWidth ≤ dst.fracWidth)
    (hmin : dst.minSubnormalExponent ≤ src.minSubnormalExponent)
    (hxy : isFinite (cast src dst x) = true) :
    toReal (cast src dst x) = toReal x := by
  exact cast_exact_of_gridExtension_policy x hfrac hmin
    (isFinite_of_isFinite_cast hdst hxy) hxy
    (by simp [((FloatFormat.isIEEE_eq_true_iff dst).mp hdst).1])

end Model
end FloatLib.Floats.Formats.BinaryInterchange
