/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module
public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Cast.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Model.Fields.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Model.ERealSemantics

/-!
# Correctness of binary format casts

A finite cast decodes the source exactly and applies one nearest-even rounding step in the
destination format. The real-valued rounding bridge assumes conventional IEEE descriptors and
a finite result; it does not assign a real value to an infinity or NaN.

## References

- IEEE Standard for Floating-Point Arithmetic, IEEE 754-2019, Section 5.4.2.
  https://doi.org/10.1109/IEEESTD.2019.8766229
- S. Boldo and G. Melquiond, "Flocq: A Unified Library for Proving Floating-Point Algorithms in
  Coq," 2011. https://doi.org/10.1109/ARITH.2011.40
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-- The ordinary cast is the nearest-even specialization of the directed cast. -/
@[simp] theorem castWithRounding_nearestEven
    (src dst : FloatFormat) (x : Model src) :
    castWithRounding src dst x .nearestEven = cast src dst x := rfl

/-- Status-bearing conversion preserves the value selected by the directed cast. -/
theorem castWithStatus_value
    (src dst : FloatFormat) (x : Model src) (mode : IEEERoundingMode) :
    (castWithStatus src dst x mode).value =
      castWithRounding src dst x mode := by
  unfold castWithStatus
  split
  · simp [outcomeWithInvalid]
  · split
    · by_cases hvalue :
          isInf (castWithRounding src dst x mode) = true <;>
        simp [hvalue]
    · rfl

/-- Casting a finite value to its own format is an exact identity, including signed zero. -/
@[simp] theorem cast_self_of_finite {fmt : FloatFormat} (x : Model fmt)
    (hx : isFinite x = true) :
    cast fmt fmt x = x := by
  have hnan := isNaN_eq_false_of_isFinite_eq_true x hx
  have hinf := isInf_eq_false_of_isFinite_eq_true x hx
  simp [cast, hnan, hinf]

/-! ## NaN propagation -/

/-- Setting the quiet bit of a word sets bit `fracWidth - 1` of its fraction field. -/
theorem fracField_or_quietBit {fmt : FloatFormat} (b : FloatFormat.ExecWord fmt) :
    fracField (ofBits (fmt := fmt) (b ||| FloatFormat.quietBit fmt)) =
      fracField (ofBits (fmt := fmt) b) ||| 2 ^ (fmt.fracWidth - 1) := by
  have hfw := fmt.fracWidth_pos
  unfold fracField ofBits FloatFormat.quietBit FloatFormat.fracMask FloatFormat.ofWordNat
    FloatFormat.quietBitNat FloatFormat.fracMaskNat
  simp only [BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_ofNat]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one,
    Nat.testBit_two_pow]
  unfold FloatFormat.bitWidth
  by_cases h1 : i < fmt.fracWidth <;> by_cases h2 : fmt.fracWidth - 1 = i <;> simp [h1, h2] <;> omega

/-- Setting the quiet bit of a word leaves its exponent field unchanged. -/
theorem expField_or_quietBit {fmt : FloatFormat} (b : FloatFormat.ExecWord fmt) :
    expField (ofBits (fmt := fmt) (b ||| FloatFormat.quietBit fmt)) = expField (ofBits (fmt := fmt) b) := by
  have hfw := fmt.fracWidth_pos
  unfold expField ofBits FloatFormat.quietBit FloatFormat.expAllOnes FloatFormat.ofWordNat
    FloatFormat.quietBitNat FloatFormat.expAllOnesNat
  simp only [BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ushiftRight]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one,
    Nat.testBit_two_pow, Nat.testBit_shiftRight]
  unfold FloatFormat.bitWidth
  have : ¬ fmt.fracWidth - 1 = fmt.fracWidth + i := by omega
  by_cases h1 : i < fmt.expWidth <;> simp [h1, this]

/-- Setting the quiet bit of a word leaves its sign bit unchanged. -/
theorem signBit_or_quietBit {fmt : FloatFormat} (b : FloatFormat.ExecWord fmt) :
    signBit (ofBits (fmt := fmt) (b ||| FloatFormat.quietBit fmt)) = signBit (ofBits (fmt := fmt) b) := by
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


/-- The quiet bit of a word is clear exactly when bit `fracWidth - 1` of its fraction is clear. -/
theorem and_quietBit_eq_zero_iff {fmt : FloatFormat} (x : Model fmt) :
    ((x.bits &&& FloatFormat.quietBit fmt) == 0) = !(fracField x).testBit (fmt.fracWidth - 1) := by
  have hfw := fmt.fracWidth_pos
  have hlt : fmt.fracWidth - 1 < fmt.bitWidth := by unfold FloatFormat.bitWidth; omega
  have hq : (2 : Nat) ^ (fmt.fracWidth - 1) < 2 ^ fmt.bitWidth := Nat.pow_lt_pow_right (by omega) hlt
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
      intro h; rw [h] at key; have := Nat.two_pow_pos (fmt.fracWidth - 1); simp at key; omega
    simpa using hne

/--
Rebuilding a NaN from its sign and IEEE payload gives the quieted NaN.

This is the same-descriptor case of IEEE 754-2019 §6.2.3, so `cast` could use `propagatedNaN` on
every NaN; it keeps `quietNaN` on the same descriptor only because that path avoids field packing.
-/
theorem propagatedNaN_eq_quietNaN {fmt : FloatFormat} (x : Model fmt) (hnan : isNaN x = true) :
    propagatedNaN fmt (signBit x) (payloadOfNaNField (isSNaN x) (fracField x)) = quietNaN x := by
  have hfw := fmt.fracWidth_pos
  unfold isNaN at hnan
  unfold propagatedNaN quietNaN isSNaN
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
      have hbits : quietNaN x = ofBits (x.bits ||| FloatFormat.quietBit fmt) := by
        simp [quietNaN, henc, hnan]
      -- the quieted word as fields
      have hq : ofBits (fmt := fmt) (x.bits ||| FloatFormat.quietBit fmt) =
          ofFields fmt (signBit x) (FloatFormat.expAllOnesNat fmt) (f ||| q) := by
        rw [← ofFields_signBit_expField_fracField (ofBits (fmt := fmt) (x.bits ||| FloatFormat.quietBit fmt)),
          signBit_or_quietBit, expField_or_quietBit, fracField_or_quietBit]
        change ofFields fmt (signBit x) (expField x) (fracField x ||| _) = _
        rw [he]
      rw [hq, IEEE.isSNaN, hnan, Bool.true_and, and_quietBit_eq_zero_iff, ← hfdef]
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
        have hf : f % q = f := Nat.mod_eq_of_lt hfq
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
        simp [hr]
        have h1 := Nat.two_pow_add_eq_or_of_lt (a := 1) (i := fmt.fracWidth - 1) hmod
        rw [← hqdef, Nat.mul_one] at h1
        have hfeq : f = q ||| f % q := by omega
        have : (f ||| q) = f := by
          conv_lhs => rw [hfeq]
          rw [Nat.or_comm (q) (f % q), Nat.or_assoc, Nat.or_self, Nat.or_comm]
          exact hfeq.symm
        omega

/-- A propagated NaN is a NaN in every destination that has a NaN encoding. -/
theorem isNaN_propagatedNaN (fmt : FloatFormat) (negative : Bool) (payload : Nat)
    (h : fmt.encoding ≠ .finite) :
    isNaN (propagatedNaN fmt negative payload) = true := by
  have hexp : FloatFormat.expAllOnesNat fmt % 2 ^ fmt.expWidth = FloatFormat.expAllOnesNat fmt :=
    Nat.mod_eq_of_lt (by unfold FloatFormat.expAllOnesNat; have := Nat.one_le_two_pow (n := fmt.expWidth); omega)
  have hfw := fmt.fracWidth_pos
  unfold propagatedNaN isNaN
  cases henc : fmt.encoding with
  | finite => exact absurd henc h
  | finiteUnsignedZero => simp [negZero, ofBits]
  | finiteMaxNaN =>
      have hm : FloatFormat.fracMaskNat fmt % 2 ^ fmt.fracWidth = FloatFormat.fracMaskNat fmt :=
        Nat.mod_eq_of_lt (by unfold FloatFormat.fracMaskNat; have := Nat.one_le_two_pow (n := fmt.fracWidth); omega)
      simp [hexp, hm]
  | ieee =>
      have hq : 2 ^ fmt.fracWidth = 2 * 2 ^ (fmt.fracWidth - 1) := by
        rw [← Nat.pow_succ']; congr 1; omega
      have hpos := Nat.one_le_two_pow (n := fmt.fracWidth - 1)
      have hlt : 2 ^ (fmt.fracWidth - 1) + (if payload < 2 ^ (fmt.fracWidth - 1) then payload else 0)
          < 2 ^ fmt.fracWidth := by split <;> omega
      simp only [IEEE.isNaN, expField_ofFields, fracField_ofFields, hexp, Nat.mod_eq_of_lt hlt]
      simp

/--
On a NaN source, `cast` is `propagatedNaN` on the source sign and IEEE payload, for equal and
unequal descriptors alike (IEEE 754-2019 §6.2.3).
-/
theorem cast_of_isNaN {src dst : FloatFormat} (x : Model src) (hnan : isNaN x = true) :
    cast src dst x = propagatedNaN dst (signBit x) (payloadOfNaNField (isSNaN x) (fracField x)) := by
  by_cases h : src = dst
  · subst h
    simp [cast, hnan, propagatedNaN_eq_quietNaN x hnan]
  · simp [cast, hnan, h]

/-- The directed cast treats a NaN source exactly as `cast` does, in every rounding mode. -/
theorem castWithRounding_of_isNaN {src dst : FloatFormat} (x : Model src)
    (mode : IEEERoundingMode) (hnan : isNaN x = true) :
    castWithRounding src dst x mode =
      propagatedNaN dst (signBit x) (payloadOfNaNField (isSNaN x) (fracField x)) := by
  cases mode <;> simp [castWithRounding, hnan, cast_of_isNaN x hnan]

/--
Casting a NaN into a destination with no NaN encoding raises invalid in every rounding mode.

Such a destination has no NaN to deliver, so `cast` returns positive zero and `castWithStatus`
reports the lost NaN through the invalid flag.
-/
theorem castWithStatus_invalid_of_isNaN_of_encoding_finite {src dst : FloatFormat}
    (x : Model src) (mode : IEEERoundingMode) (hnan : isNaN x = true)
    (hdst : dst.encoding = .finite) :
    (castWithStatus src dst x mode).status.invalid = true := by
  simp [castWithStatus, hnan, isNaN_eq_false_of_encoding_finite hdst, outcomeWithInvalid]

/-- Exact widening preserves the sign bit. -/
theorem signBit_widenExact {src dst : FloatFormat} (x : Model src)
    (hexp : src.expWidth = dst.expWidth)
    (hbias : src.exponentBias = dst.exponentBias)
    (hencoding : src.encoding = dst.encoding)
    (hfrac : src.fracWidth ≤ dst.fracWidth) :
    signBit (widenExact x hexp hbias hencoding hfrac) = signBit x := by
  simp [widenExact]

/-- Exact widening preserves the biased exponent field. -/
theorem expField_widenExact {src dst : FloatFormat} (x : Model src)
    (hexp : src.expWidth = dst.expWidth)
    (hbias : src.exponentBias = dst.exponentBias)
    (hencoding : src.encoding = dst.encoding)
    (hfrac : src.fracWidth ≤ dst.fracWidth) :
    expField (widenExact x hexp hbias hencoding hfrac) = expField x := by
  have hbound : expField x < 2 ^ dst.expWidth := by
    simpa [← hexp] using expField_lt_pow2 x
  simp [widenExact, Nat.mod_eq_of_lt hbound]

/-- Exact widening shifts the stored fraction into the high end of the destination field. -/
theorem fracField_widenExact {src dst : FloatFormat} (x : Model src)
    (hexp : src.expWidth = dst.expWidth)
    (hbias : src.exponentBias = dst.exponentBias)
    (hencoding : src.encoding = dst.encoding)
    (hfrac : src.fracWidth ≤ dst.fracWidth) :
    fracField (widenExact x hexp hbias hencoding hfrac) =
      Nat.shiftLeft (fracField x) (dst.fracWidth - src.fracWidth) := by
  have hfield := fracField_lt_pow2 x
  have hwidth : src.fracWidth + (dst.fracWidth - src.fracWidth) = dst.fracWidth := by
    omega
  have hbound : Nat.shiftLeft (fracField x) (dst.fracWidth - src.fracWidth) <
      2 ^ dst.fracWidth := by
    simpa [Nat.shiftLeft_eq, ← pow_add, hwidth] using
    (Nat.mul_lt_mul_of_pos_right hfield (Nat.two_pow_pos
      (dst.fracWidth - src.fracWidth)))
  rw [widenExact, fracField_ofFields, Nat.mod_eq_of_lt hbound]

/-- A finite value remains finite under exact widening. -/
theorem isFinite_widenExact {src dst : FloatFormat} (x : Model src)
    (hexp : src.expWidth = dst.expWidth)
    (hbias : src.exponentBias = dst.exponentBias)
    (hencoding : src.encoding = dst.encoding)
    (hfrac : src.fracWidth ≤ dst.fracWidth)
    (hx : isFinite x = true) :
    isFinite (widenExact x hexp hbias hencoding hfrac) = true := by
  let shift := dst.fracWidth - src.fracWidth
  have hexpDst : expField x < 2 ^ dst.expWidth := by
    simpa [← hexp] using expField_lt_pow2 x
  have hfracDst : Nat.shiftLeft (fracField x) shift < 2 ^ dst.fracWidth := by
    have hwidth : src.fracWidth + shift = dst.fracWidth := by
      dsimp [shift]
      omega
    simpa [Nat.shiftLeft_eq, ← pow_add, hwidth] using
      Nat.mul_lt_mul_of_pos_right (fracField_lt_pow2 x) (Nat.two_pow_pos shift)
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
`dst.fracWidth - src.fracWidth`; the destination scale loses
the same number of powers of two, so the represented real number is unchanged.
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
  have hexpDst : expField x < 2 ^ dst.expWidth := by
    simpa [← hexp] using expField_lt_pow2 x
  have hfracDst : Nat.shiftLeft (fracField x) shift < 2 ^ dst.fracWidth := by
    simpa [Nat.shiftLeft_eq, ← pow_add, hwidth] using
      Nat.mul_lt_mul_of_pos_right (fracField_lt_pow2 x) (Nat.two_pow_pos shift)
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
    · simp [hexponent, hfraction, Nat.shiftLeft_eq] at hxdecode hydecode
      rw [toReal_eq, hydecode, toReal_eq, hxdecode]
    · simp [hexponent, hfraction, Nat.shiftLeft_eq] at hxdecode hydecode
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
    (hr : FloatLib.Floats.Formats.Flocq.genericFormat FloatLib.Numerics.binaryRadix
      (fexpOf src) r) :
    FloatLib.Floats.Formats.Flocq.genericFormat FloatLib.Numerics.binaryRadix
      (fexpOf dst) r := by
  exact FloatLib.Floats.Formats.Flocq.generic_inclusion
    (fexpOf_le_of_gridExtension hfrac hmin) hr

/-- Equal biases and increased precision preserve the entire rounded-real grid. -/
theorem genericFormat_of_compatibleWidening {src dst : FloatFormat}
    (hbias : src.exponentBias = dst.exponentBias)
    (hfrac : src.fracWidth ≤ dst.fracWidth) {r : ℝ}
    (hr : FloatLib.Floats.Formats.Flocq.genericFormat FloatLib.Numerics.binaryRadix
      (fexpOf src) r) :
    FloatLib.Floats.Formats.Flocq.genericFormat FloatLib.Numerics.binaryRadix
      (fexpOf dst) r := by
  apply genericFormat_of_gridExtension hfrac ?_ hr
  simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
    Int.ofNat_eq_natCast, hbias]
  omega

/-- Compatible finite widening preserves the complete field encoding, including signed zero. -/
theorem cast_eq_widenExact_of_compatibleWidening {src dst : FloatFormat} (x : Model src)
    (hexp : src.expWidth = dst.expWidth)
    (hbias : src.exponentBias = dst.exponentBias)
    (hencoding : src.encoding = dst.encoding)
    (hfrac : src.fracWidth ≤ dst.fracWidth)
    (hx : isFinite x = true) :
    cast src dst x = widenExact x hexp hbias hencoding hfrac := by
  have hnan := isNaN_eq_false_of_isFinite_eq_true x hx
  have hinf := isInf_eq_false_of_isFinite_eq_true x hx
  by_cases hformat : src = dst
  · subst dst
    simp [cast, hnan, hinf, widenExact, ofFields_signBit_expField_fracField]
  · simp [cast, hnan, hinf, hformat, hexp, hbias, hencoding, hfrac]

/-- Every rounding mode uses the same bit-exact compatible finite widening. -/
theorem castWithRounding_eq_widenExact_of_compatibleWidening {src dst : FloatFormat}
    (x : Model src) (mode : IEEERoundingMode)
    (hexp : src.expWidth = dst.expWidth)
    (hbias : src.exponentBias = dst.exponentBias)
    (hencoding : src.encoding = dst.encoding)
    (hfrac : src.fracWidth ≤ dst.fracWidth)
    (hx : isFinite x = true) :
    castWithRounding src dst x mode = widenExact x hexp hbias hencoding hfrac := by
  have hnan := isNaN_eq_false_of_isFinite_eq_true x hx
  have hinf := isInf_eq_false_of_isFinite_eq_true x hx
  have hcast := cast_eq_widenExact_of_compatibleWidening x hexp hbias hencoding hfrac hx
  by_cases hformat : src = dst
  · subst dst
    cases mode <;>
      simp [castWithRounding, hnan, hinf, hcast, widenExact,
        ofFields_signBit_expField_fracField]
  · cases mode <;>
      simp [castWithRounding, hnan, hinf, hcast, hformat, hexp, hbias, hencoding, hfrac]

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

/--
For conventional IEEE source and destination formats, executable casting refines one nearest-even
rounding step in the destination's real-valued model.
-/
theorem cast_eq_roundAt {src dst : FloatFormat}
    (hsrc : src.isIEEE = true) (hdst : dst.isIEEE = true) (x : Model src)
    (hx : isFinite x = true) (hxy : isFinite (cast src dst x) = true) :
    toReal (cast src dst x) = roundAt dst (toReal x) := by
  have hnan := isNaN_eq_false_of_isFinite_eq_true x hx
  have hinf := isInf_eq_false_of_isFinite_eq_true x hx
  obtain ⟨hsrcEncoding, hsrcBias⟩ :=
    (FloatFormat.isIEEE_eq_true_iff src).mp hsrc
  obtain ⟨hdstEncoding, hdstBias⟩ :=
    (FloatFormat.isIEEE_eq_true_iff dst).mp hdst
  by_cases hformat : src = dst
  · subst dst
    simpa [cast, hnan, hinf] using (roundAt_toReal_eq x hx).symm
  · by_cases hexpWidth : src.expWidth = dst.expWidth
    · by_cases hfracWidth : src.fracWidth ≤ dst.fracWidth
      · have hbias : src.exponentBias = dst.exponentBias := by
          rw [hsrcBias, hdstBias]
          simp [FloatFormat.bias, hexpWidth]
        have hencoding : src.encoding = dst.encoding :=
          hsrcEncoding.trans hdstEncoding.symm
        have hcast :
            cast src dst x =
              widenExact x hexpWidth hbias hencoding hfracWidth := by
          simp [cast, hnan, hinf, hformat, hexpWidth, hbias, hencoding, hfracWidth]
        rw [hcast, toReal_widenExact x hexpWidth hbias hencoding hfracWidth hx]
        exact (FloatLib.Floats.Formats.Flocq.round_preserves_generic
          FloatLib.Floats.Formats.Flocq.nearestEven (toReal x)
          (genericFormat_of_compatibleWidening hbias hfracWidth
            (toReal_genericFormat_of_isFinite x hx))).symm
      · obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite hx
        have hcast : cast src dst x = roundDyadic dst d := by
          simp [cast, hnan, hinf, hformat, hexpWidth, hfracWidth, hd]
        rw [hcast] at hxy ⊢
        rw [toReal_roundDyadic_eq_roundAt dst hdst d hxy]
        congr 1
        rw [toReal_eq, hd]
    · obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite hx
      have hcast : cast src dst x = roundDyadic dst d := by
          simp [cast, hnan, hinf, hformat, hexpWidth, hd]
      rw [hcast] at hxy ⊢
      rw [toReal_roundDyadic_eq_roundAt dst hdst d hxy]
      congr 1
      rw [toReal_eq, hd]

/--
Conventional IEEE casting into a finer dyadic grid is exact whenever the executable result is
finite. This permits a wider exponent field and covers the usual exact standard-format widening
conversions.
-/
theorem cast_exact_of_gridExtension {src dst : FloatFormat} (x : Model src)
    (hsrc : src.isIEEE = true) (hdst : dst.isIEEE = true)
    (hfrac : src.fracWidth ≤ dst.fracWidth)
    (hmin : dst.minSubnormalExponent ≤ src.minSubnormalExponent)
    (hx : isFinite x = true) (hxy : isFinite (cast src dst x) = true) :
    toReal (cast src dst x) = toReal x := by
  rw [cast_eq_roundAt hsrc hdst x hx hxy]
  exact FloatLib.Floats.Formats.Flocq.round_preserves_generic
    FloatLib.Floats.Formats.Flocq.nearestEven (toReal x)
    (genericFormat_of_gridExtension hfrac hmin
      (toReal_genericFormat_of_isFinite x hx))

end Model
end FloatLib.Floats.Formats.BinaryInterchange
