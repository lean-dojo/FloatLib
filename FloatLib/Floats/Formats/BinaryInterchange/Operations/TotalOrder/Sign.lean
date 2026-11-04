/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.TotalOrder.Encoding
import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.SignedSemantics.Core

/-!
# Exact absolute values and encoded sign operations

For every binary descriptor the sign bit and the quiet-NaN bit sit in different positions. So
encoded absolute value keeps the signaling status (`isSNaN_abs`) and the fraction field that
carries a NaN's payload (`fracField_abs`). In a signed-zero format it also clears the sign of every
value, which gives magnitude ordering its exact-value bridge (`toDyadic?_abs_of_supportsSignedZero`,
`exactValue_abs_of_supportsSignedZero`).

Without signed zeros, absolute value leaves every NaN and zero unchanged
(`abs_eq_self_of_not_supportsSignedZero_of_isNaN`,
`abs_eq_self_of_not_supportsSignedZero_of_isZero`). The unsigned-zero encoding marks its reserved
NaN word with a set sign bit, and absolute value keeps that word instead of turning it into the
zero. The bridge therefore requires a format that supports signed zero.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

private theorem quietBits_toggleSign {fmt : FloatFormat} (x : Model fmt) :
    (toggleSign x).bits &&& fmt.quietBit = x.bits &&& fmt.quietBit := by
  change (x.bits ^^^ fmt.signMask) &&& fmt.quietBit = x.bits &&& fmt.quietBit
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor,
    FloatFormat.quietBit, FloatFormat.quietBitNat, FloatFormat.signMask,
    FloatFormat.signMaskNat, FloatFormat.signBitIndex, FloatFormat.ofWordNat,
    BitVec.getLsbD_ofNat]
  by_cases hquiet : i = fmt.fracWidth - 1
  · subst i
    have hne : fmt.bitWidth - 1 ≠ fmt.fracWidth - 1 := by
      have := fmt.fracWidth_pos
      have := fmt.expWidth_ge_two
      unfold FloatFormat.bitWidth
      omega
    simp [hi, Nat.testBit_two_pow_of_ne hne]
  · simp [Nat.testBit_two_pow_of_ne (Ne.symm hquiet)]

/-- Copying a sign preserves signaling status under every encoding policy. -/
@[simp] theorem isSNaN_copySign {fmt : FloatFormat} (x y : Model fmt) :
    isSNaN (copySign x y) = isSNaN x := by
  cases he : fmt.encoding with
  | ieee =>
      have hs : fmt.supportsSignedZero = true := by
        simp [FloatFormat.supportsSignedZero, he]
      by_cases hsign : signBit x = signBit y
      · simp [copySign, hs, hsign]
      · simp [copySign, hs, hsign, isSNaN, he, IEEE.isSNaN, IEEE.isNaN,
          quietBits_toggleSign]
  | finiteMaxNaN | finiteUnsignedZero | finite => simp [isSNaN, he]

/-- Absolute value preserves signaling status under every encoding policy. -/
@[simp] theorem isSNaN_abs {fmt : FloatFormat} (x : Model fmt) :
    isSNaN (abs x) = isSNaN x :=
  isSNaN_copySign x (posZero fmt)

/-- Absolute value preserves the fraction field, which carries a NaN's payload. -/
@[simp] theorem fracField_abs {fmt : FloatFormat} (x : Model fmt) :
    fracField (abs x) = fracField x :=
  fracField_copySign x (posZero fmt)

/--
Without signed zeros, absolute value leaves a NaN unchanged. The unsigned-zero NaN is the word with
only the sign bit set, so clearing that bit would turn it into the zero.
-/
theorem abs_eq_self_of_not_supportsSignedZero_of_isNaN {fmt : FloatFormat}
    (x : Model fmt) (hfmt : fmt.supportsSignedZero = false) (hx : isNaN x = true) :
    abs x = x := by
  simp [abs, copySign, hfmt, hx]

/-- Without signed zeros, absolute value leaves the single zero unchanged. -/
theorem abs_eq_self_of_not_supportsSignedZero_of_isZero {fmt : FloatFormat}
    (x : Model fmt) (hfmt : fmt.supportsSignedZero = false) (hx : isZero x = true) :
    abs x = x := by
  simp [abs, copySign, hfmt, hx]

/-- In a signed-zero format, encoded absolute value clears the decoded dyadic sign and no more. -/
theorem toDyadic?_abs_of_supportsSignedZero {fmt : FloatFormat} {x : Model fmt}
    (hfmt : fmt.supportsSignedZero = true) {d : Numerics.Dyadic}
    (hx : toDyadic? x = some d) :
    toDyadic? (abs x) = some { d with negative := false } := by
  have hsign := sign_eq_signBit_of_toDyadic?_some hx
  cases hs : signBit x
  · have hd : d.negative = false := hsign.trans hs
    have habs : abs x = x := by simp [abs, copySign, hfmt, hs]
    simpa [habs, ← hd] using hx
  · have hd : d.negative = true := hsign.trans hs
    have habs : abs x = neg x := by
      simp [abs, copySign, hfmt, hs, neg_eq_toggleSign_of_supportsSignedZero x hfmt]
    rw [habs]
    simpa [negDyadic, hfmt, hd] using toDyadic?_neg_of_toDyadic?_some x hx

/-- Exact interpretation commutes with absolute value whenever every sign can be cleared. -/
theorem exactValue_abs_of_supportsSignedZero {fmt : FloatFormat} (x : Model fmt)
    (hfmt : fmt.supportsSignedZero = true) :
    exactValue (abs x) = ExactValue.abs (exactValue x) := by
  cases hd : toDyadic? x with
  | some d =>
      rw [exactValue_eq_finite_of_toDyadic?_eq_some hd,
        exactValue_eq_finite_of_toDyadic?_eq_some
          (toDyadic?_abs_of_supportsSignedZero hfmt hd)]
      rfl
  | none =>
      cases hinf : isInf x
      · have hnan := isNaN_eq_true_of_toDyadic?_eq_none_of_isInf_eq_false hd hinf
        rw [exactValue_eq_nan_of_isNaN hnan,
          exactValue_eq_nan_of_isNaN (by simpa using hnan)]
        rw [signBit_abs_of_supportsSignedZero x hfmt]
        simp [ExactValue.abs, abs, isSNaN_copySign]
      · rw [exactValue_eq_infinity_of_isInf hinf,
          exactValue_eq_infinity_of_isInf (by simpa using hinf)]
        simp [ExactValue.abs, signBit_abs_of_supportsSignedZero x hfmt]

end FloatLib.Floats.Formats.BinaryInterchange.Model
