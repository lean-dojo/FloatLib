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

The sign and quiet-NaN bits occupy distinct positions for every binary descriptor. Consequently
encoded absolute value preserves signaling status and payload. In a signed-zero format it also
clears the sign of every value, giving the exact-value bridge used by magnitude ordering.
Unsigned-zero formats preserve their reserved NaN word under encoded absolute value.
The bridge therefore requires a format that supports signed zero.
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

private theorem signaling_copySign {fmt : FloatFormat} (x y : Model fmt) :
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

/-- In a signed-zero format, encoded absolute value clears exactly the decoded dyadic sign. -/
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
      · have hnan : isNaN x = true := by
          cases hn : isNaN x
          · have hf := isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x hn hinf
            have := toDyadic?_isSome_eq_isFinite x
            simp [hd, hf] at this
          · rfl
        rw [exactValue_eq_nan_of_isNaN hnan,
          exactValue_eq_nan_of_isNaN (by simpa using hnan)]
        rw [signBit_abs_of_supportsSignedZero x hfmt]
        simp [ExactValue.abs, abs, signaling_copySign]
      · rw [exactValue_eq_infinity_of_isInf hinf,
          exactValue_eq_infinity_of_isInf (by simpa using hinf)]
        simp [ExactValue.abs, signBit_abs_of_supportsSignedZero x hfmt]

end FloatLib.Floats.Formats.BinaryInterchange.Model
