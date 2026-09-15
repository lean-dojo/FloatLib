/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.TotalOrder.ExactValue
import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Classification
import FloatLib.Floats.Formats.BinaryInterchange.Model.Fields.Proof

/-!
# Complete exact data determine binary encodings

Finite decoding is injective because subnormal significands lie below the implicit leading bit,
whereas normal significands include it. Within either class the exact dyadic recovers the fields.
For exceptional values, the encoding policy and the stored sign and fraction complete
the reconstruction. This injectivity transfers antisymmetry from complete exact data to words.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

/-- Equality of all interchange fields determines the stored word. -/
theorem eq_of_signBit_expField_fracField_eq {fmt : FloatFormat} {x y : Model fmt}
    (hsign : signBit x = signBit y) (hexponent : expField x = expField y)
    (hfraction : fracField x = fracField y) : x = y := by
  rw [← ofFields_signBit_expField_fracField x,
    ← ofFields_signBit_expField_fracField y, hsign, hexponent, hfraction]

/-- Two words decoding to the same complete dyadic have identical encodings. -/
theorem eq_of_toDyadic?_eq_some {fmt : FloatFormat} {x y : Model fmt}
    {d : Numerics.Dyadic} (hx : toDyadic? x = some d) (hy : toDyadic? y = some d) :
    x = y := by
  have hsign : signBit x = signBit y :=
    (sign_eq_signBit_of_toDyadic?_some hx).symm.trans
      (sign_eq_signBit_of_toDyadic?_some hy)
  have shape (z : Model fmt) (hz : isFinite z = true) :=
    toDyadic?_ofFields_of_isFinite fmt (signBit z) (expField z) (fracField z)
      (expField_lt_pow2 z) (fracField_lt_pow2 z)
      (by simpa only [ofFields_signBit_expField_fracField] using hz)
  have hxshape := shape x (isFinite_eq_true_of_toDyadic?_some hx)
  have hyshape := shape y (isFinite_eq_true_of_toDyadic?_some hy)
  rw [ofFields_signBit_expField_fracField, hx] at hxshape
  rw [ofFields_signBit_expField_fracField, hy] at hyshape
  have hfields := congrArg
    (fun v : Option Numerics.Dyadic => v.map (fun d => (d.significand, d.exponent)))
    (hxshape.symm.trans hyshape)
  have hxfrac := fracField_lt_pow2 x
  have hyfrac := fracField_lt_pow2 y
  have hpow : 0 < pow2 fmt.fracWidth := by simp [pow2_eq_two_pow]
  have hsame : expField x = expField y ∧ fracField x = fracField y := by
    split_ifs at hfields <;>
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq,
        pow2_eq_two_pow] at hfields <;>
      first
      | omega
      | exact ⟨Int.ofNat.inj (Int.sub_left_inj _ |>.mp
          (Int.sub_left_inj _ |>.mp hfields.2)), Nat.add_left_cancel hfields.1⟩
  exact eq_of_signBit_expField_fracField_eq hsign hsame.1 hsame.2

/-- Classification as NaN exposes all the exact metadata used by total ordering. -/
theorem exactValue_eq_nan_of_isNaN {fmt : FloatFormat} {x : Model fmt}
    (hx : isNaN x = true) :
    exactValue x = .nan (signBit x) (isSNaN x) (fracField x) := by
  have hdecode := toDyadic?_eq_none_of_isNaN hx
  have hinf : isInf x = false := by
    cases he : fmt.encoding <;> simp_all [isNaN, isInf, IEEE.isNaN, IEEE.isInf]
  simp [exactValue, hdecode, hinf]

/-- Infinity decoding retains exactly its sign. -/
theorem exactValue_eq_infinity_of_isInf {fmt : FloatFormat} {x : Model fmt}
    (hx : isInf x = true) : exactValue x = .infinity (signBit x) := by
  have hdecode : toDyadic? x = none := by
    cases hd : toDyadic? x with
    | none => rfl
    | some d =>
        have := isInf_eq_false_of_toDyadic?_some hd
        simp [hx] at this
  simp [exactValue, hdecode, hx]

/-- Complete exact interpretation is injective for every binary format descriptor. -/
theorem exactValue_injective {fmt : FloatFormat} :
    Function.Injective (exactValue (fmt := fmt)) := by
  intro x y h
  cases hx : toDyadic? x with
  | some d =>
      have hexact : exactValue y = .finite d := by simpa [exactValue, hx] using h.symm
      exact eq_of_toDyadic?_eq_some hx (exactValue_eq_finite_iff.mp hexact)
  | none =>
      cases hy : toDyadic? y with
      | some d =>
          have hexact : exactValue x = .finite d := by simpa [exactValue, hy] using h
          have := exactValue_eq_finite_iff.mp hexact
          simp [hx] at this
      | none =>
          cases hi : isInf x <;> cases hj : isInf y <;>
            simp only [exactValue, hx, hy, hi, hj, Bool.false_eq_true, ite_false,
              ite_true, ExactValue.nan.injEq, ExactValue.infinity.injEq,
              reduceCtorEq] at h
          · have hxf : isFinite x = false := by
              simpa [hx] using (toDyadic?_isSome_eq_isFinite x).symm
            have hyf : isFinite y = false := by
              simpa [hy] using (toDyadic?_isSome_eq_isFinite y).symm
            cases hfmt : fmt.encoding with
            | ieee =>
                have hxe : expField x = fmt.expAllOnesNat := by
                  simpa [isFinite, hfmt, IEEE.isFinite] using hxf
                have hye : expField y = fmt.expAllOnesNat := by
                  simpa [isFinite, hfmt, IEEE.isFinite] using hyf
                exact eq_of_signBit_expField_fracField_eq h.1 (hxe.trans hye.symm) h.2.2
            | finiteMaxNaN =>
                have hxe : expField x = fmt.expAllOnesNat ∧ fracField x = fmt.fracMaskNat := by
                  simpa [isFinite, isNaN, hfmt] using hxf
                have hye : expField y = fmt.expAllOnesNat ∧ fracField y = fmt.fracMaskNat := by
                  simpa [isFinite, isNaN, hfmt] using hyf
                exact eq_of_signBit_expField_fracField_eq h.1 (hxe.1.trans hye.1.symm) h.2.2
            | finiteUnsignedZero =>
                have hxb : x.bits = fmt.signMask := by
                  simpa [isFinite, isNaN, hfmt] using hxf
                have hyb : y.bits = fmt.signMask := by
                  simpa [isFinite, isNaN, hfmt] using hyf
                exact congrArg (ofBits (fmt := fmt)) (hxb.trans hyb.symm)
            | finite => simp [isFinite, hfmt] at hxf
          · have hfmt : fmt.encoding = .ieee := by
              cases he : fmt.encoding <;> simp_all [isInf]
            have hxf : expField x = fmt.expAllOnesNat ∧ fracField x = 0 := by
              simpa [isInf, hfmt, IEEE.isInf] using hi
            have hyf : expField y = fmt.expAllOnesNat ∧ fracField y = 0 := by
              simpa [isInf, hfmt, IEEE.isInf] using hj
            exact eq_of_signBit_expField_fracField_eq h
              (hxf.1.trans hyf.1.symm) (hxf.2.trans hyf.2.symm)

end FloatLib.Floats.Formats.BinaryInterchange.Model
