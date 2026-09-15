/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.LeanModel
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.SignedSemantics.Core

/-!
# Addition and subtraction through Lean's floating-point model

The exact dyadic addition used by FloatLib and Lean's unpacked addition align the operands at
the smaller exponent before rounding once. Their agreement includes cancellation to positive
zero and overflow to infinity. A descriptor must have the conventional IEEE encoding and bias.
These bridges are checked against the logical floating-point model shipped with Lean 4.34.

NaN payloads require care at the native boundary: FloatLib propagates a quieted payload, whereas
Lean's unpacked model has a single NaN.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open Float.Model.UnpackedFloat

private theorem round_natAbs_eq_normalize (spec : Float.Model.Format)
    (mantissa exponent : Int) :
    Float.Model.UnpackedFloat.round spec (modelSign (mantissa < 0))
        mantissa.natAbs exponent =
      Float.Model.UnpackedFloat.normalize spec mantissa exponent .positive := by
  unfold Float.Model.UnpackedFloat.normalize
  split <;> rename_i hcompare
  · have hnegative := Int.compare_eq_lt.mp hcompare
    have habs : mantissa.natAbs = (-mantissa).toNat := by omega
    simp [modelSign, hnegative, habs]
  · have hzero := Int.compare_eq_eq.mp hcompare
    subst mantissa
    simp [modelSign]
  · have hpositive := Int.compare_eq_gt.mp hcompare
    have habs : mantissa.natAbs = mantissa.toNat := by omega
    simp [modelSign, not_lt.mpr hpositive.le, habs]

private theorem round_addFields_eq_normalize
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign₁ sign₂ : Bool) (mantissa₁ mantissa₂ : Nat) (exponent : Int)
    (hmantissa₁ : 0 < mantissa₁) (hmantissa₂ : 0 < mantissa₂) :
    roundDyadic fmt
        (FloatLib.Numerics.Dyadic.addFields
          sign₁ mantissa₁ exponent sign₂ mantissa₂ exponent) =
      ofModel fmt
        (Float.Model.UnpackedFloat.normalize (FloatFormat.toModel fmt)
          ((modelSign sign₁).apply mantissa₁ + (modelSign sign₂).apply mantissa₂)
          exponent .positive) := by
  unfold FloatLib.Numerics.Dyadic.addFields
  simp only [beq_iff_eq, hmantissa₁.ne', hmantissa₂.ne', ite_false,
    le_refl, ite_true, sub_self, Int.toNat_zero]
  cases sign₁ <;> cases sign₂ <;>
    simp only [Bool.false_eq_true, eq_self, ite_false, ite_true,
      modelSign_false, modelSign_true, Sign.apply]
  all_goals
    split_ifs with hzero
    · simp only [roundDyadic, hfmt, ite_true, ieeeRoundDyadic,
        Bool.false_and, Bool.true_and, modelSign_false, modelSign_true,
        round_exact_zero]
      simp_all [Float.Model.UnpackedFloat.normalize] <;> omega
    · simp only [roundDyadic, hfmt, ite_true, ieeeRoundDyadic]
      rw [← round_natAbs_eq_normalize]
      rfl

private theorem round_addDyadic_eq_ofModel_add_finite
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign₁ sign₂ : Sign) (mantissa₁ mantissa₂ : Nat) (exponent₁ exponent₂ : Int)
    (hmantissa₁ : 0 < mantissa₁) (hmantissa₂ : 0 < mantissa₂) :
    roundDyadic fmt
        (addDyadic
          ⟨modelSignBit sign₁, mantissa₁, exponent₁⟩
          ⟨modelSignBit sign₂, mantissa₂, exponent₂⟩) =
      ofModel fmt
        (Float.Model.UnpackedFloat.add (FloatFormat.toModel fmt)
          (.finite sign₁ mantissa₁ exponent₁ hmantissa₁)
          (.finite sign₂ mantissa₂ exponent₂ hmantissa₂)) := by
  have hsign (sign : Sign) : modelSign (modelSignBit sign) = sign := by
    cases sign <;> rfl
  by_cases hexponents : exponent₁ ≤ exponent₂
  · rw [addDyadic, FloatLib.Numerics.Dyadic.add_align_right_to_left_exponent
      _ _ _ _ _ _ hmantissa₁.ne' hmantissa₂.ne' hexponents]
    have hshifted : 0 < mantissa₂ <<< (exponent₂ - exponent₁).toNat :=
      Nat.shiftLeft_pos_iff.mpr hmantissa₂
    simpa only [FloatLib.Numerics.Dyadic.add, Float.Model.UnpackedFloat.add,
      min_eq_left hexponents, Float.Model.UnpackedFloat.decreaseExponent,
      sub_self, Int.toNat_zero, Nat.shiftLeft_eq', Nat.shiftLeft_zero, hsign] using
      round_addFields_eq_normalize fmt hfmt (modelSignBit sign₁) (modelSignBit sign₂)
        mantissa₁ (mantissa₂ <<< (exponent₂ - exponent₁).toNat) exponent₁
        hmantissa₁ hshifted
  · have hlt : exponent₂ < exponent₁ := lt_of_not_ge hexponents
    rw [addDyadic, FloatLib.Numerics.Dyadic.add_align_left_to_right_exponent
      _ _ _ _ _ _ hmantissa₁.ne' hmantissa₂.ne' hlt]
    have hshifted : 0 < mantissa₁ <<< (exponent₁ - exponent₂).toNat :=
      Nat.shiftLeft_pos_iff.mpr hmantissa₁
    simpa only [FloatLib.Numerics.Dyadic.add, Float.Model.UnpackedFloat.add,
      min_eq_right hlt.le, Float.Model.UnpackedFloat.decreaseExponent,
      sub_self, Int.toNat_zero, Nat.shiftLeft_eq', Nat.shiftLeft_zero, hsign] using
      round_addFields_eq_normalize fmt hfmt (modelSignBit sign₁) (modelSignBit sign₂)
        (mantissa₁ <<< (exponent₁ - exponent₂).toNat) mantissa₂ exponent₂
        hshifted hmantissa₂

/--
For finite nonzero operands, dispatched addition commutes with Lean's unpacked addition and
packing. The result may be zero or infinity; no finiteness assumption on the sum is needed.
-/
theorem add_eq_ofModel_add_of_toModel_finite
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true) (x y : Model fmt)
    (sign₁ sign₂ : Sign) (mantissa₁ mantissa₂ : Nat) (exponent₁ exponent₂ : Int)
    (hmantissa₁ : 0 < mantissa₁) (hmantissa₂ : 0 < mantissa₂)
    (hx : toModel x = .finite sign₁ mantissa₁ exponent₁ hmantissa₁)
    (hy : toModel y = .finite sign₂ mantissa₂ exponent₂ hmantissa₂) :
    add x y =
      ofModel fmt
        (Float.Model.UnpackedFloat.add (FloatFormat.toModel fmt) (toModel x) (toModel y)) := by
  rw [Proof.add_eq_spec, Spec.add, toDyadic?_ieee_eq_model fmt hfmt x,
    toDyadic?_ieee_eq_model fmt hfmt y, hx, hy]
  exact round_addDyadic_eq_ofModel_add_finite fmt hfmt
    sign₁ sign₂ mantissa₁ mantissa₂ exponent₁ exponent₂ hmantissa₁ hmantissa₂

/-- Lean's unpacked subtraction is addition after exact negation, including exceptional values. -/
theorem unpacked_sub_eq_add_neg (spec : Float.Model.Format)
    (x y : Float.Model.UnpackedFloat) :
    Float.Model.UnpackedFloat.sub spec x y =
      Float.Model.UnpackedFloat.add spec x (Float.Model.UnpackedFloat.neg y) := by
  have hsign (sign : Sign) (mantissa : Int) :
      (-sign).apply mantissa = -(sign.apply mantissa) := by
    cases sign <;> simp [Sign.apply]
  cases x <;> cases y <;>
    simp [Float.Model.UnpackedFloat.sub, Float.Model.UnpackedFloat.add,
      Float.Model.UnpackedFloat.neg, hsign, sub_eq_add_neg]

/--
For finite nonzero operands, dispatched subtraction commutes with Lean's unpacked subtraction
and packing, including exact cancellation and overflow.
-/
theorem sub_eq_ofModel_sub_of_toModel_finite
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true) (x y : Model fmt)
    (sign₁ sign₂ : Sign) (mantissa₁ mantissa₂ : Nat) (exponent₁ exponent₂ : Int)
    (hmantissa₁ : 0 < mantissa₁) (hmantissa₂ : 0 < mantissa₂)
    (hx : toModel x = .finite sign₁ mantissa₁ exponent₁ hmantissa₁)
    (hy : toModel y = .finite sign₂ mantissa₂ exponent₂ hmantissa₂) :
    sub x y =
      ofModel fmt
        (Float.Model.UnpackedFloat.sub (FloatFormat.toModel fmt) (toModel x) (toModel y)) := by
  have hdy : toDyadic? y =
      some ⟨modelSignBit sign₂, mantissa₂, exponent₂⟩ := by
    rw [toDyadic?_ieee_eq_model fmt hfmt y, hy]
    rfl
  have hneg := toDyadic?_neg_of_toDyadic?_some y hdy
  have hsign : modelSignBit (-sign₂) = !(modelSignBit sign₂) := by
    cases sign₂ <;> rfl
  have hnonzero : (mantissa₂ == 0) = false := by simp [hmantissa₂.ne']
  change toDyadic? (neg y) =
    some (if mantissa₂ == 0 && !fmt.supportsSignedZero then
      FloatLib.Numerics.Dyadic.zero else
      ⟨!(modelSignBit sign₂), mantissa₂, exponent₂⟩) at hneg
  simp only [hnonzero, Bool.false_and, Bool.false_eq_true,
    ite_false, ← hsign] at hneg
  rw [Proof.sub_eq_spec, Spec.sub, Spec.add,
    toDyadic?_ieee_eq_model fmt hfmt x, hx, hneg, hy, unpacked_sub_eq_add_neg]
  simp only [Float.Model.UnpackedFloat.neg]
  exact round_addDyadic_eq_ofModel_add_finite fmt hfmt
    sign₁ (-sign₂) mantissa₁ mantissa₂ exponent₁ exponent₂ hmantissa₁ hmantissa₂

end FloatLib.Floats.Formats.BinaryInterchange.Model
