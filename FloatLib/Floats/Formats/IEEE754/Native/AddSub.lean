/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.LeanModel.AddSub
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.Instances
public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.Representation
public import FloatLib.Floats.Formats.IEEE754.Native.Representation
public import FloatLib.Floats.ExecFloat.Instances
public import FloatLib.Floats.ExecFloat.Proof.Arithmetic

/-!
# Native addition and subtraction

These bridges are checked against the logical floating-point model shipped with Lean 4.34.
Finite inputs include both signed zeros. The result is unrestricted: cancellation, subnormal
rounding, and overflow to infinity all preserve the complete packed word through the existing
native adapters.

The finite-input hypotheses exclude NaNs and infinities. FloatLib preserves NaN details that
Lean canonicalizes; subtraction also negates the right operand's NaN sign. These model
equalities do not verify the external machine instructions used by compiled native code.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open Float.Model.UnpackedFloat

private theorem round_decoded_eq_ofModel {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (x : Model fmt) {d : Numerics.Dyadic} (hd : toDyadic? x = some d) :
    roundDyadic fmt d = ofModel fmt (toModel x) := by
  have hcanonical : IsModelCanonical x := by
    constructor
    intro he hm
    have hnan : toModel x = .notANumber := by
      simp only [toModel, unpack, he, hm, ite_true, ite_false]
    rw [toDyadic?_ieee_eq_model fmt hfmt x, hnan] at hd
    cases hd
  change roundDyadicWithRounding fmt .nearestEven d = canonicalizeModel x
  rw [roundDyadicWithRounding_toDyadic? hfmt .nearestEven hd,
    canonicalizeModel_eq_self x hcanonical]

/--
For finite operands, including signed zeros, dispatched addition produces precisely the word
obtained by adding and packing in Lean's unpacked model. The result may overflow to infinity.
-/
theorem add_eq_ofModel_add_of_isFinite {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (x y : Model fmt) (hx : (toModel x).isFinite = true)
    (hy : (toModel y).isFinite = true) :
    add x y =
      ofModel fmt
        (Float.Model.UnpackedFloat.add (FloatFormat.toModel fmt) (toModel x) (toModel y)) := by
  cases hxmodel : toModel x <;> cases hymodel : toModel y <;>
    simp only [hxmodel, hymodel, Float.Model.UnpackedFloat.isFinite,
      Bool.false_eq_true] at hx hy
  case zero.zero sign₁ sign₂ =>
    rw [Proof.add_eq_spec, Spec.add, toDyadic?_ieee_eq_model fmt hfmt x,
      toDyadic?_ieee_eq_model fmt hfmt y, hxmodel, hymodel]
    cases sign₁ <;> cases sign₂ <;>
      simp [unpackedToDyadic?, addDyadic,
        roundDyadic, hfmt, ieeeRoundDyadic, Float.Model.UnpackedFloat.add,
        modelSignBit, modelSign]
  case zero.finite sign₁ sign₂ mantissa₂ exponent₂ hmantissa₂ =>
    have hd : toDyadic? y = some ⟨modelSignBit sign₂, mantissa₂, exponent₂⟩ := by
      rw [toDyadic?_ieee_eq_model fmt hfmt y, hymodel]
      rfl
    have hr := round_decoded_eq_ofModel hfmt y hd
    rw [hymodel] at hr
    rw [Proof.add_eq_spec, Spec.add, toDyadic?_ieee_eq_model fmt hfmt x, hxmodel, hd]
    simp only [unpackedToDyadic?, addDyadic, Float.Model.UnpackedFloat.add]
    rw [Numerics.Dyadic.add_of_left_significand_eq_zero _ _ rfl]
    simpa only [hmantissa₂.ne', ite_false] using hr
  case finite.zero sign₁ mantissa₁ exponent₁ hmantissa₁ sign₂ =>
    have hd : toDyadic? x = some ⟨modelSignBit sign₁, mantissa₁, exponent₁⟩ := by
      rw [toDyadic?_ieee_eq_model fmt hfmt x, hxmodel]
      rfl
    have hr := round_decoded_eq_ofModel hfmt x hd
    rw [hxmodel] at hr
    rw [Proof.add_eq_spec, Spec.add, hd, toDyadic?_ieee_eq_model fmt hfmt y, hymodel]
    simp only [unpackedToDyadic?, addDyadic, Float.Model.UnpackedFloat.add]
    rw [Numerics.Dyadic.add_of_right_significand_eq_zero _ _ rfl]
    simpa only [hmantissa₁.ne', ite_false] using hr
  case finite.finite sign₁ mantissa₁ exponent₁ hmantissa₁ sign₂ mantissa₂ exponent₂
      hmantissa₂ =>
    simpa only [hxmodel, hymodel] using add_eq_ofModel_add_of_toModel_finite hfmt x y
      sign₁ sign₂ mantissa₁ mantissa₂ exponent₁ exponent₂ hmantissa₁ hmantissa₂
      hxmodel hymodel

/-- Negation preserves the complete finite unpacked value, including the sign of zero. -/
theorem toModel_neg_of_isFinite {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (x : Model fmt) (hx : (toModel x).isFinite = true) :
    toModel (neg x) = Float.Model.UnpackedFloat.neg (toModel x) := by
  have hdecode {d : Numerics.Dyadic} (hd : toDyadic? x = some d) :
      ieeeToDyadic? (neg x) = some d.neg := by
    have hneg := toDyadic?_neg_of_toDyadic?_some x hd
    simpa [toDyadic?, hfmt, negDyadic,
      FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt hfmt] using hneg
  have hsign (sign : Sign) : modelSign (!(modelSignBit sign)) = -sign := by
    cases sign <;> rfl
  cases hmodel : toModel x with
  | notANumber => simp [hmodel, Float.Model.UnpackedFloat.isFinite] at hx
  | infinity sign => simp [hmodel, Float.Model.UnpackedFloat.isFinite] at hx
  | zero sign =>
    have hd : toDyadic? x = some ⟨modelSignBit sign, 0, 0⟩ := by
      rw [toDyadic?_ieee_eq_model fmt hfmt x, hmodel]
      rfl
    simpa only [hsign, Float.Model.UnpackedFloat.neg] using
      toModel_eq_zero_of_ieeeToDyadic?_eq_some (neg x) (!(modelSignBit sign)) 0
        (hdecode hd)
  | finite sign mantissa exponent hmantissa =>
    have hd : toDyadic? x = some ⟨modelSignBit sign, mantissa, exponent⟩ := by
      rw [toDyadic?_ieee_eq_model fmt hfmt x, hmodel]
      rfl
    simpa only [hsign, Float.Model.UnpackedFloat.neg] using
      toModel_eq_finite_of_ieeeToDyadic?_eq_some (neg x) (!(modelSignBit sign))
        mantissa exponent hmantissa.ne' (hdecode hd)

/--
For finite operands, including signed zeros, dispatched subtraction agrees with Lean's
unpacked subtraction and packing. There is no restriction on the rounded result.
-/
theorem sub_eq_ofModel_sub_of_isFinite {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (x y : Model fmt) (hx : (toModel x).isFinite = true)
    (hy : (toModel y).isFinite = true) :
    sub x y =
      ofModel fmt
        (Float.Model.UnpackedFloat.sub (FloatFormat.toModel fmt) (toModel x) (toModel y)) := by
  have hneg := toModel_neg_of_isFinite hfmt y hy
  have hfinite : (toModel (neg y)).isFinite = true := by
    rw [hneg]
    cases hmodel : toModel y <;>
      simp_all [Float.Model.UnpackedFloat.neg, Float.Model.UnpackedFloat.isFinite]
  rw [Proof.sub_eq_spec, Spec.sub, ← Proof.add_eq_spec,
    add_eq_ofModel_add_of_isFinite hfmt x (neg y) hx hfinite,
    hneg, unpacked_sub_eq_add_neg]

end FloatLib.Floats.Formats.BinaryInterchange.Model

namespace FloatLib.Floats.ExecFloat.Binary

open Formats.BinaryInterchange

/-- Native binary32 addition commutes with the existing import adapter for all finite inputs. -/
theorem toModel_ofFloat32_add_of_isFinite (x y : Float32)
    (hx : x.isFinite = true) (hy : y.isFinite = true) :
    toModel (ofFloat32 (x + y)) =
      Model.add (toModel (ofFloat32 x)) (toModel (ofFloat32 y)) := by
  rw [toModel_ofFloat32, toModel_ofFloat32, toModel_ofFloat32]
  change Model.ofFloat32Model (Float32.Model.add x.toModel y.toModel) = _
  rw [Float32.Model.add, Model.ofFloat32Model_pack]
  have h := Model.add_eq_ofModel_add_of_isFinite (fmt := FloatFormat.binary32)
    (by decide) (Model.ofFloat32Model x.toModel) (Model.ofFloat32Model y.toModel)
    (by simpa only [Model.toModel_ofFloat32Model, Float32.isFinite,
      Float32.Model.isFinite] using hx)
    (by simpa only [Model.toModel_ofFloat32Model, Float32.isFinite,
      Float32.Model.isFinite] using hy)
  rw [Model.toModel_ofFloat32Model, Model.toModel_ofFloat32Model] at h
  exact h.symm

/-- Native binary32 subtraction commutes with the import adapter, including signed-zero inputs. -/
theorem toModel_ofFloat32_sub_of_isFinite (x y : Float32)
    (hx : x.isFinite = true) (hy : y.isFinite = true) :
    toModel (ofFloat32 (x - y)) =
      Model.sub (toModel (ofFloat32 x)) (toModel (ofFloat32 y)) := by
  rw [toModel_ofFloat32, toModel_ofFloat32, toModel_ofFloat32]
  change Model.ofFloat32Model (Float32.Model.sub x.toModel y.toModel) = _
  rw [Float32.Model.sub, Model.ofFloat32Model_pack]
  have h := Model.sub_eq_ofModel_sub_of_isFinite (fmt := FloatFormat.binary32)
    (by decide) (Model.ofFloat32Model x.toModel) (Model.ofFloat32Model y.toModel)
    (by simpa only [Model.toModel_ofFloat32Model, Float32.isFinite,
      Float32.Model.isFinite] using hx)
    (by simpa only [Model.toModel_ofFloat32Model, Float32.isFinite,
      Float32.Model.isFinite] using hy)
  rw [Model.toModel_ofFloat32Model, Model.toModel_ofFloat32Model] at h
  exact h.symm

/-- Native binary64 addition commutes with the existing import adapter for all finite inputs. -/
theorem toModel_ofFloat_add_of_isFinite (x y : Float)
    (hx : x.isFinite = true) (hy : y.isFinite = true) :
    toModel (ofFloat (x + y)) =
      Model.add (toModel (ofFloat x)) (toModel (ofFloat y)) := by
  rw [toModel_ofFloat, toModel_ofFloat, toModel_ofFloat]
  change Model.ofFloatModel (Float.Model.add x.toModel y.toModel) = _
  rw [Float.Model.add, Model.ofFloatModel_pack]
  have h := Model.add_eq_ofModel_add_of_isFinite (fmt := FloatFormat.binary64)
    (by decide) (Model.ofFloatModel x.toModel) (Model.ofFloatModel y.toModel)
    (by simpa only [Model.toModel_ofFloatModel, Float.isFinite,
      Float.Model.isFinite] using hx)
    (by simpa only [Model.toModel_ofFloatModel, Float.isFinite,
      Float.Model.isFinite] using hy)
  rw [Model.toModel_ofFloatModel, Model.toModel_ofFloatModel] at h
  exact h.symm

/-- Native binary64 subtraction commutes with the import adapter, including signed-zero inputs. -/
theorem toModel_ofFloat_sub_of_isFinite (x y : Float)
    (hx : x.isFinite = true) (hy : y.isFinite = true) :
    toModel (ofFloat (x - y)) =
      Model.sub (toModel (ofFloat x)) (toModel (ofFloat y)) := by
  rw [toModel_ofFloat, toModel_ofFloat, toModel_ofFloat]
  change Model.ofFloatModel (Float.Model.sub x.toModel y.toModel) = _
  rw [Float.Model.sub, Model.ofFloatModel_pack]
  have h := Model.sub_eq_ofModel_sub_of_isFinite (fmt := FloatFormat.binary64)
    (by decide) (Model.ofFloatModel x.toModel) (Model.ofFloatModel y.toModel)
    (by simpa only [Model.toModel_ofFloatModel, Float.isFinite,
      Float.Model.isFinite] using hx)
    (by simpa only [Model.toModel_ofFloatModel, Float.isFinite,
      Float.Model.isFinite] using hy)
  rw [Model.toModel_ofFloatModel, Model.toModel_ofFloatModel] at h
  exact h.symm

private theorem toModel_execAdd {format : FloatFormat} {plan : Configured.StoragePlan format}
    [ExecFloat.Backend.PolicyFor (Configured.Family format (Configured.Code plan) plan)]
    (x y : ExecFloat (Configured.Family format (Configured.Code plan) plan)) :
    toModel (x + y) = Model.Spec.add (toModel x) (toModel y) := by
  change toModel (ExecFloat.add x y) = _
  rw [ExecFloat.Proof.add_eq_spec]
  change Configured.Family.toModel
    (ExecFloat.ModelCodec.liftBinary Model.Spec.add x y) = _
  simp [Configured.Family.toModel, toModel]

private theorem toModel_execSub {format : FloatFormat} {plan : Configured.StoragePlan format}
    [ExecFloat.Backend.PolicyFor (Configured.Family format (Configured.Code plan) plan)]
    (x y : ExecFloat (Configured.Family format (Configured.Code plan) plan)) :
    toModel (x - y) = Model.Spec.sub (toModel x) (toModel y) := by
  change toModel (ExecFloat.sub x y) = _
  rw [ExecFloat.Proof.sub_eq_spec]
  change Configured.Family.toModel
    (ExecFloat.ModelCodec.liftBinary Model.Spec.sub x y) = _
  simp [Configured.Family.toModel, toModel]

/--
Importing the native sum equals adding the imported binary32 operands with the installed
certified software operation. Finite inputs may produce zero, a subnormal, or infinity.
-/
theorem ofFloat32_add_of_isFinite (x y : Float32)
    (hx : x.isFinite = true) (hy : y.isFinite = true) :
    ofFloat32 (x + y) = ofFloat32 x + ofFloat32 y := by
  apply Configured.Family.toModel_injective
  change toModel (ofFloat32 (x + y)) = toModel (ofFloat32 x + ofFloat32 y)
  rw [toModel_execAdd, ← Model.Proof.add_eq_spec]
  exact toModel_ofFloat32_add_of_isFinite x y hx hy

/-- Importing a native binary32 difference equals certified software subtraction of the imports. -/
theorem ofFloat32_sub_of_isFinite (x y : Float32)
    (hx : x.isFinite = true) (hy : y.isFinite = true) :
    ofFloat32 (x - y) = ofFloat32 x - ofFloat32 y := by
  apply Configured.Family.toModel_injective
  change toModel (ofFloat32 (x - y)) = toModel (ofFloat32 x - ofFloat32 y)
  rw [toModel_execSub, ← Model.Proof.sub_eq_spec]
  exact toModel_ofFloat32_sub_of_isFinite x y hx hy

/--
Importing the native sum equals adding the imported binary64 operands with the installed
certified software operation, including cancellation and overflow.
-/
theorem ofFloat_add_of_isFinite (x y : Float)
    (hx : x.isFinite = true) (hy : y.isFinite = true) :
    ofFloat (x + y) = ofFloat x + ofFloat y := by
  apply Configured.Family.toModel_injective
  change toModel (ofFloat (x + y)) = toModel (ofFloat x + ofFloat y)
  rw [toModel_execAdd, ← Model.Proof.add_eq_spec]
  exact toModel_ofFloat_add_of_isFinite x y hx hy

/-- Importing a native binary64 difference equals certified software subtraction of the imports. -/
theorem ofFloat_sub_of_isFinite (x y : Float)
    (hx : x.isFinite = true) (hy : y.isFinite = true) :
    ofFloat (x - y) = ofFloat x - ofFloat y := by
  apply Configured.Family.toModel_injective
  change toModel (ofFloat (x - y)) = toModel (ofFloat x - ofFloat y)
  rw [toModel_execSub, ← Model.Proof.sub_eq_spec]
  exact toModel_ofFloat_sub_of_isFinite x y hx hy

end FloatLib.Floats.ExecFloat.Binary
