/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.LeanModel.AddSub
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.Instances
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.NativeDispatch
public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.Representation
public import FloatLib.Floats.Formats.IEEE754.Native.Representation
public import FloatLib.Floats.ExecFloat.Instances
public import FloatLib.Floats.ExecFloat.Proof.Arithmetic
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Rounding.Proof

/-!
# Native addition and subtraction

These theorems relate FloatLib's addition and subtraction to the logical floating-point model
shipped with Lean. Finite inputs include both signed zeros. The result is unrestricted, so
cancellation, subnormal rounding and overflow to infinity are covered, and the equations hold on
the complete packed word through the native adapters.

The finite-input hypotheses exclude NaNs and infinities, because FloatLib preserves NaN details
that Lean canonicalizes and its subtraction also negates the right operand's NaN sign. Negation
alone agrees with Lean's model on every word. These model equalities do not verify the machine
instructions used by compiled native code.

The configured operations are the first-order binary32 and binary64 instances of
`Configured.NativeDispatch`, the ones a client that imports `Configured` elaborates, so `rw` and
`simp` apply the bridges to client terms in either direction.
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
  change Internal.Directed.roundDyadic fmt .nearest d = canonicalizeModel x
  rw [Internal.Directed.roundDyadic_toDyadic? hfmt .nearest hd,
    canonicalizeModel_eq_self x hcanonical]

/-- A value whose Lean unpacked model is `u` decodes to the dyadic of `u`. -/
private theorem toDyadic?_eq_of_toModel_eq {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    {x : Model fmt} {u : Float.Model.UnpackedFloat} (hu : toModel x = u) :
    toDyadic? x = unpackedToDyadic? u := by
  rw [toDyadic?_ieee_eq_model fmt hfmt x, hu]

/--
For finite operands, including signed zeros, dispatched addition gives the word that Lean's
unpacked model gets by adding and packing. The result may overflow to infinity.
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
    have hd : toDyadic? y = some ⟨modelSignBit sign₂, mantissa₂, exponent₂⟩ :=
      toDyadic?_eq_of_toModel_eq hfmt hymodel
    have hr := round_decoded_eq_ofModel hfmt y hd
    rw [hymodel] at hr
    rw [Proof.add_eq_spec, Spec.add, toDyadic?_ieee_eq_model fmt hfmt x, hxmodel, hd]
    simp only [unpackedToDyadic?, addDyadic, Float.Model.UnpackedFloat.add]
    rw [Numerics.Dyadic.add_of_left_significand_eq_zero _ _ rfl]
    simpa only [hmantissa₂.ne', ite_false] using hr
  case finite.zero sign₁ mantissa₁ exponent₁ hmantissa₁ sign₂ =>
    have hd : toDyadic? x = some ⟨modelSignBit sign₁, mantissa₁, exponent₁⟩ :=
      toDyadic?_eq_of_toModel_eq hfmt hxmodel
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

/--
Negation commutes with Lean's unpacked model on every word: finite values and zeros change sign,
infinities change sign, and NaNs stay NaNs. Toggling the stored sign keeps the exponent and
fraction fields that classify the word.
-/
theorem toModel_neg {fmt : FloatFormat} (hfmt : fmt.isIEEE = true) (x : Model fmt) :
    toModel (neg x) = Float.Model.UnpackedFloat.neg (toModel x) := by
  rw [neg_eq_toggleSign_of_supportsSignedZero x
    (FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt hfmt)]
  have hexponent :
      unpackExponent (toModelBits (toggleSign x)) = unpackExponent (toModelBits x) := by
    apply BitVec.eq_of_toNat_eq
    rw [unpackExponent_toNat, unpackExponent_toNat, expField_toggleSign]
  have hmantissa :
      unpackMantissa (toModelBits (toggleSign x)) = unpackMantissa (toModelBits x) := by
    apply BitVec.eq_of_toNat_eq
    rw [unpackMantissa_toNat, unpackMantissa_toNat, fracField_toggleSign]
  have hsign : Sign.ofBitVec (unpackSign (toModelBits (toggleSign x))) =
      -Sign.ofBitVec (unpackSign (toModelBits x)) := by
    have htoggled := modelSignBit_ofBitVec_unpackSign (toggleSign x)
    rw [signBit_toggleSign, ← modelSignBit_ofBitVec_unpackSign x] at htoggled
    revert htoggled
    cases Sign.ofBitVec (unpackSign (toModelBits (toggleSign x))) <;>
      cases Sign.ofBitVec (unpackSign (toModelBits x)) <;> simp [modelSignBit] <;> rfl
  unfold toModel unpack
  simp only [hexponent, hmantissa, hsign]
  split_ifs <;> rfl

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
  have hneg := toModel_neg hfmt y
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

/-- A finite native binary32 value imports to a finite unpacked model. -/
private theorem isFinite_toModel_ofFloat32Model {x : Float32} (hx : x.isFinite = true) :
    (Model.toModel (Model.ofFloat32Model x.toModel)).isFinite = true := by
  simpa only [Model.toModel_ofFloat32Model, Float32.isFinite, Float32.Model.isFinite] using hx

/-- A finite native binary64 value imports to a finite unpacked model. -/
private theorem isFinite_toModel_ofFloatModel {x : Float} (hx : x.isFinite = true) :
    (Model.toModel (Model.ofFloatModel x.toModel)).isFinite = true := by
  simpa only [Model.toModel_ofFloatModel, Float.isFinite, Float.Model.isFinite] using hx

/-- Native binary32 addition commutes with the import adapter on finite inputs. -/
theorem toModel_ofFloat32_add_of_isFinite (x y : Float32)
    (hx : x.isFinite = true) (hy : y.isFinite = true) :
    toModel (ofFloat32 (x + y) : Binary32) =
      Model.add (toModel (ofFloat32 x : Binary32)) (toModel (ofFloat32 y : Binary32)) := by
  rw [toModel_ofFloat32, toModel_ofFloat32, toModel_ofFloat32]
  change Model.ofFloat32Model (Float32.Model.add x.toModel y.toModel) = _
  rw [Float32.Model.add, Model.ofFloat32Model_pack]
  have h := Model.add_eq_ofModel_add_of_isFinite (fmt := FloatFormat.binary32)
    (by decide) (Model.ofFloat32Model x.toModel) (Model.ofFloat32Model y.toModel)
    (isFinite_toModel_ofFloat32Model hx) (isFinite_toModel_ofFloat32Model hy)
  rw [Model.toModel_ofFloat32Model, Model.toModel_ofFloat32Model] at h
  exact h.symm

/-- Native binary32 subtraction commutes with the import adapter, including signed-zero inputs. -/
theorem toModel_ofFloat32_sub_of_isFinite (x y : Float32)
    (hx : x.isFinite = true) (hy : y.isFinite = true) :
    toModel (ofFloat32 (x - y) : Binary32) =
      Model.sub (toModel (ofFloat32 x : Binary32)) (toModel (ofFloat32 y : Binary32)) := by
  rw [toModel_ofFloat32, toModel_ofFloat32, toModel_ofFloat32]
  change Model.ofFloat32Model (Float32.Model.sub x.toModel y.toModel) = _
  rw [Float32.Model.sub, Model.ofFloat32Model_pack]
  have h := Model.sub_eq_ofModel_sub_of_isFinite (fmt := FloatFormat.binary32)
    (by decide) (Model.ofFloat32Model x.toModel) (Model.ofFloat32Model y.toModel)
    (isFinite_toModel_ofFloat32Model hx) (isFinite_toModel_ofFloat32Model hy)
  rw [Model.toModel_ofFloat32Model, Model.toModel_ofFloat32Model] at h
  exact h.symm

/-- Native binary64 addition commutes with the import adapter on finite inputs. -/
theorem toModel_ofFloat_add_of_isFinite (x y : Float)
    (hx : x.isFinite = true) (hy : y.isFinite = true) :
    toModel (ofFloat (x + y) : Binary64) =
      Model.add (toModel (ofFloat x : Binary64)) (toModel (ofFloat y : Binary64)) := by
  rw [toModel_ofFloat, toModel_ofFloat, toModel_ofFloat]
  change Model.ofFloatModel (Float.Model.add x.toModel y.toModel) = _
  rw [Float.Model.add, Model.ofFloatModel_pack]
  have h := Model.add_eq_ofModel_add_of_isFinite (fmt := FloatFormat.binary64)
    (by decide) (Model.ofFloatModel x.toModel) (Model.ofFloatModel y.toModel)
    (isFinite_toModel_ofFloatModel hx) (isFinite_toModel_ofFloatModel hy)
  rw [Model.toModel_ofFloatModel, Model.toModel_ofFloatModel] at h
  exact h.symm

/-- Native binary64 subtraction commutes with the import adapter, including signed-zero inputs. -/
theorem toModel_ofFloat_sub_of_isFinite (x y : Float)
    (hx : x.isFinite = true) (hy : y.isFinite = true) :
    toModel (ofFloat (x - y) : Binary64) =
      Model.sub (toModel (ofFloat x : Binary64)) (toModel (ofFloat y : Binary64)) := by
  rw [toModel_ofFloat, toModel_ofFloat, toModel_ofFloat]
  change Model.ofFloatModel (Float.Model.sub x.toModel y.toModel) = _
  rw [Float.Model.sub, Model.ofFloatModel_pack]
  have h := Model.sub_eq_ofModel_sub_of_isFinite (fmt := FloatFormat.binary64)
    (by decide) (Model.ofFloatModel x.toModel) (Model.ofFloatModel y.toModel)
    (isFinite_toModel_ofFloatModel hx) (isFinite_toModel_ofFloatModel hy)
  rw [Model.toModel_ofFloatModel, Model.toModel_ofFloatModel] at h
  exact h.symm

/--
Importing the native sum equals adding the imported binary32 operands with the installed
certified software operation. Finite inputs may produce zero, a subnormal, or infinity.
-/
theorem ofFloat32_add_of_isFinite (x y : Float32)
    (hx : x.isFinite = true) (hy : y.isFinite = true) :
    (ofFloat32 (x + y) : Binary32) = ofFloat32 x + ofFloat32 y := by
  apply Configured.Family.toModel_injective
  change toModel (ofFloat32 (x + y) : Binary32) = toModel (ofFloat32 x + ofFloat32 y : Binary32)
  rw [toModel_ofFloat32_add_of_isFinite x y hx hy]
  simp only [toModel_hAdd]

/-- Importing a native binary32 difference equals certified software subtraction of the imports. -/
theorem ofFloat32_sub_of_isFinite (x y : Float32)
    (hx : x.isFinite = true) (hy : y.isFinite = true) :
    (ofFloat32 (x - y) : Binary32) = ofFloat32 x - ofFloat32 y := by
  apply Configured.Family.toModel_injective
  change toModel (ofFloat32 (x - y) : Binary32) = toModel (ofFloat32 x - ofFloat32 y : Binary32)
  rw [toModel_ofFloat32_sub_of_isFinite x y hx hy]
  simp only [toModel_hSub]

/--
Importing the native sum equals adding the imported binary64 operands with the installed
certified software operation, including cancellation and overflow.
-/
theorem ofFloat_add_of_isFinite (x y : Float)
    (hx : x.isFinite = true) (hy : y.isFinite = true) :
    (ofFloat (x + y) : Binary64) = ofFloat x + ofFloat y := by
  apply Configured.Family.toModel_injective
  change toModel (ofFloat (x + y) : Binary64) = toModel (ofFloat x + ofFloat y : Binary64)
  rw [toModel_ofFloat_add_of_isFinite x y hx hy]
  simp only [toModel_hAdd]

/-- Importing a native binary64 difference equals certified software subtraction of the imports. -/
theorem ofFloat_sub_of_isFinite (x y : Float)
    (hx : x.isFinite = true) (hy : y.isFinite = true) :
    (ofFloat (x - y) : Binary64) = ofFloat x - ofFloat y := by
  apply Configured.Family.toModel_injective
  change toModel (ofFloat (x - y) : Binary64) = toModel (ofFloat x - ofFloat y : Binary64)
  rw [toModel_ofFloat_sub_of_isFinite x y hx hy]
  simp only [toModel_hSub]

end FloatLib.Floats.ExecFloat.Binary
