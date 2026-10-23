/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.ModelBridge
public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.DivisionReference
public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.RoundingKernel.Proof
public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Addition.Runtime -- shake: keep
public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Fma.Runtime -- shake: keep
public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Multiplication.Runtime -- shake: keep
public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Addition.Proof -- shake: keep
public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Fma.Proof -- shake: keep
public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Multiplication.Proof -- shake: keep
public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Base.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Decode

/-!
# Agreement between native binary32 words and the generic model

The narrow-word core implements finite binary32 arithmetic with `UInt32` and `UInt64`. This module
proves that its finite operations equal the generic `Model FloatFormat.binary32` formulas, using
the field, decoding and rounding bridge of `Narrow.ModelBridge`.

The `Addition`, `Multiplication` and `Fma` proof modules connect their word kernels to these finite
operations. Runtime clients can import the `Runtime` modules without these proofs.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32

/-- Native finite binary32 addition rounds the generic exact dyadic sum. -/
theorem addFinite_eq (x y : Value) :
    addFinite? x y =
      match Model.toDyadic? x, Model.toDyadic? y with
      | some dx, some dy =>
          some (Model.roundDyadic FloatFormat.binary32 (Model.addDyadic dx dy))
      | _, _ => none := by
  unfold addFinite?
  rw [toDyadic_eq, toDyadic_eq]
  cases hx : Model.toDyadic? x <;>
    cases hy : Model.toDyadic? y <;>
    simp [ofUInt32_roundDyadic]

/-- Native finite binary32 multiplication equals the generic product, zero factors included. -/
theorem mulFinite_eq (x y : Value) :
    mulFinite? x y =
      match Model.toDyadic? x, Model.toDyadic? y with
      | some dx, some dy =>
          let sign := Bool.xor dx.negative dy.negative
          if dx.significand == 0 || dy.significand == 0 then
            some (if sign then Model.negZero FloatFormat.binary32
              else Model.posZero FloatFormat.binary32)
          else
            some (Model.roundDyadic FloatFormat.binary32 {
              negative := sign
              significand := dx.significand * dy.significand
              exponent := dx.exponent + dy.exponent })
      | _, _ => none := by
  unfold mulFinite?
  rw [toDyadic_eq, toDyadic_eq]
  cases hx : Model.toDyadic? x with
  | none =>
      cases hy : Model.toDyadic? y <;> rfl
  | some dx =>
      cases hy : Model.toDyadic? y with
      | none => rfl
      | some dy =>
          dsimp only
          by_cases hzero : dx.significand = 0 ∨ dy.significand = 0
          · simp only [beq_iff_eq, Bool.or_eq_true, hzero, ite_eq_left]
            exact congrArg some (ofUInt32_signedZero (Bool.xor dx.negative dy.negative))
          · simp only [beq_iff_eq, Bool.or_eq_true, hzero, ite_false]
            exact congrArg some (ofUInt32_roundDyadic {
              negative := Bool.xor dx.negative dy.negative,
              significand := dx.significand * dy.significand,
              exponent := dx.exponent + dy.exponent })

/-- Native finite binary32 division equals the generic finite quotient, zero divisors included. -/
theorem divFinite_eq (x y : Value) :
    divFinite? x y =
      match Model.toDyadic? x, Model.toDyadic? y with
      | some dx, some dy =>
          let sign := Bool.xor dx.negative dy.negative
          some <|
            if dy.significand == 0 then
              if dx.significand == 0 then Model.canonicalNaN FloatFormat.binary32
              else if sign then Model.negInf FloatFormat.binary32
              else Model.posInf FloatFormat.binary32
            else if dx.significand == 0 then
              if sign then Model.negZero FloatFormat.binary32
              else Model.posZero FloatFormat.binary32
            else
              Model.roundRatScaled FloatFormat.binary32
                sign dx.significand dy.significand (dx.exponent - dy.exponent)
      | _, _ => none := by
  unfold divFinite?
  rw [toDyadic_eq, toDyadic_eq]
  cases hx : Model.toDyadic? x with
  | none =>
      cases hy : Model.toDyadic? y <;> rfl
  | some dx =>
      cases hy : Model.toDyadic? y with
      | none => rfl
      | some dy =>
          dsimp only
          by_cases hyzero : dy.significand = 0
          · simp only [beq_iff_eq, hyzero, ite_eq_left]
            by_cases hxzero : dx.significand = 0
            · simp only [hxzero, ite_eq_left, ofUInt32_canonicalNaN]
            · simp only [hxzero, ite_false]
              exact congrArg some (ofUInt32_signedInf (Bool.xor dx.negative dy.negative))
          · simp only [beq_iff_eq, hyzero, ite_false]
            by_cases hxzero : dx.significand = 0
            · simp only [hxzero, ite_eq_left]
              exact congrArg some (ofUInt32_signedZero (Bool.xor dx.negative dy.negative))
            · simp only [hxzero, ite_false, ofUInt32_roundRatScaled]

/-- Native finite binary32 fused multiply-add rounds the exact product plus addend once. -/
theorem fmaFinite_eq (x y z : Value) :
    fmaFinite? x y z =
      match Model.toDyadic? x, Model.toDyadic? y, Model.toDyadic? z with
      | some dx, some dy, some dz =>
          let product : Numerics.Dyadic := {
            negative := Bool.xor dx.negative dy.negative,
            significand := dx.significand * dy.significand,
            exponent := dx.exponent + dy.exponent }
          some (Model.roundDyadic FloatFormat.binary32
            (Model.addDyadic product dz))
      | _, _, _ => none := by
  unfold fmaFinite?
  rw [toDyadic_eq, toDyadic_eq, toDyadic_eq]
  cases hx : Model.toDyadic? x <;>
    cases hy : Model.toDyadic? y <;>
    cases hz : Model.toDyadic? z <;>
    simp [ofUInt32_roundDyadic]

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32
