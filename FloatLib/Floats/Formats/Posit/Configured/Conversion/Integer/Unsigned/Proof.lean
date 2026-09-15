/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.Posit.Cast.Integer.Unsigned.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Conversion.Integer.Unsigned.Runtime
public import FloatLib.Floats.Formats.Posit.Configured.Storage.Family.Proof

/-!
# Configured unsigned integer semantics

The codec preserves the model's numerical guarantees: exact unsigned decoding
after accepted rounding, a half-unit error bound, even halfway results, and the
MSB-only sentinel rule including its collision with a valid unsigned integer.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.Posit FloatLib.Numerics

namespace ExecFloat.Posit

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  FloatLib.Floats.ExecFloat (Configured.Family format code plan)

/-- Decoding the configured conversion recovers the model result through any lawful codec. -/
@[simp] theorem toModel_ofUnsigned {width : Nat} (value : BitVec width) (hwidth : 0 < width) :
    toModel (ofUnsigned (format := format) (plan := plan) (code := code) value hwidth) =
      Model.ofUnsigned format value hwidth := by
  simp [ofUnsigned, ofModel, toModel]

/-- Storage choice does not change unsigned rounding or sentinel delivery. -/
theorem toUnsigned_eq_model (width : Nat) (value : Value) (hwidth : 0 < width) :
    toUnsigned width value hwidth = Model.toUnsigned width (toModel value) hwidth :=
  rfl

/-- The MSB-only input becomes NaR through every lawful storage codec. -/
theorem toModel_ofUnsigned_intMin {width : Nat} (hwidth : 0 < width) :
    toModel (ofUnsigned (format := format) (plan := plan) (code := code)
      (BitVec.intMin width) hwidth) = Model.nar format := by
  simp

/-- Outside the reserved MSB-only word, conversion rounds the unsigned natural value
by the posit rounding rule. -/
theorem ofUnsigned_eq_roundRat {width : Nat} (value : BitVec width) (hwidth : 0 < width)
    (hvalue : value ≠ BitVec.intMin width) :
    toModel (ofUnsigned (format := format) (plan := plan) (code := code) value hwidth) =
      Model.roundRat format (value.toNat : Rat) := by
  rw [toModel_ofUnsigned]
  exact Model.ofUnsigned_eq_roundRat value hwidth hvalue

/-- NaR converts to the MSB-only output sentinel. -/
theorem toUnsigned_eq_intMin_of_none (width : Nat) (value : Value) (hwidth : 0 < width)
    (hvalue : toRat? value = none) :
    toUnsigned width value hwidth = BitVec.intMin width :=
  Model.toUnsigned_eq_intMin_of_none (toModel value) hwidth hvalue

/-- Accepted output bits denote the exact rounded integer, without modular wraparound. -/
theorem toNat_toUnsigned_of_inRange (width : Nat) (value : Value) (hwidth : 0 < width) {q : Rat}
    (hvalue : toRat? value = some q)
    (hrange : (IntegerFormat.unsigned width).InRange (roundRatEven q)) :
    ((toUnsigned width value hwidth).toNat : Int) = roundRatEven q :=
  Model.toNat_toUnsigned_of_inRange (toModel value) hwidth hvalue hrange

/-- A finite input whose rounded integer is outside the unsigned range delivers the sentinel. -/
theorem toUnsigned_eq_intMin_of_not_inRange (width : Nat) (value : Value)
    (hwidth : 0 < width) {q : Rat} (hvalue : toRat? value = some q)
    (hrange : ¬ (IntegerFormat.unsigned width).InRange (roundRatEven q)) :
    toUnsigned width value hwidth = BitVec.intMin width :=
  Model.toUnsigned_eq_intMin_of_not_inRange (toModel value) hwidth hvalue hrange

/-- For finite inputs, the sentinel bits denote either a rejected rounded integer or the
successful value `2 ^ (width - 1)`. These cases cannot be distinguished from the bits alone. -/
theorem toUnsigned_eq_intMin_iff (width : Nat) (value : Value) (hwidth : 0 < width) {q : Rat}
    (hvalue : toRat? value = some q) :
    toUnsigned width value hwidth = BitVec.intMin width ↔
      ¬ (IntegerFormat.unsigned width).InRange (roundRatEven q) ∨
        roundRatEven q = (2 : Int) ^ (width - 1) :=
  Model.toUnsigned_eq_intMin_iff (toModel value) hwidth hvalue

/-- An accepted unsigned conversion differs from the exact posit value by at most half a unit. -/
theorem toUnsigned_error_le_half (width : Nat) (value : Value) (hwidth : 0 < width) {q : Rat}
    (hvalue : toRat? value = some q)
    (hrange : (IntegerFormat.unsigned width).InRange (roundRatEven q)) :
    |((toUnsigned width value hwidth).toNat : Rat) - q| ≤ (1 : Rat) / 2 :=
  Model.toUnsigned_error_le_half (toModel value) hwidth hvalue hrange

/-- An accepted halfway input rounds to an even unsigned integer, including a negative
halfway input whose rounded result is zero. -/
theorem toUnsigned_even_of_half (width : Nat) (value : Value) (hwidth : 0 < width) {q : Rat}
    (hvalue : toRat? value = some q)
    (hrange : (IntegerFormat.unsigned width).InRange (roundRatEven q))
    (hhalf : 2 * (q.num.natAbs % q.den) = q.den) :
    (toUnsigned width value hwidth).toNat % 2 = 0 :=
  Model.toUnsigned_even_of_half (toModel value) hwidth hvalue hrange hhalf

end ExecFloat.Posit
end FloatLib.Floats
