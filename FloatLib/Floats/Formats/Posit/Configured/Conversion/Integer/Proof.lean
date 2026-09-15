/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Cast.Integer.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Conversion.Integer.Runtime
public import FloatLib.Floats.Formats.Posit.Configured.Storage.Family.Proof

/-!
# Refinement of configured posit integer conversions

Both adapters refine the model conversions for arbitrary positive integer widths and lawful
posit codecs. The semantic theorems expose the exact once-rounded integer input and nearest-even
integer output, including the signed-minimum sentinel collision.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.Posit
open FloatLib.Numerics
open FloatLib.Numerics.Representations

namespace ExecFloat.Posit

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  FloatLib.Floats.ExecFloat (Configured.Family format code plan)

/-- Packing the integer conversion preserves the model result exactly. -/
@[simp] theorem toModel_ofFixedInt {width : Nat} (value : FixedInt width) (hwidth : 0 < width) :
    toModel (ofFixedInt (format := format) (plan := plan) (code := code) value hwidth) =
      Model.ofFixedInt format value hwidth := by
  simp [ofFixedInt, ofModel, toModel]

/-- Converting a configured posit to an integer is conversion of its exact model value. -/
theorem toFixedInt_eq_model (width : Nat) (value : Value) (hwidth : 0 < width) :
    toFixedInt width value hwidth = Model.toFixedInt width (toModel value) hwidth :=
  rfl

/-- The reserved integer word becomes the posit NaR encoding through every lawful codec. -/
theorem toModel_ofFixedInt_minCode {width : Nat} (hwidth : 0 < width) :
    toModel (ofFixedInt (format := format) (plan := plan) (code := code)
      (FixedInt.minCode width) hwidth) = Model.nar format := by
  simp

/-- Non-sentinel integer inputs receive exactly one posit rounding of their signed values. -/
theorem ofFixedInt_eq_roundRat {width : Nat} (value : FixedInt width) (hwidth : 0 < width)
    (hvalue : value ≠ FixedInt.minCode width) :
    toModel (ofFixedInt (format := format) (plan := plan) (code := code) value hwidth) =
      Model.roundRat format (value.toInt : Rat) := by
  rw [toModel_ofFixedInt]
  exact Model.ofFixedInt_eq_roundRat value hwidth hvalue

/-- A configured NaR observation converts to the MSB-only integer sentinel. -/
theorem toFixedInt_eq_minCode_of_none (width : Nat) (value : Value) (hwidth : 0 < width)
    (hvalue : toRat? value = none) :
    toFixedInt width value hwidth = FixedInt.minCode width := by
  change (toModel value).toRat? = none at hvalue
  simp [toFixedInt, Model.toFixedInt, hvalue]

/-- An in-range configured conversion decodes to the exact nearest-even integer. -/
theorem toInt_toFixedInt_of_inRange (width : Nat) (value : Value) (hwidth : 0 < width) {q : Rat}
    (hvalue : toRat? value = some q) (hrange : FixedInt.InRange width (roundRatEven q)) :
    (toFixedInt width value hwidth).toInt = roundRatEven q :=
  Model.toInt_toFixedInt_of_inRange (toModel value) hwidth hvalue hrange

/-- Out-of-range rounded integers produce the sentinel through every configured carrier. -/
theorem toFixedInt_eq_minCode_of_not_inRange (width : Nat) (value : Value)
    (hwidth : 0 < width) {q : Rat} (hvalue : toRat? value = some q)
    (hrange : ¬ FixedInt.InRange width (roundRatEven q)) :
    toFixedInt width value hwidth = FixedInt.minCode width :=
  Model.toFixedInt_eq_minCode_of_not_inRange (toModel value) hwidth hvalue hrange

/-- Finite sentinel output includes both overflow and a rounded result at the signed minimum. -/
theorem toFixedInt_eq_minCode_iff (width : Nat) (value : Value) (hwidth : 0 < width) {q : Rat}
    (hvalue : toRat? value = some q) :
    toFixedInt width value hwidth = FixedInt.minCode width ↔
      ¬ FixedInt.InRange width (roundRatEven q) ∨ roundRatEven q = FixedInt.minValue width :=
  Model.toFixedInt_eq_minCode_iff (toModel value) hwidth hvalue

/-- The absolute conversion error is at most one half when the rounded integer fits. -/
theorem toFixedInt_error_le_half (width : Nat) (value : Value) (hwidth : 0 < width) {q : Rat}
    (hvalue : toRat? value = some q) (hrange : FixedInt.InRange width (roundRatEven q)) :
    |((toFixedInt width value hwidth).toInt : Rat) - q| ≤ (1 : Rat) / 2 :=
  Model.toFixedInt_error_le_half (toModel value) hwidth hvalue hrange

/-- Exact halfway values convert to even integers, provided their rounded values fit. -/
theorem toFixedInt_even_of_half (width : Nat) (value : Value) (hwidth : 0 < width) {q : Rat}
    (hvalue : toRat? value = some q) (hrange : FixedInt.InRange width (roundRatEven q))
    (hhalf : 2 * (q.num.natAbs % q.den) = q.den) :
    (toFixedInt width value hwidth).toInt % 2 = 0 :=
  Model.toFixedInt_even_of_half (toModel value) hwidth hvalue hrange hhalf

end ExecFloat.Posit
end FloatLib.Floats
