/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.Posit.Configured.Functions.Basic
public import FloatLib.Floats.Formats.Posit.Configured.Value.Runtime
public import FloatLib.Floats.Formats.Posit.Functions.IntegerProof

/-!
# Exact configured posit integer functions

Every lawful storage codec transports the model's exact integer semantics. Floor, ceiling, and
nearest-even results are exactly representable at the input posit width.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.Posit
open FloatLib.Numerics

namespace ExecFloat.Posit

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  FloatLib.Floats.ExecFloat (Configured.Family format code plan)

/-- Configured floor refines model floor for every lawful storage codec. -/
@[simp] theorem toModel_floor (value : Value) :
    toModel (floor value) = Model.floor (toModel value) := by
  simp [floor, toModel, Configured.Family.toModel]

/-- Configured ceiling refines model ceiling for every lawful storage codec. -/
@[simp] theorem toModel_ceil (value : Value) :
    toModel (ceil value) = Model.ceil (toModel value) := by
  simp [ceil, toModel, Configured.Family.toModel]

/-- Configured nearest-integer rounding refines the nearest-even model operation. -/
@[simp] theorem toModel_nearestInt (value : Value) :
    toModel (nearestInt value) = Model.nearestInt (toModel value) := by
  simp [nearestInt, toModel, Configured.Family.toModel]

/-- Finite configured floor denotes the exact mathematical floor. -/
theorem toRat?_floor_of_finite (value : Value) {q : ℚ}
    (hvalue : toRat? value = some q) :
    toRat? (floor value) = some (q.floor : ℚ) := by
  simpa only [toRat?, toModel_floor] using
    Model.toRat?_floor_of_finite (toModel value) hvalue

/-- Finite configured ceiling denotes the exact mathematical ceiling. -/
theorem toRat?_ceil_of_finite (value : Value) {q : ℚ}
    (hvalue : toRat? value = some q) :
    toRat? (ceil value) = some (q.ceil : ℚ) := by
  simpa only [toRat?, toModel_ceil] using
    Model.toRat?_ceil_of_finite (toModel value) hvalue

/-- Finite configured nearest-integer rounding denotes the exact nearest-even integer. -/
theorem toRat?_nearestInt_of_finite (value : Value) {q : ℚ}
    (hvalue : toRat? value = some q) :
    toRat? (nearestInt value) = some (roundRatEven q : ℚ) := by
  simpa only [toRat?, toModel_nearestInt] using
    Model.toRat?_nearestInt_of_finite (toModel value) hvalue

/-- Configured floor has exact optional semantics, including NaR propagation. -/
@[simp] theorem toRat?_floor (value : Value) :
    toRat? (floor value) = (toRat? value).map (fun q => (q.floor : ℚ)) := by
  simpa only [toRat?, toModel_floor] using Model.toRat?_floor (toModel value)

/-- Configured ceiling has exact optional semantics, including NaR propagation. -/
@[simp] theorem toRat?_ceil (value : Value) :
    toRat? (ceil value) = (toRat? value).map (fun q => (q.ceil : ℚ)) := by
  simpa only [toRat?, toModel_ceil] using Model.toRat?_ceil (toModel value)

/-- Configured nearest-even rounding has exact optional semantics, including NaR. -/
@[simp] theorem toRat?_nearestInt (value : Value) :
    toRat? (nearestInt value) = (toRat? value).map (fun q => (roundRatEven q : ℚ)) := by
  simpa only [toRat?, toModel_nearestInt] using Model.toRat?_nearestInt (toModel value)

/-- Configured floor fixes every integer-valued input. -/
theorem floor_of_int (value : Value) {n : ℤ}
    (hvalue : toRat? value = some (n : ℚ)) : floor value = value := by
  apply Configured.Family.toModel_injective
  change toModel (floor value) = toModel value
  rw [toModel_floor]
  exact Model.floor_of_int _ hvalue

/-- Configured ceiling fixes every integer-valued input. -/
theorem ceil_of_int (value : Value) {n : ℤ}
    (hvalue : toRat? value = some (n : ℚ)) : ceil value = value := by
  apply Configured.Family.toModel_injective
  change toModel (ceil value) = toModel value
  rw [toModel_ceil]
  exact Model.ceil_of_int _ hvalue

/-- Configured nearest-integer rounding fixes every integer-valued input. -/
theorem nearestInt_of_int (value : Value) {n : ℤ}
    (hvalue : toRat? value = some (n : ℚ)) : nearestInt value = value := by
  apply Configured.Family.toModel_injective
  change toModel (nearestInt value) = toModel value
  rw [toModel_nearestInt]
  exact Model.nearestInt_of_int _ hvalue

/-- The configured result is a nearest integer, with half-unit error and even ties. -/
theorem nearestInt_spec (value : Value) {q : ℚ}
    (hvalue : toRat? value = some q) :
    ∃ n : ℤ, toRat? (nearestInt value) = some (n : ℚ) ∧
      |(n : ℚ) - q| ≤ (1 : ℚ) / 2 ∧
      (∀ z : ℤ, |(n : ℚ) - q| ≤ |(z : ℚ) - q|) ∧
      (|(n : ℚ) - q| = (1 : ℚ) / 2 → n % 2 = 0) := by
  simpa only [toRat?, toModel_nearestInt] using Model.nearestInt_spec (toModel value) hvalue

end ExecFloat.Posit
end FloatLib.Floats
