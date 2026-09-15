/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.Constants
public import FloatLib.Floats.Formats.Posit.Functions.Basic

/-!
# Basic posit functions on the public configured carrier

Every function uses the universal carrier/model codec. Static storage selection therefore does
not alter numerical behavior, while users retain one `ExecFloat.Posit (bits := n)` type.

The public functions lift the corresponding model operations. The codec inverse laws ensure
that decoding a result recovers the model result.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.Posit

namespace ExecFloat.Posit

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  FloatLib.Floats.ExecFloat (Configured.Family format code plan)

/-- Lexicographic successor of the posit representation, with wrapping. -/
@[inline] def next (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.next value

/-- Lexicographic predecessor of the posit representation, with wrapping. -/
@[inline] def prior (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.prior value

/-- Standard posit absolute value. -/
@[inline] def abs (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.abs value

/-- Standard posit sign function, returning NaR when the input is NaR. -/
@[inline] def sign (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.sign value

/-- Standard nearest integer-valued posit, with ties to an even integer. -/
@[inline] def nearestInt (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.nearestInt value

/-- Standard ceiling to an integer-valued posit. -/
@[inline] def ceil (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.ceil value

/-- Standard floor to an integer-valued posit. -/
@[inline] def floor (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.floor value

/-- Taking the predecessor after the representation successor restores the original posit. -/
@[simp, grind =] theorem prior_next (value : Value) :
  prior (next value) = value := by
  apply Configured.Family.toModel_injective
  simp [prior, next, Configured.Family.toModel]

/-- Taking the successor after the representation predecessor restores the original posit. -/
@[simp, grind =] theorem next_prior (value : Value) :
  next (prior value) = value := by
  apply Configured.Family.toModel_injective
  simp [prior, next, Configured.Family.toModel]

/-- Posit absolute value fixes the unique zero encoding. -/
@[simp, grind =] theorem abs_zero :
    abs (ExecFloat.Posit.zero (format := format) (plan := plan) (code := code)) =
      ExecFloat.Posit.zero := by
  apply Configured.Family.toModel_injective
  simp [abs, ExecFloat.Posit.zero, Configured.Family.toModel, Configured.Family.ofModel]

/-- Posit absolute value propagates Not-a-Real. -/
@[simp, grind =] theorem abs_nar :
    abs (ExecFloat.Posit.nar (format := format) (plan := plan) (code := code)) =
      ExecFloat.Posit.nar := by
  apply Configured.Family.toModel_injective
  simp [abs, ExecFloat.Posit.nar, Configured.Family.toModel, Configured.Family.ofModel]

/-- The posit sign function fixes the unique zero encoding. -/
@[simp, grind =] theorem sign_zero :
    sign (ExecFloat.Posit.zero (format := format) (plan := plan) (code := code)) =
      ExecFloat.Posit.zero := by
  apply Configured.Family.toModel_injective
  simp [sign, ExecFloat.Posit.zero, Configured.Family.toModel, Configured.Family.ofModel]

/-- The posit sign function propagates Not-a-Real. -/
@[simp, grind =] theorem sign_nar :
    sign (ExecFloat.Posit.nar (format := format) (plan := plan) (code := code)) =
      ExecFloat.Posit.nar := by
  apply Configured.Family.toModel_injective
  simp [sign, ExecFloat.Posit.nar, Configured.Family.toModel, Configured.Family.ofModel]

/-- Nearest-integer rounding fixes the unique posit zero. -/
@[simp, grind =] theorem nearestInt_zero :
    nearestInt (ExecFloat.Posit.zero (format := format) (plan := plan) (code := code)) =
      ExecFloat.Posit.zero := by
  apply Configured.Family.toModel_injective
  simp [nearestInt, ExecFloat.Posit.zero, Configured.Family.toModel, Configured.Family.ofModel]

/-- Nearest-integer rounding propagates posit Not-a-Real. -/
@[simp, grind =] theorem nearestInt_nar :
    nearestInt (ExecFloat.Posit.nar (format := format) (plan := plan) (code := code)) =
      ExecFloat.Posit.nar := by
  apply Configured.Family.toModel_injective
  simp [nearestInt, ExecFloat.Posit.nar, Configured.Family.toModel, Configured.Family.ofModel]

/-- Posit ceiling fixes the unique zero encoding. -/
@[simp, grind =] theorem ceil_zero :
    ceil (ExecFloat.Posit.zero (format := format) (plan := plan) (code := code)) =
      ExecFloat.Posit.zero := by
  apply Configured.Family.toModel_injective
  simp [ceil, ExecFloat.Posit.zero, Configured.Family.toModel, Configured.Family.ofModel]

/-- Posit ceiling propagates Not-a-Real. -/
@[simp, grind =] theorem ceil_nar :
    ceil (ExecFloat.Posit.nar (format := format) (plan := plan) (code := code)) =
      ExecFloat.Posit.nar := by
  apply Configured.Family.toModel_injective
  simp [ceil, ExecFloat.Posit.nar, Configured.Family.toModel, Configured.Family.ofModel]

/-- Posit floor fixes the unique zero encoding. -/
@[simp, grind =] theorem floor_zero :
    floor (ExecFloat.Posit.zero (format := format) (plan := plan) (code := code)) =
      ExecFloat.Posit.zero := by
  apply Configured.Family.toModel_injective
  simp [floor, ExecFloat.Posit.zero, Configured.Family.toModel, Configured.Family.ofModel]

/-- Posit floor propagates Not-a-Real. -/
@[simp, grind =] theorem floor_nar :
    floor (ExecFloat.Posit.nar (format := format) (plan := plan) (code := code)) =
      ExecFloat.Posit.nar := by
  apply Configured.Family.toModel_injective
  simp [floor, ExecFloat.Posit.nar, Configured.Family.toModel, Configured.Family.ofModel]

end ExecFloat.Posit
end FloatLib.Floats
