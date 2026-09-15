/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Algebraic.Power.Proof
public import FloatLib.Floats.Formats.Posit.Algebraic.Proof
public import FloatLib.Floats.Formats.Posit.Algebraic.Root.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Algebraic.Runtime

/-!
# Refinement and exact semantics of configured posit algebraic functions

Every configured operation decodes to its model operation, for any lawful storage codec.
The finite-domain corollaries expose the exact once-rounded rational or real expression.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.Posit

namespace ExecFloat.Posit

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  FloatLib.Floats.ExecFloat (Configured.Family format code plan)

/-- Configured reciprocal square root refines the exact model operation. -/
@[simp] theorem toModel_rSqrt (value : Value) :
    toModel (rSqrt value) = Model.rSqrt (toModel value) := by
  simp [rSqrt, toModel, Configured.Family.toModel]

/-- Configured hypotenuse refines the exact model operation. -/
@[simp] theorem toModel_hypot (left right : Value) :
    toModel (hypot left right) = Model.hypot (toModel left) (toModel right) := by
  simp [hypot, toModel, Configured.Family.toModel]

/-- Configured triple multiplication refines the exact model operation. -/
@[simp] theorem toModel_fMM (left right third : Value) :
    toModel (fMM left right third) =
      Model.fMM (toModel left) (toModel right) (toModel third) := by
  simp [fMM, toModel, Configured.Family.toModel]

/-- Configured integer roots refine the exact model operation for every integer degree. -/
@[simp] theorem toModel_rootN (value : Value) (degree : Int) :
    toModel (rootN value degree) = Model.rootN (toModel value) degree := by
  simp [rootN, toModel, Configured.Family.toModel]

/-- Configured integer powers refine the exact model operation for every integer exponent. -/
@[simp] theorem toModel_powInt (value : Value) (exponent : Int) :
    toModel (powInt value exponent) = Model.powInt (toModel value) exponent := by
  simp [powInt, toModel, Configured.Family.toModel]

/-- Configured compound refines the exact model operation for every integer exponent. -/
@[simp] theorem toModel_compound (value : Value) (exponent : Int) :
    toModel (compound value exponent) = Model.compound (toModel value) exponent := by
  simp [compound, toModel, Configured.Family.toModel]

/-- A positive finite configured reciprocal square root rounds the exact real reciprocal root. -/
theorem rSqrt_eq_roundPositive (value : Value) {q : Rat}
    (hvalue : toRat? value = some q) (hq : 0 < q) :
    toModel (rSqrt value) =
      Model.RealRounding.roundPositive format (1 / Real.sqrt (q : ℝ)) := by
  rw [toModel_rSqrt]
  exact Model.rSqrt_eq_roundPositive _ hvalue hq

/-- Finite configured hypotenuse inputs round the exact real Euclidean norm once. -/
theorem hypot_eq_roundPositive (left right : Value) {a b : Rat}
    (hleft : toRat? left = some a) (hright : toRat? right = some b) :
    toModel (hypot left right) =
      Model.RealRounding.roundPositive format
        (Real.sqrt ((a : ℝ) ^ 2 + (b : ℝ) ^ 2)) := by
  rw [toModel_hypot]
  exact Model.hypot_eq_roundPositive _ _ hleft hright

/-- Finite configured triple multiplication rounds the exact rational product once. -/
theorem fMM_eq_roundRat (left right third : Value) {a b c : Rat}
    (hleft : toRat? left = some a) (hright : toRat? right = some b)
    (hthird : toRat? third = some c) :
    toModel (fMM left right third) = Model.roundRat format (a * b * c) := by
  rw [toModel_fMM]
  exact Model.fMM_eq_roundRat _ _ _ hleft hright hthird

/-- A defined nonnegative configured integer root rounds the exact real power. -/
theorem rootN_eq_roundPositive (value : Value) {q : Rat} (degree : Int)
    (hvalue : toRat? value = some q) (hq : 0 ≤ q) (hdegree : degree ≠ 0)
    (hdomain : q ≠ 0 ∨ 0 < degree) :
    toModel (rootN value degree) =
      Model.RealRounding.roundPositive format ((q : ℝ) ^ (degree : ℝ)⁻¹) := by
  rw [toModel_rootN]
  exact Model.rootN_eq_roundPositive _ degree hvalue hq hdegree hdomain

/-- An odd-degree configured root of a negative finite input rounds the signed real root. -/
theorem rootN_eq_neg_roundPositive (value : Value) {q : Rat} (degree : Int)
    (hvalue : toRat? value = some q) (hq : q < 0) (hodd : degree % 2 ≠ 0) :
    toModel (rootN value degree) =
      Model.neg
        (Model.RealRounding.roundPositive format ((-(q : ℝ)) ^ (degree : ℝ)⁻¹)) := by
  rw [toModel_rootN]
  exact Model.rootN_eq_neg_roundPositive _ degree hvalue hq hodd

/-- Defined configured integer powers round the exact rational power once. -/
theorem powInt_eq_roundRat (value : Value) {q : Rat} (exponent : Int)
    (hvalue : toRat? value = some q) (hdomain : q ≠ 0 ∨ 0 < exponent) :
    toModel (powInt value exponent) = Model.roundRat format (q ^ exponent) := by
  rw [toModel_powInt]
  exact Model.powInt_eq_roundRat _ exponent hvalue hdomain

/-- Defined configured compound rounds the exact addition and integer power once. -/
theorem compound_eq_roundRat (value : Value) {q : Rat} (exponent : Int)
    (hvalue : toRat? value = some q) (hdomain : 1 + q ≠ 0 ∨ 0 < exponent) :
    toModel (compound value exponent) = Model.roundRat format ((1 + q) ^ exponent) := by
  rw [toModel_compound]
  exact Model.compound_eq_roundRat _ exponent hvalue hdomain

/-- Fixed exponent zero gives rounded one for every finite configured input. -/
theorem powInt_exponent_zero (value : Value) {q : Rat}
    (hvalue : toRat? value = some q) :
    toModel (powInt value 0) = Model.roundRat format 1 := by
  rw [toModel_powInt]
  exact Model.powInt_exponent_zero _ hvalue

/-- Fixed exponent zero makes compound constant one, including at input negative one. -/
theorem compound_exponent_zero (value : Value) {q : Rat}
    (hvalue : toRat? value = some q) :
    toModel (compound value 0) = Model.roundRat format 1 := by
  rw [toModel_compound]
  exact Model.compound_exponent_zero _ hvalue

end ExecFloat.Posit
end FloatLib.Floats
