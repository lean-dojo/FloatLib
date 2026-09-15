/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Algebraic.RationalPower.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Algebraic.RationalPower.Runtime
public import FloatLib.Floats.Formats.Posit.Configured.Storage.Family.Proof

/-!
# Exact semantics of configured powers and fused minus-one exponentials

The configured operations refine the model kernels for every lawful storage codec. Their real
semantics hold under the same domain conditions, independently of storage width. These are
correctness results for certified comparison and exact fallback, not bounds on execution cost.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.Posit

namespace ExecFloat.Posit

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  FloatLib.Floats.ExecFloat (Configured.Family format code plan)

/-- Configured power preserves the exact model result. -/
@[simp] theorem toModel_pow (base exponent : Value) :
    toModel (pow base exponent) = Model.pow (toModel base) (toModel exponent) := by
  simp [pow, toModel, Configured.Family.toModel]

/-- Configured base-two exponential preserves the exact model result. -/
@[simp] theorem toModel_exp2 (value : Value) :
    toModel (exp2 value) = Model.exp2 (toModel value) := by
  simp [exp2, toModel, Configured.Family.toModel]

/-- Configured base-ten exponential preserves the exact model result. -/
@[simp] theorem toModel_exp10 (value : Value) :
    toModel (exp10 value) = Model.exp10 (toModel value) := by
  simp [exp10, toModel, Configured.Family.toModel]

/-- Configured base-two exponential minus one preserves the fused model result. -/
@[simp] theorem toModel_exp2Minus1 (value : Value) :
    toModel (exp2Minus1 value) = Model.exp2Minus1 (toModel value) := by
  simp [exp2Minus1, toModel, Configured.Family.toModel]

/-- Configured base-ten exponential minus one preserves the fused model result. -/
@[simp] theorem toModel_exp10Minus1 (value : Value) :
    toModel (exp10Minus1 value) = Model.exp10Minus1 (toModel value) := by
  simp [exp10Minus1, toModel, Configured.Family.toModel]

/-- Nonnegative configured bases in the real domain round the exact real power once. -/
theorem pow_eq_roundPositive (base exponent : Value) {b e : Rat}
    (hbase : toRat? base = some b) (hexponent : toRat? exponent = some e)
    (hb : 0 ≤ b) (hdomain : b ≠ 0 ∨ 0 < e) :
    toModel (pow base exponent) =
      Model.RealRounding.roundPositive format ((b : ℝ) ^ (e : ℝ)) := by
  rw [toModel_pow]
  exact Model.pow_eq_roundPositive _ _ hbase hexponent hb hdomain

/-- Negative configured bases with integral exponents round their exact rational power once. -/
theorem pow_eq_roundRat_of_neg (base exponent : Value) {b e : Rat}
    (hbase : toRat? base = some b) (hexponent : toRat? exponent = some e)
    (hb : b < 0) (hinteger : e.den = 1) :
    toModel (pow base exponent) = Model.roundRat format (b ^ e.num) := by
  rw [toModel_pow]
  exact Model.pow_eq_roundRat_of_neg _ _ hbase hexponent hb hinteger

/-- A negative configured base with nonintegral exponent produces NaR. -/
theorem pow_eq_nar_of_neg_nonintegral (base exponent : Value) {b e : Rat}
    (hbase : toRat? base = some b) (hexponent : toRat? exponent = some e)
    (hb : b < 0) (hinteger : e.den ≠ 1) :
    toModel (pow base exponent) = Model.nar format := by
  rw [toModel_pow]
  exact Model.pow_eq_nar_of_neg_nonintegral _ _ hbase hexponent hb hinteger

/-- Every finite configured base-two exponential rounds the exact real power. -/
theorem exp2_eq_roundPositive (value : Value) {e : Rat} (hvalue : toRat? value = some e) :
    toModel (exp2 value) = Model.RealRounding.roundPositive format ((2 : ℝ) ^ (e : ℝ)) := by
  rw [toModel_exp2]
  exact Model.exp2_eq_roundPositive _ hvalue

/-- Every finite configured base-ten exponential rounds the exact real power. -/
theorem exp10_eq_roundPositive (value : Value) {e : Rat} (hvalue : toRat? value = some e) :
    toModel (exp10 value) = Model.RealRounding.roundPositive format ((10 : ℝ) ^ (e : ℝ)) := by
  rw [toModel_exp10]
  exact Model.exp10_eq_roundPositive _ hvalue

/-- A finite configured base-two exponential minus one rounds the exact fused expression. -/
theorem exp2Minus1_eq_round (value : Value) {e : Rat} (hvalue : toRat? value = some e) :
    toModel (exp2Minus1 value) =
      Model.RealRounding.round format ((2 : ℝ) ^ (e : ℝ) - 1) := by
  rw [toModel_exp2Minus1]
  exact Model.exp2Minus1_eq_round _ hvalue

/-- A finite configured base-ten exponential minus one rounds the exact fused expression. -/
theorem exp10Minus1_eq_round (value : Value) {e : Rat} (hvalue : toRat? value = some e) :
    toModel (exp10Minus1 value) =
      Model.RealRounding.round format ((10 : ℝ) ^ (e : ℝ) - 1) := by
  rw [toModel_exp10Minus1]
  exact Model.exp10Minus1_eq_round _ hvalue

end ExecFloat.Posit
end FloatLib.Floats
