/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Algebraic.Power.Runtime
public import FloatLib.Floats.Formats.Posit.Semantics.Exact.Proof

/-!
# Exact single-rounding contracts for posit integer powers

The finite-domain contracts expose the exact rational power presented to the posit rounding
kernel. Zero to a negative power is excluded; exponent zero is the constant one on all finite
inputs. No posit rounding occurs inside the exponentiation or compound's addition.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

variable {format : Format}

/-- In its real domain, rational integer exponentiation is followed by exactly one rounding. -/
theorem roundIntPower_eq_roundRat (base : Rat) (exponent : Int)
    (hdomain : base ≠ 0 ∨ 0 < exponent) :
    roundIntPower format base exponent = roundRat format (base ^ exponent) := by
  have hvalid : ¬(base = 0 ∧ exponent < 0) := by
    rcases hdomain with hbase | hexponent
    · exact fun h => hbase h.1
    · exact fun h => (not_lt.mpr hexponent.le) h.2
  simp [roundIntPower, hvalid]

/-- Zero to a negative integer power has no finite limit. -/
theorem roundIntPower_zero_of_neg (exponent : Int) (hexponent : exponent < 0) :
    roundIntPower format 0 exponent = nar format := by
  simp [roundIntPower, hexponent]

/-- At fixed exponent zero, every finite rational base gives the constant one. -/
@[simp] theorem roundIntPower_exponent_zero (base : Rat) :
    roundIntPower format base 0 = roundRat format 1 := by
  simp [roundIntPower]

/-- Finite integer powers round the exact rational power once, including negative exponents. -/
theorem powInt_eq_roundRat (value : Model format) {q : Rat} (exponent : Int)
    (hvalue : value.toRat? = some q) (hdomain : q ≠ 0 ∨ 0 < exponent) :
    powInt value exponent = roundRat format (q ^ exponent) := by
  simp only [powInt, hvalue]
  exact roundIntPower_eq_roundRat q exponent hdomain

/-- Compound rounds the exact rational expression `(1 + q) ^ exponent` once. -/
theorem compound_eq_roundRat (value : Model format) {q : Rat} (exponent : Int)
    (hvalue : value.toRat? = some q) (hdomain : 1 + q ≠ 0 ∨ 0 < exponent) :
    compound value exponent = roundRat format ((1 + q) ^ exponent) := by
  simp only [compound, hvalue]
  exact roundIntPower_eq_roundRat (1 + q) exponent hdomain

/-- Integer powers propagate NaR, including at exponent zero. -/
@[simp] theorem powInt_nar (exponent : Int) : powInt (nar format) exponent = nar format := by
  simp [powInt]

/-- Compound propagates NaR, including at exponent zero. -/
@[simp] theorem compound_nar (exponent : Int) : compound (nar format) exponent = nar format := by
  simp [compound]

/-- A zero base with negative integer exponent produces NaR. -/
theorem powInt_zero_of_neg (exponent : Int) (hexponent : exponent < 0) :
    powInt (zero format) exponent = nar format := by
  simp [powInt, roundIntPower, hexponent]

/-- Every finite input raised to the fixed integer zero produces rounded one. -/
theorem powInt_exponent_zero (value : Model format) {q : Rat}
    (hvalue : value.toRat? = some q) :
    powInt value 0 = roundRat format 1 := by
  simp [powInt, hvalue]

/-- Compound with fixed integer zero is constant one, including at input negative one. -/
theorem compound_exponent_zero (value : Model format) {q : Rat}
    (hvalue : value.toRat? = some q) :
    compound value 0 = roundRat format 1 := by
  simp [compound, hvalue]

/-- Positive integer powers of zero are zero. -/
theorem powInt_zero_of_pos (exponent : Int) (hexponent : 0 < exponent) :
    powInt (zero format) exponent = zero format := by
  simp [powInt, roundIntPower, not_lt.mpr hexponent.le, zero_zpow exponent (ne_of_gt hexponent),
    roundRat]

/-- Compound is undefined at base `1 + q = 0` and a negative exponent. -/
theorem compound_eq_nar_of_neg_one (value : Model format) (exponent : Int)
    (hvalue : value.toRat? = some (-1)) (hexponent : exponent < 0) :
    compound value exponent = nar format := by
  simp [compound, hvalue, roundIntPower, hexponent]

/-- Positive powers of the zero compound base give zero. -/
theorem compound_eq_zero_of_neg_one (value : Model format) (exponent : Int)
    (hvalue : value.toRat? = some (-1)) (hexponent : 0 < exponent) :
    compound value exponent = zero format := by
  simp [compound, hvalue, roundIntPower, not_lt.mpr hexponent.le,
    zero_zpow exponent (ne_of_gt hexponent), roundRat]

end FloatLib.Floats.Formats.Posit.Model
