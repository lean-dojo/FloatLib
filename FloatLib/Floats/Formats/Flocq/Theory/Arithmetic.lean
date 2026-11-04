/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Flocq.Calculation.Operations
public import FloatLib.Floats.Formats.Flocq.Theory.NumericalSystem
public import FloatLib.Numerics.Operation.Semantics

/-!
# Refinement contracts for exact integer-mantissa arithmetic

Through the shared numerical-system contracts, the exact operations of `Calculation.Operations`
refine real arithmetic. Negation and multiplication need nothing but integer arithmetic on the
stored mantissas and exponents: negate the mantissa, or multiply the mantissas and add the
exponents.

The real-valued decoder exists for proofs and is erased from compiled kernels.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq.FloatRep

open FloatLib.Numerics

/-- Executable mantissa negation refines real negation with no rounding. -/
theorem negExact_refines (β : Numerics.Radix) :
    Operation.Finite1 (numericalSystem β) (numericalSystem β)
      negExact (fun value : ℝ => -value) := by
  unfold Operation.Finite1 Operation.RefinesFinite1 NumericalSystem.Represents numericalSystem
  intro x value hx
  simp only [NumericalValue.finite.injEq] at hx ⊢
  rw [toReal_negExact]
  exact congrArg Neg.neg hx

/-- Executable mantissa and exponent multiplication refines real multiplication with no rounding. -/
theorem mulExact_refines (β : Numerics.Radix) :
    Operation.Finite2 (numericalSystem β) (numericalSystem β)
      (numericalSystem β) mulExact (fun left right : ℝ => left * right) := by
  unfold Operation.Finite2 Operation.RefinesFinite2 NumericalSystem.Represents numericalSystem
  intro x y left right hx hy
  simp only [NumericalValue.finite.injEq] at hx hy ⊢
  rw [toReal_mulExact, hx, hy]

end FloatLib.Floats.Formats.Flocq.FloatRep
