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

The exact operations in `Calculation.Operations` refine real arithmetic through the shared
numerical-system contracts. Negation and multiplication require only integer arithmetic on the
stored mantissas and exponents.

The real-valued decoder is proof-facing and erased from compiled kernels.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq.FloatRep

open FloatLib.Numerics

/-- Executable mantissa negation exactly refines real negation. -/
theorem negExact_refines (β : Numerics.Radix) :
    Operation.Finite1 (numericalSystem β) (numericalSystem β)
      negExact (fun value : ℝ => -value) := by
  unfold Operation.Finite1 Operation.RefinesFinite1 NumericalSystem.Represents numericalSystem
  intro x value hx
  simp only [NumericalValue.finite.injEq] at hx ⊢
  rw [toReal_negExact]
  exact congrArg Neg.neg hx

/-- Executable mantissa/exponent multiplication exactly refines real multiplication. -/
theorem mulExact_refines (β : Numerics.Radix) :
    Operation.Finite2 (numericalSystem β) (numericalSystem β)
      (numericalSystem β) mulExact (fun left right : ℝ => left * right) := by
  unfold Operation.Finite2 Operation.RefinesFinite2 NumericalSystem.Represents numericalSystem
  intro x y left right hx hy
  simp only [NumericalValue.finite.injEq] at hx hy ⊢
  rw [toReal_mulExact, hx, hy]

end FloatLib.Floats.Formats.Flocq.FloatRep
