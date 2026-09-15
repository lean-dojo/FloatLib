/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Core.System
public import Mathlib.Algebra.Order.Ring.Abs

/-!
# Representation-independent error contracts

An error theorem should describe a particular executable kernel, exact interpretation, error
measure, and bound. The universal numerical system therefore carries no mandatory norm or field
structure. This proof-only capability accepts all four as parameters and works for absolute,
relative, ulp, interval, vector, or family-specific measures.
-/

@[expose] public section

namespace FloatLib.Numerics

universe u v

/--
A code-producing kernel represents some finite result whose measured error satisfies `bound`.

The class lives in `Prop`, so the capability adds no runtime data to the kernel.
-/
class HasErrorBound {Input : Type u} {Bound : Type v} [LE Bound]
    (system : NumericalSystem)
    (run : Input → system.Code)
    (exact : Input → system.Scalar)
    (measure : system.Scalar → system.Scalar → Bound)
    (bound : Input → Bound) : Prop where
  /-- Every kernel result has a finite denotation within its declared error bound. -/
  error_le :
    ∀ input, ∃ actual,
      system.Represents (run input) actual ∧
        measure actual (exact input) ≤ bound input

/--
Absolute difference `|actual - exact|` in an additive commutative group with a linear order.
The definition does not require the order to be compatible with addition.
-/
@[inline] def absoluteError {α : Type} [AddCommGroup α] [LinearOrder α]
    (actual exact : α) : α :=
  |actual - exact|

/-- Extract the represented finite result guaranteed by an error-bound capability. -/
theorem HasErrorBound.exists_represents {Input : Type u} {Bound : Type v} [LE Bound]
    {system : NumericalSystem}
    {run : Input → system.Code}
    {exact : Input → system.Scalar}
    {measure : system.Scalar → system.Scalar → Bound}
    {bound : Input → Bound}
    [HasErrorBound system run exact measure bound]
    (input : Input) :
    ∃ actual, system.Represents (run input) actual :=
  let ⟨actual, hactual, _⟩ :=
    HasErrorBound.error_le (system := system) (run := run)
      (exact := exact) (measure := measure) (bound := bound) input
  ⟨actual, hactual⟩

end FloatLib.Numerics
