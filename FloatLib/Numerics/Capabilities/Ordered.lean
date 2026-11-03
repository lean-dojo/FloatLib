/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Directed

/-!
# Ordered-representability capability

This proof-only capability states that every exact scalar has representable lower and upper
neighbors. It provides the existence needed for total directed rounding without selecting an
executable search algorithm or adding order fields to the universal numerical-system structure.

The requirement covers the whole scalar type. A system with a largest or smallest finite value
in an unbounded scalar type, such as a bounded float, fixed-point or posit format read in `ℚ` or
`ℝ`, lacks a neighbor for inputs beyond that value and is never an instance; directed rounding
there needs an overflow result, which `Quantization.Directed` leaves unspecified. Exact systems are
the instance provided here.
-/

@[expose] public section

namespace FloatLib.Numerics

open Quantization.Ordered

/--
Every scalar admits both a lower and an upper representable neighbor. A system whose
representable values are bounded above or below in an unbounded scalar type cannot satisfy this.
-/
class OrderedRepresentable (system : NumericalSystem)
    [Preorder system.Scalar] : Prop where
  /-- Existence of a greatest representable value below an input. -/
  lower_exists :
    ∀ input, ∃ code, LowerNeighbor system input code
  /-- Existence of a least representable value above an input. -/
  upper_exists :
    ∀ input, ∃ code, UpperNeighbor system input code

/-- In an exact numerical system, each input is its own lower and upper neighbor. -/
instance exactOrderedRepresentable (α : Type) [Preorder α] :
    OrderedRepresentable (NumericalSystem.exact α) where
  lower_exists input := by
    refine ⟨input, input, ?_, le_rfl, ?_⟩
    · simp
    · intro candidate _ hcandidate
      exact hcandidate
  upper_exists input := by
    refine ⟨input, input, ?_, le_rfl, ?_⟩
    · simp
    · intro candidate _ hcandidate
      exact hcandidate

/-- Downward-directed quantization is total for an ordered-representable system. -/
theorem towardNegative_total (system : NumericalSystem) [Preorder system.Scalar]
    [OrderedRepresentable system] :
    (Quantization.Directed.towardNegative system).Total := by
  intro _ input
  exact OrderedRepresentable.lower_exists input

/-- Upward-directed quantization is total for an ordered-representable system. -/
theorem towardPositive_total (system : NumericalSystem) [Preorder system.Scalar]
    [OrderedRepresentable system] :
    (Quantization.Directed.towardPositive system).Total := by
  intro _ input
  exact OrderedRepresentable.upper_exists input

end FloatLib.Numerics
