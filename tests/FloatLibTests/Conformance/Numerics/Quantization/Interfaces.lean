/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Directed
public import FloatLib.Numerics.Quantization.Saturating
public import FloatLib.Numerics.Quantization.Stochastic
public import Mathlib.Algebra.Order.Ring.Int

/-!
# Generic quantization-interface regression checks

These examples exercise the format-independent contracts directly. They intentionally use an
exact integer system rather than an IEEE format, so a future refactor cannot accidentally make
ordered, directed, saturating, or entropy-threaded quantization depend on a radix or field width.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Numerics.Quantization.Interfaces

open FloatLib.Numerics
open FloatLib.Numerics.Quantization

abbrev intSystem := NumericalSystem.exact Int

example (input : Int) :
    Ordered.LowerNeighbor intSystem input input := by
  refine ⟨input, ?_, le_rfl, ?_⟩
  · simp
  · intro candidate _ hcandidate
    exact hcandidate

example (input : Int) :
    Ordered.UpperNeighbor intSystem input input := by
  refine ⟨input, ?_, le_rfl, ?_⟩
  · simp
  · intro candidate _ hcandidate
    exact hcandidate

example :
    (Directed.towardNegative intSystem).Total := by
  intro _ input
  exact ⟨input, by
    refine ⟨input, ?_, le_rfl, ?_⟩
    · simp
    · intro candidate _ hcandidate
      exact hcandidate⟩

example : Saturating.clamp (0 : Int) 10 7 = 7 := by
  decide

example : Saturating.clamp (0 : Int) 10 13 = 10 := by
  decide

def parityEntropy (context : Bool) (entropy : Nat) (input : Int) :
    Operation.EntropyResult Nat Int :=
  ⟨if context then input else -input, entropy + 1⟩

def parityRelation (context : Bool) (entropy : Nat) (input result : Int)
    (nextEntropy : Nat) : Prop :=
  result = (if context then input else -input) ∧ nextEntropy = entropy + 1

theorem parityEntropy_refines :
    Operation.RefinesEntropy parityEntropy parityRelation := by
  intro context entropy input
  simp [parityEntropy, parityRelation]

example :
    (Stochastic.ofRelation parityRelation).Implements
      (fun state input => parityEntropy state.1 state.2 input) := by
  rw [Stochastic.implements_ofRelation_iff]
  exact parityEntropy_refines

end FloatLibTests.Conformance.Numerics.Quantization.Interfaces
