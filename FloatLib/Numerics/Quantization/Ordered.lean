/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.Defs.PartialOrder
public import FloatLib.Numerics.Core.System

/-!
# Order-theoretic representable neighbors

Directed and stochastic quantizers need the representable values immediately below and above an
exact input. These predicates use only a numerical system's denotation and the order on its finite
scalar domain. They do not assume a radix, field layout, unique encoding, or executable search
algorithm.
-/

@[expose] public section

namespace FloatLib.Numerics.Quantization.Ordered

/-- `code` represents the greatest representable scalar not exceeding `input`. -/
def LowerNeighbor (system : NumericalSystem) [Preorder system.Scalar]
    (input : system.Scalar) (code : system.Code) : Prop :=
  ∃ output,
    system.Represents code output ∧
      output ≤ input ∧
      ∀ candidate,
        system.Representable candidate → candidate ≤ input → candidate ≤ output

/-- `code` represents the least representable scalar not smaller than `input`. -/
def UpperNeighbor (system : NumericalSystem) [Preorder system.Scalar]
    (input : system.Scalar) (code : system.Code) : Prop :=
  ∃ output,
    system.Represents code output ∧
      input ≤ output ∧
      ∀ candidate,
        system.Representable candidate → input ≤ candidate → output ≤ candidate

/-- Lower neighbors are greatest elements of the representable values below the input. -/
theorem lowerNeighbor_iff_isGreatest (system : NumericalSystem) [Preorder system.Scalar]
    (input : system.Scalar) (code : system.Code) :
    LowerNeighbor system input code ↔
      ∃ output, system.Represents code output ∧
        IsGreatest {y | system.Representable y ∧ y ≤ input} output := by
  constructor
  · rintro ⟨output, hrep, hle, hgreatest⟩
    exact ⟨output, hrep, ⟨⟨⟨code, hrep⟩, hle⟩, fun _ h => hgreatest _ h.1 h.2⟩⟩
  · rintro ⟨output, hrep, ⟨hmem, hgreatest⟩⟩
    exact ⟨output, hrep, hmem.2, fun _ hrep hle => hgreatest ⟨hrep, hle⟩⟩

/-- Upper neighbors are least elements of the representable values above the input. -/
theorem upperNeighbor_iff_isLeast (system : NumericalSystem) [Preorder system.Scalar]
    (input : system.Scalar) (code : system.Code) :
    UpperNeighbor system input code ↔
      ∃ output, system.Represents code output ∧
        IsLeast {y | system.Representable y ∧ input ≤ y} output := by
  constructor
  · rintro ⟨output, hrep, hle, hleast⟩
    exact ⟨output, hrep, ⟨⟨⟨code, hrep⟩, hle⟩, fun _ h => hleast _ h.1 h.2⟩⟩
  · rintro ⟨output, hrep, ⟨hmem, hleast⟩⟩
    exact ⟨output, hrep, hmem.2, fun _ hrep hle => hleast ⟨hrep, hle⟩⟩

/-- Two codes bracket an input by its lower and upper representable neighbors. -/
def Brackets (system : NumericalSystem) [Preorder system.Scalar]
    (input : system.Scalar) (lower upper : system.Code) : Prop :=
  LowerNeighbor system input lower ∧ UpperNeighbor system input upper

/-- A lower-neighbor code has a finite denotation. -/
theorem lowerNeighbor_isFinite {system : NumericalSystem} [Preorder system.Scalar]
    {input : system.Scalar} {code : system.Code}
    (hcode : LowerNeighbor system input code) :
    system.IsFinite code := by
  obtain ⟨output, houtput, _⟩ := hcode
  exact ⟨output, houtput⟩

/-- An upper-neighbor code has a finite denotation. -/
theorem upperNeighbor_isFinite {system : NumericalSystem} [Preorder system.Scalar]
    {input : system.Scalar} {code : system.Code}
    (hcode : UpperNeighbor system input code) :
    system.IsFinite code := by
  obtain ⟨output, houtput, _⟩ := hcode
  exact ⟨output, houtput⟩

/-- Every lower-neighbor value lies below its exact input. -/
theorem lowerNeighbor_le {system : NumericalSystem} [Preorder system.Scalar]
    {input output : system.Scalar} {code : system.Code}
    (hcode : LowerNeighbor system input code)
    (houtput : system.Represents code output) :
    output ≤ input := by
  obtain ⟨selected, hselected, hle, _⟩ := hcode
  have : selected = output := by
    rw [NumericalSystem.Represents] at hselected houtput
    exact NumericalValue.finite.inj (hselected.symm.trans houtput)
  simpa [this] using hle

/-- Every upper-neighbor value lies above its exact input. -/
theorem le_upperNeighbor {system : NumericalSystem} [Preorder system.Scalar]
    {input output : system.Scalar} {code : system.Code}
    (hcode : UpperNeighbor system input code)
    (houtput : system.Represents code output) :
    input ≤ output := by
  obtain ⟨selected, hselected, hle, _⟩ := hcode
  have : selected = output := by
    rw [NumericalSystem.Represents] at hselected houtput
    exact NumericalValue.finite.inj (hselected.symm.trans houtput)
  simpa [this] using hle

end FloatLib.Numerics.Quantization.Ordered
