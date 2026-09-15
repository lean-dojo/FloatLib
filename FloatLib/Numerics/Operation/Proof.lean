/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Numerics.Operation.Proof.Total
public import FloatLib.Numerics.Operation.Proof.Finite
public import FloatLib.Numerics.Operation.Proof.Checked
public import FloatLib.Numerics.Operation.Proof.Quantizer

/-!
# Proof-indexed application of numerical operations

These helpers apply existing executable functions to proof-indexed inputs. Runtime data remains
the concrete code returned by those functions; representation proofs are propositions erased by
the compiler.

The imports collect total, finite, checked, and quantizer proof helpers. The composition laws
below combine refinement facts directly, without wrapping the executable functions. Import a
`Proof.*` submodule when only one proof-indexed contract family is needed.
-/

@[expose] public section

/-! ## Composition of executable refinements -/

namespace FloatLib.Numerics.Operation

/-- Total unary refinement is closed under composition. -/
theorem total1_comp {A B C : NumericalSystem} {run₁ : A.Code → B.Code}
    {run₂ : B.Code → C.Code} {spec₁ : NumericalValue A.Scalar → NumericalValue B.Scalar}
    {spec₂ : NumericalValue B.Scalar → NumericalValue C.Scalar}
    (h₁ : Total1 A B run₁ spec₁) (h₂ : Total1 B C run₂ spec₂) :
    Total1 A C (run₂ ∘ run₁) (spec₂ ∘ spec₁) := by
  intro x
  change C.denote (run₂ (run₁ x)) = spec₂ (spec₁ (A.denote x))
  rw [h₂ (run₁ x), h₁ x]

/-- Finite unary refinement is closed under composition. -/
theorem finite1_comp {A B C : NumericalSystem} {run₁ : A.Code → B.Code}
    {run₂ : B.Code → C.Code} {spec₁ : A.Scalar → B.Scalar}
    {spec₂ : B.Scalar → C.Scalar}
    (h₁ : Finite1 A B run₁ spec₁) (h₂ : Finite1 B C run₂ spec₂) :
    Finite1 A C (run₂ ∘ run₁) (spec₂ ∘ spec₁) := by
  intro code x hx
  exact h₂ _ _ (h₁ code x hx)

/-- Casts implement the composed scalar maps when the intermediate value meets its precondition. -/
theorem castFiniteOn_comp {A B C : NumericalSystem} {run₁ : A.Code → B.Code}
    {run₂ : B.Code → C.Code} {embed₁ : A.Scalar → B.Scalar}
    {embed₂ : B.Scalar → C.Scalar} {pre₁ : A.Scalar → Prop} {pre₂ : B.Scalar → Prop}
    (h₁ : CastFiniteOn A B run₁ embed₁ pre₁)
    (h₂ : CastFiniteOn B C run₂ embed₂ pre₂) :
    CastFiniteOn A C (run₂ ∘ run₁) (embed₂ ∘ embed₁)
      (fun x => pre₁ x ∧ pre₂ (embed₁ x)) := by
  intro code x hx hcode
  exact h₂ _ _ hx.2 (h₁ code x hx.1 hcode)

/-- A refining quantizer is exact wherever its mathematical rounding map fixes the input. -/
theorem quantizer_exactOn {S : NumericalSystem} {quantize : S.Scalar → S.Code}
    {round : S.Scalar → S.Scalar} {pre fixed : S.Scalar → Prop}
    (hrefines : QuantizerOn S quantize round pre)
    (hfixed : ∀ x, fixed x → round x = x) :
    ∀ x, pre x → fixed x → S.Represents (quantize x) x := by
  intro x hpre hfix
  simpa [hfixed x hfix] using hrefines x hpre

end FloatLib.Numerics.Operation
