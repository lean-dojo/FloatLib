/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.MixedError.Basic

/-!
# Error bounds through list loops

A loop `input.foldl step initial` is analyzed by bounding one step for a symbolic accumulator
whose error against its reference is given. These lemmas carry that step bound through the whole
traversal, in its own order. The conditions of a step are required only at the states the loop
actually visits (`List.AllSteps`), not at every possible accumulator, and the accumulated budgets
are the recurrences `List.foldError`, `List.foldRelative` and `List.foldAbsolute` run alongside
the loop; a step that keeps zero budgets zero keeps them zero (`List.foldBudgets_eq_zero`).
Arrays, vectors and loops over `Fin n` reach these lemmas through their list traversals.
-/

@[expose] public section

namespace List

open FloatLib.Numerics

variable {α β γ : Type*}

/-- A condition holds at every step of this execution, before the step advances the
accumulator. -/
def AllSteps (step : α → β → α) (condition : α → β → Prop) : α → List β → Prop
  | _, [] => True
  | state, value :: rest => condition state value ∧ AllSteps step condition (step state value) rest

/-- The visited conditions are decidable when each condition is. -/
instance AllSteps.instDecidable (step : α → β → α) (condition : α → β → Prop)
    [∀ state value, Decidable (condition state value)] :
    ∀ (initial : α) (input : List β), Decidable (AllSteps step condition initial input)
  | _, [] => inferInstanceAs (Decidable True)
  | state, value :: rest =>
      have := AllSteps.instDecidable step condition (step state value) rest
      inferInstanceAs (Decidable (condition state value ∧ _))

/-- An invariant need only be preserved at the steps whose conditions hold. -/
theorem AllSteps.invariant {step : α → β → α} {condition : α → β → Prop} {invariant : α → Prop}
    {initial : α} {input : List β} (hvalid : AllSteps step condition initial input)
    (hinit : invariant initial)
    (hstep : ∀ state value, condition state value → invariant state →
      invariant (step state value)) : invariant (input.foldl step initial) := by
  induction input generalizing initial with
  | nil => exact hinit
  | cons value rest ih => exact ih hvalid.2 (hstep _ _ hvalid.1 hinit)

/-- Two conditions at the visited steps hold together. -/
theorem AllSteps.and {step : α → β → α} {condition other : α → β → Prop} {initial : α}
    {input : List β} (hcondition : AllSteps step condition initial input)
    (hother : AllSteps step other initial input) :
    AllSteps step (fun state value => condition state value ∧ other state value) initial input := by
  induction input generalizing initial with
  | nil => trivial
  | cons value rest ih => exact ⟨⟨hcondition.1, hother.1⟩, ih hcondition.2 hother.2⟩

/-- The conditions at the visited steps of a loop extended by one element. -/
theorem allSteps_append_singleton (step : α → β → α) (condition : α → β → Prop) (initial : α)
    (input : List β) (value : β) :
    AllSteps step condition initial (input ++ [value]) ↔
      AllSteps step condition initial input ∧ condition (input.foldl step initial) value := by
  induction input generalizing initial with
  | nil => simp [AllSteps]
  | cons head rest ih => simp [AllSteps, ih, and_assoc]

/-- Conditions that do not read auxiliary state can be checked on the original accumulator. -/
theorem AllSteps.of_map (step : α → β → α) (condition : α → β → Prop) (initial : α)
    (input : List β) (interpret : α → γ) (step' : γ → β → γ) (condition' : γ → β → Prop)
    (hstep : ∀ state value, interpret (step state value) = step' (interpret state) value)
    (hcondition : ∀ state value, condition state value = condition' (interpret state) value)
    (hvalid : AllSteps step' condition' (interpret initial) input) :
    AllSteps step condition initial input := by
  induction input generalizing initial with
  | nil => trivial
  | cons value rest ih =>
      refine ⟨(hcondition initial value).symm ▸ hvalid.1, ih (step initial value) ?_⟩
      rw [hstep]
      exact hvalid.2

/-- A condition that holds everywhere holds at the visited steps. -/
theorem AllSteps.of_forall (step : α → β → α) (condition : α → β → Prop) (initial : α)
    (input : List β) (hcondition : ∀ state value, condition state value) :
    AllSteps step condition initial input := by
  induction input generalizing initial with
  | nil => trivial
  | cons value rest ih => exact ⟨hcondition _ _, ih _⟩

/-- A property of the accumulator that every step keeps holds of the result of the loop. -/
theorem foldl_induction {step : α → β → α} {initial : α} {input : List β} (motive : α → Prop)
    (hinit : motive initial) (hstep : ∀ state value, motive state → motive (step state value)) :
    motive (input.foldl step initial) :=
  AllSteps.invariant (condition := fun _ _ => True) (AllSteps.of_forall _ _ _ _ fun _ _ => trivial)
    hinit fun state value _ => hstep state value

/-- One iteration of the absolute-error bookkeeping: the original step, the real reference and
the error budget. -/
def foldStep (step : α → β → α) (reference : ℝ → β → ℝ) (error : α → ℝ → ℝ → β → ℝ)
    (state : α × ℝ × ℝ) (value : β) : α × ℝ × ℝ :=
  (step state.1 value, reference state.2.1 value, error state.1 state.2.1 state.2.2 value)

/-- The absolute error accumulated in the loop's own traversal order. -/
def foldError (step : α → β → α) (reference : ℝ → β → ℝ) (error : α → ℝ → ℝ → β → ℝ)
    (initial : α) (initialReference initialError : ℝ) (input : List β) : ℝ :=
  (input.foldl (foldStep step reference error) (initial, initialReference, initialError)).2.2

/-- A step that keeps the incoming budget keeps it through the whole loop. -/
@[simp] theorem foldError_identity (step : α → β → α) (reference : ℝ → β → ℝ) (initial : α)
    (initialReference initialError : ℝ) (input : List β) :
    foldError step reference (fun _ _ error _ => error) initial initialReference initialError
      input = initialError := by
  unfold foldError
  induction input generalizing initial initialReference with
  | nil => rfl
  | cons value rest ih => exact ih _ _

/-- Lift a bound on one step through a list loop, including the initial error. -/
theorem fold_error (observe : α → ℝ) (step : α → β → α) (reference : ℝ → β → ℝ)
    (error : α → ℝ → ℝ → β → ℝ) (condition : α → ℝ → ℝ → β → Prop)
    (initial : α) (initialReference initialError : ℝ) (input : List β)
    (hinit : |observe initial - initialReference| ≤ initialError)
    (hstep : ∀ state realValue budget value, condition state realValue budget value →
      |observe state - realValue| ≤ budget →
      |observe (step state value) - reference realValue value| ≤
        error state realValue budget value)
    (hvalid : AllSteps (foldStep step reference error)
      (fun state value => condition state.1 state.2.1 state.2.2 value)
      (initial, initialReference, initialError) input) :
    |observe (input.foldl step initial) - input.foldl reference initialReference| ≤
      foldError step reference error initial initialReference initialError input := by
  unfold foldError
  induction input generalizing initial initialReference initialError with
  | nil => exact hinit
  | cons value rest ih => exact ih _ _ _ (hstep _ _ _ _ hvalid.1 hinit) hvalid.2

/-- One iteration of the mixed-error bookkeeping: the original step, the real reference, and the
relative and absolute parts of the error. -/
def mixedFoldStep (step : α → β → α) (reference : ℝ → β → ℝ)
    (relative absolute : α → ℝ → ℝ → ℝ → β → ℝ) (state : α × ℝ × ℝ × ℝ) (value : β) :
    α × ℝ × ℝ × ℝ :=
  (step state.1 value, reference state.2.1 value,
    relative state.1 state.2.1 state.2.2.1 state.2.2.2 value,
    absolute state.1 state.2.1 state.2.2.1 state.2.2.2 value)

/-- The relative error accumulated in the loop's own traversal order. -/
def foldRelative (step : α → β → α) (reference : ℝ → β → ℝ)
    (relative absolute : α → ℝ → ℝ → ℝ → β → ℝ) (initial : α)
    (initialReference initialRelative initialAbsolute : ℝ) (input : List β) : ℝ :=
  (input.foldl (mixedFoldStep step reference relative absolute)
    (initial, initialReference, initialRelative, initialAbsolute)).2.2.1

/-- The absolute error accumulated in the loop's own traversal order. -/
def foldAbsolute (step : α → β → α) (reference : ℝ → β → ℝ)
    (relative absolute : α → ℝ → ℝ → ℝ → β → ℝ) (initial : α)
    (initialReference initialRelative initialAbsolute : ℝ) (input : List β) : ℝ :=
  (input.foldl (mixedFoldStep step reference relative absolute)
    (initial, initialReference, initialRelative, initialAbsolute)).2.2.2

/-- A step that keeps zero budgets zero, such as an exact maximum, keeps them zero through the
whole loop. -/
theorem foldBudgets_eq_zero (step : α → β → α) (reference : ℝ → β → ℝ)
    (relative absolute : α → ℝ → ℝ → ℝ → β → ℝ) (initial : α) (initialReference : ℝ)
    (input : List β) (hrelative : ∀ state realValue value, relative state realValue 0 0 value = 0)
    (habsolute : ∀ state realValue value, absolute state realValue 0 0 value = 0) :
    foldRelative step reference relative absolute initial initialReference 0 0 input = 0 ∧
      foldAbsolute step reference relative absolute initial initialReference 0 0 input = 0 := by
  unfold foldRelative foldAbsolute
  induction input generalizing initial initialReference with
  | nil => exact ⟨rfl, rfl⟩
  | cons value rest ih =>
    simp only [List.foldl_cons, mixedFoldStep, hrelative, habsolute]
    exact ih _ _

/-- Lift a mixed bound on one step through a list loop. The relation `invariant` between the
accumulator and its reference, such as finiteness or a sign, holds initially and is preserved at
each step together with the bound. -/
theorem fold_mixedError (observe : α → ℝ) (step : α → β → α) (reference : ℝ → β → ℝ)
    (relative absolute : α → ℝ → ℝ → ℝ → β → ℝ) (invariant : α → ℝ → Prop)
    (condition : α → ℝ → ℝ → ℝ → β → Prop) (initial : α)
    (initialReference initialRelative initialAbsolute : ℝ) (input : List β)
    (hinit : MixedError (observe initial) initialReference initialRelative initialAbsolute ∧
      invariant initial initialReference)
    (hstep : ∀ state realValue r a value, condition state realValue r a value →
      MixedError (observe state) realValue r a ∧ invariant state realValue →
      MixedError (observe (step state value)) (reference realValue value)
          (relative state realValue r a value) (absolute state realValue r a value) ∧
        invariant (step state value) (reference realValue value))
    (hvalid : AllSteps (mixedFoldStep step reference relative absolute)
      (fun state value => condition state.1 state.2.1 state.2.2.1 state.2.2.2 value)
      (initial, initialReference, initialRelative, initialAbsolute) input) :
    MixedError (observe (input.foldl step initial)) (input.foldl reference initialReference)
        (foldRelative step reference relative absolute initial initialReference initialRelative
          initialAbsolute input)
        (foldAbsolute step reference relative absolute initial initialReference initialRelative
          initialAbsolute input) ∧
      invariant (input.foldl step initial) (input.foldl reference initialReference) := by
  unfold foldRelative foldAbsolute
  induction input generalizing initial initialReference initialRelative initialAbsolute with
  | nil => exact hinit
  | cons value rest ih => exact ih _ _ _ _ (hstep _ _ _ _ _ hvalid.1 hinit) hvalid.2

end List
