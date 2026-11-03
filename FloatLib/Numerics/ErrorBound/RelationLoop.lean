/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.ErrorBound.Loop

/-!
# Loops related to a shadow state

A loop `input.foldl step initial` whose state is a tuple, such as a running maximum beside a
rescaled sum, is compared at each step with a shadow state, `input.foldl reference shadow`, of
real references and discrete data, and with budgets that a recurrence run alongside the loop
accumulates (`List.foldBudget`). `List.fold_relation` lifts a relation that one step preserves,
under a condition at the visited states, through the whole traversal.
-/

@[expose] public section

namespace List

variable {α β ρ κ : Type*}

/-- One iteration of a loop together with its shadow state and its budgets. -/
def relationFoldStep (step : α → β → α) (reference : ρ → β → ρ)
    (budget : α → ρ → κ → β → κ) (state : α × ρ × κ) (value : β) : α × ρ × κ :=
  (step state.1 value, reference state.2.1 value, budget state.1 state.2.1 state.2.2 value)

/-- The budgets that `relationFoldStep` accumulates in the loop's own traversal order. -/
def foldBudget (step : α → β → α) (reference : ρ → β → ρ) (budget : α → ρ → κ → β → κ)
    (initial : α) (shadow : ρ) (budgets : κ) (input : List β) : κ :=
  (input.foldl (relationFoldStep step reference budget) (initial, shadow, budgets)).2.2

@[simp]
theorem foldBudget_nil (step : α → β → α) (reference : ρ → β → ρ)
    (budget : α → ρ → κ → β → κ) (initial : α) (shadow : ρ) (budgets : κ) :
    foldBudget step reference budget initial shadow budgets [] = budgets :=
  rfl

@[simp]
theorem foldBudget_cons (step : α → β → α) (reference : ρ → β → ρ)
    (budget : α → ρ → κ → β → κ) (initial : α) (shadow : ρ) (budgets : κ) (value : β)
    (rest : List β) :
    foldBudget step reference budget initial shadow budgets (value :: rest) =
      foldBudget step reference budget (step initial value) (reference shadow value)
        (budget initial shadow budgets value) rest :=
  rfl

/-- The first two components of the loop that `relationFoldStep` runs are the loop itself and its
shadow loop. -/
theorem foldl_relationFoldStep (step : α → β → α) (reference : ρ → β → ρ)
    (budget : α → ρ → κ → β → κ) (initial : α) (shadow : ρ) (budgets : κ) (input : List β) :
    input.foldl (relationFoldStep step reference budget) (initial, shadow, budgets) =
      (input.foldl step initial, input.foldl reference shadow,
        foldBudget step reference budget initial shadow budgets input) := by
  unfold foldBudget
  induction input generalizing initial shadow budgets with
  | nil => rfl
  | cons value rest ih => exact ih _ _ _

/-- A relation between a loop's state, its shadow state and its budgets that one step preserves
holds after the loop when the condition holds at every visited state. -/
theorem fold_relation (step : α → β → α) (reference : ρ → β → ρ)
    (budget : α → ρ → κ → β → κ) (relation : α → ρ → κ → Prop)
    (condition : α → ρ → κ → β → Prop) (initial : α) (shadow : ρ) (budgets : κ)
    (input : List β) (hinit : relation initial shadow budgets)
    (hstep : ∀ state realState budgets value, condition state realState budgets value →
      relation state realState budgets →
      relation (step state value) (reference realState value)
        (budget state realState budgets value))
    (hvalid : AllSteps (relationFoldStep step reference budget)
      (fun state value => condition state.1 state.2.1 state.2.2 value) (initial, shadow, budgets)
      input) :
    relation (input.foldl step initial) (input.foldl reference shadow)
      (foldBudget step reference budget initial shadow budgets input) := by
  unfold foldBudget
  induction input generalizing initial shadow budgets with
  | nil => exact hinit
  | cons value rest ih => exact ih _ _ _ (hstep _ _ _ _ hvalid.1 hinit) hvalid.2

end List
