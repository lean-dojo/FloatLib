/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Parenthesized reductions

`ReductionTree` records a nonempty reduction without choosing an arithmetic implementation.
Unlike mathlib's `BinaryTree`, values occur at leaves, not internal nodes. An empty reduction
needs a separately chosen identity and is deliberately not represented here.
-/

@[expose] public section

namespace FloatLib.Numerics

/-- A nonempty collection of inputs together with a binary evaluation schedule. -/
inductive ReductionTree (α : Type*) where
  | leaf (value : α)
  | node (left right : ReductionTree α)
  deriving Repr, DecidableEq

namespace ReductionTree

variable {α β γ : Type*}

/-- Input occurrences in left-to-right order, including repetitions. -/
def leaves : ReductionTree α → List α
  | .leaf x => [x]
  | .node a b => a.leaves ++ b.leaves

/-- Evaluate the chosen schedule; the combining operation need not be associative. -/
def eval (combine : β → β → β) (value : α → β) : ReductionTree α → β
  | .leaf x => value x
  | .node a b => combine (a.eval combine value) (b.eval combine value)

/-- Change leaf values without changing the evaluation schedule. -/
def map (f : α → β) : ReductionTree α → ReductionTree β
  | .leaf x => .leaf (f x)
  | .node a b => .node (a.map f) (b.map f)

/-- Mapping leaves commutes with evaluation. -/
@[simp] theorem eval_map (t : ReductionTree α) (f : α → β)
    (combine : γ → γ → γ) (value : β → γ) :
    (t.map f).eval combine value = t.eval combine (value ∘ f) := by
  induction t with
  | leaf x => rfl
  | node a b ha hb => simp [map, eval, ha, hb]

/-- Mapping preserves the order and multiplicity of leaf occurrences. -/
@[simp] theorem leaves_map (t : ReductionTree α) (f : α → β) :
    (t.map f).leaves = t.leaves.map f := by
  induction t with
  | leaf x => rfl
  | node a b ha hb => simp [map, leaves, ha, hb]

/-- Number of combining operations in the schedule. -/
def nodeCount : ReductionTree α → Nat
  | .leaf _ => 0
  | .node a b => a.nodeCount + b.nodeCount + 1

/-- A full binary reduction performs one fewer addition than it has inputs. -/
theorem length_leaves (t : ReductionTree α) : t.leaves.length = t.nodeCount + 1 := by
  induction t with
  | leaf x => simp [leaves, nodeCount]
  | node a b ha hb =>
    simp only [leaves, List.length_append, nodeCount, ha, hb]
    omega

/-- A permutation of inputs cannot change the number of combining operations. -/
theorem nodeCount_eq_of_perm {a b : ReductionTree α} (h : a.leaves.Perm b.leaves) :
    a.nodeCount = b.nodeCount := by
  have hlength := h.length_eq
  rw [length_leaves, length_leaves] at hlength
  exact Nat.add_right_cancel hlength

/-- A predicate on the two evaluated operands holds at every internal node of this tree. -/
def AllNodes (combine : β → β → β) (value : α → β) (p : β → β → Prop) :
    ReductionTree α → Prop
  | .leaf _ => True
  | .node a b => a.AllNodes combine value p ∧ b.AllNodes combine value p ∧
      p (a.eval combine value) (b.eval combine value)

/-- Interpretation commutes with evaluation when it preserves the actual operations used. -/
theorem map_eval (t : ReductionTree α) (combine : β → β → β) (value : α → β)
    (interpret : β → γ) (combine' : γ → γ → γ)
    (h : t.AllNodes combine value
      (fun x y => interpret (combine x y) = combine' (interpret x) (interpret y))) :
    interpret (t.eval combine value) = t.eval combine' (interpret ∘ value) := by
  induction t with
  | leaf x => rfl
  | node a b ha hb =>
    rw [AllNodes] at h
    simp only [eval, h.2.2, ha h.1, hb h.2.1]

/-- Exact additive evaluation agrees with the ordinary list sum. -/
theorem eval_add_eq_sum [AddMonoid β] (t : ReductionTree α) (value : α → β) :
    t.eval (· + ·) value = (t.leaves.map value).sum := by
  induction t with
  | leaf x => simp [eval, leaves]
  | node a b ha hb => simp [eval, leaves, ha, hb]

/-- Reordering leaves or changing parentheses preserves an exact commutative sum. -/
theorem eval_add_eq_of_perm [AddCommMonoid β] {a b : ReductionTree α}
    (h : a.leaves.Perm b.leaves) (value : α → β) :
    a.eval (· + ·) value = b.eval (· + ·) value := by
  rw [eval_add_eq_sum, eval_add_eq_sum]
  exact (h.map value).sum_eq

end ReductionTree
end FloatLib.Numerics
