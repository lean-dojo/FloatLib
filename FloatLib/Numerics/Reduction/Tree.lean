/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Nat.Log

/-!
# Parenthesized reductions

`ReductionTree` records a nonempty reduction without choosing an arithmetic implementation. Values
sit at the leaves, unlike Mathlib's `BinaryTree`, which keeps them at internal nodes. (a + b) + (c +
d) and ((a + b) + c) + d are two different trees over the same four leaves, and in floating point
they can round differently. An empty reduction needs an identity chosen on its own and isn't
represented here.

A loop that combines its accumulator with one more input at each step is one of these schedules,
the left chain `leftChain init inputs`: its evaluation is the left fold (`eval_leftChain`), so a
statement about every schedule holds for every such loop.

A schedule has a size, `nodeCount`, and a `depth`, the largest number of combining operations
between an input and the result. Over `n` inputs the size is always `n - 1` (`length_leaves`), and
the depth lies between `⌈log₂ n⌉` (`clog_le_depth`) and `n - 1`, which the left chain reaches
(`depth_leftChain`). The rounding-error bounds of `Reduction.Error` grow with the depth.
-/

@[expose] public section

namespace FloatLib.Numerics

/-- A nonempty collection of inputs together with a binary evaluation schedule. -/
inductive ReductionTree (α : Type*) where
  /-- One input. -/
  | leaf (value : α)
  /-- The combination of the results of two subtrees. -/
  | node (left right : ReductionTree α)
  deriving Repr, DecidableEq

namespace ReductionTree

variable {α β γ : Type*}

/-- Input occurrences in left-to-right order, including repetitions. -/
def leaves : ReductionTree α → List α
  | .leaf x => [x]
  | .node a b => a.leaves ++ b.leaves

/-- Evaluate the chosen schedule. The combining operation need not be associative. -/
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

/-- The depth of the schedule: the largest number of combining operations between an input and
the result. A single input has depth zero. -/
def depth : ReductionTree α → Nat
  | .leaf _ => 0
  | .node a b => max a.depth b.depth + 1

/-- Changing leaf values does not change the depth. -/
@[simp] theorem depth_map (t : ReductionTree α) (f : α → β) : (t.map f).depth = t.depth := by
  induction t with
  | leaf x => rfl
  | node a b ha hb => simp [map, depth, ha, hb]

/-- No input passes through more combining operations than the schedule has. -/
theorem depth_le_nodeCount (t : ReductionTree α) : t.depth ≤ t.nodeCount := by
  induction t with
  | leaf _ => exact Nat.le_refl 0
  | node a b ha hb =>
    simp only [depth, nodeCount]
    omega

/-- A schedule of depth `d` has at most `2 ^ d` inputs. -/
theorem length_leaves_le_two_pow_depth (t : ReductionTree α) :
    t.leaves.length ≤ 2 ^ t.depth := by
  induction t with
  | leaf x => simp [leaves, depth]
  | node a b ha hb =>
    have hla : 2 ^ a.depth ≤ 2 ^ max a.depth b.depth :=
      Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _)
    have hlb : 2 ^ b.depth ≤ 2 ^ max a.depth b.depth :=
      Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _)
    simp only [leaves, List.length_append, depth, Nat.pow_succ]
    omega

/-- A schedule over `n` inputs has depth at least `⌈log₂ n⌉`. -/
theorem clog_le_depth (t : ReductionTree α) : Nat.clog 2 t.leaves.length ≤ t.depth :=
  Nat.clog_le_of_le_pow t.length_leaves_le_two_pow_depth

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

/-- A predicate that holds for every pair of operands holds at every node of every schedule. -/
theorem AllNodes.of_forall (t : ReductionTree α) (combine : β → β → β) (value : α → β)
    {p : β → β → Prop} (h : ∀ x y, p x y) : t.AllNodes combine value p := by
  induction t with
  | leaf _ => trivial
  | node a b ha hb => exact ⟨ha, hb, h _ _⟩

/-! ## The left chain -/

/-- The left chain from `init` over the entries of a list: the schedule of a loop that combines
its accumulator with one more input at each step. -/
def leftChain (init : α) (inputs : List α) : ReductionTree α :=
  inputs.foldl (fun tree input => .node tree (.leaf input)) (.leaf init)

/-- Evaluating a schedule that a chain of inputs continues folds the inputs onto the value of
the schedule. -/
theorem eval_foldl_node (combine : β → β → β) (value : α → β) (inputs : List α)
    (tree : ReductionTree α) :
    (inputs.foldl (fun tree input => .node tree (.leaf input)) tree).eval combine value =
      inputs.foldl (fun acc input => combine acc (value input)) (tree.eval combine value) := by
  induction inputs generalizing tree with
  | nil => rfl
  | cons input rest ih => simp only [List.foldl_cons, ih, eval]

/-- Evaluating the left chain is the left fold from the value of `init`. -/
theorem eval_leftChain (combine : β → β → β) (value : α → β) (init : α) (inputs : List α) :
    (leftChain init inputs).eval combine value =
      inputs.foldl (fun acc input => combine acc (value input)) (value init) :=
  eval_foldl_node combine value inputs (.leaf init)

/-- The leaves of the left chain are `init` and the inputs, in order. -/
theorem leaves_leftChain (init : α) (inputs : List α) :
    (leftChain init inputs).leaves = init :: inputs := by
  have h : ∀ tree : ReductionTree α,
      (inputs.foldl (fun tree input => .node tree (.leaf input)) tree).leaves =
        tree.leaves ++ inputs := by
    induction inputs with
    | nil => intro tree; simp
    | cons input rest ih =>
      intro tree
      simp only [List.foldl_cons, ih, leaves, List.append_assoc, List.singleton_append]
  exact h (.leaf init)

/-- The left chain combines once for each input. -/
theorem nodeCount_leftChain (init : α) (inputs : List α) :
    (leftChain init inputs).nodeCount = inputs.length := by
  have h := length_leaves (leftChain init inputs)
  rw [leaves_leftChain, List.length_cons] at h
  exact (Nat.add_right_cancel h).symm

/-- The left chain is the deepest schedule over its inputs: `init` passes through every
combining operation. -/
theorem depth_leftChain (init : α) (inputs : List α) :
    (leftChain init inputs).depth = inputs.length := by
  have h : ∀ tree : ReductionTree α,
      (inputs.foldl (fun tree input => .node tree (.leaf input)) tree).depth =
        tree.depth + inputs.length := by
    induction inputs with
    | nil => intro tree; rfl
    | cons input rest ih =>
      intro tree
      simp only [List.foldl_cons, ih, depth, List.length_cons]
      omega
  simpa [depth, leftChain] using h (.leaf init)

end ReductionTree
end FloatLib.Numerics
