/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Reduction.Tree
public import Mathlib.Basic.Real.Basic

import FloatLib.Numerics.ErrorBound.Algebra
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.RingNF

/-!
# Error of repeatedly rounded reductions

Our main bound adds the local absolute errors at the nodes a reduction visits. It applies to any
carrier with a real interpretation, so an executable floating-point tree doesn't first have to be
replaced by a globally defined real rounding function.

`mixedBudget` propagates relative and absolute local errors through the schedule. The absolute term
can cover gradual underflow, and setting it to zero gives a relative-error specialization. These are
round-per-node bounds, and they say nothing about an exact accumulator rounded only at the end.

The relative-only budget is at most `((1 + u) ^ depth - 1) * Σ |xᵢ|` (`mixedBudget_zero_le_depth`,
`abs_eval_sub_exact_le_depth`): an input is rounded once at each node above it, so the bound grows
with the depth of the schedule. The bounds in the number of additions (`mixedBudget_zero_le`,
`abs_eval_sub_exact_le_geometric`) follow, since no schedule is deeper than its size.
-/

@[expose] public section

namespace FloatLib.Numerics.ReductionTree

variable {α β : Type*}

/-- Sum of local error allowances, evaluated at the actual operands of each internal node. -/
noncomputable def errorBudget (combine : β → β → β) (value : α → β)
    (allowance : β → β → ℝ) : ReductionTree α → ℝ
  | .leaf _ => 0
  | .node a b => a.errorBudget combine value allowance + b.errorBudget combine value allowance +
      allowance (a.eval combine value) (b.eval combine value)

/-- Local bounds are required only for pairs of operands encountered in this schedule. -/
theorem abs_eval_sub_exact_le_errorBudget (t : ReductionTree α)
    (combine : β → β → β) (value : α → β) (interpret : β → ℝ)
    (allowance : β → β → ℝ)
    (h : t.AllNodes combine value (fun x y =>
      |interpret (combine x y) - (interpret x + interpret y)| ≤ allowance x y)) :
    |interpret (t.eval combine value) - t.eval (· + ·) (interpret ∘ value)| ≤
      t.errorBudget combine value allowance := by
  induction t with
  | leaf x => simp [eval, errorBudget]
  | node a b ha hb =>
    exact add_error (ha h.1) (hb h.2.1) h.2.2

/-- A uniform absolute allowance is paid once per addition, independently of tree shape. -/
theorem errorBudget_const (t : ReductionTree α) (combine : β → β → β)
    (value : α → β) (δ : ℝ) :
    t.errorBudget combine value (fun _ _ => δ) = t.nodeCount * δ := by
  induction t with
  | leaf x => simp [errorBudget, nodeCount]
  | node a b ha hb => simp only [errorBudget, ha, hb, nodeCount, Nat.cast_add, Nat.cast_one]; ring

/-- Absolute local error alone suffices, including near zero. -/
theorem abs_eval_sub_exact_le_nodeCount (t : ReductionTree α)
    (combine : β → β → β) (value : α → β) (interpret : β → ℝ) (δ : ℝ)
    (h : t.AllNodes combine value (fun x y =>
      |interpret (combine x y) - (interpret x + interpret y)| ≤ δ)) :
    |interpret (t.eval combine value) - t.eval (· + ·) (interpret ∘ value)| ≤
      t.nodeCount * δ := by
  simpa only [errorBudget_const] using
    t.abs_eval_sub_exact_le_errorBudget combine value interpret (fun _ _ => δ) h

/--
A priori mixed error bound built from exact subtree sums, with no rounded intermediate values.
-/
noncomputable def mixedBudget (value : α → ℝ) (u δ : ℝ) : ReductionTree α → ℝ
  | .leaf _ => 0
  | .node a b => (1 + u) * (a.mixedBudget value u δ + b.mixedBudget value u δ) +
      u * (|a.eval (· + ·) value| + |b.eval (· + ·) value|) + δ

/-- Propagate a mixed relative/absolute bound through the actual reduction schedule. -/
theorem abs_eval_sub_exact_le_mixedBudget (t : ReductionTree α)
    (combine : β → β → β) (value : α → β) (interpret : β → ℝ)
    (u δ : ℝ) (hu : 0 ≤ u)
    (h : t.AllNodes combine value (fun x y =>
      |interpret (combine x y) - (interpret x + interpret y)| ≤
        u * (|interpret x| + |interpret y|) + δ)) :
    |interpret (t.eval combine value) - t.eval (· + ·) (interpret ∘ value)| ≤
      t.mixedBudget (interpret ∘ value) u δ := by
  induction t with
  | leaf x => simp [eval, mixedBudget]
  | node a b ha hb =>
    have ea := ha h.1
    have eb := hb h.2.1
    have magnitude (r x e : ℝ) (he : |r - x| ≤ e) : |r| ≤ e + |x| := by
      simpa only [sub_zero, add_comm] using compose_error he (le_refl |x - 0|)
    have ma := magnitude _ _ _ ea
    have mb := magnitude _ _ _ eb
    have localError := h.2.2
    have triangle := add_error ea eb localError
    dsimp only [eval, mixedBudget]
    linarith [mul_nonneg hu (sub_nonneg.mpr ma), mul_nonneg hu (sub_nonneg.mpr mb)]

/-- Relative-only analysis is the mixed bound with zero absolute allowance. -/
theorem abs_eval_sub_exact_le_relativeBudget (t : ReductionTree α)
    (combine : β → β → β) (value : α → β) (interpret : β → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (h : t.AllNodes combine value (fun x y =>
      |interpret (combine x y) - (interpret x + interpret y)| ≤
        u * (|interpret x| + |interpret y|))) :
    |interpret (t.eval combine value) - t.eval (· + ·) (interpret ∘ value)| ≤
      t.mixedBudget (interpret ∘ value) u 0 := by
  apply t.abs_eval_sub_exact_le_mixedBudget combine value interpret u 0 hu
  simpa only [add_zero] using h

/-- The absolute-input scale of a reduction, invariant under reordering. -/
noncomputable def sumAbs (value : α → ℝ) (t : ReductionTree α) : ℝ :=
  t.eval (· + ·) (fun x => |value x|)

/-- The absolute-input scale is nonnegative, even for a sum that cancels exactly. -/
theorem sumAbs_nonneg (value : α → ℝ) (t : ReductionTree α) : 0 ≤ t.sumAbs value := by
  induction t with
  | leaf x => exact abs_nonneg _
  | node a b ha hb => exact add_nonneg ha hb

/-- Reordering does not change the absolute-input scale of the common enclosure. -/
theorem sumAbs_eq_of_perm {a b : ReductionTree α} (h : a.leaves.Perm b.leaves)
    (value : α → ℝ) : a.sumAbs value = b.sumAbs value :=
  eval_add_eq_of_perm h (fun x => |value x|)

/-- Cancellation can reduce the exact sum but not its absolute-input scale. -/
theorem abs_eval_add_le_sumAbs (value : α → ℝ) (t : ReductionTree α) :
    |t.eval (· + ·) value| ≤ t.sumAbs value := by
  induction t with
  | leaf x => exact le_rfl
  | node a b ha hb => exact Backward.abs_add_le_add ha hb

/-- A relative-only budget grows with the depth of the schedule, not with its number of
additions: an input is rounded once at each of the at most `depth` nodes above it. -/
theorem mixedBudget_zero_le_depth (value : α → ℝ) (u : ℝ) (hu : 0 ≤ u)
    (t : ReductionTree α) :
    t.mixedBudget value u 0 ≤ ((1 + u) ^ t.depth - 1) * t.sumAbs value := by
  induction t with
  | leaf x => simp [mixedBudget, depth]
  | node a b ha hb =>
    let g := (1 + u) ^ max a.depth b.depth
    have hbase : 1 ≤ 1 + u := by exact le_add_of_nonneg_right hu
    have hga : (1 + u) ^ a.depth ≤ g :=
      pow_le_pow_right₀ hbase (le_max_left _ _)
    have hgb : (1 + u) ^ b.depth ≤ g :=
      pow_le_pow_right₀ hbase (le_max_right _ _)
    have hA := a.sumAbs_nonneg value
    have hB := b.sumAbs_nonneg value
    have ha' : a.mixedBudget value u 0 ≤ (g - 1) * a.sumAbs value :=
      ha.trans (mul_le_mul_of_nonneg_right (sub_le_sub_right hga 1) hA)
    have hb' : b.mixedBudget value u 0 ≤ (g - 1) * b.sumAbs value :=
      hb.trans (mul_le_mul_of_nonneg_right (sub_le_sub_right hgb 1) hB)
    have hsum := mul_le_mul_of_nonneg_left (add_le_add ha' hb') (by linarith : 0 ≤ 1 + u)
    have hexact := mul_le_mul_of_nonneg_left
      (add_le_add (a.abs_eval_add_le_sumAbs value) (b.abs_eval_add_le_sumAbs value)) hu
    change (1 + u) * (a.mixedBudget value u 0 + b.mixedBudget value u 0) +
      u * (|a.eval (· + ·) value| + |b.eval (· + ·) value|) + 0 ≤
      ((1 + u) ^ (max a.depth b.depth + 1) - 1) *
        (a.sumAbs value + b.sumAbs value)
    rw [pow_succ]
    change _ ≤ (g * (1 + u) - 1) * _
    linarith

/-- The factor of the depth bound is at most the factor of the size bound: no schedule is deeper
than its number of additions. -/
theorem depth_factor_le (value : α → ℝ) (u : ℝ) (hu : 0 ≤ u) (t : ReductionTree α) :
    ((1 + u) ^ t.depth - 1) * t.sumAbs value ≤ ((1 + u) ^ t.nodeCount - 1) * t.sumAbs value :=
  mul_le_mul_of_nonneg_right
    (sub_le_sub_right (pow_le_pow_right₀ (le_add_of_nonneg_right hu) t.depth_le_nodeCount) 1)
    (t.sumAbs_nonneg value)

/-- A relative-only budget is bounded uniformly over all schedules of the same size and scale. -/
theorem mixedBudget_zero_le (value : α → ℝ) (u : ℝ) (hu : 0 ≤ u)
    (t : ReductionTree α) :
    t.mixedBudget value u 0 ≤ ((1 + u) ^ t.nodeCount - 1) * t.sumAbs value :=
  (t.mixedBudget_zero_le_depth value u hu).trans (t.depth_factor_le value u hu)

/--
The geometric enclosure in the depth of the schedule: under local relative bounds the error is at
most `((1 + u) ^ depth - 1)` times the absolute-input scale. Over `n` inputs no schedule is
shallower than `⌈log₂ n⌉` (`clog_le_depth`), and the left chain has depth `n - 1`
(`depth_leftChain`), so this is the size bound `abs_eval_sub_exact_le_geometric` for a loop and a
much smaller one for a schedule that pairs its inputs.
-/
theorem abs_eval_sub_exact_le_depth (t : ReductionTree α)
    (combine : β → β → β) (value : α → β) (interpret : β → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (h : t.AllNodes combine value (fun x y =>
      |interpret (combine x y) - (interpret x + interpret y)| ≤
        u * (|interpret x| + |interpret y|))) :
    |interpret (t.eval combine value) - t.eval (· + ·) (interpret ∘ value)| ≤
      ((1 + u) ^ t.depth - 1) * t.sumAbs (interpret ∘ value) :=
  (t.abs_eval_sub_exact_le_relativeBudget combine value interpret u hu h).trans
    (t.mixedBudget_zero_le_depth (interpret ∘ value) u hu)

/--
The familiar geometric enclosure depends only on leaf count and absolute-input scale. The relative
premise stays local to this tree, and no global floating-point relative bound is assumed.
`nodeCount = leaves.length - 1` by `length_leaves`.
-/
theorem abs_eval_sub_exact_le_geometric (t : ReductionTree α)
    (combine : β → β → β) (value : α → β) (interpret : β → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (h : t.AllNodes combine value (fun x y =>
      |interpret (combine x y) - (interpret x + interpret y)| ≤
        u * (|interpret x| + |interpret y|))) :
    |interpret (t.eval combine value) - t.eval (· + ·) (interpret ∘ value)| ≤
      ((1 + u) ^ t.nodeCount - 1) * t.sumAbs (interpret ∘ value) :=
  (t.abs_eval_sub_exact_le_relativeBudget combine value interpret u hu h).trans
    (t.mixedBudget_zero_le (interpret ∘ value) u hu)

/--
Two schedules over the same multiset of inputs differ by at most the sum of their errors against
the exact sum, whatever bounds those errors have.
-/
theorem abs_eval_sub_eval_le_of_perm {a b : ReductionTree α}
    (combine : β → β → β) (value : α → β) (interpret : β → ℝ)
    (hperm : a.leaves.Perm b.leaves) {errorA errorB : ℝ}
    (ha : |interpret (a.eval combine value) - a.eval (· + ·) (interpret ∘ value)| ≤ errorA)
    (hb : |interpret (b.eval combine value) - b.eval (· + ·) (interpret ∘ value)| ≤ errorB) :
    |interpret (a.eval combine value) - interpret (b.eval combine value)| ≤ errorA + errorB := by
  rw [← eval_add_eq_of_perm hperm (interpret ∘ value), abs_sub_comm] at hb
  simpa only [add_comm] using compose_error ha hb

/-- Two locally bounded schedules over the same multiset share the same geometric enclosure. -/
theorem abs_eval_sub_eval_le_geometric {a b : ReductionTree α}
    (combine : β → β → β) (value : α → β) (interpret : β → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hperm : a.leaves.Perm b.leaves)
    (ha : a.AllNodes combine value (fun x y =>
      |interpret (combine x y) - (interpret x + interpret y)| ≤
        u * (|interpret x| + |interpret y|)))
    (hb : b.AllNodes combine value (fun x y =>
      |interpret (combine x y) - (interpret x + interpret y)| ≤
        u * (|interpret x| + |interpret y|))) :
    |interpret (a.eval combine value) - interpret (b.eval combine value)| ≤
      2 * (((1 + u) ^ a.nodeCount - 1) * a.sumAbs (interpret ∘ value)) := by
  have eb := b.abs_eval_sub_exact_le_geometric combine value interpret u hu hb
  rw [← nodeCount_eq_of_perm hperm, ← sumAbs_eq_of_perm hperm] at eb
  rw [two_mul]
  exact abs_eval_sub_eval_le_of_perm combine value interpret hperm
    (a.abs_eval_sub_exact_le_geometric combine value interpret u hu ha) eb

end FloatLib.Numerics.ReductionTree
