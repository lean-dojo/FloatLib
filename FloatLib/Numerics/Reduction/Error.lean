/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Reduction.Tree
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.RingNF

/-!
# Error of repeatedly rounded reductions

The main bound adds the local absolute errors at the nodes actually visited by a reduction.
It applies to any carrier with a real interpretation, so an executable floating-point tree
does not first need to be replaced by a globally defined real rounding function.

`mixedBudget` propagates relative and absolute local errors through the schedule. The absolute
term can cover gradual underflow; setting it to zero gives a relative-error specialization.
These are round-per-node bounds, not bounds for an exact accumulator rounded only at the end.
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

private theorem abs_error_node (r a b x y : ℝ) :
    |r - (x + y)| ≤ |a - x| + |b - y| + |r - (a + b)| := by
  calc
    |r - (x + y)| = |((a - x) + (b - y)) + (r - (a + b))| := by congr 1; ring
    _ ≤ |(a - x) + (b - y)| + |r - (a + b)| := abs_add_le _ _
    _ ≤ |a - x| + |b - y| + |r - (a + b)| := add_le_add (abs_add_le _ _) le_rfl

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
    exact (abs_error_node _ _ _ _ _).trans
      (add_le_add (add_le_add (ha h.1) (hb h.2.1)) h.2.2)

/-- A uniform absolute allowance is paid once per addition, independently of tree shape. -/
theorem errorBudget_const (t : ReductionTree α) (combine : β → β → β)
    (value : α → β) (δ : ℝ) :
    t.errorBudget combine value (fun _ _ => δ) = t.nodeCount * δ := by
  induction t with
  | leaf x => simp [errorBudget, nodeCount]
  | node a b ha hb => simp [errorBudget, nodeCount, ha, hb, Nat.cast_add]; ring

/-- Absolute local error alone suffices, including near zero. -/
theorem abs_eval_sub_exact_le_nodeCount (t : ReductionTree α)
    (combine : β → β → β) (value : α → β) (interpret : β → ℝ) (δ : ℝ)
    (h : t.AllNodes combine value (fun x y =>
      |interpret (combine x y) - (interpret x + interpret y)| ≤ δ)) :
    |interpret (t.eval combine value) - t.eval (· + ·) (interpret ∘ value)| ≤
      t.nodeCount * δ := by
  simpa only [errorBudget_const] using
    t.abs_eval_sub_exact_le_errorBudget combine value interpret (fun _ _ => δ) h

/-- A priori mixed error bound using exact subtree sums, not rounded intermediate values. -/
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
      calc
        |r| = |r - x + x| := by rw [sub_add_cancel]
        _ ≤ |r - x| + |x| := abs_add_le _ _
        _ ≤ e + |x| := add_le_add he le_rfl
    have ma := magnitude _ _ _ ea
    have mb := magnitude _ _ _ eb
    have localError := h.2.2
    have triangle := abs_error_node
      (interpret (combine (a.eval combine value) (b.eval combine value)))
      (interpret (a.eval combine value)) (interpret (b.eval combine value))
      (a.eval (· + ·) (interpret ∘ value)) (b.eval (· + ·) (interpret ∘ value))
    dsimp only [eval, mixedBudget]
    nlinarith [mul_nonneg hu (sub_nonneg.mpr ma), mul_nonneg hu (sub_nonneg.mpr mb)]

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
  | node a b ha hb => exact (abs_add_le _ _).trans (add_le_add ha hb)

/-- A relative-only budget is bounded uniformly over all schedules of the same size and scale. -/
theorem mixedBudget_zero_le (value : α → ℝ) (u : ℝ) (hu : 0 ≤ u)
    (t : ReductionTree α) :
    t.mixedBudget value u 0 ≤ ((1 + u) ^ t.nodeCount - 1) * t.sumAbs value := by
  induction t with
  | leaf x => simp [mixedBudget, nodeCount]
  | node a b ha hb =>
    let g := (1 + u) ^ (a.nodeCount + b.nodeCount)
    have hbase : 1 ≤ 1 + u := by linarith
    have hga : (1 + u) ^ a.nodeCount ≤ g :=
      pow_le_pow_right₀ hbase (Nat.le_add_right _ _)
    have hgb : (1 + u) ^ b.nodeCount ≤ g :=
      pow_le_pow_right₀ hbase (Nat.le_add_left _ _)
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
      ((1 + u) ^ (a.nodeCount + b.nodeCount + 1) - 1) *
        (a.sumAbs value + b.sumAbs value)
    rw [pow_succ]
    change _ ≤ (g * (1 + u) - 1) * _
    nlinarith

/--
The familiar geometric enclosure depends only on leaf count and absolute-input scale.
The relative premise is still local to this tree; no global floating-point relative bound is
assumed. `nodeCount = leaves.length - 1` by `length_leaves`.
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
  have ea := a.abs_eval_sub_exact_le_geometric combine value interpret u hu ha
  have eb := b.abs_eval_sub_exact_le_geometric combine value interpret u hu hb
  rw [← nodeCount_eq_of_perm hperm, ← sumAbs_eq_of_perm hperm] at eb
  have hs := eval_add_eq_of_perm hperm (interpret ∘ value)
  have triangle := abs_sub_le
    (interpret (a.eval combine value)) (a.eval (· + ·) (interpret ∘ value))
    (interpret (b.eval combine value))
  rw [hs, abs_sub_comm (b.eval (· + ·) (interpret ∘ value))] at triangle
  rw [hs] at ea
  linarith

end FloatLib.Numerics.ReductionTree
