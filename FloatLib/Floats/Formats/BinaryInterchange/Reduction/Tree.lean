/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.Error
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.StandardModel
public import FloatLib.Numerics.Reduction.Error

/-!
# Finite, repeatedly rounded binary sums

Each internal node uses `Model.add`, with one nearest-even rounding at that node. A finite
execution certificate excludes exceptional inputs and overflow at every intermediate result.
The error budget then follows from FloatLib's half-ULP theorem, including subnormal values.
This API does not change `Model.sum`, which accumulates exactly and rounds only once.

Each finite addition also has relative error at most `unitRoundoffAt fmt`, with no underflow
term, because a sum of two grid points below the normal range is exact. This discharges the
local premise of the mixed and geometric reduction bounds for `Model.add` trees.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Numerics

namespace ReductionTree

variable {fmt : FloatFormat}

/-- All leaves and intermediate additions have real denotations. -/
def FiniteEval : Numerics.ReductionTree (Model fmt) → Prop
  | .leaf x => isFinite x = true
  | .node a b => FiniteEval a ∧ FiniteEval b ∧
      isFinite (Numerics.ReductionTree.eval add id (.node a b)) = true

/-- Finiteness of the root is part of a finite execution certificate. -/
theorem FiniteEval.isFinite_eval {t : Numerics.ReductionTree (Model fmt)}
    (h : FiniteEval t) : isFinite (t.eval add id) = true := by
  cases t with
  | leaf x => exact h
  | node a b => exact h.2.2

/-- The rounded real interpretation agrees with encoded execution at each finite node. -/
theorem toReal_eval (t : Numerics.ReductionTree (Model fmt))
    (hfmt : fmt.isIEEE = true) (hfinite : FiniteEval t) :
    toReal (t.eval add id) = t.eval (fun x y => roundAt fmt (x + y)) toReal := by
  apply t.map_eval add id toReal (fun x y => roundAt fmt (x + y))
  induction t with
  | leaf x => trivial
  | node a b ha hb =>
    exact ⟨ha hfinite.1, hb hfinite.2.1,
      toReal_add_eq_roundAt _ _ hfmt hfinite.1.isFinite_eval
        hfinite.2.1.isFinite_eval hfinite.2.2⟩

/-- The sum of half-ULPs at the actual intermediate additions. -/
noncomputable def errorBudget (t : Numerics.ReductionTree (Model fmt)) : ℝ :=
  t.errorBudget add id (fun x y => epsilonAt fmt (toReal x + toReal y))

/-- No normal-range hypothesis is needed: each finite addition has an absolute half-ULP bound. -/
theorem abs_toReal_eval_sub_sum_le (t : Numerics.ReductionTree (Model fmt))
    (hfmt : fmt.isIEEE = true) (hfinite : FiniteEval t) :
    |toReal (t.eval add id) - (t.leaves.map toReal).sum| ≤ errorBudget t := by
  rw [← Numerics.ReductionTree.eval_add_eq_sum]
  apply t.abs_eval_sub_exact_le_errorBudget add id toReal
    (fun x y => epsilonAt fmt (toReal x + toReal y))
  induction t with
  | leaf x => trivial
  | node a b ha hb =>
    exact ⟨ha hfinite.1, hb hfinite.2.1,
      abs_toReal_add_sub_le _ _ hfmt hfinite.1.isFinite_eval
        hfinite.2.1.isFinite_eval hfinite.2.2⟩

/-- Two finite schedules over the same inputs can differ by at most their combined budgets. -/
theorem abs_toReal_eval_sub_eval_le {a b : Numerics.ReductionTree (Model fmt)}
    (hfmt : fmt.isIEEE = true) (ha : FiniteEval a) (hb : FiniteEval b)
    (hperm : a.leaves.Perm b.leaves) :
    |toReal (a.eval add id) - toReal (b.eval add id)| ≤ errorBudget a + errorBudget b := by
  have ea := abs_toReal_eval_sub_sum_le a hfmt ha
  have eb := abs_toReal_eval_sub_sum_le b hfmt hb
  have hs := (hperm.map toReal).sum_eq
  calc
    |toReal (a.eval add id) - toReal (b.eval add id)| =
        |(toReal (a.eval add id) - (a.leaves.map toReal).sum) +
          ((b.leaves.map toReal).sum - toReal (b.eval add id))| := by rw [hs]; congr 1; ring
    _ ≤ |toReal (a.eval add id) - (a.leaves.map toReal).sum| +
        |(b.leaves.map toReal).sum - toReal (b.eval add id)| := abs_add_le _ _
    _ ≤ errorBudget a + errorBudget b := add_le_add ea (by rwa [abs_sub_comm])

/--
Every finite addition in the tree has relative error at most `unitRoundoffAt fmt`, measured
against the magnitudes of its two operands, with no underflow allowance.
-/
theorem allNodes_abs_toReal_add_sub_le (t : Numerics.ReductionTree (Model fmt))
    (hfmt : fmt.isIEEE = true) (hfinite : FiniteEval t) :
    t.AllNodes add id (fun x y =>
      |toReal (add x y) - (toReal x + toReal y)| ≤
        unitRoundoffAt fmt * (|toReal x| + |toReal y|)) := by
  induction t with
  | leaf x => trivial
  | node a b ha hb =>
    refine ⟨ha hfinite.1, hb hfinite.2.1, ?_⟩
    have hu : 0 ≤ unitRoundoffAt fmt :=
      FloatLib.Floats.Formats.Flocq.bpow.nonneg Numerics.binaryRadix _
    exact (abs_toReal_add_sub_le_unitRoundoffAt _ _ hfmt hfinite.1.isFinite_eval
      hfinite.2.1.isFinite_eval hfinite.2.2).trans
      (mul_le_mul_of_nonneg_left (abs_add_le _ _) hu)

/--
A finite IEEE reduction tree satisfies the mixed-budget bound with relative allowance
`unitRoundoffAt fmt` and zero absolute allowance, including subnormal intermediate results.
-/
theorem abs_toReal_eval_sub_sum_le_mixedBudget (t : Numerics.ReductionTree (Model fmt))
    (hfmt : fmt.isIEEE = true) (hfinite : FiniteEval t) :
    |toReal (t.eval add id) - (t.leaves.map toReal).sum| ≤
      t.mixedBudget toReal (unitRoundoffAt fmt) 0 := by
  rw [← Numerics.ReductionTree.eval_add_eq_sum]
  exact t.abs_eval_sub_exact_le_relativeBudget add id toReal (unitRoundoffAt fmt)
    (FloatLib.Floats.Formats.Flocq.bpow.nonneg Numerics.binaryRadix _)
    (allNodes_abs_toReal_add_sub_le t hfmt hfinite)

/--
A finite IEEE reduction tree with `n` additions has error at most
`((1 + u)^n - 1) * Σ|xᵢ|` for `u = unitRoundoffAt fmt`, with no normal-range hypothesis.
-/
theorem abs_toReal_eval_sub_sum_le_geometric (t : Numerics.ReductionTree (Model fmt))
    (hfmt : fmt.isIEEE = true) (hfinite : FiniteEval t) :
    |toReal (t.eval add id) - (t.leaves.map toReal).sum| ≤
      ((1 + unitRoundoffAt fmt) ^ t.nodeCount - 1) * t.sumAbs toReal := by
  rw [← Numerics.ReductionTree.eval_add_eq_sum]
  exact t.abs_eval_sub_exact_le_geometric add id toReal (unitRoundoffAt fmt)
    (FloatLib.Floats.Formats.Flocq.bpow.nonneg Numerics.binaryRadix _)
    (allNodes_abs_toReal_add_sub_le t hfmt hfinite)

end ReductionTree
end FloatLib.Floats.Formats.BinaryInterchange.Model
