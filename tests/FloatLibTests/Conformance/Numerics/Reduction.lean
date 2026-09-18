/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Reduction.Tree
public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Runtime

/-!
# Correctly rounded and repeated-rounding reductions

Binary16 distinguishes an exact accumulator from a reduction that rounds every addition:
`(2048 + 1) - 2048` produces zero with repeated rounding, but one with a round-once accumulator.
The symbolic examples apply the absolute and mixed bounds without global relative assumptions.
Signed-zero and exceptional-input examples check the result bits and every IEEE status indicator
in all four rounding modes, including conversions into finite-only destination formats.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Numerics.Reduction

open FloatLib.Numerics
open FloatLib.Floats.Formats.BinaryInterchange

/-- Exactly representable binary16 value 2048. -/
def large : Model FloatFormat.binary16 := Model.ofNatBits 0x6800
/-- Exactly representable binary16 value 1. -/
def one : Model FloatFormat.binary16 := Model.ofNatBits 0x3c00
/-- Exactly representable binary16 value -2048. -/
def negativeLarge : Model FloatFormat.binary16 := Model.ofNatBits 0xe800

/-- The schedule loses the unit contribution before cancellation. -/
def cancellation : ReductionTree (Model FloatFormat.binary16) :=
  .node (.node (.leaf large) (.leaf one)) (.leaf negativeLarge)

example : Model.toNatBits (cancellation.eval Model.add id) = 0 := by
  simp only [cancellation, ReductionTree.eval, id_eq, Model.Proof.add_eq_spec]
  decide

example : Model.toNatBits
    (Model.sum FloatFormat.binary16 #[large, one, negativeLarge] .nearestEven) = 0x3c00 := by
  decide

/-- Every intermediate in this cancellation example remains finite. -/
theorem cancellation_finite : Model.ReductionTree.FiniteEval cancellation := by
  simp only [cancellation, Model.ReductionTree.FiniteEval, ReductionTree.eval, id_eq,
    Model.Proof.add_eq_spec]
  decide

/-- Changing only the parentheses preserves the unit contribution in binary16. -/
def regrouped : ReductionTree (Model FloatFormat.binary16) :=
  .node (.leaf large) (.node (.leaf one) (.leaf negativeLarge))

example : Model.toNatBits (regrouped.eval Model.add id) = 0x3c00 := by
  simp only [regrouped, ReductionTree.eval, id_eq, Model.Proof.add_eq_spec]
  decide

/-- Both schedules are finite, even though their rounded results differ. -/
theorem regrouped_finite : Model.ReductionTree.FiniteEval regrouped := by
  simp only [regrouped, Model.ReductionTree.FiniteEval, ReductionTree.eval, id_eq,
    Model.Proof.add_eq_spec]
  decide

example : |Model.toReal (cancellation.eval Model.add id) -
    Model.toReal (regrouped.eval Model.add id)| ≤
      Model.ReductionTree.errorBudget cancellation + Model.ReductionTree.errorBudget regrouped :=
  Model.ReductionTree.abs_toReal_eval_sub_eval_le (by decide)
    cancellation_finite regrouped_finite (by decide)

example : |Model.toReal (cancellation.eval Model.add id) -
    (cancellation.leaves.map Model.toReal).sum| ≤ Model.ReductionTree.errorBudget cancellation :=
  Model.ReductionTree.abs_toReal_eval_sub_sum_le cancellation (by decide) cancellation_finite

example (a b c δ : ℝ) (combine : ℝ → ℝ → ℝ)
    (hab : |combine a b - (a + b)| ≤ δ)
    (hc : |combine (combine a b) c - (combine a b + c)| ≤ δ) :
    |combine (combine a b) c - ((a + b) + c)| ≤ 2 * δ := by
  exact (ReductionTree.node (.node (.leaf a) (.leaf b)) (.leaf c)).abs_eval_sub_exact_le_nodeCount
    combine id id δ ⟨⟨trivial, trivial, hab⟩, trivial, hc⟩

example {α : Type*} (t : ReductionTree α) (value : α → ℝ) (combine : ℝ → ℝ → ℝ)
    (u δ : ℝ) (hu : 0 ≤ u)
    (h : t.AllNodes combine value (fun x y =>
      |combine x y - (x + y)| ≤ u * (|x| + |y|) + δ)) :
    |t.eval combine value - t.eval (· + ·) value| ≤ t.mixedBudget value u δ :=
  t.abs_eval_sub_exact_le_mixedBudget combine value id u δ hu h

/-- Sequential accumulation from the left, without adding an artificial zero leaf. -/
def leftSchedule : ReductionTree Nat :=
  .node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.leaf 3)

/-- Sequential accumulation from the right. -/
def rightSchedule : ReductionTree Nat :=
  .node (.leaf 0) (.node (.leaf 1) (.node (.leaf 2) (.leaf 3)))

/-- Pairwise accumulation in a balanced tree. -/
def balancedSchedule : ReductionTree Nat :=
  .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))

/-- A balanced schedule with a different traversal order. -/
def permutedSchedule : ReductionTree Nat :=
  .node (.node (.leaf 3) (.leaf 1)) (.node (.leaf 0) (.leaf 2))

example (value : Nat → ℝ) :
    leftSchedule.eval (· + ·) value = rightSchedule.eval (· + ·) value :=
  ReductionTree.eval_add_eq_of_perm (by decide) value

example (value : Nat → ℝ) :
    leftSchedule.eval (· + ·) value = balancedSchedule.eval (· + ·) value :=
  ReductionTree.eval_add_eq_of_perm (by decide) value

example (value : Nat → ℝ) :
    balancedSchedule.eval (· + ·) value = permutedSchedule.eval (· + ·) value :=
  ReductionTree.eval_add_eq_of_perm (by decide) value

example (combine : ℝ → ℝ → ℝ) (value : Nat → ℝ) (u : ℝ) (hu : 0 ≤ u)
    (hl : leftSchedule.AllNodes combine value (fun x y =>
      |combine x y - (x + y)| ≤ u * (|x| + |y|)))
    (hp : permutedSchedule.AllNodes combine value (fun x y =>
      |combine x y - (x + y)| ≤ u * (|x| + |y|))) :
    |leftSchedule.eval combine value - permutedSchedule.eval combine value| ≤
      2 * (((1 + u) ^ leftSchedule.nodeCount - 1) * leftSchedule.sumAbs value) :=
  ReductionTree.abs_eval_sub_eval_le_geometric combine value id u hu (by decide) hl hp

/-- Retain the result bits and all five exception indicators of a binary32-source sum. -/
private def binary32Sum (destination : FloatFormat) (values : List Nat)
    (mode : Model.IEEERoundingMode) : Nat × Model.IEEEStatus :=
  let outcome := Model.sumWithStatus destination
    (values.map (Model.ofNatBits (fmt := FloatFormat.binary32))).toArray mode
  (outcome.value.toNatBits, outcome.status)

/-- Retain length errors, result bits, and all five indicators of a binary32-source dot product. -/
private def binary32Dot (destination : FloatFormat) (left right : List Nat)
    (mode : Model.IEEERoundingMode) :
    Except FloatLib.Numerics.ReductionError (Nat × Model.IEEEStatus) :=
  (Model.dotWithStatus destination
    (left.map (Model.ofNatBits (fmt := FloatFormat.binary32))).toArray
    (right.map (Model.ofNatBits (fmt := FloatFormat.binary32))).toArray mode).map
    (fun outcome => (outcome.value.toNatBits, outcome.status))

-- Same-sign zeros retain their sign; only mixed signs and cancellation depend on rounding.
example (mode : Model.IEEERoundingMode) :
    [ [], [0], [0, 0], [0x80000000, 0x80000000]
    , [0, 0x80000000], [0x3f800000, 0xbf800000]
    ].map (binary32Sum FloatFormat.binary32 · mode) =
      [(0, {}), (0, {}), (0, {}), (0x80000000, {}),
        (if mode = .towardNegativeInfinity then 0x80000000 else 0, {}),
        (if mode = .towardNegativeInfinity then 0x80000000 else 0, {})] := by
  cases mode <;> decide

-- A quiet NaN before or after an invalid product cannot clear its invalid indicator.
example (mode : Model.IEEERoundingMode) :
    [ binary32Dot FloatFormat.binary32 [0, 0x7fc00000] [0x7f800000, 0x3f800000] mode
    , binary32Dot FloatFormat.binary32 [0x7fc00000, 0] [0x3f800000, 0x7f800000] mode
    ] = List.replicate 2 (.ok (0x7fc00000, { invalid := true })) := by
  cases mode <;>
    simp [binary32Dot, Model.dotWithStatus, Model.Reduction.Internal.dotState,
      Model.Reduction.Internal.dotStateLoop] <;> decide

-- Opposing infinities raise invalid with a preceding or following NaN; a NaN alone leaves it clear.
example (mode : Model.IEEERoundingMode) :
    [ [0x7f800000, 0xff800000, 0x7fc12345], [0x7fc12345, 0x7f800000, 0xff800000]
    , [0x7fc12345]
    ].map (binary32Sum FloatFormat.binary32 · mode) =
      [(0x7fc12345, { invalid := true }), (0x7fc12345, { invalid := true }),
        (0x7fc12345, {})] := by
  cases mode <;> decide

-- Infinity conversion covers IEEE, FN, FNUZ, and fully finite destination policies.
-- The complete status distinguishes a conversion overflow from an invalid operation.
example (mode : Model.IEEERoundingMode) :
    [ binary32Sum FloatFormat.binary16 [0x7f800000] mode
    , binary32Sum FloatFormat.e4m3fn [0x7f800000] mode
    , binary32Sum FloatFormat.e4m3fnuz [0x7f800000] mode
    , binary32Sum FloatFormat.e2m1 [0x7f800000] mode
    , binary32Sum FloatFormat.e2m1 [0xff800000] mode
    ] = [(0x7c00, {}),
      (0x7f, { overflow := true, inexact := true }),
      (0x80, { overflow := true, inexact := true }),
      (0x7, { overflow := true, inexact := true }),
      (0xf, { overflow := true, inexact := true })] := by
  cases mode <;> decide

end FloatLibTests.Conformance.Numerics.Reduction
