/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Reduction.Tree
public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Runtime
public import FloatLib.Numerics.Reduction.Blocked
-- The `DecidableEq (Except ε α)` instance body is needed by `decide` below.
import all Batteries.Data.Except

/-!
# Correctly rounded and repeated-rounding reductions

Binary16 distinguishes an exact accumulator from a reduction that rounds every addition:
`(2048 + 1) - 2048` produces zero with repeated rounding, but one with a round-once accumulator.
The symbolic examples apply the absolute and mixed bounds without global relative assumptions.
Signed-zero and exceptional-input examples check the result bits and every IEEE status indicator
in all six rounding modes, including conversions into finite-only destination formats.

A loop that adds one input per step is the left chain among the schedules, so the bounds of
schedules hold for it. It is also the deepest schedule: the depth bounds are applied to a
balanced schedule of four inputs, where they count two roundings instead of three.

The blocked dot product `BlockedDot.kernelEntry` is instantiated with the fused multiply-add and
the addition of a binary format: the block width changes the bits of a binary16 result, a
product computed in two calls is the product computed in one, and the product is a loop over its
full blocks followed by one short block.
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
    (Model.sum FloatFormat.binary16 #[large, one, negativeLarge] .nearest) = 0x3c00 := by
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
    (mode : Model.IEEERoundingMode) : Nat × IEEEStatus :=
  let outcome := Model.sum destination
    (values.map (Model.ofNatBits (fmt := FloatFormat.binary32))).toArray mode (status := true)
  (outcome.value.toNatBits, outcome.status)

/-- Retain length errors, result bits, and all five indicators of a binary32-source dot product. -/
private def binary32Dot (destination : FloatFormat) (left right : List Nat)
    (mode : Model.IEEERoundingMode) :
    Except FloatLib.Numerics.ReductionError (Nat × IEEEStatus) :=
  (Model.dot destination
    (left.map (Model.ofNatBits (fmt := FloatFormat.binary32))).toArray
    (right.map (Model.ofNatBits (fmt := FloatFormat.binary32))).toArray mode (status := true)).map
    (fun outcome => (outcome.value.toNatBits, outcome.status))

-- Same-sign zeros keep their sign, and only mixed signs and cancellation depend on rounding.
example (mode : Model.IEEERoundingMode) :
    [ [], [0], [0, 0], [0x80000000, 0x80000000]
    , [0, 0x80000000], [0x3f800000, 0xbf800000]
    ].map (binary32Sum FloatFormat.binary32 · mode) =
      [(0, {}), (0, {}), (0, {}), (0x80000000, {}),
        (if mode = .down then 0x80000000 else 0, {}),
        (if mode = .down then 0x80000000 else 0, {})] := by
  cases mode <;> decide

-- A quiet NaN before or after an invalid product cannot clear its invalid indicator.
example (mode : Model.IEEERoundingMode) :
    [ binary32Dot FloatFormat.binary32 [0, 0x7fc00000] [0x7f800000, 0x3f800000] mode
    , binary32Dot FloatFormat.binary32 [0x7fc00000, 0] [0x3f800000, 0x7f800000] mode
    ] = List.replicate 2 (.ok (0x7fc00000, { invalid := true })) := by
  cases mode <;> decide +kernel

-- Opposing infinities raise invalid with a preceding or following NaN. A NaN alone leaves it clear.
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
    , binary32Sum FloatFormat.e4m3 [0x7f800000] mode
    , binary32Sum FloatFormat.e4m3fnuz [0x7f800000] mode
    , binary32Sum FloatFormat.e2m1 [0x7f800000] mode
    , binary32Sum FloatFormat.e2m1 [0xff800000] mode
    ] = [(0x7c00, {}),
      (0x7f, { overflow := true, inexact := true }),
      (0x80, { overflow := true, inexact := true }),
      (0x7, { overflow := true, inexact := true }),
      (0xf, { overflow := true, inexact := true })] := by
  cases mode <;> decide

/-! ## A loop is the left chain -/

/-- A loop of additions with absolute local error `δ` is within `δ` per input of the exact sum:
the node-count bound of reduction schedules, on the left chain. -/
example (round : ℝ → ℝ) (δ : ℝ) (h : ∀ z, |round z - z| ≤ δ) (init : ℝ) (inputs : List ℝ) :
    |inputs.foldl (fun acc x => round (acc + x)) init - (init + inputs.sum)| ≤
      inputs.length * δ := by
  have hbound := (ReductionTree.leftChain init inputs).abs_eval_sub_exact_le_nodeCount
    (fun x y => round (x + y)) id id δ (ReductionTree.AllNodes.of_forall _ _ _ fun x y => h (x + y))
  rw [ReductionTree.eval_leftChain, ReductionTree.eval_add_eq_sum, ReductionTree.leaves_leftChain,
    ReductionTree.nodeCount_leftChain] at hbound
  simpa using hbound

/-! ## The depth of a schedule -/

/-- Over four inputs the loop has depth three and the balanced schedule has depth two. -/
example : leftSchedule.depth = 3 ∧ rightSchedule.depth = 3 ∧ balancedSchedule.depth = 2 := by
  decide

/-- No schedule over four inputs is shallower than the balanced one. -/
example (t : ReductionTree Nat) (h : t.leaves.length = 4) : 2 ≤ t.depth := by
  have hpow := t.length_leaves_le_two_pow_depth
  rw [h] at hpow
  by_contra hlt
  have hpow' := Nat.pow_le_pow_right (show 0 < 2 by decide) (show t.depth ≤ 1 by omega)
  omega

/-- The same lower bound for every number of inputs, and the upper bound by the size. -/
example (t : ReductionTree Nat) :
    Nat.clog 2 t.leaves.length ≤ t.depth ∧ t.depth ≤ t.nodeCount :=
  ⟨t.clog_le_depth, t.depth_le_nodeCount⟩

/-- A loop is as deep as it has inputs after the first. -/
example (init : ℝ) (inputs : List ℝ) :
    (ReductionTree.leftChain init inputs).depth = inputs.length :=
  ReductionTree.depth_leftChain init inputs

/-- The depth bound on the balanced schedule: each input is rounded twice, so the factor is
`(1 + u) ^ 2 - 1`, where the size bound has `(1 + u) ^ 3 - 1` for the three additions. -/
example (combine : ℝ → ℝ → ℝ) (value : Nat → ℝ) (u : ℝ) (hu : 0 ≤ u)
    (h : balancedSchedule.AllNodes combine value (fun x y =>
      |combine x y - (x + y)| ≤ u * (|x| + |y|))) :
    |balancedSchedule.eval combine value - balancedSchedule.eval (· + ·) value| ≤
      ((1 + u) ^ 2 - 1) * balancedSchedule.sumAbs value :=
  balancedSchedule.abs_eval_sub_exact_le_depth combine value id u hu h

/-- The depth bound of a finite binary16 tree: the cancellation schedule has depth two. -/
example : |Model.toReal (cancellation.eval Model.add id) -
    (cancellation.leaves.map Model.toReal).sum| ≤
      ((1 + Model.unitRoundoffAt FloatFormat.binary16) ^ 2 - 1) *
        cancellation.sumAbs Model.toReal :=
  Model.ReductionTree.abs_toReal_eval_sub_sum_le_depth cancellation (by decide) cancellation_finite

/-! ## The blocked dot product in a binary format -/

section Blocked

open FloatLib.Numerics.BlockedDot

/-- The blocked dot product of vectors of a binary format: nearest-even fused multiply-adds
inside a block of width `w`, and nearest-even additions of the block partials. -/
def blockedDot {fmt : FloatFormat} (a b : ℕ → Model fmt) (w K : ℕ)
    (start : Option (Model fmt)) : Model fmt :=
  kernelEntry (fun x y z => Model.fma x y z) (fun x y => Model.add x y) (Model.posZero fmt)
    a b w K start

/-- The vector `2048, 1, 1, 1, …` in binary16. -/
def leading : ℕ → Model FloatFormat.binary16 := fun k => if k = 0 then large else one
/-- The vector of ones in binary16. -/
def ones : ℕ → Model FloatFormat.binary16 := fun _ => one

/-- Five terms `2048 + 1 + 1 + 1 + 1` one by one: every unit is rounded away. -/
example : Model.toNatBits (blockedDot leading ones 1 5 none) = 0x6800 := by
  decide +kernel

/-- The same terms in blocks of two: the second block is the exact `2`, which survives, and the
last unit rounds the tie `2051` up to `2052`, the exact sum. The block width is part of the
result. -/
example : Model.toNatBits (blockedDot leading ones 2 5 none) = 0x6802 := by
  decide +kernel

/-- A product computed in two calls is the product computed in one, for every binary format,
every pair of vectors and every block width: the second call starts on a block boundary and
continues from the result of the first. -/
theorem blockedDot_continue {fmt : FloatFormat} (a b : ℕ → Model fmt) {w K lo : ℕ}
    (hw : 0 < w) (hlo : w ∣ lo) (hpos : 0 < lo) (hK : lo ≤ K) :
    blockedDot (shift a lo) (shift b lo) w (K - lo)
        (some (blockedDot (shift a 0) (shift b 0) w lo none)) =
      prefixFold (fun x y z => Model.fma x y z) (fun x y => Model.add x y) (Model.posZero fmt)
        a b w K (lo / w + blockCount w (K - lo)) := by
  unfold blockedDot
  rw [kernelEntry_first _ _ _ a b (K := K) hw hpos (Or.inl ⟨hlo, hK⟩),
    blockCount_of_dvd hw hlo]
  exact kernelEntry_continue _ _ _ a b hw hlo hpos (Or.inr (Nat.add_sub_cancel' hK))

/-- On the binary16 vectors above, three terms and then two continue to the bits of one call on
all five. -/
example : Model.toNatBits (blockedDot (shift leading 2) (shift ones 2) 2 3
      (some (blockedDot leading ones 2 2 none))) =
    Model.toNatBits (blockedDot leading ones 2 5 none) := by
  decide +kernel

/-- With exact rational arithmetic the blocked product is the dot product, for every block
width: here three terms in blocks of two. -/
example (a b : ℕ → ℚ) :
    kernelEntry (fun x y z => x * y + z) (· + ·) 0 a b 2 3 none =
      a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  rw [kernelEntry_eq_sum a b 2 3 (by decide) none]
  simp [Finset.sum_range_succ]

/-- The floating-point blocked product reads only the first `K` terms of its operands. -/
example {fmt : FloatFormat} (a a' b : ℕ → Model fmt) (w K : ℕ) (h : ∀ c < K, a c = a' c) :
    blockedDot a b w K none = blockedDot a' b w K none :=
  kernelEntry_congr _ _ _ (fun c hc => ⟨h c hc, rfl⟩) none

/-- Sixteen terms in blocks of four are four blocks, and ten more terms make seven. -/
example : 16 / 4 + blockCount 4 10 = blockCount 4 26 := blockCount_add (by decide) (by decide)

/-- Ten terms in blocks of four are two full blocks and one short block. -/
example : blockCount 4 10 = 3 := by
  rw [blockCount_eq_div_add (by decide) 10]
  decide

/-- A block that exists starts inside the product. It ends `w` terms later when it is a full
block, and `K % w` terms later when it is the short last one. -/
example {w K u : ℕ} (hw : 0 < w) (h : u < blockCount w K) :
    u * w < K ∧ min ((u + 1) * w) K = u * w + if u < K / w then w else K % w :=
  ⟨mul_lt_of_lt_blockCount hw h,
    min_succ_mul_eq hw ((Nat.le_div_iff_mul_le hw).mpr (mul_lt_of_lt_blockCount hw h).le)⟩

/-- The full blocks and the short last block of a floating-point product, for every width. -/
example {fmt : FloatFormat} (a b : ℕ → Model fmt) {w K u : ℕ} (hw : 0 < w) (h : u < K / w) :
    blockPartial (fun x y z => Model.fma x y z) (Model.posZero fmt) a b w K u =
        blockDot (fun x y z => Model.fma x y z) (Model.posZero fmt) a b (u * w) (u * w + w) ∧
      blockPartial (fun x y z => Model.fma x y z) (Model.posZero fmt) a b w K (K / w) =
        blockDot (fun x y z => Model.fma x y z) (Model.posZero fmt) a b (K / w * w)
          (K / w * w + K % w) :=
  ⟨blockPartial_of_lt_div _ _ a b h, blockPartial_div _ _ a b hw K⟩

/-- The schedule of a generated kernel at width 32, continuing from a start value: a loop over
the `K / 32` full blocks, each of exactly 32 terms, then the `K % 32` remaining terms once. -/
example {fmt : FloatFormat} (a b : ℕ → Model fmt) (K : ℕ) (start : Model fmt) :
    blockedDot a b 32 K (some start) =
      let block := fun lo hi =>
        blockDot (fun x y z => Model.fma x y z) (Model.posZero fmt) a b lo hi
      let run := (List.range' 0 (K / 32)).foldl
        (fun acc u => Model.add acc (block (u * 32) (u * 32 + 32))) start
      if 0 < K % 32 then Model.add run (block (K / 32 * 32) (K / 32 * 32 + K % 32)) else run := by
  unfold blockedDot
  rw [kernelEntry_eq_blocks _ _ _ a b (by decide) K (some start)]
  simp

/-- On the binary16 vectors above, in blocks of two: two full blocks in the loop and then the
fifth term give the bits of `kernelEntry`. -/
example : Model.toNatBits (blockedDot leading ones 2 5 none) =
    Model.toNatBits
      (Model.add
        (Model.add
          (blockDot (fun x y z => Model.fma x y z) (Model.posZero _) leading ones 0 2)
          (blockDot (fun x y z => Model.fma x y z) (Model.posZero _) leading ones 2 4))
        (blockDot (fun x y z => Model.fma x y z) (Model.posZero _) leading ones 4 5)) := by
  unfold blockedDot
  rw [kernelEntry_eq_blocks _ _ _ leading ones (by decide) 5 none]
  decide +kernel

end Blocked

end FloatLibTests.Conformance.Numerics.Reduction
