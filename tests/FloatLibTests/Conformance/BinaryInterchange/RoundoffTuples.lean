/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Automation.Roundoff
public import FloatLib.Floats.Formats.BinaryInterchange.Configured
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals
public meta import Lean.Elab.Command

/-!
# `roundoff` over folds whose state is a tuple or a record

A left fold whose state pairs several floating-point values, counts, flags or indices is proved by
`List.fold_relation`: each value of the format that the observed one depends on carries its own real
shadow and budget, each discrete component it depends on a shadow copy equal to it, and the other
components leave the relation. These checks cover online softmax with and without its weighted
values, per key and per block, over lists, arrays, vectors and `Fin n`, and through a step written
for any type with its operations; Welford's mean and second moment and their parallel merge; Kahan
summation, whose componentwise budgets grow geometrically with the length; a running maximum and its
index under strict and non-strict ties, the number of entries that reach it, and a sum weighted by
the number of times that maximum grew; an exponential moving average with its bias correction; a
copy of a rounded component, a state that starts rounded, a state of binary32 values written by
their widths, and records, among them a record of one binary32 value and a wrapper of such a record.
The references decode only stored data and use the real exponential, and exact components get zero
budgets. A flag set by a test of the rounded sum, as in a gated sum or a sum that stops when an
entry leaves it unchanged, gets the premise that the test agrees with the test of the exact sum; a
flag set by `x == 0` on an entry needs none. A flag that compares the rounded sum with the rounded
square of an entry reads the exact square in its reference, and one that compares it with the entry
held from the step before reads that entry. A reference that reads a test of rounded values, a
dependent record, a literal container, a discrete component that starts at or is updated to a number
computed from a rounded value, and a loop whose number of steps is computed from a rounded value are
rejected.

Kahan summation also has a relation of its own, `KahanRelation`, which bounds the sum minus the
compensation against the exact sum, and the compensation by itself. One step preserves it
(`kahanStep_relation`), `List.fold_relation` lifts it to the list (`kahan_sum_mixedError`), and
that theorem, registered as a rule, bounds a product with a Kahan sum
(`kahan_product_mixedError`). In an IEEE format with unit roundoff `u ≤ 1/64` and `n u ≤ 1/8` over
`n` entries, and under `KahanValid`, which asks every entry to be finite and the four range
inequalities of `KahanRange` to hold at every step, Kahan's sum is finite and its error is at most
`(5 u + 16 n u²) Σ |x|`, the sum of its budgets (`kahanBudgets_le`, `kahan_sum_abs_sub_le`). This is
more conservative than the usual leading term `2 u Σ |x|`; the recursive sum has
`((1 + u)^n - 1) Σ |x|` (`List.abs_sub_le_of_sumFold_of_exact`).
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.RoundoffTuples

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
  [ExecFloat.ModelCodec plan (Model format) code]
  [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]

local notation "Value" => ExecFloat (Configured.Family format code plan)

section Softmax

/-- The online softmax normalizer of a list of scores: a running maximum and the sum of the
exponentials shifted by it, rescaled whenever the maximum grows. -/
def onlineSum (scores : List Value) (start : Value) : Value :=
  (scores.foldl (fun (state : Value × Value) x =>
    let m := if state.1 < x then x else state.1
    (m, state.2 * ExecFloat.Binary.CorrectlyRounded.exp (state.1 - m) +
      ExecFloat.Binary.CorrectlyRounded.exp (x - m))) (start, 0)).2

/-- The online normalizer is finite and has a mixed bound against the real online fold. -/
roundoff mixed theorem online_sum_mixedError :=
  fun (scores : List Value) (start : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (onlineSum scores start)

/-- The online normalizer is within its budget of the real online fold. -/
roundoff theorem online_sum_error :=
  fun (scores : List Value) (start : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (onlineSum scores start)

/-- The reference of the online normalizer is the online fold of the decoded scores in real
arithmetic, with the real exponential. -/
example (scores : List Value) (start : Value) (hformat : format.isIEEE = true) :=
  show _ → _ ∧ MixedError _ (scores.foldl (fun (state : ℝ × ℝ) x =>
      (max state.1 (ExecFloat.Binary.toReal x),
        state.2 * Real.exp (state.1 - max state.1 (ExecFloat.Binary.toReal x)) +
          Real.exp (ExecFloat.Binary.toReal x - max state.1 (ExecFloat.Binary.toReal x))))
      (ExecFloat.Binary.toReal start, 0)).2 _ _ from online_sum_mixedError scores start hformat

/-- The online softmax normalizer of an array of scores. -/
def onlineSumArray (scores : Array Value) (start : Value) : Value :=
  (scores.foldl (fun (state : Value × Value) x =>
    let m := if state.1 < x then x else state.1
    (m, state.2 * ExecFloat.Binary.CorrectlyRounded.exp (state.1 - m) +
      ExecFloat.Binary.CorrectlyRounded.exp (x - m))) (start, 0)).2

/-- The online normalizer of an array is finite and has a mixed bound against its real fold. -/
roundoff mixed theorem online_sum_array_mixedError :=
  fun (scores : Array Value) (start : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (onlineSumArray scores start)

/-- The online softmax normalizer of scores indexed by `Fin n`. -/
def onlineSumFin {n : Nat} (scores : Fin n → Value) (start : Value) : Value :=
  ((List.finRange n).foldl (fun (state : Value × Value) i =>
    let m := if state.1 < scores i then scores i else state.1
    (m, state.2 * ExecFloat.Binary.CorrectlyRounded.exp (state.1 - m) +
      ExecFloat.Binary.CorrectlyRounded.exp (scores i - m))) (start, 0)).2

/-- The online normalizer over `Fin n` is finite and has a mixed bound against its real fold. -/
roundoff mixed theorem online_sum_fin_mixedError :=
  fun {n : Nat} (scores : Fin n → Value) (start : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (onlineSumFin scores start)

/-- One key of online softmax attention: the running maximum, the rescaled normalizer and the
rescaled weighted sum of the values. -/
def attentionStep (state : Value × Value × Value) (entry : Value × Value) :
    Value × Value × Value :=
  let top := if state.1 < entry.1 then entry.1 else state.1
  let scale := ExecFloat.Binary.CorrectlyRounded.exp (state.1 - top)
  let weight := ExecFloat.Binary.CorrectlyRounded.exp (entry.1 - top)
  (top, state.2.1 * scale + weight, state.2.2 * scale + weight * entry.2)

/-- Online softmax attention of one query over a list of (score, value) pairs. -/
def onlineAttention (entries : List (Value × Value)) (start : Value) : Value :=
  let final := entries.foldl attentionStep (start, 0, 0)
  final.2.2 / final.2.1

/-- Online attention is finite and has a mixed bound against the quotient of its real folds. -/
roundoff mixed theorem online_attention_mixedError :=
  fun (entries : List (Value × Value)) (start : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (onlineAttention entries start)

/-- Online softmax attention of one query over a vector of (score, value) pairs. -/
def attentionVector {n : Nat} (entries : Vector (Value × Value) n) (start : Value) : Value :=
  let final := entries.foldl attentionStep (start, 0, 0)
  final.2.2 / final.2.1

/-- Online attention over a vector is finite and has a mixed bound against its real folds. -/
roundoff mixed theorem attention_vector_mixedError :=
  fun {n : Nat} (entries : Vector (Value × Value) n) (start : Value)
      (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (attentionVector entries start)

/-- One block of blocked online softmax attention: the block maximum through `max`, then the
rescaled normalizer and weighted sum, each adding the block's terms by an inner fold. -/
def blockStep (state : Value × Value × Value) (block : List (Value × Value)) :
    Value × Value × Value :=
  let m := block.foldl (fun m e => max m e.1) state.1
  let scale := ExecFloat.Binary.CorrectlyRounded.exp (state.1 - m)
  (m, scale * state.2.1 +
      block.foldl (fun l e => l + ExecFloat.Binary.CorrectlyRounded.exp (e.1 - m)) 0,
    scale * state.2.2 +
      block.foldl (fun o e => o + ExecFloat.Binary.CorrectlyRounded.exp (e.1 - m) * e.2) 0)

/-- Blocked online softmax attention of one query over a list of blocks. -/
def blocked (blocks : List (List (Value × Value))) (start : Value) : Value :=
  let state := blocks.foldl blockStep (start, 0, 0)
  state.2.2 / state.2.1

/-- Blocked attention is finite and has a mixed bound against the quotient of its real folds. -/
roundoff mixed theorem blocked_mixedError :=
  fun (blocks : List (List (Value × Value))) (start : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (blocked blocks start)

/-- One key of the online softmax normalizer over any type with the operations it uses, given
its exponential. -/
def keyUpdate {β : Type} [Add β] [Sub β] [Mul β] [Max β] (exp : β → β) (state : β × β) (x : β) :
    β × β :=
  let m := max state.1 x
  (m, state.2 * exp (state.1 - m) + exp (x - m))

/-- The online normalizer of `keyUpdate` at the correctly rounded exponential, whose argument
type is written as `ExecFloat.Binary` of the format's fields. -/
def onlineSumOf (scores : List Value) (start : Value) : Value :=
  (scores.foldl (keyUpdate ExecFloat.Binary.CorrectlyRounded.exp) (start, 0)).2

/-- The normalizer of `keyUpdate` is finite and has a mixed bound against its real fold. -/
roundoff mixed theorem online_sum_of_mixedError :=
  fun (scores : List Value) (start : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (onlineSumOf scores start)

end Softmax

section Widths

local notation "Single" => ExecFloat.Binary 8 23

/-- The sum of a list of binary32 values, carried beside their running maximum. -/
def maxSum (xs : List Single) : Single :=
  (xs.foldl (fun state x => (max state.1 x, state.2 + x)) (0, 0)).2

/-- The sum carried beside the maximum is within its budget of the real sum. -/
roundoff theorem max_sum_error :=
  fun (xs : List Single) => ExecFloat.Binary.toReal (maxSum xs)

end Widths

section Moments

/-- One step of Welford's algorithm on (count, mean, sum of squared deviations). -/
def welfordStep (state : Nat × Value × Value) (x : Value) : Nat × Value × Value :=
  let n := state.1 + 1
  let delta := x - state.2.1
  let mean := state.2.1 + delta / ExecFloat.Binary.ofRat ((n : ℤ) : ℚ)
  (n, mean, state.2.2 + delta * (x - mean))

/-- Welford's running mean of a list. -/
def welfordMean (xs : List Value) : Value := (xs.foldl welfordStep (0, 0, 0)).2.1

/-- Welford's sum of squared deviations of a list. -/
def welfordSquares (xs : List Value) : Value := (xs.foldl welfordStep (0, 0, 0)).2.2

/-- Welford's mean is finite and has a mixed bound against Welford's recurrence in real
arithmetic. -/
roundoff mixed theorem welford_mean_mixedError :=
  fun (xs : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (welfordMean xs)

/-- Welford's sum of squared deviations is finite and has a mixed bound against Welford's
recurrence in real arithmetic. -/
roundoff mixed theorem welford_squares_mixedError :=
  fun (xs : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (welfordSquares xs)

/-- The parallel merge of two partial Welford states (count, mean, sum of squared deviations). -/
def welfordMerge (a b : Nat × Value × Value) : Nat × Value × Value :=
  let n := a.1 + b.1
  let delta := b.2.1 - a.2.1
  let total := ExecFloat.Binary.ofRat ((n : ℤ) : ℚ)
  let nb := ExecFloat.Binary.ofRat ((b.1 : ℤ) : ℚ)
  let na := ExecFloat.Binary.ofRat ((a.1 : ℤ) : ℚ)
  (n, a.2.1 + delta * nb / total, a.2.2 + b.2.2 + delta * delta * na * nb / total)

/-- The sum of squared deviations of partial Welford states merged from the left. -/
def mergedSquares (parts : List (Nat × Value × Value)) (first : Nat × Value × Value) : Value :=
  (parts.foldl welfordMerge first).2.2

/-- The merged sum of squared deviations is finite and has a mixed bound against the merge in
real arithmetic of the decoded partial states. -/
roundoff mixed theorem merged_squares_mixedError :=
  fun (parts : List (Nat × Value × Value)) (first : Nat × Value × Value)
      (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (mergedSquares parts first)

/-- A Welford state as a record. -/
structure Moments (α : Type) where
  /-- The number of values seen. -/
  count : Nat
  /-- Their running mean. -/
  mean : α
  /-- Their sum of squared deviations from the mean. -/
  squares : α

/-- One step of Welford's algorithm on a record. -/
def momentsStep (state : Moments Value) (x : Value) : Moments Value :=
  let count := state.count + 1
  let delta := x - state.mean
  let mean := state.mean + delta / ExecFloat.Binary.ofRat ((count : ℤ) : ℚ)
  { count := count, mean := mean, squares := state.squares + delta * (x - mean) }

/-- Welford's sum of squared deviations, carried in a record. -/
def momentsSquares (xs : List Value) : Value :=
  (xs.foldl momentsStep { count := 0, mean := 0, squares := 0 }).squares

/-- The record's sum of squared deviations is finite and has a mixed bound against Welford's
recurrence in real arithmetic. -/
roundoff mixed theorem moments_squares_mixedError :=
  fun (xs : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (momentsSquares xs)

end Moments

section Compensated

/-- One step of Kahan summation on (sum, compensation). -/
def kahanStep (state : Value × Value) (x : Value) : Value × Value :=
  let y := x - state.2
  let t := state.1 + y
  (t, (t - state.1) - y)

/-- Kahan's compensated sum of a list. -/
def kahan (xs : List Value) : Value := (xs.foldl kahanStep (0, 0)).1

/-- Kahan's sum is finite and has a mixed bound against the same recurrence in real arithmetic,
whose compensation vanishes. -/
roundoff mixed theorem kahan_mixedError :=
  fun (xs : List Value) (hformat : format.isIEEE = true) => ExecFloat.Binary.toReal (kahan xs)

/-- The relation of Kahan's state `(s, c)` to the exact running sum `sum` and the budgets
`(E, C)`: both components are finite, `s - c` is within `E` of `sum`, and `|c| ≤ C`. -/
def KahanRelation (state : Value × Value) (sum : ℝ) (budgets : ℝ × ℝ) : Prop :=
  ExecFloat.Binary.isFinite state.1 = true ∧ ExecFloat.Binary.isFinite state.2 = true ∧
    |ExecFloat.Binary.toReal state.1 - ExecFloat.Binary.toReal state.2 - sum| ≤ budgets.1 ∧
    |ExecFloat.Binary.toReal state.2| ≤ budgets.2

/-- The budgets `(E, C)` after one Kahan step on the decoded entry `x`, from the exact running sum
`sum` and the budgets before it, with unit roundoff `u`. -/
noncomputable def kahanBudget (u sum : ℝ) (budgets : ℝ × ℝ) (x : ℝ) : ℝ × ℝ :=
  let entry := |x| + budgets.2
  let total := |sum| + budgets.1 + budgets.2 + (entry + u * entry)
  let shift := entry + u * entry + u * total
  let gap := u * total + u * shift
  (budgets.1 + u * entry + u * shift + u * gap, u * total + u * shift + u * gap)

/-- The range condition of one Kahan step: the bounds of its four exact operations, as
`kahanBudget` writes them, are at most `M`. -/
def KahanRange (u M sum : ℝ) (budgets : ℝ × ℝ) (x : ℝ) : Prop :=
  let entry := |x| + budgets.2
  let total := |sum| + budgets.1 + budgets.2 + (entry + u * entry)
  let shift := entry + u * entry + u * total
  entry ≤ M ∧ total ≤ M ∧ shift ≤ M ∧ u * total + u * shift ≤ M

/-- One Kahan step on a finite entry preserves `KahanRelation` against the exact sum extended by
the entry, with the budgets of `kahanBudget`, when `KahanRange` holds for the largest finite
value. -/
theorem kahanStep_relation (hformat : format.isIEEE = true) (state : Value × Value) (sum : ℝ)
    (budgets : ℝ × ℝ) (value : Value)
    (hcondition : ExecFloat.Binary.isFinite value = true ∧
      KahanRange (Model.unitRoundoffAt format) (Model.toReal (Model.posMaxFinite format)) sum
        budgets (ExecFloat.Binary.toReal value))
    (hrelation : KahanRelation state sum budgets) :
    KahanRelation (kahanStep state value) (sum + ExecFloat.Binary.toReal value)
      (kahanBudget (Model.unitRoundoffAt format) sum budgets (ExecFloat.Binary.toReal value)) := by
  obtain ⟨hs, hc, hE, hC⟩ := hrelation
  obtain ⟨hv, hentry, htotal, hshift, hgap⟩ := hcondition
  have hu : 0 ≤ Model.unitRoundoffAt format := (Model.unitRoundoffAt_pos format).le
  have kE := abs_le.mp hE
  have kC := abs_le.mp hC
  have kS := abs_le.mp (le_refl |sum|)
  have kx := abs_le.mp (le_refl |ExecFloat.Binary.toReal value|)
  -- The entry minus the compensation.
  have bentry : |ExecFloat.Binary.toReal value - ExecFloat.Binary.toReal state.2| ≤
      |ExecFloat.Binary.toReal value| + budgets.2 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have fy : ExecFloat.Binary.isFinite (value - state.2) = true :=
    ExecFloat.Binary.isFinite_sub_of_mixedError hv hc (.refl _) (by linarith)
  have ey : |ExecFloat.Binary.toReal (value - state.2) -
      (ExecFloat.Binary.toReal value - ExecFloat.Binary.toReal state.2)| ≤
      Model.unitRoundoffAt format * (|ExecFloat.Binary.toReal value| + budgets.2) := by
    have := (ExecFloat.Binary.sub_rounding fy).bound
    have := mul_le_mul_of_nonneg_left bentry hu
    linarith
  have ky := abs_le.mp ey
  -- The running sum plus the corrected entry.
  have btotal : |ExecFloat.Binary.toReal state.1 + ExecFloat.Binary.toReal (value - state.2)| ≤
      |sum| + budgets.1 + budgets.2 + (|ExecFloat.Binary.toReal value| + budgets.2 +
        Model.unitRoundoffAt format * (|ExecFloat.Binary.toReal value| + budgets.2)) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have ft : ExecFloat.Binary.isFinite (state.1 + (value - state.2)) = true :=
    ExecFloat.Binary.isFinite_add_of_mixedError hs fy (.refl _) (by linarith)
  have et : |ExecFloat.Binary.toReal (state.1 + (value - state.2)) -
      (ExecFloat.Binary.toReal state.1 + ExecFloat.Binary.toReal (value - state.2))| ≤
      Model.unitRoundoffAt format * (|sum| + budgets.1 + budgets.2 +
        (|ExecFloat.Binary.toReal value| + budgets.2 +
          Model.unitRoundoffAt format * (|ExecFloat.Binary.toReal value| + budgets.2))) := by
    have := (ExecFloat.Binary.add_rounding ft).bound
    have := mul_le_mul_of_nonneg_left btotal hu
    linarith
  have kt := abs_le.mp et
  -- The new sum minus the old one.
  have bshift : |ExecFloat.Binary.toReal (state.1 + (value - state.2)) -
      ExecFloat.Binary.toReal state.1| ≤
      |ExecFloat.Binary.toReal value| + budgets.2 +
        Model.unitRoundoffAt format * (|ExecFloat.Binary.toReal value| + budgets.2) +
        Model.unitRoundoffAt format * (|sum| + budgets.1 + budgets.2 +
          (|ExecFloat.Binary.toReal value| + budgets.2 +
            Model.unitRoundoffAt format * (|ExecFloat.Binary.toReal value| + budgets.2))) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have fz : ExecFloat.Binary.isFinite (state.1 + (value - state.2) - state.1) = true :=
    ExecFloat.Binary.isFinite_sub_of_mixedError ft hs (.refl _) (by linarith)
  have ez := (ExecFloat.Binary.sub_rounding fz).bound
  have kz := abs_le.mp ez
  have mz := mul_le_mul_of_nonneg_left bshift hu
  -- The rounding error of the sum that the compensation recovers.
  have bgap : |ExecFloat.Binary.toReal (state.1 + (value - state.2) - state.1) -
      ExecFloat.Binary.toReal (value - state.2)| ≤
      Model.unitRoundoffAt format * (|sum| + budgets.1 + budgets.2 +
          (|ExecFloat.Binary.toReal value| + budgets.2 +
            Model.unitRoundoffAt format * (|ExecFloat.Binary.toReal value| + budgets.2))) +
        Model.unitRoundoffAt format * (|ExecFloat.Binary.toReal value| + budgets.2 +
          Model.unitRoundoffAt format * (|ExecFloat.Binary.toReal value| + budgets.2) +
          Model.unitRoundoffAt format * (|sum| + budgets.1 + budgets.2 +
            (|ExecFloat.Binary.toReal value| + budgets.2 +
              Model.unitRoundoffAt format * (|ExecFloat.Binary.toReal value| + budgets.2)))) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have fc : ExecFloat.Binary.isFinite
      (state.1 + (value - state.2) - state.1 - (value - state.2)) = true :=
    ExecFloat.Binary.isFinite_sub_of_mixedError fz fy (.refl _) (by linarith)
  have ec := (ExecFloat.Binary.sub_rounding fc).bound
  have kc := abs_le.mp ec
  have mc := mul_le_mul_of_nonneg_left bgap hu
  dsimp only [KahanRelation, kahanStep, kahanBudget]
  refine ⟨ft, fc, abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩
omit [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)] in
/-- The exact running sum extended by the decoded entries is the start plus their sum. -/
theorem foldl_add_toReal (xs : List Value) (start : ℝ) :
    xs.foldl (fun sum (value : Value) => sum + ExecFloat.Binary.toReal value) start =
      start + (xs.map ExecFloat.Binary.toReal).sum := by
  induction xs generalizing start with
  | nil => simp
  | cons value rest ih => simp [ih, add_assoc]

/-- The budgets `(E, C)` that `kahanBudget` accumulates over Kahan summation of `xs`. -/
noncomputable def kahanBudgets (xs : List Value) : ℝ × ℝ :=
  List.foldBudget kahanStep (fun sum (value : Value) => sum + ExecFloat.Binary.toReal value)
    (fun _ sum budgets value =>
      kahanBudget (Model.unitRoundoffAt format) sum budgets (ExecFloat.Binary.toReal value))
    (0, 0) 0 (0, 0) xs

/-- Every entry of `xs` is finite and `KahanRange` holds, for the largest finite value, at every
step of Kahan summation of `xs`. -/
def KahanValid (xs : List Value) : Prop :=
  List.AllSteps (List.relationFoldStep kahanStep
      (fun sum (value : Value) => sum + ExecFloat.Binary.toReal value)
      (fun _ sum budgets value =>
        kahanBudget (Model.unitRoundoffAt format) sum budgets (ExecFloat.Binary.toReal value)))
    (fun state value => ExecFloat.Binary.isFinite value = true ∧
      KahanRange (Model.unitRoundoffAt format) (Model.toReal (Model.posMaxFinite format))
        state.2.1 state.2.2 (ExecFloat.Binary.toReal value))
    ((0, 0), 0, (0, 0)) xs

/-- Kahan's sum is finite and within `E + C` of the exact sum of the decoded entries, where
`(E, C) = kahanBudgets xs`, when `KahanValid xs` holds. -/
theorem kahan_sum_mixedError (hformat : format.isIEEE = true) (xs : List Value)
    (hvalid : KahanValid xs) :
    ExecFloat.Binary.isFinite (kahan xs) = true ∧
      MixedError (ExecFloat.Binary.toReal (kahan xs)) (xs.map ExecFloat.Binary.toReal).sum 0
        ((kahanBudgets xs).1 + (kahanBudgets xs).2) := by
  obtain ⟨hs, -, hE, hC⟩ := List.fold_relation kahanStep
    (fun sum (value : Value) => sum + ExecFloat.Binary.toReal value)
    (fun _ sum budgets value =>
      kahanBudget (Model.unitRoundoffAt format) sum budgets (ExecFloat.Binary.toReal value))
    KahanRelation
    (fun _ sum budgets value => ExecFloat.Binary.isFinite value = true ∧
      KahanRange (Model.unitRoundoffAt format) (Model.toReal (Model.posMaxFinite format)) sum
        budgets (ExecFloat.Binary.toReal value))
    (0, 0) 0 (0, 0) xs
    ⟨ExecFloat.Binary.isFinite_zero, ExecFloat.Binary.isFinite_zero, by simp, by simp⟩
    (fun state sum budgets value => kahanStep_relation hformat state sum budgets value) hvalid
  rw [foldl_add_toReal, zero_add] at hE
  unfold kahan kahanBudgets
  refine ⟨hs, MixedError.of_abs_sub_le ?_⟩
  have kE := abs_le.mp hE
  have kC := abs_le.mp hC
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- For `u ≤ 1/64` and `(k + 1) u ≤ 1/8`, nonnegative budgets `E ≤ (2u + 16 k u²) A` and
`C ≤ 3 u A` of a shadow sum at most `A` in magnitude become, after one Kahan step on an entry of
magnitude `a`, nonnegative budgets at most `(2u + 16 (k + 1) u²) (A + a)` and `3 u (A + a)`. -/
theorem kahanBudget_step_le {u sum A E C a k : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 64)
    (hk0 : 0 ≤ k) (hk : (k + 1) * u ≤ 1 / 8) (hsum : |sum| ≤ A) (hE0 : 0 ≤ E)
    (hE : E ≤ (2 * u + 16 * k * u ^ 2) * A) (hC0 : 0 ≤ C) (hC : C ≤ 3 * u * A) (ha : 0 ≤ a) :
    let entry := a + C
    let total := |sum| + E + C + (entry + u * entry)
    let shift := entry + u * entry + u * total
    let gap := u * total + u * shift
    0 ≤ E + u * entry + u * shift + u * gap ∧
      E + u * entry + u * shift + u * gap ≤ (2 * u + 16 * (k + 1) * u ^ 2) * (A + a) ∧
      0 ≤ u * total + u * shift + u * gap ∧
      u * total + u * shift + u * gap ≤ 3 * u * (A + a) := by
  intro entry total shift gap
  have hA : 0 ≤ A := (abs_nonneg _).trans hsum
  have hs0 : 0 ≤ |sum| := abs_nonneg _
  have huA : u * A ≤ A / 64 := by nlinarith
  have hua : u * a ≤ a / 64 := by nlinarith
  have huC : u * C ≤ C / 64 := by nlinarith
  have hku : k * u * (u * A) ≤ 1 / 8 * (u * A) := by
    have : k * u ≤ 1 / 8 := by nlinarith
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have hE4 : E ≤ 4 * u * A := by nlinarith
  -- The sum of the total and the entry.
  have hT0 : 0 ≤ total + entry := by positivity
  have hT : total + entry ≤ 5 / 4 * A + 21 / 10 * a := by
    simp only [total, entry]
    nlinarith
  have hC' : u * total + u * shift + u * gap = u * ((1 + u) ^ 2 * (total + entry)) := by
    simp only [gap, shift]; ring
  have hE' : E + u * entry + u * shift + u * gap =
      E + 2 * u * a + 2 * u * C + u ^ 2 * ((2 + u) * (total + entry)) := by
    simp only [gap, shift, entry]; ring
  have hsq : (1 + u) ^ 2 ≤ (65 / 64) ^ 2 := by nlinarith
  have hprod : (1 + u) ^ 2 * (total + entry) ≤ 3 * (A + a) := by
    have := mul_le_mul hsq hT hT0 (by positivity)
    nlinarith
  have hprod2 : (2 + u) * (total + entry) ≤ 8 * (A + a) := by
    have := mul_le_mul (show 2 + u ≤ 129 / 64 by linarith) hT hT0 (by positivity)
    nlinarith
  have m1 := mul_le_mul_of_nonneg_left hprod hu0
  have m2 := mul_le_mul_of_nonneg_left hprod2 (sq_nonneg u)
  have m3 := mul_le_mul_of_nonneg_left hC hu0
  have p1 : 0 ≤ k * u ^ 2 * a := by positivity
  have p2 : 0 ≤ u ^ 2 * A := by positivity
  have p3 : 0 ≤ u ^ 2 * a := by positivity
  have q1 : 0 ≤ u * ((1 + u) ^ 2 * (total + entry)) := by positivity
  have q2 : 0 ≤ u ^ 2 * ((2 + u) * (total + entry)) := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hE']; nlinarith
  · rw [hE']; nlinarith
  · rw [hC']; exact q1
  · rw [hC']; nlinarith

/-- From any state and nonnegative budgets `E ≤ (2u + 16 k u²) A` and `C ≤ 3 u A` of a shadow
sum at most `A` in magnitude, the budgets that `kahanBudget` accumulates over `xs` are
nonnegative and at most `(2u + 16 (k + n) u²) (A + Σ |x|)` and `3 u (A + Σ |x|)`, when
`u ≤ 1/64` and `(k + n) u ≤ 1/8` for the `n` entries of `xs`. -/
theorem foldBudget_kahan_le (hu : Model.unitRoundoffAt format ≤ 1 / 64) (xs : List Value)
    (state : Value × Value) (sum A E C k : ℝ) (hk0 : 0 ≤ k)
    (hk : (k + xs.length) * Model.unitRoundoffAt format ≤ 1 / 8) (hsum : |sum| ≤ A)
    (hE0 : 0 ≤ E) (hE : E ≤ (2 * Model.unitRoundoffAt format +
      16 * k * Model.unitRoundoffAt format ^ 2) * A)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 * Model.unitRoundoffAt format * A) :
    0 ≤ (List.foldBudget kahanStep
        (fun sum (value : Value) => sum + ExecFloat.Binary.toReal value)
        (fun _ sum budgets value =>
          kahanBudget (Model.unitRoundoffAt format) sum budgets (ExecFloat.Binary.toReal value))
        state sum (E, C) xs).1 ∧
      (List.foldBudget kahanStep
        (fun sum (value : Value) => sum + ExecFloat.Binary.toReal value)
        (fun _ sum budgets value =>
          kahanBudget (Model.unitRoundoffAt format) sum budgets (ExecFloat.Binary.toReal value))
        state sum (E, C) xs).1 ≤
        (2 * Model.unitRoundoffAt format +
          16 * (k + xs.length) * Model.unitRoundoffAt format ^ 2) *
          (A + (xs.map fun x => |ExecFloat.Binary.toReal x|).sum) ∧
      0 ≤ (List.foldBudget kahanStep
        (fun sum (value : Value) => sum + ExecFloat.Binary.toReal value)
        (fun _ sum budgets value =>
          kahanBudget (Model.unitRoundoffAt format) sum budgets (ExecFloat.Binary.toReal value))
        state sum (E, C) xs).2 ∧
      (List.foldBudget kahanStep
        (fun sum (value : Value) => sum + ExecFloat.Binary.toReal value)
        (fun _ sum budgets value =>
          kahanBudget (Model.unitRoundoffAt format) sum budgets (ExecFloat.Binary.toReal value))
        state sum (E, C) xs).2 ≤
        3 * Model.unitRoundoffAt format *
          (A + (xs.map fun x => |ExecFloat.Binary.toReal x|).sum) := by
  have hu0 : 0 ≤ Model.unitRoundoffAt format := (Model.unitRoundoffAt_pos format).le
  induction xs generalizing state sum A E C k with
  | nil => simpa using ⟨hE0, hE, hC0, hC⟩
  | cons x rest ih =>
    have hlen : (((x :: rest).length : ℕ) : ℝ) = rest.length + 1 := by simp
    have hmag : ((x :: rest).map fun x => |ExecFloat.Binary.toReal x|).sum =
        |ExecFloat.Binary.toReal x| + (rest.map fun x => |ExecFloat.Binary.toReal x|).sum := by
      simp
    rw [hlen] at hk
    have hrest : (0 : ℝ) ≤ rest.length := Nat.cast_nonneg _
    have hk1 : (k + 1) * Model.unitRoundoffAt format ≤ 1 / 8 := by nlinarith
    obtain ⟨b1, b2, b3, b4⟩ := kahanBudget_step_le hu0 hu hk0 hk1 hsum hE0 hE hC0 hC
      (abs_nonneg (ExecFloat.Binary.toReal x))
    have ks := abs_le.mp hsum
    have kx := abs_le.mp (le_refl |ExecFloat.Binary.toReal x|)
    have hsum' : |sum + ExecFloat.Binary.toReal x| ≤ A + |ExecFloat.Binary.toReal x| :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    obtain ⟨c1, c2, c3, c4⟩ := ih (kahanStep state x) (sum + ExecFloat.Binary.toReal x)
      (A + |ExecFloat.Binary.toReal x|) _ _ (k + 1) (by linarith) (by linarith) hsum' b1 b2 b3 b4
    rw [List.foldBudget_cons, hlen, hmag]
    exact ⟨c1, c2.trans_eq (by ring), c3, c4.trans_eq (by ring)⟩

/-- For unit roundoff at most `1/64` and `n u ≤ 1/8` over the `n` entries of `xs`, the budgets
`(E, C) = kahanBudgets xs` add up to at most `(5 u + 16 n u²) Σ |x|`. -/
theorem kahanBudgets_le (xs : List Value) (hu : Model.unitRoundoffAt format ≤ 1 / 64)
    (hn : xs.length * Model.unitRoundoffAt format ≤ 1 / 8) :
    (kahanBudgets xs).1 + (kahanBudgets xs).2 ≤
      (5 * Model.unitRoundoffAt format + 16 * xs.length * Model.unitRoundoffAt format ^ 2) *
        (xs.map fun x => |ExecFloat.Binary.toReal x|).sum := by
  obtain ⟨-, b2, -, b4⟩ := foldBudget_kahan_le hu xs (0, 0) 0 0 0 0 0 le_rfl (by simpa using hn)
    (by simp) le_rfl (by simp) le_rfl (by simp)
  unfold kahanBudgets
  simp only [zero_add] at b2 b4
  nlinarith [sq_nonneg (Model.unitRoundoffAt format)]

/-- For unit roundoff at most `1/64` and `n u ≤ 1/8` over the `n` entries of `xs`, Kahan's sum is
finite and within `(5 u + 16 n u²) Σ |x|` of the exact sum, when `KahanValid xs` holds. -/
theorem kahan_sum_abs_sub_le (hformat : format.isIEEE = true) (xs : List Value)
    (hu : Model.unitRoundoffAt format ≤ 1 / 64)
    (hn : xs.length * Model.unitRoundoffAt format ≤ 1 / 8) (hvalid : KahanValid xs) :
    ExecFloat.Binary.isFinite (kahan xs) = true ∧
      |ExecFloat.Binary.toReal (kahan xs) - (xs.map ExecFloat.Binary.toReal).sum| ≤
        (5 * Model.unitRoundoffAt format + 16 * xs.length * Model.unitRoundoffAt format ^ 2) *
          (xs.map fun x => |ExecFloat.Binary.toReal x|).sum := by
  obtain ⟨hfinite, hbound⟩ := kahan_sum_mixedError hformat xs hvalid
  refine ⟨hfinite, hbound.bound.trans ?_⟩
  rw [zero_mul, zero_add]
  exact kahanBudgets_le xs hu hn

/-- The recursive sum of a list. -/
def recursiveSum (xs : List Value) : Value := xs.foldl (· + ·) 0

/-- The recursive sum is finite and has a mixed bound against the exact sum. -/
roundoff mixed theorem recursive_sum_mixedError :=
  fun (xs : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (recursiveSum xs)

/-- The recursive sum is within `((1 + u)^n - 1) Σ |x|` of the exact sum, about `n u Σ |x|`
where Kahan's sum has `(5 u + 16 n u²) Σ |x|`. -/
example (hformat : format.isIEEE = true) (xs : List Value) := fun hvalid =>
  (List.abs_sub_le_of_sumFold_of_exact _ (Model.unitRoundoffAt_pos format).le _ _ _ _
      (recursive_sum_mixedError xs hformat hvalid).2 :
    |ExecFloat.Binary.toReal (recursiveSum xs) -
        xs.foldl (fun sum value => sum + ExecFloat.Binary.toReal value) 0| ≤
      ((1 + Model.unitRoundoffAt format) ^ xs.length - 1) *
        (xs.map fun x => |ExecFloat.Binary.toReal x|).sum)

attribute [local roundoff_rule] kahan_sum_mixedError

/-- A Kahan sum times a finite value is finite and has a mixed bound against the exact sum times
the value. -/
roundoff mixed theorem kahan_product_mixedError :=
  fun (xs : List Value) (y : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (kahan xs * y)

/-- The product's bound keeps `KahanValid` among its conditions and reads the Kahan budgets. -/
example (xs : List Value) (y : Value) (hformat : format.isIEEE = true) :=
  show KahanValid xs ∧ _ → _ ∧ MixedError _ _ _
      ((1 + Model.unitRoundoffAt format) * (((kahanBudgets xs).1 + (kahanBudgets xs).2) *
        |ExecFloat.Binary.toReal y|) + Model.underflowErrorAt format) from
    kahan_product_mixedError xs y hformat

end Compensated

section Selection

/-- The running maximum of the first components of a vector of (value, index) pairs. -/
def maxVector {n : Nat} (values : Vector (Value × Nat) n) (start : Value) : Value :=
  (values.foldl (fun (state : Value × Nat) e =>
    if state.1 < e.1 then (e.1, e.2) else state) (start, 0)).1

/-- The running maximum is finite and equals the real running maximum of the decoded values. -/
roundoff mixed theorem max_vector_mixedError :=
  fun {n : Nat} (values : Vector (Value × Nat) n) (start : Value)
      (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (maxVector values start)

/-- The running maximum of a list of (value, index) pairs, a tie selecting the later pair. -/
def lastMax (values : List (Value × Nat)) (start : Value) : Value :=
  (values.foldl (fun (state : Value × Nat) e =>
    if state.1 ≤ e.1 then (e.1, e.2) else state) (start, 0)).1

/-- The maximum under non-strict ties is finite and equals the real fold of the decoded values. -/
roundoff mixed theorem last_max_mixedError :=
  fun (values : List (Value × Nat)) (start : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (lastMax values start)

/-- The running minimum of a list, carried with its running maximum. -/
def range (values : List Value) (start : Value) : Value :=
  (values.foldl (fun (state : Value × Value) x =>
    (if state.1 < x then x else state.1, if x < state.2 then x else state.2)) (start, start)).2

/-- The running minimum is finite and equals the real running minimum of the decoded values. -/
roundoff mixed theorem range_mixedError :=
  fun (values : List Value) (start : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (range values start)

/-- The number of entries that reach the running record, times the final record. -/
def recordCount (xs : List Value) (start : Value) : Value :=
  let final := xs.foldl (fun (state : Value × Nat) x =>
    if state.1 ≤ x then (x, state.2 + 1) else state) (start, 0)
  ExecFloat.Binary.ofRat ((final.2 : ℤ) : ℚ) * final.1

/-- The record count times the record is finite and has a mixed bound against the real fold. The
count compares stored values only, so it is index data. -/
roundoff mixed theorem record_count_mixedError :=
  fun (xs : List Value) (start : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (recordCount xs start)

/-- The sum of the entries, each weighted by the number of earlier entries that set a new running
maximum, carried with that maximum and that count. -/
def recordWeighted (xs : List Value) (start : Value) : Value :=
  (xs.foldl (fun (state : Value × Nat × Value) x =>
    (if state.1 < x then x else state.1, if state.1 < x then state.2.1 + 1 else state.2.1,
      state.2.2 + ExecFloat.Binary.ofRat ((state.2.1 : ℤ) : ℚ) * x)) (start, 0, 0)).2.2

/-- The weighted sum is finite and has a mixed bound against its real fold, whose count tests the
real running maximum. -/
roundoff mixed theorem record_weighted_mixedError :=
  fun (xs : List Value) (start : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (recordWeighted xs start)

/-- The largest of zero and the prefix sums of a list, carried with the running sum and the number
of times the largest one grows. -/
def prefixTop (values : List Value) : Value :=
  (values.foldl (fun (state : Value × Value × Nat) x =>
    let s := state.1 + x
    if state.2.1 < s then (s, s, state.2.2 + 1) else (s, state.2.1, state.2.2)) (0, 0, 0)).2.1

/-- The largest prefix sum is finite and has a mixed bound against its real fold. -/
roundoff mixed theorem prefix_top_mixedError :=
  fun (values : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (prefixTop values)

end Selection

section Averages

/-- The bias-corrected exponential moving average of an array: the average over its weight. -/
def emaCorrected (xs : Array Value) (beta : Value) : Value :=
  let final := xs.foldl (fun (state : Value × Value) x =>
    (beta * state.1 + (1 - beta) * x, beta * state.2 + (1 - beta))) (0, 0)
  final.1 / final.2

/-- The corrected average is within its budget of the quotient of its real folds. -/
roundoff theorem ema_corrected_error :=
  fun (xs : Array Value) (beta : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (emaCorrected xs beta)

/-- The corrected average is finite and has a mixed bound against the quotient of its real
folds. -/
roundoff mixed theorem ema_corrected_mixedError :=
  fun (xs : Array Value) (beta : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (emaCorrected xs beta)

end Averages

section Shapes

/-- The second component copies the first one's previous value, a rounded running sum. -/
def delayed (xs : List Value) : Value :=
  (xs.foldl (fun (state : Value × Value) v => (state.1 + v, state.1)) (0, 0)).2

/-- The copy is finite and has the mixed bound of the running sum it copies. -/
roundoff mixed theorem delayed_mixedError :=
  fun (xs : List Value) (hformat : format.isIEEE = true) => ExecFloat.Binary.toReal (delayed xs)

/-- A sum of products with a running sum that starts at a rounded square. -/
def pairFromSquare (xs : List Value) (a : Value) : Value :=
  (xs.foldl (fun (state : Value × Value) x =>
    (state.1 + x, state.2 + state.1 * x)) (a * a, 0)).2

/-- The sum of products is finite and has a mixed bound that includes the rounding of the
start. -/
roundoff mixed theorem pair_from_square_mixedError :=
  fun (xs : List Value) (a : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (pairFromSquare xs a)

/-- A record state of a running maximum, a running sum and a count. -/
structure Running (α : Type) where
  /-- The running maximum. -/
  top : α
  /-- The running sum. -/
  total : α
  /-- The number of values seen. -/
  count : Nat

/-- The running sum of a list, carried in a record with its maximum and count. -/
def runningTotal (xs : List Value) (start : Value) : Value :=
  (xs.foldl (fun (state : Running Value) x =>
    { top := if state.top < x then x else state.top, total := state.total + x,
      count := state.count + 1 }) { top := start, total := 0, count := 0 }).total

/-- The record's running sum is finite and has a mixed bound against the real sum. -/
roundoff mixed theorem running_total_mixedError :=
  fun (xs : List Value) (start : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (runningTotal xs start)

/-- A record of one binary32 value. -/
structure Box where
  /-- The value. -/
  value : ExecFloat.Binary 8 23

/-- A record that wraps a `Box`. -/
structure Wrap where
  /-- The wrapped record. -/
  box : Box

/-- The first component copies the previous running sum of a list of binary32 values, which the
state keeps in a `Box`. -/
def boxDelayed (xs : List (ExecFloat.Binary 8 23)) : ExecFloat.Binary 8 23 :=
  (xs.foldl (fun (state : ExecFloat.Binary 8 23 × Box) x =>
    (state.2.value, ⟨state.2.value + x⟩)) (0, ⟨0⟩)).1

/-- The field of the record is a value of the format with a real reference of its own, so the copy
has the mixed bound of the real running sum. -/
roundoff mixed theorem box_delayed_mixedError :=
  fun (xs : List (ExecFloat.Binary 8 23)) => ExecFloat.Binary.toReal (boxDelayed xs)

/-- The same copy, the running sum kept in a `Box` inside a `Wrap`. -/
def wrapDelayed (xs : List (ExecFloat.Binary 8 23)) : ExecFloat.Binary 8 23 :=
  (xs.foldl (fun (state : ExecFloat.Binary 8 23 × Wrap) x =>
    (state.2.box.value, ⟨⟨state.2.box.value + x⟩⟩)) (0, ⟨⟨0⟩⟩)).1

/-- The wrapped copy is finite and has the mixed bound of the real running sum. -/
roundoff mixed theorem wrap_delayed_mixedError :=
  fun (xs : List (ExecFloat.Binary 8 23)) => ExecFloat.Binary.toReal (wrapDelayed xs)

end Shapes

section Agreement

/-- A sum gated by a flag that tests the rounded sum. -/
def gatedSum (xs : List Value) : Value :=
  (xs.foldl (fun (state : Value × Bool) x =>
    if state.2 then (state.1 + x, decide (state.1 < x)) else (state.1, true)) (0, true)).1

/-- The gated sum has a mixed bound against the sum gated by the same test of the exact sum, for
the executions whose tests of the rounded sum agree with it. -/
roundoff mixed theorem gated_sum_mixedError :=
  fun (xs : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (gatedSum xs)

/-- A sum that stops at the first nonzero entry that leaves it unchanged, with the flag that
records the stall. -/
def stallSum (xs : List Value) : Value :=
  (xs.foldl (fun (state : Value × Bool) x =>
    if state.2 then state else
      let next := state.1 + x
      (next, x != 0 && next == state.1)) (0, false)).1

/-- The stopping sum has a mixed bound against the exact sum for the executions whose test
`next == acc` agrees with the exact one. An exact sum stalls on no nonzero entry, so these are
the executions that do not stall. -/
roundoff mixed theorem stall_sum_mixedError :=
  fun (xs : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (stallSum xs)

/-- A sum that stops at the first zero entry. -/
def zeroStopSum (xs : List Value) : Value :=
  (xs.foldl (fun (state : Value × Bool) x =>
    if state.2 then state else (state.1 + x, x == 0)) (0, false)).1

/-- The test `x == 0` of an entry is the test of its real value, so the bound needs no agreement
premise. -/
roundoff mixed theorem zero_stop_sum_mixedError :=
  fun (xs : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (zeroStopSum xs)

/-- A sum gated by a flag that compares the rounded sum with the rounded square of an entry. -/
def squareGatedSum (xs : List Value) : Value :=
  (xs.foldl (fun (state : Value × Bool) x =>
    if state.2 then (state.1 + x, decide (state.1 < x * x)) else (state.1, true)) (0, true)).1

/-- The flag of the reference compares the exact sum with the exact square of the entry: neither
the rounded sum nor the rounded square enters the reference through the test, only the premise
that the two tests agree. -/
roundoff mixed theorem square_gated_sum_mixedError :=
  fun (xs : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (squareGatedSum xs)

/-- A sum gated by a flag that compares it with the entry held from the step before. -/
def delayedGate (xs : List Value) : Value :=
  (xs.foldl (fun (state : Value × Value × Bool) x =>
    (if state.2.2 then state.1 + x else state.1, x, decide (state.1 < state.2.1))) (0, 0, true)).1

/-- The held entry's reference is the decoded entry, a plain real expression, so the flag compares
the exact sum with it under the premise that the two tests agree. -/
roundoff mixed theorem delayed_gate_mixedError :=
  fun (xs : List Value) (hformat : format.isIEEE = true) => ExecFloat.Binary.toReal (delayedGate xs)

end Agreement

section Exact

/-- A sum gated by a flag that compares each entry with an entry of a table at a given index. -/
def tableGateAt (table : Vector Value 2) (xs : List Value) (i : Fin 2) : Value :=
  (xs.foldl (fun (state : Value × Bool) x =>
    (if state.2 then state.1 + x else state.1, decide (table[i] < x))) (0, true)).1

/-- The index is index data, so the test of the stored values is the test of their references. -/
roundoff mixed theorem table_gate_at_mixedError :=
  fun (table : Vector Value 2) (xs : List Value) (i : Fin 2) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (tableGateAt table xs i)

/-- A sum gated by a test of one of two stored values that index data chooses. -/
def indexGate (a b : Value) (n : Nat) (xs : List Value) : Value :=
  (xs.foldl (fun (state : Value × Bool) x =>
    (if state.2 then state.1 + x else state.1, decide ((if n ≤ 3 then a else b) < x))) (0, true)).1

/-- The choice is index data, so the test is the test of the chosen value's reference. -/
roundoff mixed theorem index_gate_mixedError :=
  fun (a b : Value) (n : Nat) (xs : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (indexGate a b n xs)

/-- A sum gated by a test of the difference of an entry, read at an index that rounding chooses,
with itself. -/
def differenceGate (table : Vector Value 2) (c : Value) (xs : List Value) : Value :=
  (xs.foldl (fun (state : Value × Bool) x =>
    (if state.2 then state.1 + x else state.1,
      decide (table[(if x * x ≤ c then 0 else 1 : Fin 2)] -
        table[(if x * x ≤ c then 0 else 1 : Fin 2)] < x))) (0, true)).1

/-- The difference is exactly zero, so the reference of the test, `0 < x`, makes no choice. -/
roundoff mixed theorem difference_gate_mixedError :=
  fun (table : Vector Value 2) (c : Value) (xs : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (differenceGate table c xs)

/-- An order on the reals that a section declares, which no reference may take. -/
local instance (priority := high) shiftedOrder : LT ℝ := ⟨fun a b => Real.instLT.lt a (b + 1)⟩

/-- The same sum with that order in scope. -/
roundoff mixed theorem shifted_gate_mixedError :=
  fun (table : Vector Value 2) (xs : List Value) (i : Fin 2) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (tableGateAt table xs i)

open Lean Meta in
-- The reference of the test compares by the reals' own order, `Real.instLT`.
run_meta do
  let found ← IO.mkRef (#[] : Array Lean.Expr)
  discard <| Meta.transform (← getConstInfo ``shifted_gate_mixedError).type (pre := fun term => do
    if term.isAppOfArity ``LT.lt 4 && (term.getArg! 0).isConstOf ``Real then
      found.modify (·.push (term.getArg! 1))
    return .continue)
  let orders ← found.get
  if orders.isEmpty || !orders.all (·.isConstOf ``Real.instLT) then
    throwError "the reference of the test does not compare by Real.instLT: {orders}"

end Exact

section Rejected

/-- The same sum gated by a test of a table entry read at an index that rounding chooses. -/
def tableGate (table : Vector Value 2) (xs : List Value) : Value :=
  (xs.foldl (fun (state : Value × Bool) x =>
    (if state.2 then state.1 + x else state.1,
      decide (table[(if x * x < x then 0 else 1 : Fin 2)] < x))) (0, true)).1

/--
error: roundoff: a discrete component of the loop state, decide (table[if value * value < value then
0 else 1] < value), is computed from real or floating-point values other than tests of exact ones,
so its shadow copy would keep their rounding
-/
#guard_msgs (whitespace := lax) in
roundoff mixed theorem table_gate_mixedError :=
  fun (table : Vector Value 2) (xs : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (tableGate table xs)

/-- The same sum gated by a test of one of two stored values that rounding chooses. -/
def branchGate (a b c : Value) (xs : List Value) : Value :=
  (xs.foldl (fun (state : Value × Bool) x =>
    (if state.2 then state.1 + x else state.1,
      decide ((if x * x ≤ c then a else b) < x))) (0, true)).1

/--
error: roundoff: a discrete component of the loop state, decide ((if value * value ≤ c then a else
b) < value), is computed from real or floating-point values other than tests of exact ones, so its
shadow copy would keep their rounding
-/
#guard_msgs (whitespace := lax) in
roundoff mixed theorem branch_gate_mixedError :=
  fun (a b c : Value) (xs : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (branchGate a b c xs)

/-- An entry of a table, read by a helper. -/
def lookup (table : Vector Value 2) (i : Fin 2) : Value := table[i]

/-- The same sum gated by a test of the entry the helper reads at an index rounding chooses. -/
def lookupGate (table : Vector Value 2) (c : Value) (xs : List Value) : Value :=
  (xs.foldl (fun (state : Value × Bool) x =>
    (if state.2 then state.1 + x else state.1,
      decide (lookup table (if x * x ≤ c then 0 else 1) < x))) (0, true)).1

/--
error: roundoff: a discrete component of the loop state, decide (lookup table (if value * value ≤ c
then 0 else 1) < value), is computed from real or floating-point values other than tests of exact
ones, so its shadow copy would keep their rounding
-/
#guard_msgs (whitespace := lax) in
roundoff mixed theorem lookup_gate_mixedError :=
  fun (table : Vector Value 2) (c : Value) (xs : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (lookupGate table c xs)

/-- The same sum gated by a test of a stored function at one of two indices rounding chooses. -/
def functionGate (f : Fin 2 → Value) (c : Value) (xs : List Value) : Value :=
  (xs.foldl (fun (state : Value × Bool) x =>
    (if state.2 then state.1 + x else state.1,
      decide ((if x * x ≤ c then f 0 else f 1) < x))) (0, true)).1

/--
error: roundoff: a discrete component of the loop state, decide ((if value * value ≤ c then f 0 else
f 1) < value), is computed from real or floating-point values other than tests of exact ones, so its
shadow copy would keep their rounding
-/
#guard_msgs (whitespace := lax) in
roundoff mixed theorem function_gate_mixedError :=
  fun (f : Fin 2 → Value) (c : Value) (xs : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (functionGate f c xs)

/-- The same sum gated by a test of a value that an optional read at a rounded index chooses. -/
def tagGate (tags : List Nat) (a b c : Value) (xs : List Value) : Value :=
  (xs.foldl (fun (state : Value × Bool) x =>
    (if state.2 then state.1 + x else state.1,
      decide ((match tags[(if x * x ≤ c then 0 else 1 : Nat)]? with
        | some _ => a
        | none => b) < x))) (0, true)).1

/--
error: roundoff: a discrete component of the loop state, decide ((match tags[if value * value ≤ c
then 0 else 1]? with | some val => a | none => b) < value), is computed from real or floating-point
values other than tests of exact ones, so its shadow copy would keep their rounding
-/
#guard_msgs (whitespace := lax) in
roundoff mixed theorem tag_gate_mixedError :=
  fun (tags : List Nat) (a b c : Value) (xs : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (tagGate tags a b c xs)

/-- Indices into a table of two entries, under a name that takes a value. -/
abbrev GateIndex (_ : Value) : Type := Fin 2

/-- An index that rounding chooses, of that type. -/
def roundedIndex (x c : Value) : GateIndex x := if x * x ≤ c then 0 else 1

/-- The same sum gated by a test of the entry at that index. -/
def aliasGate (table : Vector Value 2) (c : Value) (xs : List Value) : Value :=
  (xs.foldl (fun (state : Value × Bool) x =>
    (if state.2 then state.1 + x else state.1, decide (table[roundedIndex x c] < x))) (0, true)).1

/--
error: roundoff: a discrete component of the loop state, decide (table[roundedIndex value c] <
value), is computed from real or floating-point values other than tests of exact ones, so its shadow
copy would keep their rounding
-/
#guard_msgs (whitespace := lax) in
roundoff mixed theorem alias_gate_mixedError :=
  fun (table : Vector Value 2) (c : Value) (xs : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (aliasGate table c xs)

/-- The running mean of the values that set a running record. -/
def recordMean (xs : List Value) (start : Value) : Value :=
  (xs.foldl (fun (state : Value × Nat × Value) x =>
    if state.1 < x then
      let count := state.2.1 + 1
      (x, count, state.2.2 + (x - state.2.2) / ExecFloat.Binary.ofRat ((count : ℤ) : ℚ))
    else state) (start, 0, 0)).2.2

/--
error: roundoff: the loop's real reference depends on its rounded accumulator; establish agreement
of its branch conditions first
-/
#guard_msgs (whitespace := lax) in
roundoff mixed theorem record_mean_mixedError :=
  fun (xs : List Value) (start : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (recordMean xs start)

/-- One step of Neumaier summation, which compares the magnitudes of the rounded sum and the
entry. -/
def neumaierStep (state : Value × Value) (x : Value) : Value × Value :=
  let t := state.1 + x
  let large := if state.1 < 0 then -state.1 else state.1
  let small := if x < 0 then -x else x
  (t, state.2 + if small ≤ large then (state.1 - t) + x else (x - t) + state.1)

/-- Neumaier's compensated sum of a list. -/
def neumaier (xs : List Value) : Value :=
  let final := xs.foldl neumaierStep (0, 0)
  final.1 + final.2

/--
error: roundoff: the loop's real reference depends on its rounded accumulator; establish agreement
of its branch conditions first
-/
#guard_msgs (whitespace := lax) in
roundoff mixed theorem neumaier_mixedError :=
  fun (xs : List Value) (hformat : format.isIEEE = true) => ExecFloat.Binary.toReal (neumaier xs)

/-- A record whose index depends on its size. -/
structure Indexed (α : Type) where
  /-- The number of values seen. -/
  size : Nat
  /-- An index below the size. -/
  index : Fin (size + 1)
  /-- The running sum. -/
  value : α

/-- The running sum of a list, carried in a dependent record. -/
def indexedValue (xs : List Value) : Value :=
  (xs.foldl (fun (state : Indexed Value) x =>
    { size := state.size + 1, index := 0, value := state.value + x })
    { size := 0, index := 0, value := 0 }).value

/--
error: roundoff: the loop state component Indexed Value is neither a value of the observed format
Value, data without real or floating-point values, nor a pair or nondependent record of them
-/
#guard_msgs (whitespace := lax) in
roundoff mixed theorem indexed_value_mixedError :=
  fun (xs : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (indexedValue xs)

/-- A sum whose discrete component starts at the numerator and denominator of a rounded square, so
that each step would add the rounded square back. -/
def encodedStart (x : Value) (n : Nat) : Value :=
  let q := (ExecFloat.Binary.toRat? (x * x)).getD 0
  ((List.range n).foldl (fun (state : Value × (Int × Nat)) _ =>
      (state.1 + ExecFloat.Binary.ofRat ((state.2.1 : ℚ) / (state.2.2 : ℚ)), state.2))
    (0, (q.num, q.den))).1

/--
error: roundoff: a discrete component of the loop state starts at
(((ExecFloat.Binary.toRat? (x * x)).getD 0).num, ((ExecFloat.Binary.toRat? (x * x)).getD 0).den),
which is computed from real or floating-point values, so its shadow copy would keep their rounding
-/
#guard_msgs (whitespace := lax) in
roundoff mixed theorem encoded_start_mixedError :=
  fun (x : Value) (n : Nat) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (encodedStart x n)

/-- A sum whose discrete component holds the numerator and denominator of the rounded square of the
previous entry. -/
def encodedUpdate (xs : List Value) : Value :=
  (xs.foldl (fun (state : Value × (Int × Nat)) x =>
    let q := (ExecFloat.Binary.toRat? (x * x)).getD 0
    (state.1 + ExecFloat.Binary.ofRat ((state.2.1 : ℚ) / (state.2.2 : ℚ)), (q.num, q.den)))
    (0, (0, 1))).1

/--
error: roundoff: a discrete component of the loop state, (((ExecFloat.Binary.toRat? (value *
value)).getD 0).num, ((ExecFloat.Binary.toRat? (value * value)).getD 0).den), is computed from real
or floating-point values other than tests of exact ones, so its shadow copy would keep their
rounding
-/
#guard_msgs (whitespace := lax) in
roundoff mixed theorem encoded_update_mixedError :=
  fun (xs : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (encodedUpdate xs)

/-- A fold of a pair over a literal list of two values. -/
def literalPair (a b : Value) : Value :=
  ([a, b].foldl (fun (state : Value × Value) x => (state.1 + x, state.2 * x)) (0, 1)).2

/--
error: roundoff: the loop reads the entries of the computed container [a, b] as exact data, so its
reference would omit their rounding; write the producer into the step or register a law that does
(`Loop.fusions`)
-/
#guard_msgs (whitespace := lax) in
roundoff mixed theorem literal_pair_mixedError :=
  fun (a b : Value) (hformat : format.isIEEE = true) => ExecFloat.Binary.toReal (literalPair a b)

end Rejected

open Lean Elab Command

/-- The fold theorems, whether each is mixed, and whether each is exact, with zero budgets. -/
meta def proved : Array (Lean.Name × Bool × Option Bool) :=
  #[(``online_sum_mixedError, true, some false), (``online_sum_error, false, none),
    (``online_sum_array_mixedError, true, some false),
    (``online_sum_fin_mixedError, true, some false),
    (``online_sum_of_mixedError, true, some false), (``max_sum_error, false, some false),
    (``online_attention_mixedError, true, none), (``attention_vector_mixedError, true, none),
    (``blocked_mixedError, true, none), (``welford_mean_mixedError, true, some false),
    (``welford_squares_mixedError, true, some false),
    (``merged_squares_mixedError, true, some false),
    (``moments_squares_mixedError, true, some false), (``kahan_mixedError, true, some false),
    (``kahan_sum_mixedError, true, some false),
    (``max_vector_mixedError, true, some true), (``last_max_mixedError, true, some true),
    (``range_mixedError, true, some true), (``record_count_mixedError, true, none),
    (``record_weighted_mixedError, true, some false),
    (``prefix_top_mixedError, true, some false), (``ema_corrected_error, false, none),
    (``ema_corrected_mixedError, true, none), (``delayed_mixedError, true, some false),
    (``pair_from_square_mixedError, true, some false),
    (``running_total_mixedError, true, some false), (``box_delayed_mixedError, true, some false),
    (``wrap_delayed_mixedError, true, some false),
    (``gated_sum_mixedError, true, some false), (``stall_sum_mixedError, true, some false),
    (``zero_stop_sum_mixedError, true, some false),
    (``square_gated_sum_mixedError, true, some false),
    (``delayed_gate_mixedError, true, some false)]

/-- Fail unless each theorem of `theorems`, given with whether it is mixed and whether it is
exact, concludes finiteness and a mixed bound, or an absolute bound, whose reference decodes only
stored data, never a computed float, and calls neither a definition of the namespaces `here` nor
the floating-point exponential; an exact fold has zero budgets. -/
meta def checkFolds (here : Array Lean.Name)
    (theorems : Array (Lean.Name × Bool × Option Bool)) : CommandElabM Unit := do
  liftTermElabM do
    let environment ← getEnv
    let stored (term : Lean.Expr) : Bool := Id.run do
      let mut term := term
      while term.isProj || term.isAppOfArity ``Prod.fst 3 || term.isAppOfArity ``Prod.snd 3 do
        term := if term.isProj then term.projExpr! else term.appArg!
      return (term.getAppFn.isFVar || term.getAppFn.isBVar) &&
        term.getAppArgs.all fun argument => argument.isFVar || argument.isBVar
    let zero (term : Lean.Expr) : Bool :=
      term.isAppOfArity ``OfNat.ofNat 3 && (term.getArg! 1).rawNatLit? == some 0
    let arity ← Meta.forallTelescope (← getConstInfo ``ExecFloat.Binary.toReal).type
      fun arguments _ => pure arguments.size
    for (name, mixed, exact) in theorems do
      let type ← Meta.zetaReduce (← getConstInfo name).type
      Meta.forallTelescope type fun _ conclusion => do
        let (reference, budgets) ← if mixed then do
            unless conclusion.isAppOfArity ``And 2 do throwError "{name}: no finiteness"
            let bound := conclusion.appArg!
            unless bound.isAppOfArity ``MixedError 4 do throwError "{name}: no mixed bound"
            pure (bound.getArg! 1, #[bound.getArg! 2, bound.getArg! 3])
          else do
            unless conclusion.isAppOfArity ``LE.le 4 do throwError "{name}: no absolute bound"
            pure ((conclusion.getArg! 2).appArg!.appArg!, #[conclusion.getArg! 3])
        if let some read := reference.find? fun term =>
            term.isConstOf ``ExecFloat.Binary.CorrectlyRounded.exp ||
              (term.isConst && here.any (·.isPrefixOf term.constName!) &&
                !(environment.find? term.constName! matches some (.thmInfo _))) ||
              (term.isAppOfArity ``ExecFloat.Binary.toReal arity && !stored term.appArg!) then
          throwError "{name}: the reference reads {read}"
        if let some exact := exact then
          unless budgets.all zero == exact do
            throwError "{name}: the budgets {budgets} are {if exact then "not " else ""}zero"

-- Every tuple fold concludes the bound of its kind and has a reference that decodes only stored
-- data and calls no definition of this file.
run_cmd checkFolds #[`FloatLibTests.Conformance.BinaryInterchange.RoundoffTuples] proved

-- A test of the rounded sum enters the step condition as the premise that it agrees with the test
-- of the exact sum, an order test as an equivalence and `==` as an equation of decisions, each
-- between FloatLib's own test and the test of real numbers; the test `x == 0` of an entry is the
-- test of its real value and needs no premise.
run_cmd liftTermElabM do
  let own (test : Lean.Expr) (dictionary : Lean.Name) : Bool :=
    (test.getArg! 1).getAppFn.isConstOf dictionary
  let real (test : Lean.Expr) : Bool := (test.getArg! 0).isConstOf ``Real
  let agrees (name : Lean.Name) : MetaM Bool := do
    let type ← Meta.zetaReduce (← getConstInfo name).type
    return (type.find? fun term =>
      (term.isAppOfArity ``Iff 2 && (term.getArg! 0).isAppOfArity ``LT.lt 4 &&
          own (term.getArg! 0) ``ExecFloat.Binary.instLTFamily &&
          (term.getArg! 1).isAppOfArity ``LT.lt 4 && real (term.getArg! 1)) ||
        (term.isAppOfArity ``Eq 3 && (term.getArg! 1).isAppOfArity ``BEq.beq 4 &&
          own (term.getArg! 1) ``execFloatBEq &&
          (term.getArg! 2).isAppOfArity ``Decidable.decide 2 &&
          ((term.getArg! 2).getArg! 0).isAppOfArity ``Eq 3 &&
          real ((term.getArg! 2).getArg! 0))).isSome
  for name in #[``gated_sum_mixedError, ``stall_sum_mixedError, ``square_gated_sum_mixedError,
      ``delayed_gate_mixedError] do
    unless ← agrees name do throwError "{name} states no agreement of its test"
  if ← agrees ``zero_stop_sum_mixedError then
    throwError "zero_stop_sum_mixedError states an agreement of an exact test"

end FloatLibTests.Conformance.BinaryInterchange.RoundoffTuples
