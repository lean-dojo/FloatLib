/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Automation.Roundoff
public import FloatLib.Floats.Formats.BinaryInterchange.Configured
public import FloatLibTests.Conformance.BinaryInterchange.RoundoffTuples
public meta import FloatLibTests.Conformance.BinaryInterchange.RoundoffTuples
public meta import Lean.Elab.Command

/-!
# `roundoff` over loops read through registered step relations

A step relation registered in `Roundoff.Extension.stepRelations` is read by the tactic itself.
An observation that one of its readers concludes about, of a loop whose step unfolds to the
relation's step and whose start an initial lemma states, is bounded through `List.fold_relation`
before the rules for its operations are tried. Kahan's sum written inline over a list, an array or
a vector gets the compensated budget `E + C` of `kahan_sum_mixedError` (`kahan_list_mixedError`),
which `kahanBudgets_le` bounds.
Neumaier's sum, whose relation `NeumaierRelation` is proved here, gets a mixed bound with relative
part `u` under a range condition on its final addition (`neumaier_sum_mixedError`). A loop with
another step, or over computed entries, is proved by its components.
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.RoundoffStepRelations

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics
open FloatLibTests.Conformance.BinaryInterchange.RoundoffTuples

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
  [ExecFloat.ModelCodec plan (Model format) code]
  [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]

local notation "Value" => ExecFloat (Configured.Family format code plan)

omit [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)] in
/-- Kahan's relation holds at the start, against the empty sum with zero budgets. -/
theorem kahanRelation_zero : KahanRelation ((0 : Value), (0 : Value)) 0 (0, 0) :=
  ⟨ExecFloat.Binary.isFinite_zero, ExecFloat.Binary.isFinite_zero, by simp, by simp⟩

omit [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)] in
/-- Under Kahan's relation the sum is finite and within `E + C` of the exact sum. -/
theorem kahanRelation_read (state : Value × Value) (sum : ℝ) (budgets : ℝ × ℝ)
    (hrelation : KahanRelation state sum budgets) :
    ExecFloat.Binary.isFinite state.1 = true ∧
      MixedError (ExecFloat.Binary.toReal state.1) sum 0 (budgets.1 + budgets.2) := by
  obtain ⟨hs, -, hE, hC⟩ := hrelation
  refine ⟨hs, MixedError.of_abs_sub_le ?_⟩
  have kE := abs_le.mp hE
  have kC := abs_le.mp hC
  exact abs_le.mpr ⟨by linarith, by linarith⟩

public meta section

/-- Kahan's step relation, with its start and its reading of the sum. -/
def kahanRelation : Roundoff.Extension where
  stepRelations := #[{
    preservation := ``kahanStep_relation
    initial := #[``kahanRelation_zero]
    readers := #[``kahanRelation_read] }]

end

attribute [local roundoff_extension] kahanRelation

/-- Kahan's sum of a list, written inline. -/
def kahanList (xs : List Value) : Value :=
  (xs.foldl (fun (state : Value × Value) x =>
    let y := x - state.2
    let t := state.1 + y
    (t, (t - state.1) - y)) (0, 0)).1

/-- The inline sum is finite and has Kahan's compensated mixed bound. -/
roundoff mixed theorem kahan_list_mixedError :=
  fun (xs : List Value) (hformat : format.isIEEE = true) => ExecFloat.Binary.toReal (kahanList xs)

/-- The inline sum is within Kahan's compensated budget of the exact sum. -/
roundoff theorem kahan_list_error :=
  fun (xs : List Value) (hformat : format.isIEEE = true) => ExecFloat.Binary.toReal (kahanList xs)

/-- The inline sum has the budgets `kahanBudgets` of `kahan_sum_mixedError`. -/
example (hformat : format.isIEEE = true) (xs : List Value) (hvalid : KahanValid xs) :
    |ExecFloat.Binary.toReal (kahanList xs) -
        xs.foldl (fun sum value => sum + ExecFloat.Binary.toReal value) 0| ≤
      (kahanBudgets xs).1 + (kahanBudgets xs).2 :=
  kahan_list_error xs hformat hvalid

/-- The inline sum is within `(5 u + 16 n u²) Σ |x|` of the exact sum. -/
example (hformat : format.isIEEE = true) (xs : List Value)
    (hu : Model.unitRoundoffAt format ≤ 1 / 64)
    (hn : xs.length * Model.unitRoundoffAt format ≤ 1 / 8) (hvalid : KahanValid xs) :
    |ExecFloat.Binary.toReal (kahanList xs) -
        xs.foldl (fun sum value => sum + ExecFloat.Binary.toReal value) 0| ≤
      (5 * Model.unitRoundoffAt format + 16 * xs.length * Model.unitRoundoffAt format ^ 2) *
        (xs.map fun x => |ExecFloat.Binary.toReal x|).sum :=
  (kahan_list_error xs hformat hvalid).trans (kahanBudgets_le xs hu hn)

/-- Kahan's sum of an array, written inline. -/
def kahanArray (xs : Array Value) : Value :=
  (xs.foldl (fun (state : Value × Value) x =>
    let y := x - state.2
    let t := state.1 + y
    (t, (t - state.1) - y)) (0, 0)).1

/-- The array sum is finite and has Kahan's compensated mixed bound. -/
roundoff mixed theorem kahan_array_mixedError :=
  fun (xs : Array Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (kahanArray xs)

/-- Kahan's sum of a vector, written inline. -/
def kahanVector {n : Nat} (xs : Vector Value n) : Value :=
  (xs.foldl (fun (state : Value × Value) x =>
    let y := x - state.2
    let t := state.1 + y
    (t, (t - state.1) - y)) (0, 0)).1

/-- The vector sum is finite and has Kahan's compensated mixed bound. -/
roundoff mixed theorem kahan_vector_mixedError :=
  fun {n : Nat} (xs : Vector Value n) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (kahanVector xs)

/-- The vector sum has the budgets `kahanBudgets` of its entries. -/
example (hformat : format.isIEEE = true) {n : Nat} (xs : Vector Value n)
    (hvalid : KahanValid xs.toList) :
    ExecFloat.Binary.isFinite (kahanVector xs) = true ∧
      MixedError (ExecFloat.Binary.toReal (kahanVector xs))
        (xs.toList.foldl (fun sum value => sum + ExecFloat.Binary.toReal value) 0) 0
        ((kahanBudgets xs.toList).1 + (kahanBudgets xs.toList).2) :=
  kahan_vector_mixedError xs hformat hvalid

omit [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)] in
/-- The magnitude of a finite value, as Neumaier's step computes it, is finite and decodes to
the magnitude of the decoded value. -/
theorem magnitude_toReal {value : Value} (hvalue : ExecFloat.Binary.isFinite value = true) :
    ExecFloat.Binary.isFinite (if value < 0 then -value else value) = true ∧
      ExecFloat.Binary.toReal (if value < 0 then -value else value) =
        |ExecFloat.Binary.toReal value| := by
  have hzero := ExecFloat.Binary.isFinite_zero (format := format) (plan := plan) (code := code)
  by_cases hneg : value < 0
  · have hlt := (ExecFloat.Binary.lt_iff_toReal_lt hvalue hzero).mp hneg
    have hexact := (ExecFloat.Binary.mixedError_toReal_neg hvalue (MixedError.refl _)).bound
    rw [ExecFloat.Binary.toReal_zero] at hlt
    rw [ite_eq_left hneg, ExecFloat.Binary.isFinite_neg, abs_of_neg hlt]
    refine ⟨hvalue, ?_⟩
    simp only [zero_mul, add_zero, abs_nonpos_iff, sub_eq_zero] at hexact
    exact hexact
  · have hge := mt (ExecFloat.Binary.lt_iff_toReal_lt hvalue hzero).mpr hneg
    rw [ExecFloat.Binary.toReal_zero, not_lt] at hge
    rw [ite_eq_right hneg, abs_of_nonneg hge]
    exact ⟨hvalue, rfl⟩

/-- The relation of Neumaier's state `(s, c)` to the exact running sum `sum` and the budgets
`(E, C)`: both components are finite, `s + c` is within `E` of `sum`, and `|c| ≤ C`. -/
def NeumaierRelation (state : Value × Value) (sum : ℝ) (budgets : ℝ × ℝ) : Prop :=
  ExecFloat.Binary.isFinite state.1 = true ∧ ExecFloat.Binary.isFinite state.2 = true ∧
    |ExecFloat.Binary.toReal state.1 + ExecFloat.Binary.toReal state.2 - sum| ≤ budgets.1 ∧
    |ExecFloat.Binary.toReal state.2| ≤ budgets.2

/-- The budgets `(E, C)` after one Neumaier step on the decoded entry `x`, from the exact running
sum `sum` and the budgets before it, with unit roundoff `u`. -/
noncomputable def neumaierBudget (u sum : ℝ) (budgets : ℝ × ℝ) (x : ℝ) : ℝ × ℝ :=
  let total := |sum| + budgets.1 + budgets.2 + |x|
  let difference := |x| + u * total
  let inner := u * total + u * difference
  let gap := budgets.2 + inner + u * inner
  (budgets.1 + u * difference + u * inner + u * gap, gap + u * gap)

/-- The range condition of one Neumaier step: the bounds of its four exact operations, as
`neumaierBudget` writes them, are at most `M`. -/
def NeumaierRange (u M sum : ℝ) (budgets : ℝ × ℝ) (x : ℝ) : Prop :=
  let total := |sum| + budgets.1 + budgets.2 + |x|
  let difference := |x| + u * total
  let inner := u * total + u * difference
  total ≤ M ∧ difference ≤ M ∧ inner ≤ M ∧ budgets.2 + inner + u * inner ≤ M

/-- One Neumaier step on a finite entry preserves `NeumaierRelation` against the exact sum
extended by the entry, with the budgets of `neumaierBudget`, when `NeumaierRange` holds for the
largest finite value. Each branch's subtraction is bounded by the entry's magnitude, the smaller
one, so the compensation is not needed exact. -/
theorem neumaierStep_relation (hformat : format.isIEEE = true) (state : Value × Value) (sum : ℝ)
    (budgets : ℝ × ℝ) (value : Value)
    (hcondition : ExecFloat.Binary.isFinite value = true ∧
      NeumaierRange (Model.unitRoundoffAt format) (Model.toReal (Model.posMaxFinite format)) sum
        budgets (ExecFloat.Binary.toReal value))
    (hrelation : NeumaierRelation state sum budgets) :
    NeumaierRelation (neumaierStep state value) (sum + ExecFloat.Binary.toReal value)
      (neumaierBudget (Model.unitRoundoffAt format) sum budgets
        (ExecFloat.Binary.toReal value)) := by
  obtain ⟨hs, hc, hE, hC⟩ := hrelation
  obtain ⟨hv, htotal, hdifference, hinner, hgap⟩ := hcondition
  have hu : 0 ≤ Model.unitRoundoffAt format := (Model.unitRoundoffAt_pos format).le
  have kE := abs_le.mp hE
  have kC := abs_le.mp hC
  have kS := abs_le.mp (le_refl |sum|)
  have kx := abs_le.mp (le_refl |ExecFloat.Binary.toReal value|)
  have ks := abs_le.mp (le_refl |ExecFloat.Binary.toReal state.1|)
  -- The rounded sum.
  have btotal : |ExecFloat.Binary.toReal state.1 + ExecFloat.Binary.toReal value| ≤
      |sum| + budgets.1 + budgets.2 + |ExecFloat.Binary.toReal value| :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have ft : ExecFloat.Binary.isFinite (state.1 + value) = true :=
    ExecFloat.Binary.isFinite_add_of_mixedError hs hv (.refl _) (by linarith)
  have et : |ExecFloat.Binary.toReal (state.1 + value) -
      (ExecFloat.Binary.toReal state.1 + ExecFloat.Binary.toReal value)| ≤
      Model.unitRoundoffAt format *
        (|sum| + budgets.1 + budgets.2 + |ExecFloat.Binary.toReal value|) := by
    have := (ExecFloat.Binary.add_rounding ft).bound
    have := mul_le_mul_of_nonneg_left btotal hu
    linarith
  have kt := abs_le.mp et
  -- The test compares the magnitudes of the entry and of the sum.
  obtain ⟨fsmall, rsmall⟩ := magnitude_toReal hv
  obtain ⟨flarge, rlarge⟩ := magnitude_toReal hs
  have kv := abs_le.mp (le_refl |ExecFloat.Binary.toReal value|)
  dsimp only [NeumaierRelation, neumaierStep, neumaierBudget]
  by_cases htest : (if value < 0 then -value else value) ≤
      (if state.1 < 0 then -state.1 else state.1)
  · have hle := (ExecFloat.Binary.le_iff_toReal_le fsmall flarge).mp htest
    rw [rsmall, rlarge] at hle
    rw [ite_eq_left htest]
    -- The sum minus the rounded sum is the entry and the sum's rounding error.
    have bz : |ExecFloat.Binary.toReal state.1 - ExecFloat.Binary.toReal (state.1 + value)| ≤
        |ExecFloat.Binary.toReal value| + Model.unitRoundoffAt format *
          (|sum| + budgets.1 + budgets.2 + |ExecFloat.Binary.toReal value|) :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    have fz : ExecFloat.Binary.isFinite (state.1 - (state.1 + value)) = true :=
      ExecFloat.Binary.isFinite_sub_of_mixedError hs ft (.refl _) (by linarith)
    have ez := (ExecFloat.Binary.sub_rounding fz).bound
    have mz := mul_le_mul_of_nonneg_left bz hu
    have kz := abs_le.mp ez
    have bw : |ExecFloat.Binary.toReal (state.1 - (state.1 + value)) +
        ExecFloat.Binary.toReal value| ≤
        Model.unitRoundoffAt format *
            (|sum| + budgets.1 + budgets.2 + |ExecFloat.Binary.toReal value|) +
          Model.unitRoundoffAt format * (|ExecFloat.Binary.toReal value| +
            Model.unitRoundoffAt format *
              (|sum| + budgets.1 + budgets.2 + |ExecFloat.Binary.toReal value|)) := by
      have := abs_le.mp (le_refl |ExecFloat.Binary.toReal state.1 -
        ExecFloat.Binary.toReal (state.1 + value)|)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have fw : ExecFloat.Binary.isFinite (state.1 - (state.1 + value) + value) = true :=
      ExecFloat.Binary.isFinite_add_of_mixedError fz hv (.refl _) (by linarith)
    have ew := (ExecFloat.Binary.add_rounding fw).bound
    have mw := mul_le_mul_of_nonneg_left bw hu
    have kw := abs_le.mp ew
    have bc : |ExecFloat.Binary.toReal state.2 +
        ExecFloat.Binary.toReal (state.1 - (state.1 + value) + value)| ≤
        budgets.2 + (Model.unitRoundoffAt format *
            (|sum| + budgets.1 + budgets.2 + |ExecFloat.Binary.toReal value|) +
          Model.unitRoundoffAt format * (|ExecFloat.Binary.toReal value| +
            Model.unitRoundoffAt format *
              (|sum| + budgets.1 + budgets.2 + |ExecFloat.Binary.toReal value|))) +
        Model.unitRoundoffAt format * (Model.unitRoundoffAt format *
            (|sum| + budgets.1 + budgets.2 + |ExecFloat.Binary.toReal value|) +
          Model.unitRoundoffAt format * (|ExecFloat.Binary.toReal value| +
            Model.unitRoundoffAt format *
              (|sum| + budgets.1 + budgets.2 + |ExecFloat.Binary.toReal value|))) := by
      have := abs_le.mp (le_refl |ExecFloat.Binary.toReal (state.1 - (state.1 + value)) +
        ExecFloat.Binary.toReal value|)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have fc : ExecFloat.Binary.isFinite
        (state.2 + (state.1 - (state.1 + value) + value)) = true :=
      ExecFloat.Binary.isFinite_add_of_mixedError hc fw (.refl _) (by linarith)
    have ec := (ExecFloat.Binary.add_rounding fc).bound
    have mc := mul_le_mul_of_nonneg_left bc hu
    have kc := abs_le.mp ec
    refine ⟨ft, fc, abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  · have hlt := mt (ExecFloat.Binary.le_iff_toReal_le fsmall flarge).mpr htest
    rw [rsmall, rlarge, not_le] at hlt
    rw [ite_eq_right htest]
    -- The entry minus the rounded sum is the sum and the sum's rounding error, and the sum is the
    -- smaller one.
    have bz : |ExecFloat.Binary.toReal value - ExecFloat.Binary.toReal (state.1 + value)| ≤
        |ExecFloat.Binary.toReal value| + Model.unitRoundoffAt format *
          (|sum| + budgets.1 + budgets.2 + |ExecFloat.Binary.toReal value|) :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    have fz : ExecFloat.Binary.isFinite (value - (state.1 + value)) = true :=
      ExecFloat.Binary.isFinite_sub_of_mixedError hv ft (.refl _) (by linarith)
    have ez := (ExecFloat.Binary.sub_rounding fz).bound
    have mz := mul_le_mul_of_nonneg_left bz hu
    have kz := abs_le.mp ez
    have bw : |ExecFloat.Binary.toReal (value - (state.1 + value)) +
        ExecFloat.Binary.toReal state.1| ≤
        Model.unitRoundoffAt format *
            (|sum| + budgets.1 + budgets.2 + |ExecFloat.Binary.toReal value|) +
          Model.unitRoundoffAt format * (|ExecFloat.Binary.toReal value| +
            Model.unitRoundoffAt format *
              (|sum| + budgets.1 + budgets.2 + |ExecFloat.Binary.toReal value|)) := by
      have := abs_le.mp (le_refl |ExecFloat.Binary.toReal value -
        ExecFloat.Binary.toReal (state.1 + value)|)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have fw : ExecFloat.Binary.isFinite (value - (state.1 + value) + state.1) = true :=
      ExecFloat.Binary.isFinite_add_of_mixedError fz hs (.refl _) (by linarith)
    have ew := (ExecFloat.Binary.add_rounding fw).bound
    have mw := mul_le_mul_of_nonneg_left bw hu
    have kw := abs_le.mp ew
    have bc : |ExecFloat.Binary.toReal state.2 +
        ExecFloat.Binary.toReal (value - (state.1 + value) + state.1)| ≤
        budgets.2 + (Model.unitRoundoffAt format *
            (|sum| + budgets.1 + budgets.2 + |ExecFloat.Binary.toReal value|) +
          Model.unitRoundoffAt format * (|ExecFloat.Binary.toReal value| +
            Model.unitRoundoffAt format *
              (|sum| + budgets.1 + budgets.2 + |ExecFloat.Binary.toReal value|))) +
        Model.unitRoundoffAt format * (Model.unitRoundoffAt format *
            (|sum| + budgets.1 + budgets.2 + |ExecFloat.Binary.toReal value|) +
          Model.unitRoundoffAt format * (|ExecFloat.Binary.toReal value| +
            Model.unitRoundoffAt format *
              (|sum| + budgets.1 + budgets.2 + |ExecFloat.Binary.toReal value|))) := by
      have := abs_le.mp (le_refl |ExecFloat.Binary.toReal (value - (state.1 + value)) +
        ExecFloat.Binary.toReal state.1|)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have fc : ExecFloat.Binary.isFinite
        (state.2 + (value - (state.1 + value) + state.1)) = true :=
      ExecFloat.Binary.isFinite_add_of_mixedError hc fw (.refl _) (by linarith)
    have ec := (ExecFloat.Binary.add_rounding fc).bound
    have mc := mul_le_mul_of_nonneg_left bc hu
    have kc := abs_le.mp ec
    refine ⟨ft, fc, abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩

omit [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)] in
/-- Neumaier's relation holds at the start, against the empty sum with zero budgets. -/
theorem neumaierRelation_zero : NeumaierRelation ((0 : Value), (0 : Value)) 0 (0, 0) :=
  ⟨ExecFloat.Binary.isFinite_zero, ExecFloat.Binary.isFinite_zero, by simp, by simp⟩

/-- Under Neumaier's relation the rounded sum of the two components is finite and has a mixed
bound against the exact sum, when the sum's magnitude and budget are at most the largest finite
value. -/
theorem neumaierRelation_read (hformat : format.isIEEE = true) (state : Value × Value)
    (sum : ℝ) (budgets : ℝ × ℝ) (hrelation : NeumaierRelation state sum budgets)
    (hrange : |sum| + budgets.1 ≤ Model.toReal (Model.posMaxFinite format)) :
    ExecFloat.Binary.isFinite (state.1 + state.2) = true ∧
      MixedError (ExecFloat.Binary.toReal (state.1 + state.2)) sum (Model.unitRoundoffAt format)
        ((1 + Model.unitRoundoffAt format) * budgets.1) := by
  obtain ⟨hs, hc, hE, -⟩ := hrelation
  have hu : 0 ≤ Model.unitRoundoffAt format := (Model.unitRoundoffAt_pos format).le
  have kE := abs_le.mp hE
  have kS := abs_le.mp (le_refl |sum|)
  have hE0 : 0 ≤ budgets.1 := (abs_nonneg _).trans hE
  have bsum : |ExecFloat.Binary.toReal state.1 + ExecFloat.Binary.toReal state.2| ≤
      |sum| + budgets.1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have fsum : ExecFloat.Binary.isFinite (state.1 + state.2) = true :=
    ExecFloat.Binary.isFinite_add_of_mixedError hs hc (.refl _) (by linarith)
  have esum := (ExecFloat.Binary.add_rounding fsum).bound
  have msum := mul_le_mul_of_nonneg_left bsum hu
  have kr := abs_le.mp esum
  refine ⟨fsum, ⟨hu, mul_nonneg (by linarith) hE0, abs_le.mpr ⟨by linarith, by linarith⟩⟩⟩

public meta section

/-- Neumaier's step relation, with its start and its reading of the rounded sum `s + c`. -/
def neumaierRelation : Roundoff.Extension where
  stepRelations := #[{
    preservation := ``neumaierStep_relation
    initial := #[``neumaierRelation_zero]
    readers := #[``neumaierRelation_read] }]

end

attribute [local roundoff_extension] neumaierRelation

/-- Neumaier's sum is finite and has a mixed bound with relative part `u` against the exact sum,
under the range conditions of its steps and of its final addition. -/
roundoff mixed theorem neumaier_sum_mixedError :=
  fun (xs : List Value) (hformat : format.isIEEE = true) => ExecFloat.Binary.toReal (neumaier xs)

/-- Neumaier's sum has an absolute bound against the exact sum. -/
roundoff theorem neumaier_sum_error :=
  fun (xs : List Value) (hformat : format.isIEEE = true) => ExecFloat.Binary.toReal (neumaier xs)

/-- Neumaier's sum of an array, with the step written inline. -/
def neumaierArray (xs : Array Value) : Value :=
  let final := xs.foldl (fun (state : Value × Value) x =>
    let t := state.1 + x
    let large := if state.1 < 0 then -state.1 else state.1
    let small := if x < 0 then -x else x
    (t, state.2 + if small ≤ large then (state.1 - t) + x else (x - t) + state.1)) (0, 0)
  final.1 + final.2

/-- The inline sum over an array has Neumaier's mixed bound. -/
roundoff mixed theorem neumaier_array_mixedError :=
  fun (xs : Array Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (neumaierArray xs)

/-- A sum beside its running maximum, whose step is not Kahan's: the step relations do not match,
and the sum, which does not read the maximum, is proved as a loop of its own. -/
def sumBesideMax (xs : List Value) : Value :=
  (xs.foldl (fun (state : Value × Value) x => (state.1 + x, max state.2 x)) (0, 0)).1

/-- The sum beside a maximum has the mixed bound of a recursive sum. -/
roundoff mixed theorem sum_beside_max_mixedError :=
  fun (xs : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (sumBesideMax xs)

/-- Kahan's sum of the squares of a list. -/
def kahanSquares (xs : List Value) : Value :=
  ((xs.map fun x => x * x).foldl kahanStep (0, 0)).1

/-- The squares are computed, so the step relation, which reads stored entries, does not apply,
and the loop is proved by its components. -/
roundoff mixed theorem kahan_squares_mixedError :=
  fun (xs : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (kahanSquares xs)

open Lean Elab Command

/-- The theorems read through a registered step relation or proved by their components, whether
each is mixed, and whether each is exact, with zero budgets. -/
meta def relationFolds : Array (Lean.Name × Bool × Option Bool) :=
  #[(``kahan_list_mixedError, true, some false), (``kahan_list_error, false, some false),
    (``kahan_array_mixedError, true, some false),
    (``kahan_vector_mixedError, true, some false),
    (``neumaier_sum_mixedError, true, some false), (``neumaier_sum_error, false, some false),
    (``neumaier_array_mixedError, true, some false),
    (``kahan_squares_mixedError, true, some false)]

-- Each concludes the bound of its kind and has a reference that decodes only stored data and
-- calls no definition of this file or of `RoundoffTuples`.
run_cmd checkFolds #[`FloatLibTests.Conformance.BinaryInterchange.RoundoffTuples,
  `FloatLibTests.Conformance.BinaryInterchange.RoundoffStepRelations] relationFolds

end FloatLibTests.Conformance.BinaryInterchange.RoundoffStepRelations
