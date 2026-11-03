/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Batteries.Data.Fin.Fold
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.Rational
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.CorrectlyRounded
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Instances
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.MixedError.Rounding
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Operations.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Real
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Rounding.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.CoreProof
public import FloatLib.Numerics.Capabilities.Elementary
public import FloatLib.Numerics.Enclosure.Interval.HyperbolicProof
public import FloatLib.Numerics.ErrorBound
public import FloatLib.Numerics.ErrorBound.Loop
public import FloatLib.Numerics.ErrorBound.RelationLoop
public import FloatLib.Numerics.MixedError.Elementary
public import Mathlib.Data.Rat.Cast.Lemmas
public meta import FloatLib.Floats.Formats.BinaryInterchange.Automation.Roundoff.Extension

/-!
# FloatLib's rules for `roundoff`

The codec laws let the analysis read a configured value through the model operation that
computes it, and a split of an optional value keeps its payload as computed. The registrations
below give `roundoff` FloatLib's own numerical theorems: the rounding of each configured and model
operation, the propagation of absolute and mixed errors through exact real operations, rational
and integer conversions, rounding to an integral value and C's integer casts, and the finiteness
and order facts that range conditions and signs need. The range of an `int8_t` cast is a condition
on the bound of the integer it casts, so it reads as a bound on the real reference.

FloatLib's containers are registered here too. An entry of a list, an array or a vector is read by
`GetElem.getElem`, and an entry of a function on `Fin n` or of a matrix by application; an entry of
a stored input is exact data. A loop over a list carries the invariant of `List.fold_error` and
`List.fold_mixedError`, or the relation of `List.fold_relation` when its state is a tuple, and loops
over `Fin n`, arrays and vectors are first written as loops over their lists. A loop over a map or a
pointwise combination of such containers is a loop over the containers it reads, with the producer
in its step. The sums of a list and of a function on `Fin n` are such loops.
-/

public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Roundoff

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
  [ExecFloat.ModelCodec plan (Model format) code]

/-- The binary decoder preserves values packed by the same configured family. -/
theorem decode_family (value : Model format) :
    ExecFloat.Binary.toModel
        (Configured.Family.ofModel (plan := plan) (code := code) value) = value := by
  change Configured.Family.toModel (Configured.Family.ofModel value) = value
  exact Configured.Family.toModel_ofModel value

/-- The codec preserves any unary model operation, including the scalar context's functions. -/
theorem decode_unary (operation : Model format → Model format)
    (value : ExecFloat (Configured.Family format code plan)) :
    ExecFloat.Binary.toModel
        (ExecFloat.ModelCodec.liftUnary (Model := Model format) (plan := plan) operation value) =
      operation (ExecFloat.Binary.toModel value) :=
  ExecFloat.ModelCodec.decode_liftUnary operation value

/-- Binary scalar lifts use the same codec law regardless of their numerical operation. -/
theorem decode_binary (operation : Model format → Model format → Model format)
    (left right : ExecFloat (Configured.Family format code plan)) :
    ExecFloat.Binary.toModel
        (ExecFloat.ModelCodec.liftBinary (Model := Model format) (plan := plan)
          operation left right) =
      operation (ExecFloat.Binary.toModel left) (ExecFloat.Binary.toModel right) :=
  ExecFloat.ModelCodec.decode_liftBinary operation left right

/-- The codec preserves an outcome's value independently of its exception indicators. -/
theorem decode_outcome (outcome : Model.IEEEOutcome format) :
    ExecFloat.Binary.toModel
        ((ExecFloat.Binary.IEEEOutcome.ofModel (plan := plan) (code := code) outcome).value) =
      outcome.value := by
  simpa only [ExecFloat.Binary.IEEEOutcome.toModel] using
    congrArg Model.IEEEOutcome.value
      (ExecFloat.Binary.IEEEOutcome.toModel_ofModel (plan := plan) (code := code) outcome)

/-- A real observation can pass through a scalar lift before its numerical law is applied. -/
theorem toReal_liftUnary (operation : Model format → Model format)
    (value : ExecFloat (Configured.Family format code plan)) :
    ExecFloat.Binary.toReal
        (ExecFloat.ModelCodec.liftUnary (Model := Model format) (plan := plan) operation value) =
      Model.toReal (operation (ExecFloat.Binary.toModel value)) :=
  congrArg Model.toReal (decode_unary operation value)

/-- Binary lifts retain the chosen model operation and both operands. -/
theorem toReal_liftBinary (operation : Model format → Model format → Model format)
    (left right : ExecFloat (Configured.Family format code plan)) :
    ExecFloat.Binary.toReal
        (ExecFloat.ModelCodec.liftBinary (Model := Model format) (plan := plan)
          operation left right) =
      Model.toReal (operation (ExecFloat.Binary.toModel left) (ExecFloat.Binary.toModel right)) :=
  congrArg Model.toReal (decode_binary operation left right)

universe u v

/-- The left fold of `+` from zero over the indices of `Fin n` is their finite sum. -/
theorem foldl_finRange_add_eq_sum {β : Type} [AddCommMonoid β] {n : Nat} (f : Fin n → β) :
    (List.finRange n).foldl (fun s i => s + f i) 0 = (Finset.univ : Finset (Fin n)).sum f := by
  classical
  calc
    _ = ((List.finRange n).map f).sum := by
      rw [List.sum_eq_foldl, List.foldl_map]
    _ = _ := by
      simp only [Finset.sum, Finset.val_univ_fin, Multiset.map_coe, Multiset.sum_coe]

/-- A sum of positive terms over the indices of `Fin (n + 1)` is positive. -/
theorem foldl_finRange_add_pos {n : Nat} {f : Fin (n + 1) → ℝ} (h : ∀ i, 0 < f i) :
    0 < (List.finRange (n + 1)).foldl (fun s i => s + f i) 0 := by
  rw [foldl_finRange_add_eq_sum]
  exact Finset.sum_pos (fun i _ => h i) Finset.univ_nonempty

/-- The first component of a left fold whose step computes it from the accumulator's first
component alone is the fold of that component. -/
theorem foldl_fst {α : Type u} {β : Type v} {γ : Type*} (step : α × β → γ → α × β)
    (first : α → γ → α) (h : ∀ state value, (step state value).1 = first state.1 value)
    (initial : α × β) (input : List γ) :
    (input.foldl step initial).1 = input.foldl first initial.1 := by
  induction input generalizing initial with
  | nil => rfl
  | cons value rest ih => rw [List.foldl_cons, List.foldl_cons, ih, h]

/-- Split an actual optional computation without replacing its payload by a fresh input. -/
theorem option_apply_eq_dite {α : Type u} {β : Sort v}
    (program : Option α → β) (source : Option α) :
    program source = if found : source.isSome then
      program (some (source.get found)) else program none := by
  cases source <;> rfl

/-- C's `int8_t` cast keeps an integer whose mixed enclosure is below `2 ^ 7` in magnitude. -/
theorem mixedError_int8_toInt_ofInt {n : ℤ} {reference relative absolute : ℝ}
    (hn : MixedError (n : ℝ) reference relative absolute)
    (hrange : (1 + relative) * |reference| + absolute < 2 ^ 7) :
    MixedError (((Int8.ofInt n).toInt : ℤ) : ℝ) reference relative absolute := by
  have habs : |n| < 2 ^ 7 := by exact_mod_cast lt_of_le_of_lt hn.abs_le hrange
  rw [Int8.toInt_ofInt_of_le (by linarith [neg_abs_le n]) (by linarith [le_abs_self n])]
  exact hn

/-- C's `int8_t` cast keeps an integer within `error` of a reference when the reference's
magnitude plus `error` is below `2 ^ 7`. -/
theorem abs_int8_toInt_ofInt_sub_le {n : ℤ} {reference error : ℝ}
    (hn : |(n : ℝ) - reference| ≤ error) (hrange : |reference| + error < 2 ^ 7) :
    |(((Int8.ofInt n).toInt : ℤ) : ℝ) - reference| ≤ error := by
  have hle : |(n : ℝ)| ≤ |reference| + error := by
    have := abs_sub_abs_le_abs_sub (n : ℝ) reference
    linarith
  have habs : |n| < 2 ^ 7 := by exact_mod_cast lt_of_le_of_lt hle hrange
  rw [Int8.toInt_ofInt_of_le (by linarith [neg_abs_le n]) (by linarith [le_abs_self n])]
  exact hn

-- FloatLib's numerical theorems use the same rule mechanism as a user's.
attribute [roundoff_rule]
  ExecFloat.Binary.abs_toReal_add_sub_le
  ExecFloat.Binary.abs_toReal_sub_sub_le
  ExecFloat.Binary.abs_toReal_mul_sub_le
  ExecFloat.Binary.abs_toReal_div_sub_le
  ExecFloat.Binary.abs_toReal_sqrt_sub_le
  ExecFloat.Binary.abs_toReal_execFloat_sqrt_sub_le
  ExecFloat.Binary.toReal_ite_lt_eq_max ExecFloat.Binary.toReal_ite_lt_eq_min
  ExecFloat.Binary.toReal_ite_le_eq_max ExecFloat.Binary.toReal_ite_le_eq_min
  Model.abs_toReal_add_sub_le
  Model.abs_toReal_sub_sub_le
  Model.abs_toReal_mul_sub_le
  Model.abs_toReal_div_sub_le
  Model.abs_toReal_sqrt_sub_le
  Model.abs_toReal_fma_sub_le
  Model.abs_toReal_cast_sub_le
  Model.abs_roundAt_sub_le
  Model.toReal_pi_eq_roundAt
  Model.toReal_neg
  Model.toReal_abs_of_isFinite
  Model.toReal_minimum_eq_min_of_isFinite
  Model.toReal_maximum_eq_max_of_isFinite
  Model.toReal_ofRat_of_toRat?
  Model.abs_toReal_ofRat_sub_le
  Model.toReal_ofRat_eq_roundAt
  Model.abs_toReal_roundToIntegral_nearest_sub_le
  Model.abs_toReal_roundToIntegral_nearestAway_sub_le
  Model.abs_toReal_roundToIntegral_towardZero_sub_le Model.abs_toReal_roundToIntegral_up_sub_le
  Model.abs_toReal_roundToIntegral_down_sub_le Model.abs_toReal_roundToIntegral_away_sub_le
  ExecFloat.Binary.cast_toInt?_getD
  abs_int8_toInt_ofInt_sub_le
  decode_outcome
  Model.value_ofRat Model.value_add Model.value_sub Model.value_mul Model.value_div
  Model.value_fma Model.value_sqrt
  Model.cast_toRat_eq_toReal
  Rat.cast_add Rat.cast_sub Rat.cast_mul Rat.cast_div Rat.cast_neg
  Rat.cast_zero Rat.cast_one Rat.cast_natCast Rat.cast_intCast Rat.cast_ofNat
  Rat.cast_ofScientific Nat.cast_zero Nat.cast_one
  toReal_liftUnary
  toReal_liftBinary
  ExecFloat.Binary.toReal_zero
  add_error sub_error mul_error div_error
  neg_error abs_error min_error max_error
  sqrt_error_min exp_error log_error rpow_const_error rpow_error
  sin_error cos_error tanh_error sinh_error cosh_error

-- Mixed-error rules, in the order the analysis prefers them: Sterbenz subtraction, which does
-- not round, the local rounding of each configured operation, then exact real operations with
-- their sign-aware and more specific forms first, such as `exp x - 1` before a difference. Range
-- theorems derive finiteness from an enclosure of the exact result, and order facts supply
-- signs.
attribute [roundoff_rule]
  ExecFloat.Binary.mixedError_toReal_sub_of_sterbenz ExecFloat.Binary.mixedError_toReal_neg
  ExecFloat.Binary.add_rounding ExecFloat.Binary.sub_rounding ExecFloat.Binary.mul_rounding
  ExecFloat.Binary.div_rounding ExecFloat.Binary.sqrt_rounding
  ExecFloat.Binary.execFloat_sqrt_rounding ExecFloat.Binary.ofRat_intCast_rounding
  ExecFloat.Binary.ofRat_natCast_rounding mixedError_int8_toInt_ofInt
  MixedError.add_of_mul_nonneg_weighted MixedError.add
  MixedError.exp_sub_one MixedError.exp_sub_one_of_abs_le
  MixedError.sub_of_mul_nonpos_weighted MixedError.sub MixedError.mul MixedError.div
  MixedError.div_of_le_abs MixedError.neg MixedError.abs MixedError.max_of_nonneg MixedError.max
  MixedError.min_of_nonpos MixedError.min MixedError.sqrt_of_pos MixedError.sqrt
  MixedError.exp MixedError.log MixedError.rpow_const MixedError.rpow
  MixedError.log_one_add MixedError.log_one_add_of_le
  ExecFloat.Binary.isFinite_add_of_mixedError ExecFloat.Binary.isFinite_sub_of_mixedError
  ExecFloat.Binary.isFinite_mul_of_mixedError ExecFloat.Binary.isFinite_div_of_mixedError
  ExecFloat.Binary.isFinite_max ExecFloat.Binary.isFinite_abs_of_isFinite
  ExecFloat.Binary.isFinite_roundToIntegral ExecFloat.Binary.isFinite_ofRat
  ExecFloat.Binary.isFinite_sqrt
  ExecFloat.Binary.isFinite_execFloat_sqrt
  ExecFloat.Binary.toReal_add_nonneg ExecFloat.Binary.toReal_add_nonpos
  ExecFloat.Binary.toReal_ofScientific_nonneg
  ExecFloat.Binary.isFinite_ofScientific
  Model.isFinite_ofRat

end FloatLib.Floats.Formats.BinaryInterchange.Roundoff

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.Roundoff

open Lean

/-- FloatLib's containers. An entry of a list, an array or a vector is read by `GetElem.getElem`
through its own dictionary, at a natural number or an index of `Fin n`; a getter of another
dictionary is analyzed as the function it is. A loop over a list carries the invariant of
`List.fold_error` and `List.fold_mixedError`, or the relation of `List.fold_relation` when its state
is a tuple, and loops over `Fin n`, arrays and vectors are written as loops over their lists first.
A loop over `List.map`, `List.zipWith` or their array and vector forms is fused into a loop over the
containers they read. The exact sum of a list or of a function on `Fin n` is a loop of `+` from
zero, and such a loop over the indices of `Fin (n + 1)` is positive when its terms are. -/
def containers : Extension where
  reads := #[{
    head := ``GetElem.getElem, arity := 8, fromEnd := 3, types := #[``List, ``Array, ``Vector],
    dictionary := some 4,
    dictionaries := #[``List.instGetElemNatLtLength, ``Array.instGetElemNatLtSize,
      ``Vector.instGetElemNatLt],
    forwarding := #[``Fin.instGetElemFinVal] }]
  loops := #[{
    fold := ``List.foldl, arity := 5, element := 1, state := 0, step := 2, initial := 3,
    input := 4, foldStep := ``List.foldStep, allSteps := ``List.AllSteps,
    allStepsOfMap := ``List.AllSteps.of_map, allStepsOfForall := ``List.AllSteps.of_forall,
    foldError := ``List.foldError, foldErrorIdentity := ``List.foldError_identity,
    errorBound := ``List.fold_error, mixedFoldStep := ``List.mixedFoldStep,
    foldRelative := ``List.foldRelative, foldAbsolute := ``List.foldAbsolute,
    mixedBound := ``List.fold_mixedError, induction := ``List.foldl_induction,
    exactBudgets := some ``List.foldBudgets_eq_zero,
    positiveSum := some ``foldl_finRange_add_pos, projection := some ``foldl_fst,
    relation := some (``List.relationFoldStep, ``List.foldBudget, ``List.fold_relation),
    -- A map or a pointwise combination of lists, arrays or vectors is moved into the step.
    fusions := #[``List.foldl_map, ``List.zipWith_foldl_eq_zip_foldl, ``Array.toList_map,
      ``Array.toList_zipWith, ``Array.toList_zip, ``Vector.toList_map, ``Vector.toList_zipWith,
      ``Vector.toList_zip],
    -- Lists also compute index data, such as the size of a shape; such folds are not named.
    named := false }]
  conversions := #[(``Fin.foldl_eq_foldl_finRange, false), (``Array.foldl_toList, true),
    (``Vector.foldl_toList, true)]
  reductions := #[``Array.foldl, ``Vector.foldl, ``Fin.foldl]
  sums := #[{ head := ``Finset.sum, laws := #[(``foldl_finRange_add_eq_sum, true)], exact := true },
    { head := ``List.sum, laws := #[(``List.sum_eq_foldl, false)], exact := true }]

attribute [roundoff_extension] containers

end FloatLib.Floats.Formats.BinaryInterchange.Roundoff
