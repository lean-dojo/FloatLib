/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Tactic.Roundoff.Extension
public import Batteries.Data.Fin.Fold
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.MixedError.Attribute
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Codec.Observation
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.CorrectlyRounded
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Expm1x
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.MixedError.Rounding
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.MixedPrecision
public import FloatLib.Numerics.Capabilities.Elementary
public import FloatLib.Numerics.Enclosure.Interval.HyperbolicProof
public import FloatLib.Numerics.ErrorBound.Containers
public import FloatLib.Numerics.ErrorBound.RelationLoop
public import FloatLib.Numerics.MixedError.Elementary
public import FloatLib.Numerics.MixedError.Integer

/-!
# FloatLib's rules for `roundoff`

The registrations below give `roundoff` FloatLib's own numerical theorems: the rounding of each
configured and model operation, the propagation of absolute and mixed errors through exact real
operations, rational and integer conversions, rounding to an integral value and C's integer casts,
and the finiteness and order facts that range conditions and signs need. With the codec laws, the
analysis reads a configured value through the model operation that computes it, and a split of an
optional value keeps its payload as computed. An `int8_t` cast's range is a condition on the bound
of the integer it casts, so it reads as a bound on the real reference.

FloatLib's containers are registered here too. An entry of a list, an array or a vector is read by
`GetElem.getElem`, and an entry of a function on `Fin n` or of a matrix by application. An entry
of a stored input is exact data. A loop over a list carries the invariant of `List.fold_error` and
`List.fold_mixedError`, or the relation of `List.fold_relation` when its state is a tuple. Loops
over `Fin n`, arrays and vectors are first written as loops over their lists. A loop over a map or
a pointwise combination of such containers is a loop over the containers it reads, with the
producer in its step. So are the sums of a list and of a function on `Fin n`.
-/

public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Roundoff

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

/-- Nearest-even rounding misses a real by at most half an ulp there:
`Model.abs_roundAt_sub_le` as a mixed bound with no relative part. This is the bound that mixed
analysis states for one rounding to nearest, of a literal for example; the unit roundoff and
the underflow allowance of `Model.mixedError_roundAt` are at least as large. -/
theorem mixedError_roundAt_halfUlp (format : FloatFormat) (t : ℝ) :
    MixedError (Model.roundAt format t) t 0 (Model.halfUlpAt format t) :=
  MixedError.of_abs_sub_le (Model.abs_roundAt_sub_le format t)

-- FloatLib's numerical theorems use the same rule mechanism as a user's.
attribute [roundoff_rule]
  ExecFloat.Binary.abs_toReal_add_sub_le
  ExecFloat.Binary.abs_toReal_sub_sub_le
  ExecFloat.Binary.abs_toReal_mul_sub_le
  ExecFloat.Binary.abs_toReal_div_sub_le
  ExecFloat.Binary.abs_toReal_fma_sub_le
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
  Model.abs_roundAt_sub_le_mode
  ExecFloat.Binary.toReal_add_nearest ExecFloat.Binary.toReal_sub_nearest
  ExecFloat.Binary.toReal_mul_nearest
  ExecFloat.Binary.abs_toReal_add_sub_le_mode ExecFloat.Binary.abs_toReal_sub_sub_le_mode
  ExecFloat.Binary.abs_toReal_mul_sub_le_mode ExecFloat.Binary.abs_toReal_fma_sub_le_mode
  Model.abs_toReal_add_sub_le_mode Model.abs_toReal_sub_sub_le_mode
  Model.abs_toReal_mul_sub_le_mode Model.abs_toReal_fma_sub_le_mode
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
  ExecFloat.Binary.toReal_ofModel
  ExecFloat.Binary.toReal_mul_cast_exact
  add_error sub_error mul_error div_error
  neg_error abs_error min_error max_error
  sqrt_error_min exp_error log_error rpow_const_error rpow_error
  sin_error cos_error tanh_error sinh_error cosh_error

-- Mixed-error rules, in the order the analysis prefers them: Sterbenz subtraction, which does
-- not round, the local rounding of each configured operation, then exact real operations with
-- their sign-aware and more specific forms first, such as `exp x - 1` before a difference. A
-- rounding of a real to nearest states half an ulp at that real, or the unit roundoff and the
-- underflow allowance of a format without variables, which are numerals. A rounding of a real
-- in another attribute, and a sum, a difference, a product or a fused multiply-add with a
-- rounding attribute, states the unit roundoff of its attribute. The Sterbenz rule is stated
-- like a generated theorem, so the difference is finite with no range condition. Range theorems
-- derive finiteness from an enclosure of the exact result, and order facts supply signs.
attribute [roundoff_rule]
  ExecFloat.Binary.sub_of_sterbenz ExecFloat.Binary.mixedError_toReal_neg
  ExecFloat.Binary.add_rounding ExecFloat.Binary.sub_rounding ExecFloat.Binary.mul_rounding
  ExecFloat.Binary.fma_rounding
  ExecFloat.Binary.add_rounding_mode ExecFloat.Binary.sub_rounding_mode
  ExecFloat.Binary.mul_rounding_mode ExecFloat.Binary.fma_rounding_mode
  ExecFloat.Binary.div_rounding ExecFloat.Binary.sqrt_rounding
  ExecFloat.Binary.execFloat_sqrt_rounding ExecFloat.Binary.ofRat_intCast_rounding
  ExecFloat.Binary.ofRat_natCast_rounding mixedError_int8_toInt_ofInt
  MixedError.add_of_mul_nonneg_weighted MixedError.add
  MixedError.exp_sub_one_sub MixedError.exp_sub_one MixedError.exp_sub_one_of_abs_le
  MixedError.sub_of_mul_nonpos_weighted MixedError.sub MixedError.mul MixedError.div
  MixedError.div_of_le_abs MixedError.neg MixedError.abs MixedError.max_of_nonneg MixedError.max
  MixedError.min_of_nonpos MixedError.min MixedError.sqrt_of_pos MixedError.sqrt
  MixedError.exp MixedError.log MixedError.rpow_const MixedError.rpow
  MixedError.log_one_add MixedError.log_one_add_of_le
  mixedError_roundAt_halfUlp Model.mixedError_roundAt Model.mixedError_roundAt_mode
  ExecFloat.Binary.isFinite_add_of_mixedError ExecFloat.Binary.isFinite_sub_of_mixedError
  ExecFloat.Binary.isFinite_mul_of_mixedError ExecFloat.Binary.isFinite_div_of_mixedError
  ExecFloat.Binary.isFinite_add_of_mixedError_mode ExecFloat.Binary.isFinite_sub_of_mixedError_mode
  ExecFloat.Binary.isFinite_mul_of_mixedError_mode ExecFloat.Binary.isFinite_fma_of_mixedError_mode
  ExecFloat.Binary.isFinite_max ExecFloat.Binary.isFinite_abs_of_isFinite
  ExecFloat.Binary.isFinite_roundToIntegral ExecFloat.Binary.isFinite_ofRat
  ExecFloat.Binary.isFinite_sqrt
  ExecFloat.Binary.isFinite_execFloat_sqrt
  exp_sub_one_sub_nonneg
  ExecFloat.Binary.toReal_add_nonneg ExecFloat.Binary.toReal_add_nonpos
  ExecFloat.Binary.toReal_ofScientific_nonneg
  ExecFloat.Binary.isFinite_ofScientific
  Model.isFinite_ofRat

end FloatLib.Floats.Formats.BinaryInterchange.Roundoff

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.Roundoff

open Lean

/-- FloatLib's containers. An entry of a list, an array or a vector is read by `GetElem.getElem`
through its own dictionary, at a natural number or an index of `Fin n`. A getter of another
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
