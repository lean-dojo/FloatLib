/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Cast.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Status.Runtime
public import FloatLib.Numerics.Exact.Dyadic.Arithmetic.Runtime
public import FloatLib.Numerics.Reduction

/-!
# Correctly rounded binary reductions

`sum` decodes every operand exactly, adds in the shared dyadic domain, and rounds once into the
requested destination format. `dot` does the same with exact products. Source and destination
formats may differ, so the operations cover ordinary uniform reductions and explicit
mixed-precision accumulation with one API.

Exceptional inputs are deterministic:

* the first signaling NaN in traversal order is selected and quieted, ahead of every quiet NaN;
* otherwise the first quiet NaN is selected;
* opposite-signed infinities and `0 * ∞` raise invalid, even when a quiet NaN supplies the result;
* one infinity sign is preserved; and
* finite inputs are accumulated exactly and rounded once.

NaN payloads are preserved when source and destination formats agree. Cross-format NaNs follow
the ordinary `Model.cast` policy. An infinite result follows the destination's native overflow
rule, matching casts: IEEE encodings preserve infinity, finite-with-NaN encodings return NaN,
and fully finite encodings return the same-sign maximum. A destination without infinity raises
overflow and inexact. Empty reductions return positive zero. A sum of zeros with the same sign
keeps that sign; cancellation and mixed-sign zeros are negative only under rounding toward
negative infinity. FNUZ destinations use positive zero.

There is deliberately no initial-addend argument. One product plus an addend is already IEEE FMA,
and larger finite algebraic expressions can use `ExecFloat.roundOnce`. A repeated FMA chain is a
different operation because it rounds every prefix; it agrees with `dot` only when those
intermediate roundings are exact and the exceptional and signed-zero rules also agree.

The binary reducer and a posit quire share the useful idea “exact products, then one final round,”
but not the same machine model. This reducer uses an unbounded software dyadic accumulator and IEEE
NaN, infinity, signed-zero, and status semantics. A posit quire is a fixed `16n`-bit accumulator
with NaR and an explicit coefficient-range condition.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

namespace Reduction.Internal

/--
Accumulator state used by the transparent reduction kernels.

The state records exact finite contributions separately from exceptional inputs, so NaN priority
and infinity cancellation can be resolved after traversal.
-/
structure State (destination : FloatFormat) where
  /-- Exact finite contribution accumulated so far. -/
  exact : Numerics.Dyadic := .zero
  /-- Whether the reduction has consumed at least one finite term. -/
  sawFiniteTerm : Bool := false
  /-- Whether every consumed finite term was a negative zero. -/
  allTermsNegativeZero : Bool := true
  /-- Whether every consumed finite term was a positive zero. -/
  allTermsPositiveZero : Bool := true
  /-- Whether a positive infinity has occurred. -/
  positiveInfinity : Bool := false
  /-- Whether a negative infinity has occurred. -/
  negativeInfinity : Bool := false
  /-- First signaling NaN in traversal order, quieted into the destination format. -/
  signalingNaN : Option (Model destination) := none
  /-- First quiet NaN in traversal order, converted into the destination format. -/
  quietNaN : Option (Model destination) := none
  /-- Whether a product generated an invalid operation such as `0 * ∞`. -/
  generatedInvalid : Bool := false

/-- Record the first NaN of each class while preserving signaling-NaN priority. -/
def State.captureNaN {destination source : FloatFormat}
    (state : State destination) (value : Model source) :
    State destination :=
  if isSNaN value then
    match state.signalingNaN with
    | some _ => state
    | none =>
        { state with
          signalingNaN := some (cast source destination (Model.quietNaN value)) }
  else if isNaN value then
    match state.quietNaN with
    | some _ => state
    | none =>
        { state with
          quietNaN := some (cast source destination (Model.quietNaN value)) }
  else
    state

/-- Add one exact finite term to the shared dyadic accumulator. -/
@[inline] def State.pushExact {destination : FloatFormat}
    (state : State destination) (value : Numerics.Dyadic) :
    State destination :=
  { state with
    exact := Numerics.Dyadic.add state.exact value
    sawFiniteTerm := true
    allTermsNegativeZero :=
      state.allTermsNegativeZero &&
        value.significand == 0 && value.negative
    allTermsPositiveZero :=
      state.allTermsPositiveZero &&
        value.significand == 0 && !value.negative }

/-- Record an infinity sign without discarding a possible opposing infinity. -/
@[inline] def State.pushInfinity {destination : FloatFormat}
    (state : State destination) (negative : Bool) :
    State destination :=
  if negative then
    { state with negativeInfinity := true }
  else
    { state with positiveInfinity := true }

/-- Consume one summand according to the reduction's exceptional-value policy. -/
def State.pushValue {destination source : FloatFormat}
    (state : State destination) (value : Model source) :
    State destination :=
  if hnan : isNaN value = true then
    state.captureNaN value
  else if hinf : isInf value = true then
    state.pushInfinity (signBit value)
  else
    let hfinite :=
      isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false value
        (Bool.eq_false_of_not_eq_true hnan)
        (Bool.eq_false_of_not_eq_true hinf)
    state.pushExact (finiteDyadic value hfinite)

/-- Consume one exact product while detecting NaNs, infinities, and `0 * ∞`. -/
def State.pushProduct
    {destination leftFormat rightFormat : FloatFormat}
    (state : State destination)
    (left : Model leftFormat) (right : Model rightFormat) :
    State destination :=
  let state := state.captureNaN left
  let state := state.captureNaN right
  if hnan : (isNaN left || isNaN right) = true then
    state
  else if ((isInf left && isZero right) || (isInf right && isZero left)) = true then
    { state with generatedInvalid := true }
  else if hinf : (isInf left || isInf right) = true then
    state.pushInfinity (Bool.xor (signBit left) (signBit right))
  else
    have hnanFields := Bool.or_eq_false_iff.mp (Bool.eq_false_of_not_eq_true hnan)
    have hinfFields := Bool.or_eq_false_iff.mp (Bool.eq_false_of_not_eq_true hinf)
    let hleftFinite :=
      isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false left
        hnanFields.1 hinfFields.1
    let hrightFinite :=
      isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false right
        hnanFields.2 hinfFields.2
    state.pushExact <|
      Numerics.Dyadic.mul
        (finiteDyadic left hleftFinite)
        (finiteDyadic right hrightFinite)

/--
Accumulate a contiguous dot-product slice without allocating a zipped collection.

`index` is the first pair to consume and `remaining` is the number of pairs. The size proofs are
erased after compilation; they make every array access bounds-safe without a default value.
-/
def dotStateLoop
    {destination leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (state : State destination) (index remaining : Nat)
    (hleft : index + remaining ≤ left.size)
    (hright : index + remaining ≤ right.size) :
    State destination :=
  match remaining with
  | 0 => state
  | count + 1 =>
      have hleftIndex : index < left.size := by omega
      have hrightIndex : index < right.size := by omega
      dotStateLoop left right
        (state.pushProduct left[index] right[index])
        (index + 1) count (by omega) (by omega)
termination_by remaining

/-- Accumulate every pair in two equal-sized arrays in left-to-right traversal order. -/
@[inline] def dotState
    {destination leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (hsize : left.size = right.size) :
    State destination :=
  dotStateLoop left right {} 0 left.size (by simp) (by simp [hsize])

/-- Resolve exceptional values or round the exact finite result once. -/
def State.finish {destination : FloatFormat}
    (state : State destination) (mode : IEEERoundingMode) :
    IEEEOutcome destination :=
  let invalid := state.generatedInvalid ||
    (state.positiveInfinity && state.negativeInfinity)
  match state.signalingNaN with
  | some value =>
      outcomeWithInvalid value true
  | none =>
      match state.quietNaN with
      | some value =>
          outcomeWithInvalid value (invalid || !isNaN value)
      | none =>
          if invalid then
            outcomeWithInvalid (invalidResult destination) true
          else if state.negativeInfinity || state.positiveInfinity then
            let value := nativeOverflow destination state.negativeInfinity
            { value
              status := if isInf value then .clear
                else { overflow := true, inexact := true } }
          else if state.exact.significand == 0 then
            let negative :=
              state.sawFiniteTerm &&
                (state.allTermsNegativeZero ||
                  (!state.allTermsPositiveZero &&
                    mode == .towardNegativeInfinity))
            outcomeWithInvalid (zero destination negative) false
          else
            let value := roundDyadicWithRounding destination mode state.exact
            { value
              status := dyadicRoundingStatus destination mode state.exact value }

end Reduction.Internal

/--
Correctly rounded sum of an array.

Every finite source value is decoded exactly, the exact dyadic sum is formed without intermediate
rounding, and the result is rounded once into `destination`.
-/
def sumWithStatus (destination : FloatFormat) {source : FloatFormat}
    (values : Array (Model source)) (mode : IEEERoundingMode) :
    IEEEOutcome destination :=
  let state := values.foldl Reduction.Internal.State.pushValue
    ({} : Reduction.Internal.State destination)
  state.finish mode

/-- Value-only projection of `sumWithStatus`. -/
@[inline] def sum (destination : FloatFormat) {source : FloatFormat}
    (values : Array (Model source)) (mode : IEEERoundingMode) :
    Model destination :=
  (sumWithStatus destination values mode).value

/-- List entry point for correctly rounded summation. -/
@[inline] def sumListWithStatus (destination : FloatFormat) {source : FloatFormat}
    (values : List (Model source)) (mode : IEEERoundingMode) :
    IEEEOutcome destination :=
  sumWithStatus destination values.toArray mode

/-- Value-only list entry point for correctly rounded summation. -/
@[inline] def sumList (destination : FloatFormat) {source : FloatFormat}
    (values : List (Model source)) (mode : IEEERoundingMode) :
    Model destination :=
  (sumListWithStatus destination values mode).value

/--
Correctly rounded dot product of two arrays.

Each finite pair is multiplied in the exact dyadic domain, all products are added exactly, and
the result
is rounded once into `destination`. Unequal lengths are rejected before any arithmetic occurs.
-/
def dotWithStatus (destination : FloatFormat)
    {leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (mode : IEEERoundingMode) :
    Except Numerics.ReductionError (IEEEOutcome destination) :=
  if hsize : left.size = right.size then
    let state : Reduction.Internal.State destination :=
      Reduction.Internal.dotState left right hsize
    .ok (state.finish mode)
  else
    .error (.lengthMismatch left.size right.size)

/-- Value-only projection of `dotWithStatus`. -/
def dot (destination : FloatFormat)
    {leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (mode : IEEERoundingMode) :
    Except Numerics.ReductionError (Model destination) :=
  (dotWithStatus destination left right mode).map IEEEOutcome.value

/-- List entry point for a correctly rounded dot product. -/
@[inline] def dotListWithStatus (destination : FloatFormat)
    {leftFormat rightFormat : FloatFormat}
    (left : List (Model leftFormat)) (right : List (Model rightFormat))
    (mode : IEEERoundingMode) :
    Except Numerics.ReductionError (IEEEOutcome destination) :=
  dotWithStatus destination left.toArray right.toArray mode

/-- Value-only list entry point for a correctly rounded dot product. -/
@[inline] def dotList (destination : FloatFormat)
    {leftFormat rightFormat : FloatFormat}
    (left : List (Model leftFormat)) (right : List (Model rightFormat))
    (mode : IEEERoundingMode) :
    Except Numerics.ReductionError (Model destination) :=
  dot destination left.toArray right.toArray mode

end Model
end FloatLib.Floats.Formats.BinaryInterchange
