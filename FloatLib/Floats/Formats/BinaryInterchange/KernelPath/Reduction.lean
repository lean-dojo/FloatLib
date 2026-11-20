/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Extrema
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.FormatOf
public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Magnitude.Runtime

/-!
# The exact reductions on encodings

IEEE 754-2019 §9.4 `sum`, `dot`, `sumAbs` and `sumSquare` are specified in the reference by a
state machine (`Model.Reduction.Internal.State`): each operand is pushed into a state that
keeps the exact dyadic sum of the finite terms apart from the NaNs and infinities, and the
state is finished by one rounding.

This module runs the same state machine on a list of encodings. `pushWord` pushes a finite
word as its exact value `KernelPath.decode`, and `pushProductWord` the exact product of two
finite words; a word that is not finite is pushed by the reference rule on the decoded word
(`pushWord_eq`, `pushProductWord_eq`). `finishWord` encodes the result of a state: for a state
without a NaN or an infinity it is `KernelPath.roundDyadic` of the exact sum, or the zero whose
sign the terms decide (`finishWord_eq`).

`sum`, `sumAbs`, `dot` and `sumSquare` are the four reductions built from these, on lists of
encodings, and `sum_eq_spec`, `sumAbs_eq_spec`, `dot_eq_spec` and `sumSquare_eq_spec` prove
them equal to the encodings of the values of the reference reductions, for every source and
destination descriptor, every rounding direction and all operands.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics
open Model.Reduction.Internal (State)

variable {source left right destination : FloatFormat}

/--
Add one exact finite term to the state (`pushExact_eq`): `State.pushExact` with the sum formed
by `KernelPath.addExact`.
-/
def pushExact (state : State destination) (value : Numerics.Dyadic) : State destination :=
  { state with
    exact := addExact state.exact value
    sawFiniteTerm := true
    allTermsNegativeZero :=
      state.allTermsNegativeZero && value.significand == 0 && value.negative
    allTermsPositiveZero :=
      state.allTermsPositiveZero && value.significand == 0 && !value.negative }

/-- `pushExact` is the reference step. -/
theorem pushExact_eq (state : State destination) (value : Numerics.Dyadic) :
    pushExact state value = state.pushExact value := by
  unfold pushExact State.pushExact
  rw [addExact_eq]

/--
Push the summand that the word `a` of `source` encodes (`pushWord_eq`): the exact value of a
finite word, and the reference rule for a NaN or an infinity.
-/
def pushWord (source : FloatFormat) (state : State destination) (a : Nat) : State destination :=
  Bool.casesOn (motive := fun _ => State destination) (Nat.beq (finiteCode source a) 1)
    (state.pushValue (Model.ofNatBits a : Model source))
    (pushExact state (decode source a))

/--
Push the product of the values that the words `a` of `left` and `b` of `right` encode
(`pushProductWord_eq`): the exact product of two finite words, and the reference rule
otherwise.
-/
def pushProductWord (left right : FloatFormat) (state : State destination) (a b : Nat) :
    State destination :=
  Bool.casesOn (motive := fun _ => State destination) (bothFinite left right a b)
    (state.pushProduct (Model.ofNatBits a : Model left) (Model.ofNatBits b : Model right))
    (pushExact state (mulExact (decode left a) (decode right b)))

/--
Encoding of the value of a finished state (`finishWord_eq`): one rounding of the exact sum
when no NaN or infinity was pushed, the zero whose sign the terms decide for an exact zero, and
the reference rule otherwise.
-/
def finishWord (destination : FloatFormat) (mode : Model.IEEERoundingMode)
    (state : State destination) : Nat :=
  Bool.casesOn (motive := fun _ => Nat)
    (state.signalingNaN.isNone && state.quietNaN.isNone && !state.generatedInvalid &&
      !state.positiveInfinity && !state.negativeInfinity)
    (state.finishValue mode).toNatBits
    (Bool.casesOn (motive := fun _ => Nat) (Nat.beq state.exact.significand 0)
      (roundDyadic destination mode state.exact)
      (zeroWord destination
        (state.sawFiniteTerm &&
          (state.allTermsNegativeZero || (!state.allTermsPositiveZero && mode == .down)))))

/-- `pushWord` is the reference step on the decoded word. -/
theorem pushWord_eq (state : State destination) (x : Model source) :
    pushWord source state x.toNatBits = state.pushValue x := by
  unfold pushWord
  rw [finiteCode_eq, Model.ofNatBits_toNatBits]
  cases hfinite : Model.isFinite x
  · rfl
  · have hd := toDyadic?_eq_decode x hfinite
    have hnan := Model.isNaN_eq_false_of_toDyadic?_some hd
    have hinf := Model.isInfinite_eq_false_of_toDyadic?_some hd
    unfold State.pushValue
    simp only [hnan, hinf, Bool.false_eq_true, dite_false,
      Model.finiteDyadic_eq_of_toDyadic _ hd, pushExact_eq]

/-- Capturing a value that is not a NaN leaves the state unchanged. -/
theorem captureNaN_of_isNaN_eq_false (state : State destination) (x : Model source)
    (hnan : Model.isNaN x = false) : state.captureNaN x = state := by
  have hsignaling : Model.isSignaling x = false :=
    Model.isSignaling_eq_false_of_isNaN_eq_false x hnan
  unfold State.captureNaN
  simp only [hsignaling, hnan, Bool.false_eq_true, ite_false]

/-- `pushProductWord` is the reference step on the decoded words. -/
theorem pushProductWord_eq (state : State destination) (x : Model left) (y : Model right) :
    pushProductWord left right state x.toNatBits y.toNatBits = state.pushProduct x y := by
  unfold pushProductWord
  rw [bothFinite_eq, Model.ofNatBits_toNatBits, Model.ofNatBits_toNatBits]
  cases hx : Model.isFinite x
  · rfl
  · cases hy : Model.isFinite y
    · rfl
    · have hdx := toDyadic?_eq_decode x hx
      have hdy := toDyadic?_eq_decode y hy
      have hnanx := Model.isNaN_eq_false_of_toDyadic?_some hdx
      have hnany := Model.isNaN_eq_false_of_toDyadic?_some hdy
      have hinfx := Model.isInfinite_eq_false_of_toDyadic?_some hdx
      have hinfy := Model.isInfinite_eq_false_of_toDyadic?_some hdy
      unfold State.pushProduct
      simp only [captureNaN_of_isNaN_eq_false _ _ hnanx, captureNaN_of_isNaN_eq_false _ _ hnany,
        hnanx, hnany, hinfx, hinfy, Bool.or_self, Bool.false_and, Bool.false_eq_true,
        dite_false, ite_false, Model.finiteDyadic_eq_of_toDyadic _ hdx,
        Model.finiteDyadic_eq_of_toDyadic _ hdy, pushExact_eq, mulExact_eq]
      rfl

/-- `finishWord` is the encoding of the value of the finished state. -/
theorem finishWord_eq (mode : Model.IEEERoundingMode) (state : State destination) :
    finishWord destination mode state = (state.finishValue mode).toNatBits := by
  unfold finishWord
  cases hfast : (state.signalingNaN.isNone && state.quietNaN.isNone &&
      !state.generatedInvalid && !state.positiveInfinity && !state.negativeInfinity)
  · rfl
  · simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.not_eq_true'] at hfast
    obtain ⟨⟨⟨⟨hsignaling, hquiet⟩, hinvalid⟩, hpositive⟩, hnegative⟩ := hfast
    unfold State.finishValue State.finish
    simp only [inline, hsignaling, hquiet, hinvalid, hpositive, hnegative, Bool.and_self,
      Bool.or_self, Bool.false_eq_true, ite_false]
    by_cases hzero : state.exact.significand = 0
    · simp only [hzero, beq_self_eq_true, ite_true]
      rw [zeroWord_eq]
      rfl
    · have hbeq : (state.exact.significand == 0) = false := by simpa using hzero
      simp only [hbeq, Bool.false_eq_true, ite_false, beq_zero_eq_false hzero, roundDyadic_eq]
      rfl

/--
Encoding in `destination` of the exact sum of the values that `words` encode in `source`,
rounded once in the direction `mode` (`sum_eq_spec`).
-/
def sum (source destination : FloatFormat) (mode : Model.IEEERoundingMode) (words : List Nat) :
    Nat :=
  finishWord destination mode (words.foldl (pushWord source) {})

/-- The fold of `pushWord` over encodings is the reference fold over the values. -/
theorem foldl_pushWord (values : List (Model source)) (state : State destination) :
    (values.map Model.toNatBits).foldl (pushWord source) state =
      values.foldl State.pushValue state := by
  induction values generalizing state with
  | nil => rfl
  | cons value rest ih =>
      rw [List.map_cons, List.foldl_cons, List.foldl_cons, pushWord_eq, ih]

/--
`sum` computes the encoding of `Model.sum destination values mode`, for every source and
destination descriptor, every rounding direction and all operands.
-/
theorem sum_eq_spec (mode : Model.IEEERoundingMode) (values : Array (Model source)) :
    sum source destination mode (values.toList.map Model.toNatBits) =
      (Model.sum destination values mode).toNatBits := by
  unfold sum
  rw [finishWord_eq, foldl_pushWord, Array.foldl_toList]
  rfl

/--
Encoding in `destination` of the exact sum of the magnitudes of the values that `words` encode
in `source`, rounded once in the direction `mode` (`sumAbs_eq_spec`): `sum` of the words with
their signs cleared when none is an infinity, and the reference rule otherwise.
-/
def sumAbs (source destination : FloatFormat) (mode : Model.IEEERoundingMode)
    (words : List Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (words.all fun a => !Nat.beq (infCode source a) 1)
    (Model.sumAbs destination
      (words.map fun a => (Model.ofNatBits a : Model source)).toArray mode).toNatBits
    (sum source destination mode (words.map (KernelPath.abs source)))

/-- Decoding the encodings of a list of values gives the values back. -/
theorem map_ofNatBits_toNatBits (values : List (Model source)) :
    (values.map Model.toNatBits).map (fun a => (Model.ofNatBits a : Model source)) = values := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id values]
  exact List.map_congr_left fun x _ => Model.ofNatBits_toNatBits x

/--
`sumAbs` computes the encoding of `Model.sumAbs destination values mode`, for every source and
destination descriptor, every rounding direction and all operands.
-/
theorem sumAbs_eq_spec (mode : Model.IEEERoundingMode) (values : Array (Model source)) :
    sumAbs source destination mode (values.toList.map Model.toNatBits) =
      (Model.sumAbs destination values mode).toNatBits := by
  unfold sumAbs
  rw [map_ofNatBits_toNatBits, Array.toArray_toList, List.all_map]
  cases hall : values.toList.all
      ((fun a => !Nat.beq (infCode source a) 1) ∘ Model.toNatBits)
  · rfl
  · have hnone : Model.Reduction.Internal.decidingInfinity? values = none := by
      unfold Model.Reduction.Internal.decidingInfinity?
      split
      · rfl
      · rw [Array.find?_eq_none]
        intro x hx
        have h := List.all_eq_true.mp hall x (Array.mem_toList_iff.mpr hx)
        simpa [infCode_eq] using h
    have hmap : (values.toList.map Model.toNatBits).map (KernelPath.abs source) =
        (values.map Model.abs).toList.map Model.toNatBits := by
      rw [Array.toList_map, List.map_map, List.map_map]
      exact List.map_congr_left fun x _ => abs_eq_spec x
    unfold Model.sumAbs
    rw [hnone, hmap, sum_eq_spec]

/--
Encoding in `destination` of the exact dot product of the values that `as` encode in `left`
and `bs` in `right`, rounded once in the direction `mode`, or the length mismatch
(`dot_eq_spec`).
-/
def dot (left right destination : FloatFormat) (mode : Model.IEEERoundingMode)
    (as bs : List Nat) : Except Numerics.ReductionError Nat :=
  Bool.casesOn (motive := fun _ => Except Numerics.ReductionError Nat)
    (Nat.beq as.length bs.length)
    (.error (.lengthMismatch as.length bs.length))
    (.ok (finishWord destination mode
      ((as.zip bs).foldl (fun state pair => pushProductWord left right state pair.1 pair.2)
        {})))

/-- The loop of the reference dot product is a fold over the zipped operands. -/
theorem dotStateLoop_eq_foldl (xs : Array (Model left)) (ys : Array (Model right))
    (state : State destination) (index remaining : Nat)
    (hleft : index + remaining ≤ xs.size) (hright : index + remaining ≤ ys.size) :
    Model.Reduction.Internal.dotStateLoop xs ys state index remaining hleft hright =
      (((xs.toList.drop index).zip (ys.toList.drop index)).take remaining).foldl
        (fun state pair => state.pushProduct pair.1 pair.2) state := by
  induction remaining generalizing state index with
  | zero =>
      unfold Model.Reduction.Internal.dotStateLoop
      rfl
  | succ count ih =>
      have hx : index < xs.toList.length := by rw [Array.length_toList]; omega
      have hy : index < ys.toList.length := by rw [Array.length_toList]; omega
      unfold Model.Reduction.Internal.dotStateLoop
      rw [ih, List.drop_eq_getElem_cons hx, List.drop_eq_getElem_cons hy, List.zip_cons_cons,
        List.take_succ_cons, List.foldl_cons]
      rfl

/-- The fold of `pushProductWord` over encodings is the reference fold over the values. -/
theorem foldl_pushProductWord (pairs : List (Model left × Model right))
    (state : State destination) :
    (pairs.map fun pair => (pair.1.toNatBits, pair.2.toNatBits)).foldl
        (fun state pair => pushProductWord left right state pair.1 pair.2) state =
      pairs.foldl (fun state pair => state.pushProduct pair.1 pair.2) state := by
  induction pairs generalizing state with
  | nil => rfl
  | cons pair rest ih =>
      rw [List.map_cons, List.foldl_cons, List.foldl_cons, pushProductWord_eq, ih]

/-- The state of the reference dot product, as a fold over the encodings of the operands. -/
theorem dotState_eq_foldl (xs : Array (Model left)) (ys : Array (Model right))
    (hsize : xs.size = ys.size) :
    (Model.Reduction.Internal.dotState xs ys hsize : State destination) =
      ((xs.toList.map Model.toNatBits).zip (ys.toList.map Model.toNatBits)).foldl
        (fun state pair => pushProductWord left right state pair.1 pair.2) {} := by
  have hzip : (xs.toList.map Model.toNatBits).zip (ys.toList.map Model.toNatBits) =
      (xs.toList.zip ys.toList).map fun pair => (pair.1.toNatBits, pair.2.toNatBits) := by
    rw [List.zip_map]
    rfl
  unfold Model.Reduction.Internal.dotState
  rw [dotStateLoop_eq_foldl, hzip, foldl_pushProductWord, List.drop_zero, List.drop_zero,
    List.take_of_length_le]
  rw [List.length_zip, Array.length_toList, Array.length_toList]
  omega

/--
`dot` computes `Model.dot destination xs ys mode` with its value encoded, for all descriptors,
every rounding direction and all operands.
-/
theorem dot_eq_spec (mode : Model.IEEERoundingMode) (xs : Array (Model left))
    (ys : Array (Model right)) :
    dot left right destination mode (xs.toList.map Model.toNatBits)
        (ys.toList.map Model.toNatBits) =
      (Model.dot destination xs ys mode).map Model.toNatBits := by
  unfold dot
  simp only [List.length_map, Array.length_toList]
  change _ = (Model.Internal.Value.dot destination xs ys mode).map Model.toNatBits
  unfold Model.Internal.Value.dot
  by_cases hsize : xs.size = ys.size
  · have hbeq : Nat.beq xs.size ys.size = true := Nat.beq_eq_true_eq _ _ ▸ hsize
    rw [dite_eq_left hsize, hbeq, finishWord_eq, dotState_eq_foldl]
    rfl
  · have hbeq : Nat.beq xs.size ys.size = false := by
      rw [← Bool.not_eq_true, Nat.beq_eq]
      exact hsize
    rw [dite_eq_right hsize, hbeq]
    rfl

/--
Encoding in `destination` of the exact sum of the squares of the values that `words` encode in
`source`, rounded once in the direction `mode` (`sumSquare_eq_spec`): the exact squares of
finite words when none is an infinity, and the reference rule otherwise.
-/
def sumSquare (source destination : FloatFormat) (mode : Model.IEEERoundingMode)
    (words : List Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (words.all fun a => !Nat.beq (infCode source a) 1)
    (Model.sumSquare destination
      (words.map fun a => (Model.ofNatBits a : Model source)).toArray mode).toNatBits
    (finishWord destination mode
      ((words.zip words).foldl
        (fun state pair => pushProductWord source source state pair.1 pair.2) {}))

/--
`sumSquare` computes the encoding of `Model.sumSquare destination values mode`, for every
source and destination descriptor, every rounding direction and all operands.
-/
theorem sumSquare_eq_spec (mode : Model.IEEERoundingMode) (values : Array (Model source)) :
    sumSquare source destination mode (values.toList.map Model.toNatBits) =
      (Model.sumSquare destination values mode).toNatBits := by
  unfold sumSquare
  rw [map_ofNatBits_toNatBits, Array.toArray_toList, List.all_map]
  cases hall : values.toList.all
      ((fun a => !Nat.beq (infCode source a) 1) ∘ Model.toNatBits)
  · rfl
  · have hnone : Model.Reduction.Internal.decidingInfinity? values = none := by
      unfold Model.Reduction.Internal.decidingInfinity?
      split
      · rfl
      · rw [Array.find?_eq_none]
        intro x hx
        have h := List.all_eq_true.mp hall x (Array.mem_toList_iff.mpr hx)
        simpa [infCode_eq] using h
    unfold Model.sumSquare
    rw [hnone, finishWord_eq, ← dotState_eq_foldl values values rfl]

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
