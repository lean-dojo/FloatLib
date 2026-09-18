/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Model.ERealSemantics
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Proof
public import FloatLib.Numerics.Exact.Dyadic.Arithmetic.Proof

/-!
# Correctness of sums and dot products

Finite operands accumulate exactly as dyadics and undergo one final rounding. `Semantics`
defines the rational list and array-slice specifications; `Internal` proves that the accumulator
preserves them. The final theorems connect these invariants to `sumWithStatus` and `dotWithStatus`.

The zero-result theorems preserve the signed-zero rules. The real-valued rounding theorems require
a finite output, since overflow to infinity has no real denotation. Permutation invariance applies
to the finite accumulator; NaN selection can depend on traversal order.

Nonempty sums of same-sign zeros preserve that sign in every rounding mode. Generated invalid
indicators survive later dot-product terms, including NaNs. Infinite singleton sums agree with
casts, including the destination's conversion status.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace Reduction

namespace Semantics

/-- Exact rational contribution to the accumulator; exceptional encodings contribute zero. -/
def finiteContribution {format : FloatFormat} (value : Model format) : Rat :=
  match toDyadic? value with
  | some exact => exact.toRat
  | none => 0

/-- Exact sum of the finite contributions. -/
def finiteSum {format : FloatFormat} (values : List (Model format)) : Rat :=
  (values.map finiteContribution).sum

/-- Exact sum of pairwise products, with an explicit error for unequal lengths. -/
def finiteDot {leftFormat rightFormat : FloatFormat}
    (left : List (Model leftFormat)) (right : List (Model rightFormat)) :
    Except Numerics.ReductionError Rat :=
  if left.length != right.length then
    .error (.lengthMismatch left.length right.length)
  else
    .ok ((List.zipWith
      (fun x y => finiteContribution x * finiteContribution y)
      left right).sum)

/-- Exact dot product of `remaining` pairs from `index`, with bounds for both arrays. -/
def finiteDotSlice
    {leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (index remaining : Nat)
    (hleft : index + remaining ≤ left.size)
    (hright : index + remaining ≤ right.size) : Rat :=
  match remaining with
  | 0 => 0
  | count + 1 =>
      have hleftIndex : index < left.size := by omega
      have hrightIndex : index < right.size := by omega
      finiteContribution left[index] * finiteContribution right[index] +
        finiteDotSlice left right (index + 1) count (by omega) (by omega)
termination_by remaining

/--
The bounded Array specification is the corresponding list dot product over the same slice.

This bridge lets the kernel traverse indexed arrays while public theorems use ordinary
list operations. The bounds ensure that `drop` and `take` select exactly `remaining` pairs.
-/
theorem finiteDotSlice_eq_zipWith_sum
    {leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (index remaining : Nat)
    (hleft : index + remaining ≤ left.size)
    (hright : index + remaining ≤ right.size) :
    finiteDotSlice left right index remaining hleft hright =
      (List.zipWith
        (fun x y => finiteContribution x * finiteContribution y)
        (left.toList.drop index |>.take remaining)
        (right.toList.drop index |>.take remaining)).sum := by
  induction remaining generalizing index with
  | zero =>
      simp [finiteDotSlice]
  | succ count ih =>
      have hleftIndex : index < left.size := by omega
      have hrightIndex : index < right.size := by omega
      have hleftDrop :
          left.toList.drop index =
            left[index] :: left.toList.drop (index + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using hleftIndex), Array.getElem_toList]
      have hrightDrop :
          right.toList.drop index =
            right[index] :: right.toList.drop (index + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using hrightIndex), Array.getElem_toList]
      rw [finiteDotSlice]
      rw [hleftDrop, hrightDrop]
      simp only [List.take_succ_cons, List.zipWith_cons_cons, List.sum_cons]
      rw [ih]

/-- On equal-sized arrays, the list and bounded-Array dot specifications agree exactly. -/
theorem finiteDot_toList_eq_slice
    {leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (hsize : left.size = right.size) :
    finiteDot left.toList right.toList =
      .ok (finiteDotSlice left right 0 left.size
        (by simp) (by simp [hsize])) := by
  simp [finiteDot, finiteDotSlice_eq_zipWith_sum, List.take_of_length_le, hsize]

/-- The finite-sum specification is independent of traversal order. -/
theorem finiteSum_eq_of_perm
    {format : FloatFormat} {left right : List (Model format)}
    (hperm : left.Perm right) :
    finiteSum left = finiteSum right :=
  (hperm.map finiteContribution).sum_eq

/-- A one-pair finite dot product is exactly the product of the two contributions. -/
@[simp] theorem finiteDot_singleton
    {leftFormat rightFormat : FloatFormat}
    (left : Model leftFormat) (right : Model rightFormat) :
    finiteDot [left] [right] =
      .ok (finiteContribution left *
        finiteContribution right) := by
  simp [finiteDot]

end Semantics

namespace Internal

/--
Finite-only accumulator states contain no exceptional value or generated invalid operation.

The finite sum proofs use this predicate to discharge every exceptional branch in `State.finish`
at once.
-/
def State.HasOnlyFiniteTerms {destination : FloatFormat}
    (state : State destination) : Prop :=
  state.positiveInfinity = false ∧
    state.negativeInfinity = false ∧
    state.signalingNaN = none ∧
    state.quietNaN = none ∧
    state.generatedInvalid = false

/-- The empty reduction state contains only finite terms. -/
@[simp] theorem State.hasOnlyFiniteTerms_empty (destination : FloatFormat) :
    HasOnlyFiniteTerms ({} : State destination) := by
  simp [HasOnlyFiniteTerms]

/-- Adding an exact dyadic preserves the finite-only state invariant. -/
theorem State.HasOnlyFiniteTerms.pushExact
    {destination : FloatFormat} {state : State destination}
    (hstate : state.HasOnlyFiniteTerms) (value : Numerics.Dyadic) :
    (state.pushExact value).HasOnlyFiniteTerms := by
  simpa [State.HasOnlyFiniteTerms, State.pushExact] using hstate

/-- A finite encoded value takes exactly the `pushExact` branch. -/
theorem State.pushValue_eq_pushExact
    {destination source : FloatFormat}
    (state : State destination) (value : Model source)
    (hfinite : isFinite value = true) :
    state.pushValue value = state.pushExact (finiteDyadic value hfinite) := by
  obtain ⟨exact, hdecode⟩ := exists_toDyadic?_of_isFinite hfinite
  have hnan := isNaN_eq_false_of_toDyadic?_some hdecode
  have hinf := isInf_eq_false_of_toDyadic?_some hdecode
  simp [State.pushValue, hnan, hinf]

/-- Consuming a finite encoded value preserves the finite-only state invariant. -/
theorem State.HasOnlyFiniteTerms.pushValue
    {destination source : FloatFormat} {state : State destination}
    (hstate : state.HasOnlyFiniteTerms) (value : Model source)
    (hfinite : isFinite value = true) :
    (state.pushValue value).HasOnlyFiniteTerms := by
  rw [State.pushValue_eq_pushExact state value hfinite]
  exact hstate.pushExact _

/-- A finite pair takes exactly the exact-product branch. -/
theorem State.pushProduct_eq_pushExact
    {destination leftFormat rightFormat : FloatFormat}
    (state : State destination)
    (left : Model leftFormat) (right : Model rightFormat)
    (hleft : isFinite left = true) (hright : isFinite right = true) :
    state.pushProduct left right =
      state.pushExact
        (Numerics.Dyadic.mul
          (finiteDyadic left hleft)
          (finiteDyadic right hright)) := by
  obtain ⟨leftExact, hleftExact⟩ := exists_toDyadic?_of_isFinite hleft
  obtain ⟨rightExact, hrightExact⟩ := exists_toDyadic?_of_isFinite hright
  have hleftNaN := isNaN_eq_false_of_toDyadic?_some hleftExact
  have hrightNaN := isNaN_eq_false_of_toDyadic?_some hrightExact
  have hleftSNaN := isSNaN_eq_false_of_toDyadic?_some hleftExact
  have hrightSNaN := isSNaN_eq_false_of_toDyadic?_some hrightExact
  have hleftInf := isInf_eq_false_of_toDyadic?_some hleftExact
  have hrightInf := isInf_eq_false_of_toDyadic?_some hrightExact
  simp [State.pushProduct, State.captureNaN, hleftNaN, hrightNaN,
    hleftSNaN, hrightSNaN, hleftInf, hrightInf]

/-- Consuming two finite factors preserves the finite-only state invariant. -/
theorem State.HasOnlyFiniteTerms.pushProduct
    {destination leftFormat rightFormat : FloatFormat}
    {state : State destination} (hstate : state.HasOnlyFiniteTerms)
    (left : Model leftFormat) (right : Model rightFormat)
    (hleft : isFinite left = true) (hright : isFinite right = true) :
    (state.pushProduct left right).HasOnlyFiniteTerms := by
  rw [State.pushProduct_eq_pushExact state left right hleft hright]
  exact hstate.pushExact _

/-- Folding a list of finite values preserves the finite-only state invariant. -/
theorem foldl_pushValue_hasOnlyFiniteTerms
    {destination source : FloatFormat}
    (state : State destination) (values : List (Model source))
    (hstate : state.HasOnlyFiniteTerms)
    (hfinite : ∀ value ∈ values, isFinite value = true) :
    (values.foldl State.pushValue state).HasOnlyFiniteTerms := by
  exact List.foldlRecOn values State.pushValue hstate fun _ hstate value hmem =>
    hstate.pushValue value (hfinite value hmem)

/-- Recording a NaN leaves the exact finite accumulator unchanged. -/
@[simp] theorem State.captureNaN_exact
    {destination source : FloatFormat}
    (state : State destination) (value : Model source) :
    (state.captureNaN value).exact = state.exact := by
  unfold State.captureNaN
  split
  · split <;> rfl
  · split
    · split <;> rfl
    · rfl

/-- Recording a NaN preserves an invalid operation generated by an earlier product. -/
@[simp] theorem State.captureNaN_generatedInvalid
    {destination source : FloatFormat}
    (state : State destination) (value : Model source) :
    (state.captureNaN value).generatedInvalid = state.generatedInvalid := by
  unfold State.captureNaN
  split
  · split <;> rfl
  · split
    · split <;> rfl
    · rfl

/-- Recording an infinity leaves the exact finite accumulator unchanged. -/
@[simp] theorem State.pushInfinity_exact
    {destination : FloatFormat} (state : State destination) (negative : Bool) :
    (state.pushInfinity negative).exact = state.exact := by
  cases negative <;> rfl

/-- Every subsequent product preserves a previously generated invalid operation. -/
theorem State.pushProduct_generatedInvalid
    {destination leftFormat rightFormat : FloatFormat}
    (state : State destination)
    (left : Model leftFormat) (right : Model rightFormat)
    (hinvalid : state.generatedInvalid = true) :
    (state.pushProduct left right).generatedInvalid = true := by
  unfold State.pushProduct
  split
  · simpa using hinvalid
  · split
    · rfl
    · split
      · unfold State.pushInfinity
        split <;> simpa using hinvalid
      · simpa [State.pushExact] using hinvalid

/-- Generated invalid operations and opposing infinities raise invalid even in the NaN branches. -/
theorem State.finish_invalid
    {destination : FloatFormat} (state : State destination) (mode : IEEERoundingMode)
    (hinvalid : (state.generatedInvalid ||
      (state.positiveInfinity && state.negativeInfinity)) = true) :
    (state.finish mode).status.invalid = true := by
  simp only [State.finish, hinvalid]
  split
  · rfl
  · split
    · simp [outcomeWithInvalid]
    · rfl

/-- An arbitrary dot-product suffix cannot clear an invalid operation generated by its prefix. -/
theorem dotStateLoop_generatedInvalid
    {destination leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (state : State destination) (index remaining : Nat)
    (hleft : index + remaining ≤ left.size)
    (hright : index + remaining ≤ right.size)
    (hinvalid : state.generatedInvalid = true) :
    (dotStateLoop left right state index remaining hleft hright).generatedInvalid = true := by
  induction remaining generalizing state index with
  | zero => simpa [dotStateLoop] using hinvalid
  | succ count ih =>
      rw [dotStateLoop]
      exact ih _ _ _ _ (state.pushProduct_generatedInvalid _ _ hinvalid)

/-- Consuming one value changes the exact field by precisely its finite rational contribution. -/
theorem State.pushValue_exact_toRat
    {destination source : FloatFormat}
    (state : State destination) (value : Model source) :
    (state.pushValue value).exact.toRat =
      state.exact.toRat + Semantics.finiteContribution value := by
  by_cases hnan : isNaN value = true
  · have hdecode := toDyadic?_eq_none_of_isNaN hnan
    simp [State.pushValue, Semantics.finiteContribution, hnan, hdecode]
  · by_cases hinf : isInf value = true
    · cases hdecode : toDyadic? value with
      | none =>
          simp [State.pushValue, Semantics.finiteContribution, hnan, hinf, hdecode]
      | some exact =>
          have hinfFalse := isInf_eq_false_of_toDyadic?_some hdecode
          simp [hinf] at hinfFalse
    · have hnanFalse := Bool.eq_false_of_not_eq_true hnan
      have hinfFalse := Bool.eq_false_of_not_eq_true hinf
      have hfinite :=
        isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false
          value hnanFalse hinfFalse
      obtain ⟨exact, hdecode⟩ := exists_toDyadic?_of_isFinite hfinite
      simp [State.pushValue, Semantics.finiteContribution, hnan, hinf, hdecode,
        State.pushExact, Numerics.Dyadic.add_toRat]

/-- Folding values accumulates exactly the rational sum of their finite contributions. -/
theorem foldl_pushValue_exact_toRat
    {destination source : FloatFormat}
    (state : State destination) (values : List (Model source)) :
    (values.foldl State.pushValue state).exact.toRat =
      state.exact.toRat + Semantics.finiteSum values := by
  induction values generalizing state with
  | nil =>
      simp [Semantics.finiteSum]
  | cons value values ih =>
      rw [List.foldl_cons, ih, State.pushValue_exact_toRat]
      simp only [Semantics.finiteSum, List.map_cons, List.sum_cons]
      ring

/-- The Array summation kernel accumulates the exact rational finite sum. -/
theorem array_foldl_pushValue_exact_toRat
    {destination source : FloatFormat}
    (values : Array (Model source)) :
    (values.foldl State.pushValue
      ({} : State destination)).exact.toRat =
        Semantics.finiteSum values.toList := by
  rw [← Array.foldl_toList]
  simpa using
    foldl_pushValue_exact_toRat
      ({} : State destination) values.toList

/-- Consuming one product adds exactly the product of its two finite rational contributions. -/
theorem State.pushProduct_exact_toRat
    {destination leftFormat rightFormat : FloatFormat}
    (state : State destination)
    (left : Model leftFormat) (right : Model rightFormat)
    (hleft : isFinite left = true) (hright : isFinite right = true) :
    (state.pushProduct left right).exact.toRat =
      state.exact.toRat +
        Semantics.finiteContribution left * Semantics.finiteContribution right := by
  rw [State.pushProduct_eq_pushExact state left right hleft hright]
  obtain ⟨leftExact, hleftExact⟩ := exists_toDyadic?_of_isFinite hleft
  obtain ⟨rightExact, hrightExact⟩ := exists_toDyadic?_of_isFinite hright
  simp [State.pushExact, Semantics.finiteContribution, hleftExact, hrightExact,
    Numerics.Dyadic.add_toRat, Numerics.Dyadic.mul_toRat]

/--
The indexed dot loop accumulates exactly the rational product sum of its Array slice.
-/
theorem dotStateLoop_exact_toRat
    {destination leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (state : State destination) (index remaining : Nat)
    (hleft : index + remaining ≤ left.size)
    (hright : index + remaining ≤ right.size)
    (hleftFinite :
      ∀ position (hposition : position < left.size),
        isFinite left[position] = true)
    (hrightFinite :
      ∀ position (hposition : position < right.size),
        isFinite right[position] = true) :
    (dotStateLoop left right state index remaining hleft hright).exact.toRat =
      state.exact.toRat +
        Semantics.finiteDotSlice left right index remaining hleft hright := by
  induction remaining generalizing state index with
  | zero =>
      simp [dotStateLoop, Semantics.finiteDotSlice]
  | succ count ih =>
      have hleftIndex : index < left.size := by omega
      have hrightIndex : index < right.size := by omega
      rw [dotStateLoop, Semantics.finiteDotSlice]
      rw [ih]
      rw [State.pushProduct_exact_toRat
        _ _ _ (hleftFinite index hleftIndex) (hrightFinite index hrightIndex)]
      ring

/-- Finite input pairs keep the indexed dot loop free of exceptional state. -/
theorem dotStateLoop_hasOnlyFiniteTerms
    {destination leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (state : State destination) (index remaining : Nat)
    (hleft : index + remaining ≤ left.size)
    (hright : index + remaining ≤ right.size)
    (hstate : state.HasOnlyFiniteTerms)
    (hleftFinite :
      ∀ position (hposition : position < left.size),
        isFinite left[position] = true)
    (hrightFinite :
      ∀ position (hposition : position < right.size),
        isFinite right[position] = true) :
    (dotStateLoop left right state index remaining hleft hright).HasOnlyFiniteTerms := by
  induction remaining generalizing state index with
  | zero =>
      simpa [dotStateLoop] using hstate
  | succ count ih =>
      have hleftIndex : index < left.size := by omega
      have hrightIndex : index < right.size := by omega
      rw [dotStateLoop]
      apply ih
      exact hstate.pushProduct left[index] right[index]
        (hleftFinite index hleftIndex) (hrightFinite index hrightIndex)

/-- The complete finite dot kernel accumulates exactly its rational Array specification. -/
theorem dotState_exact_toRat
    {destination leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (hsize : left.size = right.size)
    (hleftFinite :
      ∀ position (hposition : position < left.size),
        isFinite left[position] = true)
    (hrightFinite :
      ∀ position (hposition : position < right.size),
        isFinite right[position] = true) :
    (dotState left right hsize : State destination).exact.toRat =
      Semantics.finiteDotSlice left right 0 left.size
        (by simp) (by simp [hsize]) := by
  unfold dotState
  rw [dotStateLoop_exact_toRat
    left right ({} : State destination) 0 left.size
      (by simp) (by simp [hsize]) hleftFinite hrightFinite]
  simp

/-- The complete finite dot kernel cannot produce exceptional accumulator state. -/
theorem dotState_hasOnlyFiniteTerms
    {destination leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (hsize : left.size = right.size)
    (hleftFinite :
      ∀ position (hposition : position < left.size),
        isFinite left[position] = true)
    (hrightFinite :
      ∀ position (hposition : position < right.size),
        isFinite right[position] = true) :
    (dotState left right hsize : State destination).HasOnlyFiniteTerms := by
  unfold dotState
  exact dotStateLoop_hasOnlyFiniteTerms
    left right ({} : State destination) 0 left.size
      (by simp) (by simp [hsize]) (by simp)
      hleftFinite hrightFinite

end Internal

/--
The executable sum accumulator has the same exact rational value after any permutation.

This theorem concerns the finite accumulator field, not the complete exceptional result. NaN
selection deliberately remains traversal-order dependent.
-/
theorem sumAccumulator_toRat_eq_of_perm
    {destination source : FloatFormat}
    {left right : List (Model source)} (hperm : left.Perm right) :
    (left.foldl Internal.State.pushValue
      ({} : Internal.State destination)).exact.toRat =
    (right.foldl Internal.State.pushValue
      ({} : Internal.State destination)).exact.toRat := by
  rw [Internal.foldl_pushValue_exact_toRat,
    Internal.foldl_pushValue_exact_toRat]
  simp only [Numerics.Dyadic.zero_toRat, zero_add]
  exact Semantics.finiteSum_eq_of_perm hperm

/--
A mathematically nonzero finite sum gives a nonzero exact accumulator.

This keeps callers in the rational specification and hides the dyadic accumulator's internal
representation.
-/
theorem sumAccumulator_significand_ne_zero_of_finiteSum_ne_zero
    (destination : FloatFormat) {source : FloatFormat}
    (values : Array (Model source))
    (hnonzero : Semantics.finiteSum values.toList ≠ 0) :
    (values.foldl Internal.State.pushValue
      ({} : Internal.State destination)).exact.significand ≠ 0 := by
  intro hzero
  apply hnonzero
  have hrat :
      (values.foldl Internal.State.pushValue
        ({} : Internal.State destination)).exact.toRat = 0 :=
    (Numerics.Dyadic.toRat_eq_zero_iff _).2 hzero
  rw [Internal.array_foldl_pushValue_exact_toRat] at hrat
  exact hrat

/--
A mathematically nonzero finite dot product gives a nonzero exact accumulator.

The premise uses the public list specification; equal array lengths rule out the error branch.
-/
theorem dotAccumulator_significand_ne_zero_of_finiteDot_ne_zero
    (destination : FloatFormat) {leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (hsize : left.size = right.size)
    (hleftFinite :
      ∀ position (hposition : position < left.size),
        isFinite left[position] = true)
    (hrightFinite :
      ∀ position (hposition : position < right.size),
        isFinite right[position] = true)
    (hnonzero : Semantics.finiteDot left.toList right.toList ≠ .ok 0) :
    (Internal.dotState left right hsize :
      Internal.State destination).exact.significand ≠ 0 := by
  intro hzero
  apply hnonzero
  rw [Semantics.finiteDot_toList_eq_slice left right hsize]
  congr 1
  rw [← Internal.dotState_exact_toRat
    left right hsize hleftFinite hrightFinite]
  exact (Numerics.Dyadic.toRat_eq_zero_iff _).2 hzero

/--
A nonzero sum of finite inputs performs one final dyadic rounding and reports exactly that
rounding's status.
-/
theorem sumWithStatus_eq_round_of_finite_nonzero
    (destination : FloatFormat) {source : FloatFormat}
    (values : Array (Model source)) (mode : IEEERoundingMode)
    (hfinite : ∀ value ∈ values.toList, isFinite value = true)
    (hnonzero : Semantics.finiteSum values.toList ≠ 0) :
    sumWithStatus destination values mode =
      {
        value := roundDyadicWithRounding destination mode
          (values.foldl Internal.State.pushValue
            ({} : Internal.State destination)).exact
        status := dyadicRoundingStatus destination mode
          (values.foldl Internal.State.pushValue
            ({} : Internal.State destination)).exact
          (roundDyadicWithRounding destination mode
            (values.foldl Internal.State.pushValue
              ({} : Internal.State destination)).exact)
      } := by
  have haccumulator :=
    sumAccumulator_significand_ne_zero_of_finiteSum_ne_zero
      destination values hnonzero
  have hstate :
      (values.foldl Internal.State.pushValue
        ({} : Internal.State destination)).HasOnlyFiniteTerms := by
    rw [← Array.foldl_toList]
    exact Internal.foldl_pushValue_hasOnlyFiniteTerms
      ({} : Internal.State destination) values.toList (by simp) hfinite
  simp [sumWithStatus, Internal.State.finish,
    Internal.State.HasOnlyFiniteTerms] at hstate ⊢
  simp [hstate, haccumulator]

/--
For finite inputs with a nonzero exact sum, the executable nearest-even reduction is the exact
mathematical sum followed by one destination-format rounding.

The result-finiteness premise excludes overflow to infinity, whose encoding has no real
denotation. Exact accumulation itself is established independently of this premise.
-/
theorem sumWithStatus_value_toReal_eq_roundAt_of_finite_nonzero
    (destination : FloatFormat) {source : FloatFormat}
    (values : Array (Model source))
    (hfmt : destination.isIEEE = true)
    (hfinite : ∀ value ∈ values.toList, isFinite value = true)
    (hnonzero : Semantics.finiteSum values.toList ≠ 0)
    (hresult :
      isFinite (sumWithStatus destination values .nearestEven).value = true) :
    toReal (sumWithStatus destination values .nearestEven).value =
      roundAt destination (Semantics.finiteSum values.toList : ℝ) := by
  rw [sumWithStatus_eq_round_of_finite_nonzero
    destination values .nearestEven hfinite hnonzero] at hresult ⊢
  simp only [roundDyadicWithRounding] at hresult ⊢
  rw [toReal_roundDyadic_eq_roundAt destination hfmt _ hresult]
  congr 1
  rw [← Numerics.Dyadic.cast_toRat,
    Internal.array_foldl_pushValue_exact_toRat]

/--
A finite sum whose exact accumulator is zero returns the specified signed zero and raises no
status indicator.
-/
theorem sumWithStatus_eq_zero_of_finite
    (destination : FloatFormat) {source : FloatFormat}
    (values : Array (Model source)) (mode : IEEERoundingMode)
    (hfinite : ∀ value ∈ values.toList, isFinite value = true)
    (hzero :
      (values.foldl Internal.State.pushValue
        ({} : Internal.State destination)).exact.significand = 0) :
    sumWithStatus destination values mode =
      {
        value := zero destination <|
          (values.foldl Internal.State.pushValue
            ({} : Internal.State destination)).sawFiniteTerm &&
          ((values.foldl Internal.State.pushValue
              ({} : Internal.State destination)).allTermsNegativeZero ||
            (!(values.foldl Internal.State.pushValue
                ({} : Internal.State destination)).allTermsPositiveZero &&
              mode == .towardNegativeInfinity))
        status := .clear
      } := by
  have hstate :
      (values.foldl Internal.State.pushValue
        ({} : Internal.State destination)).HasOnlyFiniteTerms := by
    rw [← Array.foldl_toList]
    exact Internal.foldl_pushValue_hasOnlyFiniteTerms
      ({} : Internal.State destination) values.toList (by simp) hfinite
  simp [sumWithStatus, Internal.State.finish,
    Internal.State.HasOnlyFiniteTerms] at hstate ⊢
  simp [hstate, hzero, outcomeWithInvalid]

/--
A nonempty sum of zeros with one common sign preserves that sign in every rounding mode.

The destination's zero constructor accounts for formats without a negative zero. The hypotheses
refer only to the input values, independently of the accumulator's signed-zero flags.
-/
theorem sumWithStatus_eq_zero_of_same_sign_zeros
    (destination : FloatFormat) {source : FloatFormat}
    (values : Array (Model source)) (mode : IEEERoundingMode) (negative : Bool)
    (hnonempty : values ≠ #[])
    (hzero : ∀ value ∈ values.toList, isZero value = true)
    (hsign : ∀ value ∈ values.toList, signBit value = negative) :
    sumWithStatus destination values mode =
      { value := zero destination negative, status := .clear } := by
  let state : Internal.State destination :=
    { sawFiniteTerm := true
      allTermsNegativeZero := negative
      allTermsPositiveZero := !negative }
  have hstep (value : Model source) (hmem : value ∈ values.toList)
      (accumulator : Internal.State destination) :
      accumulator.pushValue value =
        accumulator.pushExact { negative, significand := 0, exponent := 0 } := by
    have hfinite := isFinite_eq_true_of_isZero_eq_true value (hzero value hmem)
    rw [Internal.State.pushValue_eq_pushExact _ _ hfinite,
      finiteDyadic_eq_of_toDyadic hfinite
        (toDyadic?_eq_zero_of_isZero_eq_true value (hzero value hmem)), hsign value hmem]
  unfold sumWithStatus
  rw [← Array.foldl_toList]
  cases hlist : values.toList with
  | nil => exact (hnonempty (Array.toList_eq_nil_iff.mp hlist)).elim
  | cons value rest =>
      have hfirst : ({} : Internal.State destination).pushValue value = state := by
        rw [hstep value (by simp [hlist])]
        cases negative <;> simp [state, Internal.State.pushExact, Numerics.Dyadic.zero]
      have hrest : rest.foldl Internal.State.pushValue state = state := by
        refine List.foldlRecOn (motive := fun accumulator => accumulator = state)
          rest Internal.State.pushValue rfl ?_
        intro accumulator haccumulator term hmem
        rw [haccumulator, hstep term (by simp [hlist, hmem])]
        cases negative <;> simp [state, Internal.State.pushExact, Numerics.Dyadic.zero]
      rw [List.foldl_cons, hfirst, hrest]
      cases negative <;> simp [state, Internal.State.finish, outcomeWithInvalid]

/-- A singleton infinity has exactly the value and exception indicators of a destination cast. -/
theorem sumWithStatus_singleton_eq_castWithStatus_of_isInf
    (destination : FloatFormat) {source : FloatFormat}
    (value : Model source) (mode : IEEERoundingMode)
    (hinf : isInf value = true) :
    sumWithStatus destination #[value] mode = castWithStatus source destination value mode := by
  have hnan := isNaN_eq_false_of_isInf_eq_true value hinf
  cases mode <;> cases hsign : signBit value <;>
    simp [sumWithStatus, Internal.State.pushValue, Internal.State.pushInfinity,
      Internal.State.finish, castWithStatus, castWithRounding, cast, hnan, hinf, hsign] <;>
    split <;> rfl

/--
A nonzero dot product of finite inputs performs one final dyadic rounding and reports exactly that
rounding's status.
-/
theorem dotWithStatus_eq_round_of_finite_nonzero
    (destination : FloatFormat) {leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (mode : IEEERoundingMode) (hsize : left.size = right.size)
    (hleftFinite :
      ∀ position (hposition : position < left.size),
        isFinite left[position] = true)
    (hrightFinite :
      ∀ position (hposition : position < right.size),
        isFinite right[position] = true)
    (hnonzero : Semantics.finiteDot left.toList right.toList ≠ .ok 0) :
    dotWithStatus destination left right mode =
      .ok {
        value := roundDyadicWithRounding destination mode
          (Internal.dotState left right hsize :
            Internal.State destination).exact
        status := dyadicRoundingStatus destination mode
          (Internal.dotState left right hsize :
            Internal.State destination).exact
          (roundDyadicWithRounding destination mode
            (Internal.dotState left right hsize :
              Internal.State destination).exact)
      } := by
  have haccumulator :=
    dotAccumulator_significand_ne_zero_of_finiteDot_ne_zero
      destination left right hsize hleftFinite hrightFinite hnonzero
  have hstate :
      (Internal.dotState left right hsize :
        Internal.State destination).HasOnlyFiniteTerms :=
    Internal.dotState_hasOnlyFiniteTerms
      left right hsize hleftFinite hrightFinite
  simp [dotWithStatus, hsize, Internal.State.finish,
    Internal.State.HasOnlyFiniteTerms] at hstate ⊢
  simp [hstate, haccumulator]

/--
For finite equal-sized inputs with a nonzero exact dot product, the executable nearest-even
reduction is the mathematical list dot product followed by one destination-format rounding.

`outcome` names the successful result of the `Except`-valued API. Its finiteness premise excludes
overflow to infinity, whose encoding has no real denotation.
-/
theorem dotWithStatus_value_toReal_eq_roundAt_of_finite_nonzero
    (destination : FloatFormat) {leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (exact : Rat) (outcome : IEEEOutcome destination)
    (hfmt : destination.isIEEE = true)
    (hsize : left.size = right.size)
    (hleftFinite :
      ∀ position (hposition : position < left.size),
        isFinite left[position] = true)
    (hrightFinite :
      ∀ position (hposition : position < right.size),
        isFinite right[position] = true)
    (hspec : Semantics.finiteDot left.toList right.toList = .ok exact)
    (hnonzero : exact ≠ 0)
    (houtcome :
      dotWithStatus destination left right .nearestEven = .ok outcome)
    (hresult : isFinite outcome.value = true) :
    toReal outcome.value = roundAt destination (exact : ℝ) := by
  have hspecNonzero :
      Semantics.finiteDot left.toList right.toList ≠ .ok 0 := by
    intro hzero
    rw [hspec] at hzero
    exact hnonzero (Except.ok.inj hzero)
  rw [dotWithStatus_eq_round_of_finite_nonzero
    destination left right .nearestEven hsize
      hleftFinite hrightFinite hspecNonzero] at houtcome
  simp only [Except.ok.injEq] at houtcome
  subst outcome
  simp only [roundDyadicWithRounding] at hresult ⊢
  rw [toReal_roundDyadic_eq_roundAt destination hfmt _ hresult]
  congr 1
  rw [← Numerics.Dyadic.cast_toRat,
    Internal.dotState_exact_toRat
      left right hsize hleftFinite hrightFinite]
  have hbridge := Semantics.finiteDot_toList_eq_slice left right hsize
  rw [hspec] at hbridge
  exact_mod_cast (Except.ok.inj hbridge).symm

/--
A finite dot product whose exact accumulator is zero returns the specified signed zero and raises
no status indicator.
-/
theorem dotWithStatus_eq_zero_of_finite
    (destination : FloatFormat) {leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (mode : IEEERoundingMode) (hsize : left.size = right.size)
    (hleftFinite :
      ∀ position (hposition : position < left.size),
        isFinite left[position] = true)
    (hrightFinite :
      ∀ position (hposition : position < right.size),
        isFinite right[position] = true)
    (hzero :
      (Internal.dotState left right hsize :
        Internal.State destination).exact.significand = 0) :
    dotWithStatus destination left right mode =
      .ok {
        value := zero destination <|
          (Internal.dotState left right hsize :
            Internal.State destination).sawFiniteTerm &&
          ((Internal.dotState left right hsize :
              Internal.State destination).allTermsNegativeZero ||
            (!(Internal.dotState left right hsize :
                Internal.State destination).allTermsPositiveZero &&
              mode == .towardNegativeInfinity))
        status := .clear
      } := by
  have hstate :
      (Internal.dotState left right hsize :
        Internal.State destination).HasOnlyFiniteTerms :=
    Internal.dotState_hasOnlyFiniteTerms
      left right hsize hleftFinite hrightFinite
  simp [dotWithStatus, hsize, Internal.State.finish,
    Internal.State.HasOnlyFiniteTerms] at hstate ⊢
  simp [hstate, hzero, outcomeWithInvalid]

/-- The empty correctly rounded sum is positive zero with no exception indicator. -/
@[simp] theorem sumWithStatus_empty
    (destination source : FloatFormat) (mode : IEEERoundingMode) :
    sumWithStatus destination (#[] : Array (Model source)) mode =
      { value := zero destination false, status := .clear } := by
  simp [sumWithStatus, Internal.State.finish, outcomeWithInvalid]

/-- A mismatched dot product reports both observed lengths and performs no reduction. -/
theorem dotWithStatus_lengthMismatch
    (destination : FloatFormat) {leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (mode : IEEERoundingMode) (hsize : left.size ≠ right.size) :
    dotWithStatus destination left right mode =
      .error (.lengthMismatch left.size right.size) := by
  simp [dotWithStatus, hsize]

/-- The empty correctly rounded dot product is positive zero with no exception indicator. -/
@[simp] theorem dotWithStatus_empty
    (destination leftFormat rightFormat : FloatFormat) (mode : IEEERoundingMode) :
    dotWithStatus destination
        (#[] : Array (Model leftFormat)) (#[] : Array (Model rightFormat)) mode =
      .ok { value := zero destination false, status := .clear } := by
  simp [dotWithStatus, Internal.dotState, Internal.dotStateLoop,
    Internal.State.finish, outcomeWithInvalid]

end Reduction
end Model
end FloatLib.Floats.Formats.BinaryInterchange
