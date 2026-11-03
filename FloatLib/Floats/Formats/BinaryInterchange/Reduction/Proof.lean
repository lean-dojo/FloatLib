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
defines the rational list and array-slice specifications, and `Internal` proves that the
accumulator preserves them. The final theorems connect these invariants to `sum` and `dot`.

For finite inputs the zero-result theorems give the sign of a zero total by the accumulator's
signed-zero flags. For sums the sign is also stated from the inputs alone: the empty sum is a
positive zero, a nonempty sum of zeros of one sign keeps that sign in every rounding mode, and any
other exact zero total, from cancellation or mixed-sign zeros, is negative only when rounding
toward negative infinity. The real-valued rounding theorems require a finite output, since
overflow to infinity has no real denotation. Permutation invariance applies to the finite
accumulator, while NaN selection can depend on traversal order.

Generated invalid indicators survive later dot-product terms, including NaNs. Infinite singleton
sums agree with casts, including the destination's conversion status.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace Reduction

namespace Semantics

/-- Exact rational contribution to the accumulator. Exceptional encodings contribute zero. -/
def finiteContribution {format : FloatFormat} (value : Model format) : Rat :=
  match toDyadic? value with
  | some exact => exact.toRat
  | none => 0

/-- Exact sum of the finite contributions. -/
def finiteSum {format : FloatFormat} (values : List (Model format)) : Rat :=
  (values.map finiteContribution).sum

/-- Exact sum of pairwise products, with an error for unequal lengths. -/
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

/-- On equal-sized arrays, the list and bounded-Array dot specifications agree. -/
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

/-- A one-pair finite dot product is the product of the two contributions. -/
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

/-- A finite encoded value takes the `pushExact` branch. -/
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

/-- A finite pair takes the exact-product branch. -/
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

/-- Folding an array of finite values from the empty state keeps only finite terms. -/
private theorem array_foldl_pushValue_hasOnlyFiniteTerms
    {destination source : FloatFormat} (values : Array (Model source))
    (hfinite : ∀ value ∈ values.toList, isFinite value = true) :
    (values.foldl State.pushValue ({} : State destination)).HasOnlyFiniteTerms := by
  rw [← Array.foldl_toList]
  exact foldl_pushValue_hasOnlyFiniteTerms ({} : State destination) values.toList (by simp)
    hfinite

/--
Folding finite values records whether a finite term was seen and whether every term was a zero of
negative or of positive sign.
-/
private theorem foldl_pushValue_flags
    {destination source : FloatFormat} (state : State destination)
    (values : List (Model source)) (hfinite : ∀ value ∈ values, isFinite value = true) :
    (values.foldl State.pushValue state).sawFiniteTerm =
        (state.sawFiniteTerm || !values.isEmpty) ∧
      (values.foldl State.pushValue state).allTermsNegativeZero =
        (state.allTermsNegativeZero && values.all fun value => isZero value && signBit value) ∧
      (values.foldl State.pushValue state).allTermsPositiveZero =
        (state.allTermsPositiveZero && values.all fun value => isZero value && !signBit value) := by
  induction values generalizing state with
  | nil => simp
  | cons value rest ih =>
      have hvalue := hfinite value (by simp)
      obtain ⟨exact, hexact⟩ := exists_toDyadic?_of_isFinite hvalue
      obtain ⟨hsaw, hnegative, hpositive⟩ :=
        ih (state.pushExact (finiteDyadic value hvalue))
          (fun other hother => hfinite other (by simp [hother]))
      rw [List.foldl_cons, State.pushValue_eq_pushExact state value hvalue, hsaw, hnegative,
        hpositive]
      simp only [State.pushExact, finiteDyadic_eq_of_toDyadic hvalue hexact,
        isZero_eq_beq_zero_of_toDyadic?_some hexact,
        ← sign_eq_signBit_of_toDyadic?_some hexact, List.all_cons, List.isEmpty_cons]
      cases state.sawFiniteTerm <;> cases state.allTermsNegativeZero <;>
        cases state.allTermsPositiveZero <;> simp [Bool.and_assoc]

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

/-- A finite-only state with a nonzero exact accumulator rounds it once. -/
private theorem State.finish_of_hasOnlyFiniteTerms_of_ne_zero
    {destination : FloatFormat} (state : State destination) (mode : IEEERoundingMode)
    (hstate : state.HasOnlyFiniteTerms) (hnonzero : state.exact.significand ≠ 0) :
    state.finish mode =
      { value := Internal.Directed.roundDyadic destination mode state.exact
        status := dyadicRoundingStatus destination mode state.exact
          (Internal.Directed.roundDyadic destination mode state.exact)
        ternary := dyadicTernary state.exact
          (Internal.Directed.roundDyadic destination mode state.exact) } := by
  simp [State.finish, dyadicRoundingOutcome, State.HasOnlyFiniteTerms] at hstate ⊢
  simp [hstate, hnonzero]

/--
A finite-only state with a zero exact accumulator returns the zero whose sign its signed-zero flags
select, with clear status.
-/
private theorem State.finish_of_hasOnlyFiniteTerms_of_eq_zero
    {destination : FloatFormat} (state : State destination) (mode : IEEERoundingMode)
    (hstate : state.HasOnlyFiniteTerms) (hzero : state.exact.significand = 0) :
    state.finish mode =
      { value := zero destination <|
          state.sawFiniteTerm &&
            (state.allTermsNegativeZero || (!state.allTermsPositiveZero && mode == .down))
        status := .clear
        ternary := .eq } := by
  simp [State.finish, State.HasOnlyFiniteTerms] at hstate ⊢
  simp [hstate, hzero, outcomeWithInvalid]

/--
Nearest-even finishing of a finite-only state with a finite result is one real rounding of the
exact accumulator, a zero accumulator included.
-/
private theorem State.toReal_finish_nearest_eq_roundAt
    {destination : FloatFormat} (state : State destination)
    (hfmt : destination.isIEEE = true) (hstate : state.HasOnlyFiniteTerms)
    (hresult : isFinite (state.finish .nearest).value = true) :
    toReal (state.finish .nearest).value = roundAt destination (state.exact.toRat : ℝ) := by
  by_cases hzero : state.exact.significand = 0
  · rw [State.finish_of_hasOnlyFiniteTerms_of_eq_zero state .nearest hstate hzero]
    simp [(Numerics.Dyadic.toRat_eq_zero_iff _).2 hzero]
  · rw [State.finish_of_hasOnlyFiniteTerms_of_ne_zero state .nearest hstate hzero] at hresult ⊢
    simp only [Internal.Directed.roundDyadic] at hresult ⊢
    rw [toReal_roundDyadic_eq_roundAt destination hfmt _ hresult, Numerics.Dyadic.cast_toRat]

/-- A state invariant preserved by each indexed product push holds after the whole dot loop. -/
private theorem dotStateLoop_preserves
    {destination leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (P : State destination → Prop)
    (hstep : ∀ state index (hleft : index < left.size) (hright : index < right.size),
      P state → P (state.pushProduct left[index] right[index]))
    (state : State destination) (index remaining : Nat)
    (hleft : index + remaining ≤ left.size)
    (hright : index + remaining ≤ right.size)
    (hstate : P state) :
    P (dotStateLoop left right state index remaining hleft hright) := by
  induction remaining generalizing state index with
  | zero => simpa [dotStateLoop] using hstate
  | succ count ih =>
      rw [dotStateLoop]
      exact ih _ _ _ _ (hstep state index (by omega) (by omega) hstate)

/-- An arbitrary dot-product suffix cannot clear an invalid operation generated by its prefix. -/
theorem dotStateLoop_generatedInvalid
    {destination leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (state : State destination) (index remaining : Nat)
    (hleft : index + remaining ≤ left.size)
    (hright : index + remaining ≤ right.size)
    (hinvalid : state.generatedInvalid = true) :
    (dotStateLoop left right state index remaining hleft hright).generatedInvalid = true :=
  dotStateLoop_preserves left right (fun state => state.generatedInvalid = true)
    (fun state _ _ _ h => state.pushProduct_generatedInvalid _ _ h)
    state index remaining hleft hright hinvalid

/-- Consuming one value changes the exact field by its finite rational contribution. -/
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

/--
Consuming one product adds exactly the product of its two finite rational contributions. An
exceptional factor contributes zero and leaves the exact field unchanged.
-/
theorem State.pushProduct_exact_toRat
    {destination leftFormat rightFormat : FloatFormat}
    (state : State destination)
    (left : Model leftFormat) (right : Model rightFormat) :
    (state.pushProduct left right).exact.toRat =
      state.exact.toRat +
        Semantics.finiteContribution left * Semantics.finiteContribution right := by
  by_cases hfinite : isFinite left = true ∧ isFinite right = true
  · obtain ⟨hleft, hright⟩ := hfinite
    rw [State.pushProduct_eq_pushExact state left right hleft hright]
    obtain ⟨leftExact, hleftExact⟩ := exists_toDyadic?_of_isFinite hleft
    obtain ⟨rightExact, hrightExact⟩ := exists_toDyadic?_of_isFinite hright
    simp [State.pushExact, Semantics.finiteContribution, hleftExact, hrightExact,
      Numerics.Dyadic.add_toRat, Numerics.Dyadic.mul_toRat]
  have hnone {format : FloatFormat} {value : Model format} (h : isFinite value = false) :
      Semantics.finiteContribution value = 0 := by
    have hsome := toDyadic?_isSome_eq_isFinite value
    rw [h] at hsome
    cases hdecode : toDyadic? value with
    | none => simp [Semantics.finiteContribution, hdecode]
    | some exact => simp [hdecode] at hsome
  have hcontribution :
      Semantics.finiteContribution left * Semantics.finiteContribution right = 0 := by
    rcases not_and_or.mp hfinite with h | h
    · simp [hnone (Bool.eq_false_of_not_eq_true h)]
    · simp [hnone (Bool.eq_false_of_not_eq_true h)]
  have hexact : (state.pushProduct left right).exact = state.exact := by
    unfold State.pushProduct
    split
    · simp
    · split
      · simp
      · split
        · simp
        · rename_i hnan _ hinf
          have hnanFields := Bool.or_eq_false_iff.mp (Bool.eq_false_of_not_eq_true hnan)
          have hinfFields := Bool.or_eq_false_iff.mp (Bool.eq_false_of_not_eq_true hinf)
          exact absurd ⟨isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false left
            hnanFields.1 hinfFields.1, isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false right
            hnanFields.2 hinfFields.2⟩ hfinite
  rw [hexact, hcontribution, add_zero]

/--
The indexed dot loop accumulates exactly the rational product sum of its Array slice, in which
exceptional entries contribute zero.
-/
theorem dotStateLoop_exact_toRat
    {destination leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (state : State destination) (index remaining : Nat)
    (hleft : index + remaining ≤ left.size)
    (hright : index + remaining ≤ right.size) :
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
      rw [ih, State.pushProduct_exact_toRat]
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
    (dotStateLoop left right state index remaining hleft hright).HasOnlyFiniteTerms :=
  dotStateLoop_preserves left right State.HasOnlyFiniteTerms
    (fun _ index hleftIndex hrightIndex h => h.pushProduct left[index] right[index]
      (hleftFinite index hleftIndex) (hrightFinite index hrightIndex))
    state index remaining hleft hright hstate

/--
The complete dot kernel accumulates exactly its rational Array specification, in which exceptional
entries contribute zero.
-/
theorem dotState_exact_toRat
    {destination leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (hsize : left.size = right.size) :
    (dotState left right hsize : State destination).exact.toRat =
      Semantics.finiteDotSlice left right 0 left.size
        (by simp) (by simp [hsize]) := by
  unfold dotState
  rw [dotStateLoop_exact_toRat
    left right ({} : State destination) 0 left.size
      (by simp) (by simp [hsize])]
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

/-- When the rational dot product of the inputs is `exact`, the dot accumulator holds `exact`. -/
private theorem dotState_exact_toRat_of_finiteDot_eq_ok
    {destination leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (hsize : left.size = right.size)
    {exact : Rat} (hspec : Semantics.finiteDot left.toList right.toList = .ok exact) :
    (dotState left right hsize : State destination).exact.toRat = exact := by
  rw [dotState_exact_toRat left right hsize]
  have hbridge := Semantics.finiteDot_toList_eq_slice left right hsize
  rw [hspec] at hbridge
  exact (Except.ok.inj hbridge).symm

end Internal

/--
The executable sum accumulator has the same exact rational value after any permutation.

This theorem concerns the finite accumulator field, not the complete exceptional result. NaN
selection depends on traversal order.
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

Callers can stay in the rational specification without seeing the dyadic accumulator's internal
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

The premise uses the public list specification, and equal array lengths rule out the error branch.
Exceptional entries contribute zero to both sides.
-/
theorem dotAccumulator_significand_ne_zero_of_finiteDot_ne_zero
    (destination : FloatFormat) {leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (hsize : left.size = right.size)
    (hnonzero : Semantics.finiteDot left.toList right.toList ≠ .ok 0) :
    (Internal.dotState left right hsize :
      Internal.State destination).exact.significand ≠ 0 := by
  intro hzero
  apply hnonzero
  rw [Semantics.finiteDot_toList_eq_slice left right hsize]
  congr 1
  rw [← Internal.dotState_exact_toRat left right hsize]
  exact (Numerics.Dyadic.toRat_eq_zero_iff _).2 hzero

/--
A nonzero sum of finite inputs performs one final dyadic rounding and reports that rounding's
status and ternary value.
-/
theorem sum_status_eq_round_of_finite_nonzero
    (destination : FloatFormat) {source : FloatFormat}
    (values : Array (Model source)) (mode : IEEERoundingMode)
    (hfinite : ∀ value ∈ values.toList, isFinite value = true)
    (hnonzero : Semantics.finiteSum values.toList ≠ 0) :
    sum destination values mode (status := true) =
      {
        value := Internal.Directed.roundDyadic destination mode
          (values.foldl Internal.State.pushValue
            ({} : Internal.State destination)).exact
        status := dyadicRoundingStatus destination mode
          (values.foldl Internal.State.pushValue
            ({} : Internal.State destination)).exact
          (Internal.Directed.roundDyadic destination mode
            (values.foldl Internal.State.pushValue
              ({} : Internal.State destination)).exact)
        ternary := dyadicTernary
          (values.foldl Internal.State.pushValue
            ({} : Internal.State destination)).exact
          (Internal.Directed.roundDyadic destination mode
            (values.foldl Internal.State.pushValue
              ({} : Internal.State destination)).exact)
      } :=
  Internal.State.finish_of_hasOnlyFiniteTerms_of_ne_zero _ mode
    (Internal.array_foldl_pushValue_hasOnlyFiniteTerms values hfinite)
    (sumAccumulator_significand_ne_zero_of_finiteSum_ne_zero destination values hnonzero)

/--
A finite sum whose exact accumulator is zero returns a zero and raises no status indicator. Its sign
is the accumulator's signed-zero rule: if at least one term was accumulated, the zero is negative
when every term was a negative zero, or when the terms were not all positive zeros and the direction
is downward. The empty sum accumulates no term and gives a positive zero. A destination without
signed zero returns its single zero. The sign is stated from the inputs by `sum_status_empty`,
`sum_status_eq_zero_of_same_sign_zeros` and `sum_status_eq_zero_of_finiteSum_eq_zero`.
-/
theorem sum_status_eq_zero_of_finite
    (destination : FloatFormat) {source : FloatFormat}
    (values : Array (Model source)) (mode : IEEERoundingMode)
    (hfinite : ∀ value ∈ values.toList, isFinite value = true)
    (hzero :
      (values.foldl Internal.State.pushValue
        ({} : Internal.State destination)).exact.significand = 0) :
    sum destination values mode (status := true) =
      {
        value := zero destination <|
          (values.foldl Internal.State.pushValue
            ({} : Internal.State destination)).sawFiniteTerm &&
          ((values.foldl Internal.State.pushValue
              ({} : Internal.State destination)).allTermsNegativeZero ||
            (!(values.foldl Internal.State.pushValue
                ({} : Internal.State destination)).allTermsPositiveZero &&
              mode == .down))
        status := .clear
        ternary := .eq
      } :=
  Internal.State.finish_of_hasOnlyFiniteTerms_of_eq_zero _ mode
    (Internal.array_foldl_pushValue_hasOnlyFiniteTerms values hfinite) hzero

/--
Every finite-input nearest-even sum with a finite result is one real rounding of the exact sum.
Zero totals include empty input, signed zeros, and cancellation. Their stored signs are specified
by `sum_status_eq_zero_of_finite` and disappear only in the real-valued conclusion.
-/
theorem sum_status_value_toReal_eq_roundAt_of_finite
    (destination : FloatFormat) {source : FloatFormat}
    (values : Array (Model source))
    (hfmt : destination.isIEEE = true)
    (hfinite : ∀ value ∈ values.toList, isFinite value = true)
    (hresult : isFinite (sum destination values .nearest (status := true)).value = true) :
    toReal (sum destination values .nearest (status := true)).value =
      roundAt destination (Semantics.finiteSum values.toList : ℝ) := by
  have hround := Internal.State.toReal_finish_nearest_eq_roundAt
    (values.foldl Internal.State.pushValue ({} : Internal.State destination)) hfmt
    (Internal.array_foldl_pushValue_hasOnlyFiniteTerms values hfinite) hresult
  rwa [Internal.array_foldl_pushValue_exact_toRat] at hround

/--
A nonempty sum of zeros with one common sign preserves that sign in every rounding mode.

The destination's zero constructor accounts for formats without a negative zero. The hypotheses
refer only to the input values, independently of the accumulator's signed-zero flags.
-/
theorem sum_status_eq_zero_of_same_sign_zeros
    (destination : FloatFormat) {source : FloatFormat}
    (values : Array (Model source)) (mode : IEEERoundingMode) (negative : Bool)
    (hnonempty : values ≠ #[])
    (hzero : ∀ value ∈ values.toList, isZero value = true)
    (hsign : ∀ value ∈ values.toList, signBit value = negative) :
    sum destination values mode (status := true) =
      { value := zero destination negative, status := .clear, ternary := .eq } := by
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
  unfold sum Internal.Status.sum
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

/--
A nonempty finite sum whose exact value is zero, but whose terms are not all zeros of one sign,
returns the zero IEEE 754 assigns to an exact cancellation or to mixed-sign zeros: negative when
rounding toward negative infinity and positive otherwise, with clear status. A destination without
signed zero returns its single zero. The hypotheses refer only to the input values. The two sign
premises fail for the empty sum, which gives a positive zero in every mode (`sum_status_empty`).
-/
theorem sum_status_eq_zero_of_finiteSum_eq_zero
    (destination : FloatFormat) {source : FloatFormat}
    (values : Array (Model source)) (mode : IEEERoundingMode)
    (hfinite : ∀ value ∈ values.toList, isFinite value = true)
    (hzero : Semantics.finiteSum values.toList = 0)
    (hnegative : ¬∀ value ∈ values.toList, isZero value = true ∧ signBit value = true)
    (hpositive : ¬∀ value ∈ values.toList, isZero value = true ∧ signBit value = false) :
    sum destination values mode (status := true) =
      { value := zero destination (mode == .down), status := .clear, ternary := .eq } := by
  have hsig : (values.foldl Internal.State.pushValue
      ({} : Internal.State destination)).exact.significand = 0 := by
    apply (Numerics.Dyadic.toRat_eq_zero_iff _).mp
    rw [Internal.array_foldl_pushValue_exact_toRat, hzero]
  rw [sum_status_eq_zero_of_finite destination values mode hfinite hsig, ← Array.foldl_toList]
  obtain ⟨hsaw, hallNegative, hallPositive⟩ :=
    Internal.foldl_pushValue_flags ({} : Internal.State destination) values.toList hfinite
  have hnonempty : values.toList.isEmpty = false := by
    cases hlist : values.toList with
    | nil => exact absurd (by simp [hlist]) hnegative
    | cons _ _ => rfl
  have hnotNegative : (values.toList.all fun value => isZero value && signBit value) = false := by
    rw [Bool.eq_false_iff]
    intro hall
    exact hnegative fun value hmem => by simpa using List.all_eq_true.mp hall value hmem
  have hnotPositive :
      (values.toList.all fun value => isZero value && !signBit value) = false := by
    rw [Bool.eq_false_iff]
    intro hall
    exact hpositive fun value hmem => by simpa using List.all_eq_true.mp hall value hmem
  rw [hsaw, hallNegative, hallPositive, hnonempty, hnotNegative, hnotPositive]
  simp

/-- A singleton infinity has the value and exception indicators of a destination cast. -/
theorem sum_status_singleton_eq_cast_status_of_isInf
    (destination : FloatFormat) {source : FloatFormat}
    (value : Model source) (mode : IEEERoundingMode)
    (hinf : isInf value = true) :
    sum destination #[value] mode (status := true) =
      cast source destination value mode (status := true) := by
  have hnan := isNaN_eq_false_of_isInf_eq_true value hinf
  cases mode <;> cases hsign : signBit value <;>
    simp [sum, Internal.Status.sum, Internal.State.pushValue, Internal.State.pushInfinity,
      Internal.State.finish, cast, Internal.Status.cast, Internal.Directed.cast,
      Internal.Nearest.cast, hnan, hinf, hsign] <;>
    split <;> rfl

/-- With equal lengths, the dot product with status finishes the accumulated dot-product state. -/
private theorem dot_status_eq_ok_finish
    (destination : FloatFormat) {leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (mode : IEEERoundingMode) (hsize : left.size = right.size) :
    dot destination left right mode (status := true) =
      .ok ((Internal.dotState left right hsize : Internal.State destination).finish mode) := by
  simp [dot, Internal.Status.dot, hsize]

/--
A nonzero dot product of finite inputs performs one final dyadic rounding and reports that
rounding's status and ternary value.
-/
theorem dot_status_eq_round_of_finite_nonzero
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
    dot destination left right mode (status := true) =
      .ok {
        value := Internal.Directed.roundDyadic destination mode
          (Internal.dotState left right hsize :
            Internal.State destination).exact
        status := dyadicRoundingStatus destination mode
          (Internal.dotState left right hsize :
            Internal.State destination).exact
          (Internal.Directed.roundDyadic destination mode
            (Internal.dotState left right hsize :
              Internal.State destination).exact)
        ternary := dyadicTernary
          (Internal.dotState left right hsize :
            Internal.State destination).exact
          (Internal.Directed.roundDyadic destination mode
            (Internal.dotState left right hsize :
              Internal.State destination).exact)
      } := by
  rw [dot_status_eq_ok_finish destination left right mode hsize,
    Internal.State.finish_of_hasOnlyFiniteTerms_of_ne_zero _ mode
      (Internal.dotState_hasOnlyFiniteTerms left right hsize hleftFinite hrightFinite)
      (dotAccumulator_significand_ne_zero_of_finiteDot_ne_zero
        destination left right hsize hnonzero)]

/--
A finite dot product whose exact accumulator is zero returns a zero and raises no status indicator.
Its sign is the accumulator's signed-zero rule applied to the exact products: if at least one
product was accumulated, the zero is negative when every product was a negative zero, or when the
products were not all positive zeros and the direction is downward. The empty dot product
accumulates no product and gives a positive zero (`dot_status_empty`). A destination without signed
zero returns its single zero.
-/
theorem dot_status_eq_zero_of_finite
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
    dot destination left right mode (status := true) =
      .ok {
        value := zero destination <|
          (Internal.dotState left right hsize :
            Internal.State destination).sawFiniteTerm &&
          ((Internal.dotState left right hsize :
              Internal.State destination).allTermsNegativeZero ||
            (!(Internal.dotState left right hsize :
                Internal.State destination).allTermsPositiveZero &&
              mode == .down))
        status := .clear
        ternary := .eq
      } := by
  rw [dot_status_eq_ok_finish destination left right mode hsize,
    Internal.State.finish_of_hasOnlyFiniteTerms_of_eq_zero _ mode
      (Internal.dotState_hasOnlyFiniteTerms left right hsize hleftFinite hrightFinite) hzero]

/--
Every successful finite-input nearest-even dot product with a finite result is one real rounding
of the exact product sum, including cancellation to zero. The successful specification forces equal
input lengths, and the finite-result premise excludes exceptional outputs.
-/
theorem dot_status_value_toReal_eq_roundAt_of_finite
    (destination : FloatFormat) {leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (exact : Rat) (outcome : IEEEOutcome destination)
    (hfmt : destination.isIEEE = true)
    (hleftFinite : ∀ position (hposition : position < left.size), isFinite left[position] = true)
    (hrightFinite : ∀ position (hposition : position < right.size), isFinite right[position] = true)
    (hspec : Semantics.finiteDot left.toList right.toList = .ok exact)
    (houtcome : dot destination left right .nearest (status := true) = .ok outcome)
    (hresult : isFinite outcome.value = true) :
    toReal outcome.value = roundAt destination (exact : ℝ) := by
  have hsize : left.size = right.size := by
    by_contra hne
    simp [Semantics.finiteDot, hne] at hspec
  rw [dot_status_eq_ok_finish destination left right .nearest hsize, Except.ok.injEq] at houtcome
  subst outcome
  rw [Internal.State.toReal_finish_nearest_eq_roundAt _ hfmt
      (Internal.dotState_hasOnlyFiniteTerms left right hsize hleftFinite hrightFinite) hresult,
    Internal.dotState_exact_toRat_of_finiteDot_eq_ok left right hsize hspec]

/-- The empty correctly rounded sum is an exact positive zero with no exception indicator. -/
@[simp] theorem sum_status_empty
    (destination source : FloatFormat) (mode : IEEERoundingMode) :
    sum destination (#[] : Array (Model source)) mode (status := true) =
      { value := zero destination false, status := .clear, ternary := .eq } := by
  simp [sum, Internal.Status.sum, Internal.State.finish, outcomeWithInvalid]

/-- A mismatched dot product reports both observed lengths and performs no reduction. -/
theorem dot_status_lengthMismatch
    (destination : FloatFormat) {leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (mode : IEEERoundingMode) (hsize : left.size ≠ right.size) :
    dot destination left right mode (status := true) =
      .error (.lengthMismatch left.size right.size) := by
  simp [dot, Internal.Status.dot, hsize]

/--
The empty correctly rounded dot product is an exact positive zero with no exception indicator.
-/
@[simp] theorem dot_status_empty
    (destination leftFormat rightFormat : FloatFormat) (mode : IEEERoundingMode) :
    dot destination
        (#[] : Array (Model leftFormat)) (#[] : Array (Model rightFormat)) mode (status := true) =
      .ok { value := zero destination false, status := .clear, ternary := .eq } := by
  simp [dot, Internal.Status.dot, Internal.dotState, Internal.dotStateLoop,
    Internal.State.finish, outcomeWithInvalid]

/-- The sum with `status := true` delivers the value of the sum in the same direction. -/
@[simp] theorem value_sum (destination : FloatFormat) {source : FloatFormat}
    (values : Array (Model source)) (mode : IEEERoundingMode) :
    (sum destination values mode (status := true)).value = sum destination values mode :=
  rfl

/--
The dot product with `status := true` has the value and the length check of the dot product in
the same direction.
-/
@[simp] theorem map_value_dot (destination : FloatFormat)
    {leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat))
    (mode : IEEERoundingMode) :
    (dot destination left right mode (status := true)).map IEEEOutcome.value =
      dot destination left right mode := by
  unfold dot Internal.Status.dot Internal.Value.dot
  split <;> rfl

end Reduction
end Model
end FloatLib.Floats.Formats.BinaryInterchange
