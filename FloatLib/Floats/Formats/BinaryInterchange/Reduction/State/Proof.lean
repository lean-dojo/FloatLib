/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Model.ERealSemantics
public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Semantics
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Proof
public import FloatLib.Numerics.Exact.Dyadic.Arithmetic.Proof

/-!
# Exact and finite-state invariants of reduction accumulators

Pushing an operand or product updates the accumulator's exact dyadic field by its rational
contribution. Finite inputs preserve the absence of exceptional terms. The finishing lemmas
identify final rounding, signed zero and generated-invalid flags. These state facts are shared by
sums and dot products.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace Reduction

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
  have hinf := isInfinite_eq_false_of_toDyadic?_some hdecode
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
  have hleftSNaN := isSignaling_eq_false_of_toDyadic?_some hleftExact
  have hrightSNaN := isSignaling_eq_false_of_toDyadic?_some hrightExact
  have hleftInf := isInfinite_eq_false_of_toDyadic?_some hleftExact
  have hrightInf := isInfinite_eq_false_of_toDyadic?_some hrightExact
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
theorem array_foldl_pushValue_hasOnlyFiniteTerms
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
theorem foldl_pushValue_flags
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
theorem State.finish_of_hasOnlyFiniteTerms_of_ne_zero
    {destination : FloatFormat} (state : State destination) (mode : IEEERoundingMode)
    (hstate : state.HasOnlyFiniteTerms) (hnonzero : state.exact.significand ≠ 0) :
    state.finish mode =
      { value := Internal.Directed.roundDyadic destination mode state.exact
        status := dyadicRoundingStatus destination mode state.exact
          (Internal.Directed.roundDyadic destination mode state.exact)
        ternary := dyadicTernary state.exact
          (Internal.Directed.roundDyadic destination mode state.exact) } := by
  simp only [HasOnlyFiniteTerms, finish, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq, dyadicRoundingOutcome] at hstate ⊢
  simp [hstate, hnonzero]

/--
A finite-only state with a zero exact accumulator returns the zero whose sign its signed-zero flags
select, with clear status.
-/
theorem State.finish_of_hasOnlyFiniteTerms_of_eq_zero
    {destination : FloatFormat} (state : State destination) (mode : IEEERoundingMode)
    (hstate : state.HasOnlyFiniteTerms) (hzero : state.exact.significand = 0) :
    state.finish mode =
      { value := zero destination <|
          state.sawFiniteTerm &&
            (state.allTermsNegativeZero || (!state.allTermsPositiveZero && mode == .down))
        status := .clear
        ternary := .eq } := by
  simp only [HasOnlyFiniteTerms, finish, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq] at hstate ⊢
  simp [hstate, hzero, outcomeWithInvalid]

/--
Nearest-even finishing of a finite-only state with a finite result is one real rounding of the
exact accumulator, a zero accumulator included.
-/
theorem State.toReal_finish_nearest_eq_roundAt
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
  · by_cases hinf : isInfinite value = true
    · cases hdecode : toDyadic? value with
      | none =>
          simp [State.pushValue, Semantics.finiteContribution, hnan, hinf, hdecode]
      | some exact =>
          have hinfFalse := isInfinite_eq_false_of_toDyadic?_some hdecode
          simp [hinf] at hinfFalse
    · have hnanFalse := Bool.eq_false_of_not_eq_true hnan
      have hinfFalse := Bool.eq_false_of_not_eq_true hinf
      have hfinite :=
        isFinite_eq_true_of_isNaN_eq_false_of_isInfinite_eq_false
          value hnanFalse hinfFalse
      obtain ⟨exact, hdecode⟩ := exists_toDyadic?_of_isFinite hfinite
      simp [State.pushValue, Semantics.finiteContribution, hnan, hinf, hdecode,
        State.pushExact, Numerics.Dyadic.add_toRat]

/-- Folding values accumulates the exact rational sum of their finite contributions. -/
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
      ac_rfl

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
Consuming one product adds the exact product of its two finite rational contributions. An
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
          exact absurd ⟨isFinite_eq_true_of_isNaN_eq_false_of_isInfinite_eq_false left
            hnanFields.1 hinfFields.1,
              isFinite_eq_true_of_isNaN_eq_false_of_isInfinite_eq_false right
            hnanFields.2 hinfFields.2⟩ hfinite
  rw [hexact, hcontribution, add_zero]

/--
The indexed dot loop accumulates the exact rational product sum of its Array slice, in which
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
      rw [dotStateLoop, Semantics.finiteDotSlice]
      rw [ih, State.pushProduct_exact_toRat]
      ac_rfl

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
The complete dot kernel accumulates the exact value of its rational Array specification, in which
exceptional entries contribute zero.
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
theorem dotState_exact_toRat_of_finiteDot_eq_ok
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

end Reduction
end Model
end FloatLib.Floats.Formats.BinaryInterchange
