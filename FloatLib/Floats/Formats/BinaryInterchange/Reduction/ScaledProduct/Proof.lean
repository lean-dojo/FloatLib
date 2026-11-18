/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.ScaledProduct.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Dot.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Sum.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.MixedError
import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Proof

/-!
# Contracts of the scaled products

For finite factors whose exact product is not zero, a conventional IEEE destination and
nearest-even rounding:

* `scaledProduct_of_finite`: the kernel result on a list of finite factors. Its scale factor is
  the exponent of the leading bit of the exact product, and its product is the one rounding of
  the exact product scaled by that power of two, a real of magnitude in `[1, 2)`.
* `toReal_scaledProd_product`: these two facts for `scaledProd`, against
  `Semantics.finiteProd`, the exact rational product of the operands.
* `mixedError_scaledProd`: the scaled product carries the mixed error of one rounding,
  `unitRoundoffAt destination` relative to the exact scaled product plus
  `underflowErrorAt destination`, which is the form `roundoff` composes.
* `toReal_scaledProdOfSums_product`: the same for `scaledProdSum` and `scaledProdDiff`, against
  the exact product of the sums or differences of the operands.

The finite-result premise is observable on the result. It holds whenever the destination can
hold the value two, which a rounding carry may deliver.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace Reduction

open FloatLib.Numerics

variable {destination source : FloatFormat}

/-- Exact product of the finite contributions. -/
def Semantics.finiteProd {format : FloatFormat} (values : List (Model format)) : Rat :=
  (values.map Semantics.finiteContribution).prod

namespace Internal

/-- The state has consumed finite factors only. -/
def ProductState.HasOnlyFiniteFactors (state : ProductState destination) : Prop :=
  state.sawInfinity = false ∧ state.signalingNaN = none ∧ state.quietNaN = none ∧
    state.generatedInvalid = false

/-- The empty state has consumed finite factors only, and its exact product is one. -/
theorem ProductState.hasOnlyFiniteFactors_empty :
    ({} : ProductState destination).HasOnlyFiniteFactors ∧
      ({} : ProductState destination).exact.toRat = 1 := by
  refine ⟨⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  simp [Numerics.Dyadic.toRat, Numerics.Dyadic.signedSignificand]

/--
Consuming finite factors keeps the state free of exceptional factors and multiplies its exact
product by theirs.
-/
theorem foldl_push_finite (exacts : List Numerics.Dyadic) (state : ProductState destination)
    (hstate : state.HasOnlyFiniteFactors) :
    ((exacts.map Factor.finite).foldl ProductState.push state).HasOnlyFiniteFactors ∧
      ((exacts.map Factor.finite).foldl ProductState.push state).exact.toRat =
        state.exact.toRat * (exacts.map Numerics.Dyadic.toRat).prod := by
  induction exacts generalizing state with
  | nil => simpa using hstate
  | cons head tail ih =>
      have hpush : (state.push (.finite head)).HasOnlyFiniteFactors := hstate
      obtain ⟨hfinite, hexact⟩ := ih (state.push (.finite head)) hpush
      refine ⟨hfinite, ?_⟩
      rw [List.map_cons, List.foldl_cons, hexact]
      simp only [ProductState.push, Numerics.Dyadic.mul_toRat, List.map_cons, List.prod_cons]
      ring

/-- The scaled form of a nonzero exact product: its significand at the exponent that puts the
leading bit at one. -/
private def scaledExact (exact : Numerics.Dyadic) : Numerics.Dyadic :=
  { exact with exponent := -(exact.significand.log2 : Int) }

/-- The scaled form denotes the exact product divided by two to the scale factor. -/
private theorem toReal_scaledExact (exact : Numerics.Dyadic) :
    (scaledExact exact).toReal =
      exact.toReal * (2 : ℝ) ^ (-((exact.significand.log2 : Int) + exact.exponent)) := by
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  simp only [scaledExact, Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand]
  rw [mul_assoc, ← zpow_add₀ h2]
  congr 2
  ring

/-- The scaled form of a nonzero exact product has magnitude in `[1, 2)`. -/
private theorem one_le_abs_toReal_scaledExact (exact : Numerics.Dyadic)
    (hne : exact.significand ≠ 0) :
    1 ≤ |(scaledExact exact).toReal| ∧ |(scaledExact exact).toReal| < 2 := by
  have hlow : 2 ^ exact.significand.log2 ≤ exact.significand := Nat.log2_self_le hne
  have hhigh : exact.significand < 2 ^ (exact.significand.log2 + 1) := Nat.lt_log2_self
  have hpos : (0 : ℝ) < (2 : ℝ) ^ exact.significand.log2 := by positivity
  have habs : |(scaledExact exact).toReal| =
      (exact.significand : ℝ) / (2 : ℝ) ^ exact.significand.log2 := by
    rw [Dyadic.abs_toReal]
    simp [scaledExact, Flocq.bpow, binaryRadix, Numerics.Radix.toReal, div_eq_mul_inv]
  rw [habs]
  constructor
  · rw [le_div_iff₀ hpos, one_mul]
    exact_mod_cast hlow
  · rw [div_lt_iff₀ hpos]
    have : (exact.significand : ℝ) < (2 : ℝ) ^ (exact.significand.log2 + 1) := by
      exact_mod_cast hhigh
    rw [pow_succ] at this
    linarith

/--
The result on finite factors with a nonzero exact product: the scale factor is the exponent of
the leading bit, and the product is the one rounding of the scaled exact product.
-/
theorem ProductState.finish_of_hasOnlyFiniteFactors (state : ProductState destination)
    (mode : IEEERoundingMode) (hstate : state.HasOnlyFiniteFactors)
    (hne : state.exact.significand ≠ 0) :
    (state.finish mode).product =
        Internal.Directed.roundDyadic destination mode
          { state.exact with exponent := -(state.exact.significand.log2 : Int) } ∧
      (state.finish mode).scaleFactor =
        (state.exact.significand.log2 : Int) + state.exact.exponent := by
  obtain ⟨hinfinity, hsignaling, hquiet, hinvalid⟩ := hstate
  simp [ProductState.finish, hinfinity, hsignaling, hquiet, hinvalid, hne]

/--
For finite factors with a nonzero exact product and a finite result in a conventional IEEE
destination, the nearest-even scaled product is one real rounding of the exact product divided
by two to the scale factor, a real of magnitude in `[1, 2)`.
-/
theorem scaledProduct_of_finite (exacts : List Numerics.Dyadic)
    (hfmt : destination.isIEEE = true)
    (hne : (exacts.map Numerics.Dyadic.toRat).prod ≠ 0)
    (hresult : isFinite (((exacts.map Factor.finite).foldl ProductState.push
      ({} : ProductState destination)).finish .nearest).product = true) :
    let outcome := ((exacts.map Factor.finite).foldl ProductState.push
      ({} : ProductState destination)).finish .nearest
    let scaled := (((exacts.map Numerics.Dyadic.toRat).prod : Rat) : ℝ) *
      (2 : ℝ) ^ (-outcome.scaleFactor)
    toReal outcome.product = roundAt destination scaled ∧ 1 ≤ |scaled| ∧ |scaled| < 2 := by
  obtain ⟨hstate, hexact⟩ := foldl_push_finite (destination := destination) exacts {}
    ProductState.hasOnlyFiniteFactors_empty.1
  rw [ProductState.hasOnlyFiniteFactors_empty.2, one_mul] at hexact
  generalize (exacts.map Factor.finite).foldl ProductState.push
    ({} : ProductState destination) = state at hstate hexact hresult ⊢
  have hsignificand : state.exact.significand ≠ 0 := by
    intro hzero
    apply hne
    rw [← hexact]
    simp [Numerics.Dyadic.toRat, Numerics.Dyadic.signedSignificand, hzero]
  obtain ⟨hproduct, hscale⟩ :=
    ProductState.finish_of_hasOnlyFiniteFactors state .nearest hstate hsignificand
  have hreal := toReal_scaledExact state.exact
  rw [← Numerics.Dyadic.cast_toRat state.exact, hexact, ← hscale] at hreal
  dsimp only
  rw [← hreal]
  rw [hproduct] at hresult ⊢
  exact ⟨toReal_roundDyadic_eq_roundAt destination hfmt _ hresult,
    one_le_abs_toReal_scaledExact _ hsignificand⟩

/-- A finite operand is the finite factor of its exact value. -/
theorem Factor.ofValue_of_toDyadic?_eq_some {value : Model source} {exact : Numerics.Dyadic}
    (h : toDyadic? value = some exact) :
    (Factor.ofValue value : Factor destination) = .finite exact := by
  simp [Factor.ofValue, h]

end Internal

/-- The exact value of a finite operand, whose rational value is its contribution. -/
private theorem exists_exact_of_isFinite {value : Model source} (h : isFinite value = true) :
    ∃ exact, toDyadic? value = some exact ∧ exact.toRat = Semantics.finiteContribution value := by
  obtain ⟨exact, hexact⟩ := exists_toDyadic?_of_isFinite h
  exact ⟨exact, hexact, by simp [Semantics.finiteContribution, hexact]⟩

/-- The factors of finite operands are the finite factors of their exact values. -/
private theorem exists_exacts_of_isFinite (values : List (Model source))
    (hfinite : ∀ value ∈ values, isFinite value = true) :
    ∃ exacts : List Numerics.Dyadic,
      values.map (Internal.Factor.ofValue (destination := destination)) =
          exacts.map Internal.Factor.finite ∧
        exacts.map Numerics.Dyadic.toRat = values.map Semantics.finiteContribution := by
  induction values with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons head tail ih =>
      obtain ⟨exact, hexact, hrat⟩ := exists_exact_of_isFinite (hfinite head (by simp))
      obtain ⟨exacts, hfactors, hrats⟩ := ih fun value hmem => hfinite value (by simp [hmem])
      refine ⟨exact :: exacts, ?_, ?_⟩
      · simp [hfactors, Internal.Factor.ofValue_of_toDyadic?_eq_some hexact]
      · simp [hrats, hrat]

/-- `scaledProd` folds the factors of its operands. -/
private theorem scaledProd_eq_foldl (destination : FloatFormat) (values : Array (Model source))
    (mode : IEEERoundingMode) :
    scaledProd destination values mode =
      ((values.toList.map Internal.Factor.ofValue).foldl Internal.ProductState.push
        ({} : Internal.ProductState destination)).finish mode := by
  rw [scaledProd, ← Array.foldl_toList, List.foldl_map]

/--
For finite operands with a nonzero exact product and a finite result in a conventional IEEE
destination, the nearest-even `scaledProd` is one real rounding of the exact product divided by
two to the scale factor, and that scaled exact product has magnitude in `[1, 2)`.
-/
theorem toReal_scaledProd_product (destination : FloatFormat) (values : Array (Model source))
    (hfmt : destination.isIEEE = true)
    (hfinite : ∀ value ∈ values.toList, isFinite value = true)
    (hne : Semantics.finiteProd values.toList ≠ 0)
    (hresult : isFinite (scaledProd destination values).product = true) :
    toReal (scaledProd destination values).product =
        roundAt destination ((Semantics.finiteProd values.toList : ℝ) *
          (2 : ℝ) ^ (-(scaledProd destination values).scaleFactor)) ∧
      1 ≤ |(Semantics.finiteProd values.toList : ℝ) *
        (2 : ℝ) ^ (-(scaledProd destination values).scaleFactor)| ∧
      |(Semantics.finiteProd values.toList : ℝ) *
        (2 : ℝ) ^ (-(scaledProd destination values).scaleFactor)| < 2 := by
  obtain ⟨exacts, hfactors, hrats⟩ :=
    exists_exacts_of_isFinite (destination := destination) values.toList hfinite
  rw [scaledProd_eq_foldl, hfactors] at hresult ⊢
  have h := Internal.scaledProduct_of_finite exacts hfmt (by rw [hrats]; exact hne) hresult
  rw [hrats] at h
  exact h

/--
The scaled product of `scaledProd` carries the mixed error of one rounding against the exact
scaled product: relative `unitRoundoffAt destination` plus absolute
`underflowErrorAt destination`.
-/
theorem mixedError_scaledProd (destination : FloatFormat) (values : Array (Model source))
    (hfmt : destination.isIEEE = true)
    (hfinite : ∀ value ∈ values.toList, isFinite value = true)
    (hne : Semantics.finiteProd values.toList ≠ 0)
    (hresult : isFinite (scaledProd destination values).product = true) :
    MixedError (toReal (scaledProd destination values).product)
      ((Semantics.finiteProd values.toList : ℝ) *
        (2 : ℝ) ^ (-(scaledProd destination values).scaleFactor))
      (unitRoundoffAt destination) (underflowErrorAt destination) := by
  rw [(toReal_scaledProd_product destination values hfmt hfinite hne hresult).1]
  exact mixedError_roundAt destination _

/--
For finite operands whose sums (`subtract := false`) or differences (`subtract := true`) have a
nonzero exact product, and a finite result in a conventional IEEE destination, the nearest-even
scaled product of `scaledProdSum` and `scaledProdDiff` is one real rounding of that exact product
divided by two to the scale factor.
-/
theorem toReal_scaledProdOfSums_product (destination : FloatFormat)
    {leftFormat rightFormat : FloatFormat}
    (left : Array (Model leftFormat)) (right : Array (Model rightFormat)) (subtract : Bool)
    (outcome : ScaledProduct (Model destination)) (hfmt : destination.isIEEE = true)
    (hleft : ∀ value ∈ left.toList, isFinite value = true)
    (hright : ∀ value ∈ right.toList, isFinite value = true)
    (houtcome : Internal.scaledProdOfSums destination left right subtract .nearest = .ok outcome)
    (hne : ((left.toList.zip right.toList).map fun pair =>
        Semantics.finiteContribution pair.1 +
          Semantics.finiteContribution (if subtract then neg pair.2 else pair.2)).prod ≠ 0)
    (hresult : isFinite outcome.product = true) :
    toReal outcome.product =
      roundAt destination
        ((((left.toList.zip right.toList).map fun pair =>
            Semantics.finiteContribution pair.1 +
              Semantics.finiteContribution (if subtract then neg pair.2 else pair.2)).prod : ℝ) *
          (2 : ℝ) ^ (-outcome.scaleFactor)) := by
  have hpairs : ∃ exacts : List Numerics.Dyadic,
      (left.toList.zip right.toList).map (fun pair =>
          Internal.Factor.add (destination := destination) (Internal.Factor.ofValue pair.1)
            (Internal.Factor.ofValue (if subtract then neg pair.2 else pair.2))) =
        exacts.map Internal.Factor.finite ∧
      exacts.map Numerics.Dyadic.toRat =
        (left.toList.zip right.toList).map fun pair =>
          Semantics.finiteContribution pair.1 +
            Semantics.finiteContribution (if subtract then neg pair.2 else pair.2) := by
    have hmem : ∀ pair ∈ left.toList.zip right.toList,
        isFinite pair.1 = true ∧ isFinite pair.2 = true := fun pair hpair =>
      ⟨hleft _ (List.of_mem_zip hpair).1, hright _ (List.of_mem_zip hpair).2⟩
    generalize left.toList.zip right.toList = pairs at hmem
    induction pairs with
    | nil => exact ⟨[], rfl, rfl⟩
    | cons head tail ih =>
        obtain ⟨hx, hy⟩ := hmem head (by simp)
        have hy' : isFinite (if subtract then neg head.2 else head.2) = true := by
          cases subtract <;> simp [hy]
        obtain ⟨dx, hdx, hratx⟩ := exists_exact_of_isFinite hx
        obtain ⟨dy, hdy, hraty⟩ := exists_exact_of_isFinite hy'
        obtain ⟨exacts, hfactors, hrats⟩ := ih fun pair hpair => hmem pair (by simp [hpair])
        refine ⟨addDyadic dx dy :: exacts, ?_, ?_⟩
        · rw [List.map_cons, List.map_cons, hfactors,
            Internal.Factor.ofValue_of_toDyadic?_eq_some hdx,
            Internal.Factor.ofValue_of_toDyadic?_eq_some hdy]
          rfl
        · simp [hrats, ← hratx, ← hraty, addDyadic, Numerics.Dyadic.add_toRat]
  obtain ⟨exacts, hfactors, hrats⟩ := hpairs
  unfold Internal.scaledProdOfSums at houtcome
  split at houtcome
  · rw [Except.ok.injEq] at houtcome
    subst houtcome
    rw [← Array.foldl_toList, Array.toList_zip,
      ← List.foldl_map (f := fun pair : Model leftFormat × Model rightFormat =>
        Internal.Factor.add (destination := destination) (Internal.Factor.ofValue pair.1)
          (Internal.Factor.ofValue (if subtract then neg pair.2 else pair.2)))
        (g := Internal.ProductState.push), hfactors] at hresult ⊢
    have h := Internal.scaledProduct_of_finite exacts hfmt (by rw [hrats]; exact hne) hresult
    rw [hrats] at h
    exact h.1
  · cases houtcome

end Reduction
end Model
end FloatLib.Floats.Formats.BinaryInterchange
