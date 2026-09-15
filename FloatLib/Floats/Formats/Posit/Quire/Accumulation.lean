/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Quire.Capacity
import Mathlib.Tactic.Ring

/-!
# Exact accumulation loops in a standard posit quire

`Capacity` bounds one signed coefficient sum. This module turns those bounds into statements about
the loops a program actually runs: folding `qMulAdd` over a list of posit pairs, or `qAddP` over a
list of posits, starting from the zero quire.

Below the Posit Standard's term limits (`productSumTermLimit = 2^31` exact products, or
`positSumTermLimit format = 2^(23 + 4n)` posit addends) every intermediate quire stays ordinary, so
the loop never produces quire NaR and the final quire denotes the exact rational sum.

The helpers `exactValues?` and `exactProducts?` collect the exact rational terms of a list; they
are `some` exactly when no input is NaR, which is the only hypothesis a caller must supply besides
the term count.

## References

* Posit Working Group, *Standard for Posit Arithmetic (2022)*, March 2, 2022,
  Sections 3.4 and 5.11, <https://posithub.org/docs/posit_standard-2.pdf>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Quire.Model

open FloatLib.Numerics

variable {format : Format}

/-- Exact rational values of a list of posits, or `none` when some entry is NaR. -/
def exactValues? :
    List (FloatLib.Floats.Formats.Posit.Model format) → Option (List Rat)
  | [] => some []
  | addend :: rest => do
      let value ← addend.toRat?
      let values ← exactValues? rest
      pure (value :: values)

/-- Exact rational products of a list of posit pairs, or `none` when some entry is NaR. -/
def exactProducts? :
    List (FloatLib.Floats.Formats.Posit.Model format ×
      FloatLib.Floats.Formats.Posit.Model format) → Option (List Rat)
  | [] => some []
  | pair :: rest => do
      let left ← pair.1.toRat?
      let right ← pair.2.toRat?
      let products ← exactProducts? rest
      pure (left * right :: products)

/-- Fold exact product accumulation over a list of posit pairs. -/
@[inline] def foldMulAdd
    (accumulator : Model format)
    (pairs : List (FloatLib.Floats.Formats.Posit.Model format ×
      FloatLib.Floats.Formats.Posit.Model format)) : Model format :=
  pairs.foldl (fun quire pair => qMulAdd quire pair.1 pair.2) accumulator

/-- Fold exact posit accumulation over a list of posits. -/
@[inline] def foldAddP
    (accumulator : Model format)
    (addends : List (FloatLib.Floats.Formats.Posit.Model format)) : Model format :=
  addends.foldl qAddP accumulator

/-! ## Helpers -/

private theorem exists_toDyadic?_eq_some_of_toRat?_eq_some
    (value : FloatLib.Floats.Formats.Posit.Model format) (rational : Rat)
    (hvalue : value.toRat? = some rational) :
    ∃ dyadic : FloatLib.Numerics.Dyadic,
      value.toDyadic? = some dyadic ∧ dyadic.toRat = rational := by
  rw [FloatLib.Floats.Formats.Posit.Model.toRat?_eq_toDyadic?_map] at hvalue
  cases hdyadic : value.toDyadic? with
  | none =>
      rw [hdyadic] at hvalue
      simp at hvalue
  | some dyadic =>
      rw [hdyadic] at hvalue
      exact ⟨dyadic, rfl, by simpa using hvalue⟩

private theorem toRat?_eq_some_iff (accumulator : Model format) (value : Rat) :
    accumulator.toRat? = some value ↔
      accumulator.isNaR = false ∧
        Rat.ofInt accumulator.coefficient * (2 : Rat) ^ scaleExponent format = value := by
  unfold toRat?
  by_cases hnar : accumulator.isNaR = true
  · simp [hnar]
  · simp [hnar]

private theorem productSumTermLimit_mul_productCoefficientBound (format : Format) :
    productSumTermLimit * productCoefficientBound format = 2 ^ (width format - 1) := by
  unfold productSumTermLimit productCoefficientBound width
  rw [← Nat.pow_add]
  congr 1
  have hbits := format.bits_ge_two
  omega

private theorem positSumTermLimit_mul_positCoefficientBound (format : Format) :
    positSumTermLimit format * positCoefficientBound format = 2 ^ (width format - 1) := by
  unfold positSumTermLimit positCoefficientBound width
  rw [← Nat.pow_add]
  congr 1
  have hbits := format.bits_ge_two
  omega

private theorem ordinaryCoefficient_of_natAbs_le_mul
    {value : Int} {consumed limit bound : Nat}
    (hvalue : value.natAbs ≤ consumed * bound)
    (hconsumed : consumed < limit)
    (hbound : 0 < bound)
    (hlimit : limit * bound = 2 ^ (width format - 1)) :
    OrdinaryCoefficient format value := by
  apply ordinaryCoefficient_of_natAbs_lt
  refine lt_of_le_of_lt hvalue ?_
  rw [← hlimit]
  exact Nat.mul_lt_mul_of_pos_right hconsumed hbound

/-! ## Fused product accumulation -/

/--
Loop invariant for exact product accumulation.

The accumulator denotes `value` and its coefficient magnitude is bounded by `consumed` product
bounds; after folding `pairs` with `consumed + pairs.length` below the product limit, the result
denotes `value` plus the exact sum of the products.
-/
theorem toRat?_foldMulAdd
    (pairs : List (FloatLib.Floats.Formats.Posit.Model format ×
      FloatLib.Floats.Formats.Posit.Model format))
    (products : List Rat)
    (hproducts : exactProducts? pairs = some products)
    (accumulator : Model format) (value : Rat) (consumed : Nat)
    (haccumulator : accumulator.toRat? = some value)
    (hcoefficient :
      accumulator.coefficient.natAbs ≤ consumed * productCoefficientBound format)
    (hlength : consumed + pairs.length < productSumTermLimit) :
    (foldMulAdd accumulator pairs).toRat? = some (value + products.sum) := by
  induction pairs generalizing products accumulator value consumed with
  | nil =>
      simp only [exactProducts?, Option.some.injEq] at hproducts
      subst hproducts
      simpa [foldMulAdd] using haccumulator
  | cons pair rest ih =>
      simp only [exactProducts?, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at hproducts
      obtain ⟨leftRat, hleft, rightRat, hright, rests, hrests, rfl⟩ := hproducts
      obtain ⟨leftDyadic, hleftDyadic, rfl⟩ :=
        exists_toDyadic?_eq_some_of_toRat?_eq_some pair.1 leftRat hleft
      obtain ⟨rightDyadic, hrightDyadic, rfl⟩ :=
        exists_toDyadic?_eq_some_of_toRat?_eq_some pair.2 rightRat hright
      obtain ⟨hnar, rfl⟩ := (toRat?_eq_some_iff accumulator value).mp haccumulator
      have hordinary : OrdinaryCoefficient format accumulator.coefficient :=
        (ordinaryCoefficient_iff_isNaR_eq_false accumulator).mpr hnar
      have hincrement :=
        natAbs_coefficientOfDyadic_mul_le_productCoefficientBound
          pair.1 pair.2 leftDyadic rightDyadic hleftDyadic hrightDyadic
      have hsum :
          (accumulator.coefficient +
              coefficientOfDyadic format
                (FloatLib.Numerics.Dyadic.mul leftDyadic rightDyadic)).natAbs ≤
            (consumed + 1) * productCoefficientBound format := by
        calc
          _ ≤ accumulator.coefficient.natAbs +
                (coefficientOfDyadic format
                  (FloatLib.Numerics.Dyadic.mul leftDyadic rightDyadic)).natAbs :=
            Int.natAbs_add_le _ _
          _ ≤ consumed * productCoefficientBound format +
                productCoefficientBound format :=
            Nat.add_le_add hcoefficient hincrement
          _ = (consumed + 1) * productCoefficientBound format := by ring
      have hlengthRest : consumed + 1 + rest.length < productSumTermLimit := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlength
      have hresult :=
        ordinaryCoefficient_of_natAbs_le_mul (format := format) hsum
          (by omega) (Nat.two_pow_pos _)
          (productSumTermLimit_mul_productCoefficientBound format)
      have hstep :=
        toRat?_qMulAdd_of_ordinary accumulator pair.1 pair.2 leftDyadic rightDyadic
          hleftDyadic hrightDyadic hordinary hresult
      have hstepCoefficient :=
        coefficient_qMulAdd_of_ordinary accumulator pair.1 pair.2 leftDyadic rightDyadic
          hleftDyadic hrightDyadic hordinary hresult
      simp only [foldMulAdd, List.foldl_cons] at ih ⊢
      rw [ih rests hrests (qMulAdd accumulator pair.1 pair.2) _ (consumed + 1) hstep
        (by rw [hstepCoefficient]; exact hsum) hlengthRest]
      rw [List.sum_cons, add_assoc]

/--
Fewer than `2^31` exact products of ordinary posits accumulate exactly from the zero quire.

`exactProducts? pairs = some products` says that no input is NaR and names the exact rational
products; the final quire is ordinary and denotes their sum with no rounding at any step.
-/
theorem toRat?_foldMulAdd_zero
    (pairs : List (FloatLib.Floats.Formats.Posit.Model format ×
      FloatLib.Floats.Formats.Posit.Model format))
    (products : List Rat)
    (hproducts : exactProducts? pairs = some products)
    (hlength : pairs.length < productSumTermLimit) :
    (foldMulAdd (zero format) pairs).toRat? = some products.sum := by
  have hfold :=
    toRat?_foldMulAdd pairs products hproducts (zero format) 0 0 (toRat?_zero format)
      (by simp) (by simpa using hlength)
  simpa using hfold

/-- Below the product limit, accumulating ordinary products never produces quire NaR. -/
theorem isNaR_foldMulAdd_zero
    (pairs : List (FloatLib.Floats.Formats.Posit.Model format ×
      FloatLib.Floats.Formats.Posit.Model format))
    (products : List Rat)
    (hproducts : exactProducts? pairs = some products)
    (hlength : pairs.length < productSumTermLimit) :
    (foldMulAdd (zero format) pairs).isNaR = false := by
  have hrat := toRat?_foldMulAdd_zero pairs products hproducts hlength
  rcases hnar : (foldMulAdd (zero format) pairs).isNaR with _ | _
  · rfl
  · rw [(toRat?_eq_none_iff _).mpr hnar] at hrat
    contradiction

/-! ## Posit accumulation -/

/--
Loop invariant for exact posit accumulation.

The accumulator denotes `value` and its coefficient magnitude is bounded by `consumed` posit
bounds; after folding `addends` with `consumed + addends.length` below the addend limit, the result
denotes `value` plus the exact sum of the addends.
-/
theorem toRat?_foldAddP
    (addends : List (FloatLib.Floats.Formats.Posit.Model format))
    (values : List Rat)
    (hvalues : exactValues? addends = some values)
    (accumulator : Model format) (value : Rat) (consumed : Nat)
    (haccumulator : accumulator.toRat? = some value)
    (hcoefficient :
      accumulator.coefficient.natAbs ≤ consumed * positCoefficientBound format)
    (hlength : consumed + addends.length < positSumTermLimit format) :
    (foldAddP accumulator addends).toRat? = some (value + values.sum) := by
  induction addends generalizing values accumulator value consumed with
  | nil =>
      simp only [exactValues?, Option.some.injEq] at hvalues
      subst hvalues
      simpa [foldAddP] using haccumulator
  | cons addend rest ih =>
      simp only [exactValues?, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at hvalues
      obtain ⟨addendRat, haddend, rests, hrests, rfl⟩ := hvalues
      obtain ⟨dyadic, hdyadic, rfl⟩ :=
        exists_toDyadic?_eq_some_of_toRat?_eq_some addend addendRat haddend
      obtain ⟨hnar, rfl⟩ := (toRat?_eq_some_iff accumulator value).mp haccumulator
      have hordinary : OrdinaryCoefficient format accumulator.coefficient :=
        (ordinaryCoefficient_iff_isNaR_eq_false accumulator).mpr hnar
      have hincrement :=
        natAbs_coefficientOfDyadic_le_positCoefficientBound addend dyadic hdyadic
      have hsum :
          (accumulator.coefficient + coefficientOfDyadic format dyadic).natAbs ≤
            (consumed + 1) * positCoefficientBound format := by
        calc
          _ ≤ accumulator.coefficient.natAbs +
                (coefficientOfDyadic format dyadic).natAbs :=
            Int.natAbs_add_le _ _
          _ ≤ consumed * positCoefficientBound format + positCoefficientBound format :=
            Nat.add_le_add hcoefficient hincrement
          _ = (consumed + 1) * positCoefficientBound format := by ring
      have hlengthRest : consumed + 1 + rest.length < positSumTermLimit format := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlength
      have hresult :=
        ordinaryCoefficient_of_natAbs_le_mul (format := format) hsum
          (by omega) (Nat.two_pow_pos _)
          (positSumTermLimit_mul_positCoefficientBound format)
      have hstep :=
        toRat?_qAddP_of_ordinary accumulator addend dyadic hdyadic hordinary hresult
      have hstepCoefficient :=
        coefficient_qAddP_of_ordinary accumulator addend dyadic hdyadic hordinary hresult
      simp only [foldAddP, List.foldl_cons] at ih ⊢
      rw [ih rests hrests (qAddP accumulator addend) _ (consumed + 1) hstep
        (by rw [hstepCoefficient]; exact hsum) hlengthRest]
      rw [List.sum_cons, add_assoc]

/--
Fewer than `2^(23 + 4n)` ordinary posits accumulate exactly from the zero quire.

`exactValues? addends = some values` says that no input is NaR and names the exact rational
addends; the final quire is ordinary and denotes their sum.
-/
theorem toRat?_foldAddP_zero
    (addends : List (FloatLib.Floats.Formats.Posit.Model format))
    (values : List Rat)
    (hvalues : exactValues? addends = some values)
    (hlength : addends.length < positSumTermLimit format) :
    (foldAddP (zero format) addends).toRat? = some values.sum := by
  have hfold :=
    toRat?_foldAddP addends values hvalues (zero format) 0 0 (toRat?_zero format)
      (by simp) (by simpa using hlength)
  simpa using hfold

/-- Below the addend limit, accumulating ordinary posits never produces quire NaR. -/
theorem isNaR_foldAddP_zero
    (addends : List (FloatLib.Floats.Formats.Posit.Model format))
    (values : List Rat)
    (hvalues : exactValues? addends = some values)
    (hlength : addends.length < positSumTermLimit format) :
    (foldAddP (zero format) addends).isNaR = false := by
  have hrat := toRat?_foldAddP_zero addends values hvalues hlength
  rcases hnar : (foldAddP (zero format) addends).isNaR with _ | _
  · rfl
  · rw [(toRat?_eq_none_iff _).mpr hnar] at hrat
    contradiction

end FloatLib.Floats.Formats.Posit.Quire.Model
