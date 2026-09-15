/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Quire.Model.Core
public import FloatLib.Numerics.Representations.FixedInt.Semantics.Basic

/-!
# Correctness of the standard posit quire model

The standard quire model has raw-word round-trip laws, an exact characterization of the reserved
NaR word, ordinary coefficient bounds, and rational semantics for integer dyadic conversion.

## References

* Posit Working Group, *Standard for Posit Arithmetic (2022)*, March 2, 2022,
  Sections 3.4 and 5.11, <https://posithub.org/docs/posit_standard-2.pdf>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Quire

open FloatLib.Numerics
open FloatLib.Numerics.Representations

/-- The quire width is positive for every valid posit descriptor. -/
theorem width_pos (format : Format) : 0 < width format := by
  unfold width
  have := format.bits_ge_two
  omega

namespace Model

variable {format : Format}

/-- Re-encoding a quire's complete bit pattern preserves it. -/
@[simp] theorem ofNatBits_toNatBits (value : Model format) :
    ofNatBits format value.toNatBits = value := by
  cases value with
  | mk word =>
      simp [ofNatBits, toNatBits]

/-- An in-range unsigned word is unchanged by standard-quire encoding. -/
@[simp] theorem toNatBits_ofNatBits_of_lt (format : Format) (bits : Nat)
    (bits_lt : bits < 2 ^ width format) :
    (ofNatBits format bits).toNatBits = bits := by
  simpa [ofNatBits, toNatBits] using
    FixedInt.toNatBits_ofNatBits_of_lt
      (width := width format) bits bits_lt

/-- The canonical zero quire has integer coefficient zero. -/
@[simp] theorem coefficient_zero (format : Format) :
    (zero format).coefficient = 0 := by
  simp [zero, coefficient, FixedInt.toInt_ofInt]

/-- The canonical NaR quire uses the reserved sign-bit coefficient. -/
@[simp] theorem coefficient_nar (format : Format) :
    (nar format).coefficient = FixedInt.minValue (width format) := by
  simp [nar, coefficient]

/-- Zero and quire NaR are distinct at every valid posit width. -/
theorem zero_ne_nar (format : Format) : zero format ≠ nar format := by
  intro equality
  have coefficients := congrArg coefficient equality
  simp only [coefficient_zero, coefficient_nar] at coefficients
  rw [FixedInt.minValue_eq (width_pos format)] at coefficients
  have hpower : (0 : Int) < 2 ^ (width format - 1) :=
    Int.pow_pos (by decide)
  omega

/-- The quire NaR predicate recognizes the canonical NaR value. -/
@[simp] theorem isNaR_nar (format : Format) :
    isNaR (nar format) = true := by
  simp [isNaR]

/-- The canonical zero quire is not NaR. -/
@[simp] theorem isNaR_zero (format : Format) :
    isNaR (zero format) = false := by
  simp [isNaR, zero_ne_nar]

/-- The executable NaR test recognizes exactly the reserved word. -/
@[simp] theorem isNaR_eq_true_iff (value : Model format) :
    value.isNaR = true ↔ value = nar format := by
  simp [isNaR]

/-- A quire word equals NaR exactly when its signed coefficient is the reserved minimum. -/
theorem eq_nar_iff_coefficient_eq_min (value : Model format) :
    value = nar format ↔
      value.coefficient = FixedInt.minValue (width format) := by
  constructor
  · intro hvalue
    subst value
    exact coefficient_nar format
  · intro hcoefficient
    have hword : value.word = (nar format).word := by
      rw [← FixedInt.ofInt_toInt value.word]
      change FixedInt.ofInt value.coefficient = (nar format).word
      rw [hcoefficient, ← coefficient_nar format]
      exact FixedInt.ofInt_toInt (nar format).word
    cases value with
    | mk word =>
        change word = (nar format).word at hword
        cases hword
        rfl

/-- Every stored quire coefficient lies in the inclusive signed range of its physical word. -/
theorem coefficient_in_fixedRange (value : Model format) :
    FixedInt.InRange (width format) value.coefficient := by
  constructor
  · exact BitVec.toInt_intMin_le value.word.bits
  · rw [FixedInt.maxValue_eq]
    exact BitVec.toInt_le

/-- A coefficient is ordinary exactly when the quire word is not the reserved NaR code. -/
theorem ordinaryCoefficient_iff_isNaR_eq_false (value : Model format) :
    OrdinaryCoefficient format value.coefficient ↔ value.isNaR = false := by
  constructor
  · intro hordinary
    apply Bool.eq_false_iff.mpr
    intro hnar
    have hvalue : value = nar format :=
      (isNaR_eq_true_iff value).mp hnar
    subst value
    simpa using hordinary.1
  · intro hordinary
    have hrange := coefficient_in_fixedRange value
    refine ⟨lt_of_le_of_ne hrange.1 ?_, hrange.2⟩
    intro hequal
    have hvalue : value = nar format :=
      (eq_nar_iff_coefficient_eq_min value).mpr hequal.symm
    have hnar : value.isNaR = true :=
      (isNaR_eq_true_iff value).mpr hvalue
    rw [hordinary] at hnar
    contradiction

/-- Negation preserves the set of ordinary quire coefficients. -/
theorem ordinaryCoefficient_neg
    {value : Int} (hvalue : OrdinaryCoefficient format value) :
    OrdinaryCoefficient format (-value) := by
  rw [OrdinaryCoefficient, FixedInt.minValue_eq (width_pos format),
    FixedInt.maxValue_eq] at hvalue ⊢
  have hpower : (0 : Int) < 2 ^ (width format - 1) :=
    Int.pow_pos (by decide)
  omega

/--
Any integer whose absolute magnitude is below the positive half-range is an ordinary quire
coefficient.

The strict bound excludes both signed overflow and the reserved most-negative NaR word.
-/
theorem ordinaryCoefficient_of_natAbs_lt
    {value : Int}
    (hvalue : value.natAbs < 2 ^ (width format - 1)) :
    OrdinaryCoefficient format value := by
  rw [OrdinaryCoefficient, FixedInt.minValue_eq (width_pos format),
    FixedInt.maxValue_eq]
  have hcast :
      (value.natAbs : Int) < (2 : Int) ^ (width format - 1) := by
    exact_mod_cast hvalue
  have hlower : -(value.natAbs : Int) ≤ value := by
    have habsolute : -value ≤ (value.natAbs : Int) := by
      simpa using Int.le_natAbs (a := -value)
    simpa using neg_le_neg habsolute
  have hupper : value ≤ (value.natAbs : Int) :=
    Int.le_natAbs
  constructor
  · exact lt_of_lt_of_le (neg_lt_neg hcast) hlower
  · omega

/-- Encoding an ordinary coefficient preserves it exactly. -/
theorem coefficient_ofCoefficient_of_ordinary
    {value : Int} (hvalue : OrdinaryCoefficient format value) :
    (ofCoefficient format value).coefficient = value := by
  unfold ofCoefficient
  rw [if_pos hvalue]
  apply FixedInt.toInt_ofInt_eq_self (width_pos format)
  exact ⟨le_of_lt hvalue.1, hvalue.2⟩

/-- A coefficient outside the ordinary range, including the reserved minimum, becomes NaR. -/
theorem ofCoefficient_eq_nar_of_not_ordinary
    {value : Int} (hvalue : ¬OrdinaryCoefficient format value) :
    ofCoefficient format value = nar format := by
  simp [ofCoefficient, hvalue]

/-- Dyadic-to-quire scaling preserves exact value when the stored exponent is high enough. -/
theorem coefficientOfDyadic_denotes
    (format : Format) (value : FloatLib.Numerics.Dyadic)
    (hscale : scaleExponent format ≤ value.exponent) :
    Rat.ofInt (coefficientOfDyadic format value) *
        (2 : Rat) ^ scaleExponent format =
      value.toRat := by
  have hdifference :
      value.exponent - scaleExponent format =
        Int.ofNat (Int.toNat (value.exponent - scaleExponent format)) := by
    exact (Int.toNat_of_nonneg (sub_nonneg.mpr hscale)).symm
  have hexponent :
      value.exponent =
        scaleExponent format +
          Int.ofNat (Int.toNat (value.exponent - scaleExponent format)) := by
    omega
  rw [FloatLib.Numerics.Dyadic.toRat, hexponent,
    zpow_add₀ (by norm_num : (2 : Rat) ≠ 0)]
  simp only [coefficientOfDyadic, Rat.ofInt_eq_cast, Int.cast_mul,
    Int.cast_pow, Int.cast_ofNat]
  rw [Int.ofNat_eq_natCast, zpow_natCast]
  ac_rfl

end Model
end FloatLib.Floats.Formats.Posit.Quire
