/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Quire.Arithmetic.Runtime
public import FloatLib.Floats.Formats.Posit.Quire.Arithmetic.Proof
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Zify

/-!
# Standard posit quire capacity

The Posit Standard (2022) `16n`-bit quire satisfies two finite-term capacity guarantees:

* fewer than `2^(23 + 4n)` ordinary posit addends cannot overflow the associated quire; and
* fewer than `2^31` exact products of two ordinary posits cannot overflow it.

The proof first bounds one posit relative to `minPos`, then transports that bound to the quire's
fixed scale. A list-level absolute-value argument proves that every signed sum within the stated
exclusive term limit remains an `OrdinaryCoefficient`, excluding both two's-complement overflow
and the reserved quire-NaR word.

`Accumulation` applies these coefficient bounds to the executable accumulation loops.

## References

* Posit Working Group, *Standard for Posit Arithmetic (2022)*, March 2, 2022,
  Sections 3.4 and 5.11, <https://posithub.org/docs/posit_standard-2.pdf>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Quire.Model

open FloatLib.Numerics

variable {format : Format}

private def minPosUnitCoefficient
    (format : Format) (value : FloatLib.Numerics.Dyadic) : Nat :=
  value.significand *
    2 ^ Int.toNat
      (value.exponent -
        (FloatLib.Floats.Formats.Posit.Model.DyadicRounding.minPositive
          format).exponent)

/-- The smallest positive posit exponent, written in terms of the total width. -/
private theorem minPositive_exponent_eq (format : Format) :
    (FloatLib.Floats.Formats.Posit.Model.DyadicRounding.minPositive format).exponent =
      -(4 * ((format.bits : Int) - 2)) := by
  rw [FloatLib.Floats.Formats.Posit.Model.DyadicRounding.minPositive_eq_fields]
  have hbits := format.bits_ge_two
  simp only [Format.payloadBits, Int.ofNat_eq_natCast]
  omega

private theorem decodeFields_significand_lt_two_pow_succ_fractionBits
    (value : FloatLib.Floats.Formats.Posit.Model format) :
    value.decodeFields.significand <
      2 ^ (value.fractionBits + 1) := by
  have hfraction :
      value.fractionField < 2 ^ value.fractionBits := by
    unfold FloatLib.Floats.Formats.Posit.Model.fractionField
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  change
    2 ^ value.fractionBits + value.fractionField <
      2 ^ (value.fractionBits + 1)
  rw [Nat.pow_succ]
  omega

/-- A word whose regime fills the payload has no exponent or fraction bits, so its scale is a
multiple of four bounded by the `maxpos` scale. -/
private theorem scale_le_and_fractionBits_eq_zero_of_regimeRunLength_eq_payloadBits
    (value : FloatLib.Floats.Formats.Posit.Model format)
    (hfull : value.regimeRunLength = format.payloadBits) :
    value.scale ≤ 4 * ((format.bits : Int) - 2) ∧ value.fractionBits = 0 := by
  have htrailing : value.trailingBits = 0 := by
    unfold FloatLib.Floats.Formats.Posit.Model.trailingBits
    rw [hfull]
    simp
  have hfractionBits : value.fractionBits = 0 := by
    unfold FloatLib.Floats.Formats.Posit.Model.fractionBits
    rw [htrailing]
    simp
  have hexponent : value.exponentField = 0 := by
    have hused : value.usedExponentBits = 0 := by
      simp [FloatLib.Floats.Formats.Posit.Model.usedExponentBits, htrailing]
    simp [FloatLib.Floats.Formats.Posit.Model.exponentField,
      FloatLib.Floats.Formats.Posit.Model.storedExponentField, hused, Nat.mod_one]
  have hbits := format.bits_ge_two
  refine ⟨?_, hfractionBits⟩
  unfold FloatLib.Floats.Formats.Posit.Model.scale
    FloatLib.Floats.Formats.Posit.Model.regimeValue Format.payloadBits at *
  simp only [Format.regimeExponentStep, hexponent, hfractionBits, Int.ofNat_eq_natCast]
  split <;> omega

/-- A word with a regime terminator leaves its scale plus fraction width strictly below the
`maxpos` scale. -/
private theorem scale_add_fractionBits_lt_of_regimeRunLength_lt_payloadBits
    (value : FloatLib.Floats.Formats.Posit.Model format)
    (hlt : value.regimeRunLength < format.payloadBits) :
    value.scale + value.fractionBits + 1 ≤ 4 * ((format.bits : Int) - 2) := by
  have hexponent := value.exponentField_lt_four
  have hpos := value.regimeRunLength_pos
  have hbits := format.bits_ge_two
  unfold FloatLib.Floats.Formats.Posit.Model.scale
    FloatLib.Floats.Formats.Posit.Model.regimeValue Format.payloadBits at *
  simp only [Format.regimeExponentStep, Int.ofNat_eq_natCast]
  split <;> omega

/-- Every ordinary posit magnitude is at most `2^(8(n-2))` units of `minPos`. -/
private theorem minPosUnitCoefficient_le
    (value : FloatLib.Floats.Formats.Posit.Model format)
    (dyadic : FloatLib.Numerics.Dyadic)
    (hvalue : value.toDyadic? = some dyadic) :
    minPosUnitCoefficient format dyadic ≤
      2 ^ (8 * (format.bits - 2)) := by
  unfold FloatLib.Floats.Formats.Posit.Model.toDyadic? at hvalue
  cases hdecode : value.decodeExact with
  | zero =>
      simp only [hdecode] at hvalue
      injection hvalue with hdyadic
      subst dyadic
      simp [minPosUnitCoefficient, FloatLib.Numerics.Dyadic.zero]
  | finite fields =>
      simp only [hdecode] at hvalue
      injection hvalue with hdyadic
      subst dyadic
      obtain ⟨hnar, hzero, rfl⟩ :=
        (FloatLib.Floats.Formats.Posit.Model.decodeExact_eq_finite_iff
          value fields).mp hdecode
      have hminExponent :=
        FloatLib.Floats.Formats.Posit.Model.DyadicRounding.minPositive_exponent_le_scale_of_not_special
          value hzero hnar
      have hmin := minPositive_exponent_eq format
      have hbits := format.bits_ge_two
      have hsignificand :=
        decodeFields_significand_lt_two_pow_succ_fractionBits value
      unfold minPosUnitCoefficient
      change
        value.decodeFields.significand *
            2 ^ Int.toNat
              (value.scale -
                (FloatLib.Floats.Formats.Posit.Model.DyadicRounding.minPositive
                  format).exponent) ≤
          2 ^ (8 * (format.bits - 2))
      rcases lt_or_eq_of_le value.regimeRunLength_le_payload with hlt | hfull
      · have hscale :=
          scale_add_fractionBits_lt_of_regimeRunLength_lt_payloadBits value hlt
        calc
          value.decodeFields.significand *
                2 ^ Int.toNat
                  (value.scale -
                    (FloatLib.Floats.Formats.Posit.Model.DyadicRounding.minPositive
                      format).exponent) ≤
              2 ^ (value.fractionBits + 1 +
                Int.toNat
                  (value.scale -
                    (FloatLib.Floats.Formats.Posit.Model.DyadicRounding.minPositive
                      format).exponent)) := by
            rw [Nat.pow_add]
            exact Nat.mul_le_mul_right _ hsignificand.le
          _ ≤ 2 ^ (8 * (format.bits - 2)) :=
            Nat.pow_le_pow_right (by decide) (by omega)
      · obtain ⟨hscale, hfractionBits⟩ :=
          scale_le_and_fractionBits_eq_zero_of_regimeRunLength_eq_payloadBits value hfull
        have hsignificandEq : value.decodeFields.significand = 1 := by
          have hfraction :
              value.fractionField < 2 ^ value.fractionBits := by
            unfold FloatLib.Floats.Formats.Posit.Model.fractionField
            exact Nat.mod_lt _ (Nat.two_pow_pos _)
          change 2 ^ value.fractionBits + value.fractionField = 1
          rw [hfractionBits] at hfraction ⊢
          omega
        rw [hsignificandEq, Nat.one_mul]
        exact Nat.pow_le_pow_right (by decide) (by omega)
  | nar =>
      simp only [hdecode] at hvalue
      contradiction

/--
Exclusive upper bound on the number of ordinary posit addends guaranteed to fit in a standard
quire.
-/
def positSumTermLimit (format : Format) : Nat :=
  2 ^ (23 + 4 * format.bits)

/--
Exclusive upper bound on the number of exact posit products guaranteed to fit in a standard
quire.
-/
def productSumTermLimit : Nat :=
  2 ^ 31

/-- Uniform quire-coefficient magnitude bound for one ordinary posit. -/
def positCoefficientBound (format : Format) : Nat :=
  2 ^ (12 * (format.bits - 2))

/-- Uniform quire-coefficient magnitude bound for one exact product of two ordinary posits. -/
def productCoefficientBound (format : Format) : Nat :=
  2 ^ (16 * (format.bits - 2))

/-- One ordinary posit contributes at most `2^(12(n-2))` quire coefficient units. -/
theorem natAbs_coefficientOfDyadic_le_positCoefficientBound
    (value : FloatLib.Floats.Formats.Posit.Model format)
    (dyadic : FloatLib.Numerics.Dyadic)
    (hvalue : value.toDyadic? = some dyadic) :
    (coefficientOfDyadic format dyadic).natAbs ≤
      positCoefficientBound format := by
  have hminExponent :=
    minPositive_exponent_le_exponent_of_toDyadic?_eq_some
      value dyadic hvalue
  have hscale :=
    scaleExponent_le_exponent_of_toDyadic?_eq_some
      value dyadic hvalue
  have hmin := minPositive_exponent_eq format
  have hshift :
      Int.toNat (dyadic.exponent - scaleExponent format) =
        Int.toNat
            (dyadic.exponent -
              (FloatLib.Floats.Formats.Posit.Model.DyadicRounding.minPositive
                format).exponent) +
          4 * (format.bits - 2) := by
    have hshiftInt :
        (Int.toNat (dyadic.exponent - scaleExponent format) : Int) =
          Int.toNat
              (dyadic.exponent -
                (FloatLib.Floats.Formats.Posit.Model.DyadicRounding.minPositive
                  format).exponent) +
            4 * Int.ofNat (format.bits - 2) := by
      rw [Int.toNat_of_nonneg (sub_nonneg.mpr hscale),
        Int.toNat_of_nonneg (sub_nonneg.mpr hminExponent),
        scaleExponent_eq_two_mul_minPositive_exponent, hmin]
      have hbits := format.bits_ge_two
      simp only [Int.ofNat_eq_natCast]
      omega
    apply Int.ofNat_inj.mp
    push_cast
    exact hshiftInt
  rw [coefficientOfDyadic, Int.natAbs_mul,
    FloatLib.Numerics.Dyadic.natAbs_signedSignificand, hshift]
  simp only [Int.natAbs_pow]
  norm_num only [Int.natAbs_of_nonneg]
  unfold positCoefficientBound
  rw [Nat.pow_add, ← Nat.mul_assoc]
  rw [show 12 * (format.bits - 2) =
      8 * (format.bits - 2) + 4 * (format.bits - 2) by omega,
    Nat.pow_add]
  exact Nat.mul_le_mul_right _ (minPosUnitCoefficient_le value dyadic hvalue)

/--
One exact product of two ordinary posits contributes at most `2^(16(n-2))` quire coefficient
units.
-/
theorem natAbs_coefficientOfDyadic_mul_le_productCoefficientBound
    (left right : FloatLib.Floats.Formats.Posit.Model format)
    (leftDyadic rightDyadic : FloatLib.Numerics.Dyadic)
    (hleft : left.toDyadic? = some leftDyadic)
    (hright : right.toDyadic? = some rightDyadic) :
    (coefficientOfDyadic format
        (FloatLib.Numerics.Dyadic.mul leftDyadic rightDyadic)).natAbs ≤
      productCoefficientBound format := by
  have hleftExponent :=
    minPositive_exponent_le_exponent_of_toDyadic?_eq_some
      left leftDyadic hleft
  have hrightExponent :=
    minPositive_exponent_le_exponent_of_toDyadic?_eq_some
      right rightDyadic hright
  have hscale :=
    scaleExponent_le_mul_exponent_of_toDyadic?_eq_some
      left right leftDyadic rightDyadic hleft hright
  have hshift :
      Int.toNat
          ((FloatLib.Numerics.Dyadic.mul leftDyadic rightDyadic).exponent -
            scaleExponent format) =
        Int.toNat
            (leftDyadic.exponent -
              (FloatLib.Floats.Formats.Posit.Model.DyadicRounding.minPositive
                format).exponent) +
          Int.toNat
            (rightDyadic.exponent -
              (FloatLib.Floats.Formats.Posit.Model.DyadicRounding.minPositive
                format).exponent) := by
    have hshiftInt :
        (Int.toNat
            ((FloatLib.Numerics.Dyadic.mul leftDyadic rightDyadic).exponent -
              scaleExponent format) : Int) =
          Int.toNat
              (leftDyadic.exponent -
                (FloatLib.Floats.Formats.Posit.Model.DyadicRounding.minPositive
                  format).exponent) +
            Int.toNat
              (rightDyadic.exponent -
                (FloatLib.Floats.Formats.Posit.Model.DyadicRounding.minPositive
                  format).exponent) := by
      rw [Int.toNat_of_nonneg (sub_nonneg.mpr hscale),
        Int.toNat_of_nonneg (sub_nonneg.mpr hleftExponent),
        Int.toNat_of_nonneg (sub_nonneg.mpr hrightExponent),
        scaleExponent_eq_two_mul_minPositive_exponent]
      simp only [FloatLib.Numerics.Dyadic.mul,
        FloatLib.Numerics.Dyadic.mulFields]
      ring
    apply Int.ofNat_inj.mp
    push_cast
    exact hshiftInt
  rw [coefficientOfDyadic, Int.natAbs_mul,
    FloatLib.Numerics.Dyadic.natAbs_signedSignificand, hshift]
  simp only [Int.natAbs_pow]
  norm_num only [Int.natAbs_of_nonneg]
  simp only [FloatLib.Numerics.Dyadic.mul,
    FloatLib.Numerics.Dyadic.mulFields, Nat.pow_add]
  unfold productCoefficientBound
  calc
    leftDyadic.significand * rightDyadic.significand *
          (2 ^ Int.toNat
              (leftDyadic.exponent -
                (FloatLib.Floats.Formats.Posit.Model.DyadicRounding.minPositive
                  format).exponent) *
            2 ^ Int.toNat
              (rightDyadic.exponent -
                (FloatLib.Floats.Formats.Posit.Model.DyadicRounding.minPositive
                  format).exponent)) =
        minPosUnitCoefficient format leftDyadic *
          minPosUnitCoefficient format rightDyadic := by
            unfold minPosUnitCoefficient
            ring
    _ ≤
        2 ^ (8 * (format.bits - 2)) *
          2 ^ (8 * (format.bits - 2)) :=
      Nat.mul_le_mul
        (minPosUnitCoefficient_le left leftDyadic hleft)
        (minPosUnitCoefficient_le right rightDyadic hright)
    _ = 2 ^ (16 * (format.bits - 2)) := by
      rw [← Nat.pow_add]
      congr 1
      omega

private theorem natAbs_list_sum_le_length_mul
    (values : List Int) (bound : Nat)
    (hvalue : ∀ value ∈ values, value.natAbs ≤ bound) :
    values.sum.natAbs ≤ values.length * bound := by
  induction values with
  | nil =>
      simp
  | cons head tail ih =>
      have hhead : head.natAbs ≤ bound :=
        hvalue head (by simp)
      have htail : ∀ value ∈ tail, value.natAbs ≤ bound := by
        intro value hmembership
        exact hvalue value (by simp [hmembership])
      calc
        (head :: tail).sum.natAbs =
            (head + tail.sum).natAbs := by simp
        _ ≤ head.natAbs + tail.sum.natAbs :=
          Int.natAbs_add_le head tail.sum
        _ ≤ bound + tail.length * bound :=
          Nat.add_le_add hhead (ih htail)
        _ = (head :: tail).length * bound := by
          simp [Nat.succ_mul, Nat.add_comm]

/--
Any coefficient list shorter than the ordinary-addend limit has an ordinary sum,
provided each term satisfies the uniform posit coefficient bound.
-/
theorem ordinaryCoefficient_sum_of_length_lt_positSumTermLimit
    (coefficients : List Int)
    (hcoefficient :
      ∀ coefficient ∈ coefficients,
        coefficient.natAbs ≤ positCoefficientBound format)
    (hlength : coefficients.length < positSumTermLimit format) :
    OrdinaryCoefficient format coefficients.sum := by
  apply ordinaryCoefficient_of_natAbs_lt
  have hsum :=
    natAbs_list_sum_le_length_mul
      coefficients (positCoefficientBound format) hcoefficient
  refine lt_of_le_of_lt hsum ?_
  have hstrict :
      coefficients.length * positCoefficientBound format <
        positSumTermLimit format * positCoefficientBound format :=
    Nat.mul_lt_mul_of_pos_right hlength
      (by exact Nat.two_pow_pos _)
  refine lt_of_lt_of_eq hstrict ?_
  unfold positSumTermLimit positCoefficientBound width
  rw [← Nat.pow_add]
  congr 1
  have hbits := format.bits_ge_two
  omega

/--
Any coefficient list shorter than the exact-product limit has an ordinary sum,
provided each term satisfies the uniform product coefficient bound.
-/
theorem ordinaryCoefficient_sum_of_length_lt_productSumTermLimit
    (coefficients : List Int)
    (hcoefficient :
      ∀ coefficient ∈ coefficients,
        coefficient.natAbs ≤ productCoefficientBound format)
    (hlength : coefficients.length < productSumTermLimit) :
    OrdinaryCoefficient format coefficients.sum := by
  apply ordinaryCoefficient_of_natAbs_lt
  have hsum :=
    natAbs_list_sum_le_length_mul
      coefficients (productCoefficientBound format) hcoefficient
  refine lt_of_le_of_lt hsum ?_
  have hstrict :
      coefficients.length * productCoefficientBound format <
        productSumTermLimit * productCoefficientBound format :=
    Nat.mul_lt_mul_of_pos_right hlength
      (by exact Nat.two_pow_pos _)
  refine lt_of_lt_of_eq hstrict ?_
  unfold productSumTermLimit productCoefficientBound width
  rw [← Nat.pow_add]
  congr 1
  have hbits := format.bits_ge_two
  omega

end FloatLib.Floats.Formats.Posit.Quire.Model
