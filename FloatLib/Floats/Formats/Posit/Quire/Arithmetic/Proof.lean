/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Quire.Arithmetic.Runtime
public import FloatLib.Floats.Formats.Posit.Quire.Semantics.Proof
public import FloatLib.Floats.Formats.Posit.Rounding.Dyadic.Proof
public import FloatLib.Floats.Formats.Posit.Semantics.Exact.Proof

import FloatLib.Numerics.Exact.Dyadic.Order

/-!
# Correctness of standard posit quire operations

The executable quire operations agree with their exact coefficient, dyadic, and rational
semantics. The refinement theorems cover these operations from Posit Standard (2022), §5.11:

* `pToQ`;
* `qNegate` and `qAbs`;
* `qAddP` and `qSubP`;
* `qAddQ` and `qSubQ`;
* `qMulAdd` and `qMulSub`; and
* `qToP`.

For each accumulation and quire-quire operation there are three kinds of result: on ordinary
inputs whose exact coefficient stays ordinary, the stored coefficient and the rational value are
exact (`coefficient_*_of_ordinary`, `toRat?_*_of_ordinary`); an exact coefficient outside the
ordinary range gives quire NaR (`*_eq_nar_of_not_ordinary`); and every NaR input gives quire NaR
(the `*_nar_*` simp lemmas).

The runtime definitions live in `Arithmetic.Runtime`. Keeping the refinement layer separate lets
execution-only clients use the integer and dyadic kernels without importing the full proof graph.

## References

* Posit Working Group, *Standard for Posit Arithmetic (2022)*, March 2, 2022,
  Section 5.11, <https://posithub.org/docs/posit_standard-2.pdf>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Quire.Model

open FloatLib.Numerics

variable {format : Format}

/-- Converting posit NaR to a quire produces quire NaR. -/
@[simp] theorem pToQ_nar (format : Format) :
    pToQ (FloatLib.Floats.Formats.Posit.Model.nar format) = nar format := by
  simp [pToQ]

/-- Zero is an ordinary quire coefficient. -/
private theorem ordinaryCoefficient_zero : OrdinaryCoefficient format 0 :=
  ordinaryCoefficient_of_natAbs_lt (by simp)

/-- Converting posit zero to a quire produces quire zero. -/
@[simp] theorem pToQ_zero (format : Format) :
    pToQ (FloatLib.Floats.Formats.Posit.Model.zero format) = zero format := by
  simp [pToQ, coefficientOfDyadic, FloatLib.Numerics.Dyadic.zero,
    FloatLib.Numerics.Dyadic.signedSignificand, ofCoefficient, ordinaryCoefficient_zero, zero]

/-- Quire negation fixes NaR. -/
@[simp] theorem qNegate_nar (format : Format) :
    qNegate (nar format) = nar format := by
  simp [qNegate]

/-- Quire negation fixes zero. -/
@[simp] theorem qNegate_zero (format : Format) :
    qNegate (zero format) = zero format := by
  unfold qNegate
  rw [isNaR_zero]
  simp only [Bool.false_eq_true, ite_false, coefficient_zero, neg_zero]
  simp [ofCoefficient, ordinaryCoefficient_zero, zero]

/-- Quire absolute value fixes NaR. -/
@[simp] theorem qAbs_nar (format : Format) :
    qAbs (nar format) = nar format := by
  simp [qAbs]

/-- Quire absolute value fixes zero. -/
@[simp] theorem qAbs_zero (format : Format) :
    qAbs (zero format) = zero format := by
  simp [qAbs]

/-- NaR propagates from the left operand of quire addition. -/
@[simp] theorem qAddQ_nar_left (format : Format) (right : Model format) :
    qAddQ (nar format) right = nar format := by
  simp [qAddQ]

/-- NaR propagates from the right operand of quire addition. -/
@[simp] theorem qAddQ_nar_right (format : Format) (left : Model format) :
    qAddQ left (nar format) = nar format := by
  simp [qAddQ]

/-- NaR propagates from the left operand of quire subtraction. -/
@[simp] theorem qSubQ_nar_left (format : Format) (right : Model format) :
    qSubQ (nar format) right = nar format := by
  simp [qSubQ]

/-- NaR propagates from the right operand of quire subtraction. -/
@[simp] theorem qSubQ_nar_right (format : Format) (left : Model format) :
    qSubQ left (nar format) = nar format := by
  simp [qSubQ]

/-- Converting quire NaR back to a posit produces posit NaR. -/
@[simp] theorem qToP_nar (format : Format) :
    qToP (nar format) = FloatLib.Floats.Formats.Posit.Model.nar format := by
  simp [qToP]

/-- Converting quire zero back to a posit produces posit zero. -/
@[simp] theorem qToP_zero (format : Format) :
    qToP (zero format) = FloatLib.Floats.Formats.Posit.Model.zero format := by
  simp [qToP, FloatLib.Numerics.Dyadic.ofScaledInt,
    FloatLib.Floats.Formats.Posit.Model.DyadicRounding.round]

/-! ## Exact coefficient and rational refinement theorems -/

/--
The standard quire scale is no greater than the decoded scale of any nonzero finite posit.

For widths of at least three this follows from the format-wide regime bound. The two-bit standard
format is the only arithmetic boundary case: its two ordinary nonzero words are `1` and `-1`, both
at scale zero.
-/
theorem scaleExponent_le_scale_of_not_special
    (value : FloatLib.Floats.Formats.Posit.Model format)
    (hzero : value.isZero = false)
    (hnar : value.isNaR = false) :
    scaleExponent format ≤ value.scale := by
  by_cases hthree : 3 ≤ format.bits
  · have hpayload : format.payloadBits + 1 = format.bits := by
      simpa only [Format.payloadBits] using
        Nat.sub_add_cancel
          (Nat.le_trans (by decide : 1 ≤ 2) format.bits_ge_two)
    have hpayloadInt :
        (format.payloadBits : Int) + 1 = format.bits := by
      exact_mod_cast hpayload
    have hthreeInt : (3 : Int) ≤ format.bits := by
      exact_mod_cast hthree
    apply le_trans ?_
      (FloatLib.Floats.Formats.Posit.Model.neg_four_payloadBits_le_scale value)
    unfold scaleExponent
    simp only [Int.ofNat_eq_natCast]
    omega
  · have hbits : format.bits = 2 := by
      have hminimum := format.bits_ge_two
      omega
    rcases
        FloatLib.Floats.Formats.Posit.Model.zero_or_nar_or_scale_eq_zero_of_bits_eq_two
          value hbits with
      hvalue | hvalue | hscale
    · subst value
      simp at hzero
    · subst value
      simp at hnar
    · rw [hscale]
      simp [scaleExponent, hbits]

/--
A successful exact decoding is either the zero dyadic or the decoded fields of a word that is
neither zero nor NaR.
-/
private theorem toDyadic?_eq_some_cases
    {value : FloatLib.Floats.Formats.Posit.Model format}
    {dyadic : FloatLib.Numerics.Dyadic}
    (hvalue : value.toDyadic? = some dyadic) :
    dyadic = FloatLib.Numerics.Dyadic.zero ∨
      (value.isNaR = false ∧ value.isZero = false ∧
        dyadic = value.decodeFields.toDyadic) := by
  unfold FloatLib.Floats.Formats.Posit.Model.toDyadic? at hvalue
  cases hdecode : value.decodeExact with
  | zero =>
      simp only [hdecode] at hvalue
      injection hvalue with hdyadic
      exact Or.inl hdyadic.symm
  | finite fields =>
      simp only [hdecode] at hvalue
      injection hvalue with hdyadic
      obtain ⟨hnar, hzero, hfields⟩ :=
        (FloatLib.Floats.Formats.Posit.Model.decodeExact_eq_finite_iff
          value fields).mp hdecode
      subst fields
      exact Or.inr ⟨hnar, hzero, hdyadic.symm⟩
  | nar =>
      simp only [hdecode] at hvalue
      contradiction

/--
Every ordinary posit dyadic aligns exactly with the least-significant bit of its associated quire.

This supplies the conversion kernel's scale condition at every width, including the two-bit
boundary format.
-/
theorem scaleExponent_le_exponent_of_toDyadic?_eq_some
    (value : FloatLib.Floats.Formats.Posit.Model format)
    (dyadic : FloatLib.Numerics.Dyadic)
    (hvalue : value.toDyadic? = some dyadic) :
    scaleExponent format ≤ dyadic.exponent := by
  rcases toDyadic?_eq_some_cases hvalue with rfl | ⟨hnar, hzero, rfl⟩
  · have hbits : (2 : Int) ≤ format.bits := by
      exact_mod_cast format.bits_ge_two
    simp only [FloatLib.Numerics.Dyadic.zero]
    unfold scaleExponent
    simp only [Int.ofNat_eq_natCast]
    omega
  · exact scaleExponent_le_scale_of_not_special value hzero hnar

/-- Every ordinary decoded posit significand fits below its complete encoded modulus. -/
theorem significand_lt_modulus_of_toDyadic?_eq_some
    (value : FloatLib.Floats.Formats.Posit.Model format)
    (dyadic : FloatLib.Numerics.Dyadic)
    (hvalue : value.toDyadic? = some dyadic) :
    dyadic.significand < format.modulus := by
  rcases toDyadic?_eq_some_cases hvalue with rfl | ⟨_, _, rfl⟩
  · simp [FloatLib.Numerics.Dyadic.zero, Format.modulus]
  · exact FloatLib.Floats.Formats.Posit.Model.decodeFields_significand_lt_modulus value

/-- The dyadic scale of every ordinary posit is below four times its encoded width. -/
theorem exponent_lt_four_bits_of_toDyadic?_eq_some
    (value : FloatLib.Floats.Formats.Posit.Model format)
    (dyadic : FloatLib.Numerics.Dyadic)
    (hvalue : value.toDyadic? = some dyadic) :
    dyadic.exponent < 4 * Int.ofNat format.bits := by
  rcases toDyadic?_eq_some_cases hvalue with rfl | ⟨_, _, rfl⟩
  · simp only [FloatLib.Numerics.Dyadic.zero]
    have hbits : (0 : Int) < format.bits := by
      exact_mod_cast
        (lt_of_lt_of_le (by decide : 0 < 2) format.bits_ge_two)
    simp only [Int.ofNat_eq_natCast]
    omega
  · exact FloatLib.Floats.Formats.Posit.Model.scale_lt_four_bits value

/--
Aligning an ordinary posit to the quire scale requires at most twelve shift bits per posit bit.

This linear bound suffices to prove that conversion fits in the standard `16n`-bit quire.
-/
theorem conversionShift_le_twelve_bits
    (value : FloatLib.Floats.Formats.Posit.Model format)
    (dyadic : FloatLib.Numerics.Dyadic)
    (hvalue : value.toDyadic? = some dyadic) :
    Int.toNat (dyadic.exponent - scaleExponent format) ≤
      12 * format.bits := by
  have hscale :=
    scaleExponent_le_exponent_of_toDyadic?_eq_some value dyadic hvalue
  have hupper :=
    exponent_lt_four_bits_of_toDyadic?_eq_some value dyadic hvalue
  have hdifference :
      (Int.toNat (dyadic.exponent - scaleExponent format) : Int) =
        dyadic.exponent - scaleExponent format :=
    Int.toNat_of_nonneg (sub_nonneg.mpr hscale)
  have hbound :
      (Int.toNat (dyadic.exponent - scaleExponent format) : Int) ≤
        12 * (format.bits : Int) := by
    rw [hdifference]
    unfold scaleExponent
    simp only [Int.ofNat_eq_natCast] at hupper ⊢
    omega
  exact_mod_cast hbound

/--
The magnitude of the integer coefficient produced by posit-to-quire alignment is strictly
below the quire's signed half-range.
-/
theorem natAbs_coefficientOfDyadic_lt_halfRange
    (value : FloatLib.Floats.Formats.Posit.Model format)
    (dyadic : FloatLib.Numerics.Dyadic)
    (hvalue : value.toDyadic? = some dyadic) :
    (coefficientOfDyadic format dyadic).natAbs <
      2 ^ (width format - 1) := by
  let shift :=
    Int.toNat (dyadic.exponent - scaleExponent format)
  have hsignificand :=
    significand_lt_modulus_of_toDyadic?_eq_some value dyadic hvalue
  have hshift :
      shift ≤ 12 * format.bits := by
    exact conversionShift_le_twelve_bits value dyadic hvalue
  have hproduct :
      dyadic.significand * 2 ^ shift <
        2 ^ (format.bits + shift) := by
    have hmul :=
      Nat.mul_lt_mul_of_pos_right hsignificand (Nat.two_pow_pos shift)
    simpa [Format.modulus, Nat.pow_add] using hmul
  have hexponent :
      format.bits + shift ≤ 13 * format.bits := by
    omega
  have hthirteen :
      dyadic.significand * 2 ^ shift <
        2 ^ (13 * format.bits) :=
    lt_of_lt_of_le hproduct
      (Nat.pow_le_pow_right (by decide) hexponent)
  have hhalfExponent :
      13 * format.bits ≤ width format - 1 := by
    unfold width
    have hbits := format.bits_ge_two
    omega
  have hhalf :
      dyadic.significand * 2 ^ shift <
        2 ^ (width format - 1) :=
    lt_of_lt_of_le hthirteen
      (Nat.pow_le_pow_right (by decide) hhalfExponent)
  simpa [coefficientOfDyadic, shift, Int.natAbs_mul] using hhalf

/-- Every ordinary posit converts to an ordinary quire coefficient without overflow. -/
theorem coefficientOfDyadic_ordinary
    (value : FloatLib.Floats.Formats.Posit.Model format)
    (dyadic : FloatLib.Numerics.Dyadic)
    (hvalue : value.toDyadic? = some dyadic) :
    OrdinaryCoefficient format (coefficientOfDyadic format dyadic) :=
  ordinaryCoefficient_of_natAbs_lt
    (natAbs_coefficientOfDyadic_lt_halfRange value dyadic hvalue)

/-- On an ordinary quire, negation is `ofCoefficient` of the negated coefficient. -/
private theorem qNegate_eq_ofCoefficient
    (value : Model format)
    (hvalue : OrdinaryCoefficient format value.coefficient) :
    qNegate value = ofCoefficient format (-value.coefficient) := by
  have hnar : value.isNaR = false :=
    (ordinaryCoefficient_iff_isNaR_eq_false value).mp hvalue
  unfold qNegate
  rw [hnar]
  simp only [Bool.false_eq_true, ite_false]

/-- On ordinary quires, addition is `ofCoefficient` of the coefficient sum. -/
private theorem qAddQ_eq_ofCoefficient
    (left right : Model format)
    (hleft : OrdinaryCoefficient format left.coefficient)
    (hright : OrdinaryCoefficient format right.coefficient) :
    qAddQ left right = ofCoefficient format (left.coefficient + right.coefficient) := by
  have hleftNaR : left.isNaR = false :=
    (ordinaryCoefficient_iff_isNaR_eq_false left).mp hleft
  have hrightNaR : right.isNaR = false :=
    (ordinaryCoefficient_iff_isNaR_eq_false right).mp hright
  unfold qAddQ
  simp only [hleftNaR, hrightNaR, Bool.false_or, Bool.false_eq_true, ite_false]

/-- On ordinary quires, subtraction is `ofCoefficient` of the coefficient difference. -/
private theorem qSubQ_eq_ofCoefficient
    (left right : Model format)
    (hleft : OrdinaryCoefficient format left.coefficient)
    (hright : OrdinaryCoefficient format right.coefficient) :
    qSubQ left right = ofCoefficient format (left.coefficient - right.coefficient) := by
  have hleftNaR : left.isNaR = false :=
    (ordinaryCoefficient_iff_isNaR_eq_false left).mp hleft
  have hrightNaR : right.isNaR = false :=
    (ordinaryCoefficient_iff_isNaR_eq_false right).mp hright
  unfold qSubQ
  simp only [hleftNaR, hrightNaR, Bool.false_or, Bool.false_eq_true, ite_false]

/-- Ordinary quire negation stores the exact negated coefficient. -/
theorem coefficient_qNegate_of_ordinary
    (value : Model format)
    (hvalue : OrdinaryCoefficient format value.coefficient) :
    (qNegate value).coefficient = -value.coefficient := by
  rw [qNegate_eq_ofCoefficient value hvalue]
  exact coefficient_ofCoefficient_of_ordinary
    (ordinaryCoefficient_neg hvalue)

/-- Ordinary quire negation refines exact rational negation. -/
theorem toRat?_qNegate_of_ordinary
    (value : Model format)
    (hvalue : OrdinaryCoefficient format value.coefficient) :
    (qNegate value).toRat? =
      some
        (-(Rat.ofInt value.coefficient *
          (2 : Rat) ^ scaleExponent format)) := by
  rw [qNegate_eq_ofCoefficient value hvalue, toRat?_ofCoefficient_of_ordinary
    (ordinaryCoefficient_neg hvalue)]
  simp

/-- Ordinary quire absolute value stores the absolute value of the coefficient. -/
theorem coefficient_qAbs_of_ordinary
    (value : Model format)
    (hvalue : OrdinaryCoefficient format value.coefficient) :
    (qAbs value).coefficient = |value.coefficient| := by
  have hnar : value.isNaR = false :=
    (ordinaryCoefficient_iff_isNaR_eq_false value).mp hvalue
  unfold qAbs
  rw [hnar]
  simp only [Bool.false_eq_true, ite_false]
  split
  next hnegative =>
    rw [coefficient_qNegate_of_ordinary value hvalue, abs_of_neg hnegative]
  next hnonnegative =>
    rw [abs_of_nonneg (not_lt.mp hnonnegative)]

/-- Ordinary quire absolute value refines the exact rational absolute value. -/
theorem toRat?_qAbs_of_ordinary
    (value : Model format)
    (hvalue : OrdinaryCoefficient format value.coefficient) :
    (qAbs value).toRat? =
      some
        |Rat.ofInt value.coefficient *
          (2 : Rat) ^ scaleExponent format| := by
  have hnar : value.isNaR = false :=
    (ordinaryCoefficient_iff_isNaR_eq_false value).mp hvalue
  have hscale : 0 < (2 : Rat) ^ scaleExponent format := zpow_pos (by norm_num) _
  unfold qAbs
  rw [hnar]
  simp only [Bool.false_eq_true, ite_false]
  split
  next hnegative =>
    have hcoefficient : Rat.ofInt value.coefficient < 0 := by
      simpa using hnegative
    rw [toRat?_qNegate_of_ordinary value hvalue,
      abs_of_neg (mul_neg_of_neg_of_pos hcoefficient hscale)]
  next hnonnegative =>
    have hcoefficient : 0 ≤ Rat.ofInt value.coefficient := by
      simpa using hnonnegative
    rw [abs_of_nonneg (mul_nonneg hcoefficient hscale.le)]
    simp [toRat?, hnar]

/--
Quire absolute value is exact on the rational semantics: a quire with rational value `q` has
absolute value `|q|`. Negating an ordinary coefficient stays in the ordinary range, so the result is
never NaR; NaR itself stays NaR (`qAbs_nar`).
-/
theorem toRat?_qAbs (value : Model format) {q : Rat} (hvalue : value.toRat? = some q) :
    (qAbs value).toRat? = some |q| := by
  have hnar : value.isNaR = false := by
    cases h : value.isNaR
    · rfl
    · simp [toRat?, h] at hvalue
  have hq : Rat.ofInt value.coefficient * (2 : Rat) ^ scaleExponent format = q := by
    simpa [toRat?, hnar] using hvalue
  rw [toRat?_qAbs_of_ordinary value
    ((ordinaryCoefficient_iff_isNaR_eq_false value).mpr hnar), hq]

/-- Quire absolute value is NaR exactly when its argument is. -/
@[simp] theorem isNaR_qAbs (value : Model format) :
    (qAbs value).isNaR = value.isNaR := by
  cases hnar : value.isNaR
  · have hsome := toRat?_qAbs_of_ordinary value
      ((ordinaryCoefficient_iff_isNaR_eq_false value).mpr hnar)
    cases h : (qAbs value).isNaR
    · rfl
    · rw [(toRat?_eq_none_iff (qAbs value)).mpr h] at hsome
      cases hsome
  · simp [qAbs, hnar]

/-- Successful exact quire addition stores the mathematical coefficient sum. -/
theorem coefficient_qAddQ_of_ordinary
    (left right : Model format)
    (hleft : OrdinaryCoefficient format left.coefficient)
    (hright : OrdinaryCoefficient format right.coefficient)
    (hresult :
      OrdinaryCoefficient format (left.coefficient + right.coefficient)) :
    (qAddQ left right).coefficient =
      left.coefficient + right.coefficient := by
  rw [qAddQ_eq_ofCoefficient left right hleft hright]
  exact coefficient_ofCoefficient_of_ordinary hresult

/-- Successful exact quire addition refines rational addition at the shared fixed scale. -/
theorem toRat?_qAddQ_of_ordinary
    (left right : Model format)
    (hleft : OrdinaryCoefficient format left.coefficient)
    (hright : OrdinaryCoefficient format right.coefficient)
    (hresult :
      OrdinaryCoefficient format (left.coefficient + right.coefficient)) :
    (qAddQ left right).toRat? =
      some
        (Rat.ofInt left.coefficient *
            (2 : Rat) ^ scaleExponent format +
          Rat.ofInt right.coefficient *
            (2 : Rat) ^ scaleExponent format) := by
  rw [qAddQ_eq_ofCoefficient left right hleft hright,
    toRat?_ofCoefficient_of_ordinary hresult]
  simp only [Rat.ofInt_eq_cast, Int.cast_add]
  rw [add_mul]

/-- Successful exact quire subtraction stores the mathematical coefficient difference. -/
theorem coefficient_qSubQ_of_ordinary
    (left right : Model format)
    (hleft : OrdinaryCoefficient format left.coefficient)
    (hright : OrdinaryCoefficient format right.coefficient)
    (hresult :
      OrdinaryCoefficient format (left.coefficient - right.coefficient)) :
    (qSubQ left right).coefficient =
      left.coefficient - right.coefficient := by
  rw [qSubQ_eq_ofCoefficient left right hleft hright]
  exact coefficient_ofCoefficient_of_ordinary hresult

/-- Successful exact quire subtraction refines rational subtraction at the shared fixed scale. -/
theorem toRat?_qSubQ_of_ordinary
    (left right : Model format)
    (hleft : OrdinaryCoefficient format left.coefficient)
    (hright : OrdinaryCoefficient format right.coefficient)
    (hresult :
      OrdinaryCoefficient format (left.coefficient - right.coefficient)) :
    (qSubQ left right).toRat? =
      some
        (Rat.ofInt left.coefficient *
            (2 : Rat) ^ scaleExponent format -
          Rat.ofInt right.coefficient *
            (2 : Rat) ^ scaleExponent format) := by
  rw [qSubQ_eq_ofCoefficient left right hleft hright,
    toRat?_ofCoefficient_of_ordinary hresult]
  simp only [Rat.ofInt_eq_cast, Int.cast_sub]
  rw [sub_mul]

/--
Quire addition whose exact coefficient sum is not ordinary returns quire NaR. Nothing is assumed
about the operands: a NaR operand gives NaR anyway (`qAddQ_nar_left`, `qAddQ_nar_right`).
-/
theorem qAddQ_eq_nar_of_not_ordinary
    (left right : Model format)
    (hresult : ¬OrdinaryCoefficient format (left.coefficient + right.coefficient)) :
    qAddQ left right = nar format := by
  unfold qAddQ
  split
  · rfl
  · exact ofCoefficient_eq_nar_of_not_ordinary hresult

/--
Quire subtraction whose exact coefficient difference is not ordinary returns quire NaR. A NaR
operand gives NaR anyway (`qSubQ_nar_left`, `qSubQ_nar_right`).
-/
theorem qSubQ_eq_nar_of_not_ordinary
    (left right : Model format)
    (hresult : ¬OrdinaryCoefficient format (left.coefficient - right.coefficient)) :
    qSubQ left right = nar format := by
  unfold qSubQ
  split
  · rfl
  · exact ofCoefficient_eq_nar_of_not_ordinary hresult

/-- The dyadic accumulation kernel propagates quire NaR. -/
@[simp] theorem addDyadic_nar (format : Format) (increment : FloatLib.Numerics.Dyadic) :
    addDyadic (nar format) increment = nar format := by
  simp [addDyadic]

/-- A NaR accumulator absorbs posit addition. -/
@[simp] theorem qAddP_nar_accumulator (format : Format)
    (addend : FloatLib.Floats.Formats.Posit.Model format) :
    qAddP (nar format) addend = nar format := by
  unfold qAddP
  split <;> simp

/-- Adding posit NaR to a quire gives quire NaR. -/
@[simp] theorem qAddP_nar_addend (format : Format) (accumulator : Model format) :
    qAddP accumulator (FloatLib.Floats.Formats.Posit.Model.nar format) = nar format := by
  simp [qAddP]

/-- A NaR accumulator absorbs posit subtraction. -/
@[simp] theorem qSubP_nar_accumulator (format : Format)
    (subtrahend : FloatLib.Floats.Formats.Posit.Model format) :
    qSubP (nar format) subtrahend = nar format := by
  unfold qSubP
  split <;> simp

/-- Subtracting posit NaR from a quire gives quire NaR. -/
@[simp] theorem qSubP_nar_subtrahend (format : Format) (accumulator : Model format) :
    qSubP accumulator (FloatLib.Floats.Formats.Posit.Model.nar format) = nar format := by
  simp [qSubP]

/-- A NaR accumulator absorbs fused product accumulation. -/
@[simp] theorem qMulAdd_nar_accumulator (format : Format)
    (left right : FloatLib.Floats.Formats.Posit.Model format) :
    qMulAdd (nar format) left right = nar format := by
  unfold qMulAdd
  split <;> simp

/-- A NaR left factor makes fused product accumulation return quire NaR. -/
@[simp] theorem qMulAdd_nar_left (format : Format) (accumulator : Model format)
    (right : FloatLib.Floats.Formats.Posit.Model format) :
    qMulAdd accumulator (FloatLib.Floats.Formats.Posit.Model.nar format) right =
      nar format := by
  simp [qMulAdd]

/-- A NaR right factor makes fused product accumulation return quire NaR. -/
@[simp] theorem qMulAdd_nar_right (format : Format) (accumulator : Model format)
    (left : FloatLib.Floats.Formats.Posit.Model format) :
    qMulAdd accumulator left (FloatLib.Floats.Formats.Posit.Model.nar format) =
      nar format := by
  unfold qMulAdd
  split <;> simp_all

/-- A NaR accumulator absorbs fused product subtraction. -/
@[simp] theorem qMulSub_nar_accumulator (format : Format)
    (left right : FloatLib.Floats.Formats.Posit.Model format) :
    qMulSub (nar format) left right = nar format := by
  unfold qMulSub
  split <;> simp

/-- A NaR left factor makes fused product subtraction return quire NaR. -/
@[simp] theorem qMulSub_nar_left (format : Format) (accumulator : Model format)
    (right : FloatLib.Floats.Formats.Posit.Model format) :
    qMulSub accumulator (FloatLib.Floats.Formats.Posit.Model.nar format) right =
      nar format := by
  simp [qMulSub]

/-- A NaR right factor makes fused product subtraction return quire NaR. -/
@[simp] theorem qMulSub_nar_right (format : Format) (accumulator : Model format)
    (left : FloatLib.Floats.Formats.Posit.Model format) :
    qMulSub accumulator left (FloatLib.Floats.Formats.Posit.Model.nar format) =
      nar format := by
  unfold qMulSub
  split <;> simp_all

/--
An increment whose stored exponent is below the quire scale produces quire NaR.

Otherwise `coefficientOfDyadic` would clamp the negative shift to zero. The guard does not inspect
trailing zeros in the significand, so it may reject a dyadic whose value is nevertheless aligned.
-/
theorem addDyadic_eq_nar_of_exponent_lt
    (accumulator : Model format)
    (increment : FloatLib.Numerics.Dyadic)
    (hexponent : increment.exponent < scaleExponent format) :
    addDyadic accumulator increment = nar format := by
  unfold addDyadic
  by_cases hnar : accumulator.isNaR = true
  · rw [ite_eq_left hnar]
  · rw [ite_eq_right hnar, ite_eq_left hexponent]

/--
Once the accumulator is ordinary and the increment is aligned, the kernel is exactly
`ofCoefficient` applied to the coefficient sum.
-/
theorem addDyadic_eq_ofCoefficient
    (accumulator : Model format)
    (increment : FloatLib.Numerics.Dyadic)
    (haccumulator :
      OrdinaryCoefficient format accumulator.coefficient)
    (hscale : scaleExponent format ≤ increment.exponent) :
    addDyadic accumulator increment =
      ofCoefficient format
        (accumulator.coefficient + coefficientOfDyadic format increment) := by
  have hnar : accumulator.isNaR = false :=
    (ordinaryCoefficient_iff_isNaR_eq_false accumulator).mp haccumulator
  unfold addDyadic
  rw [hnar, ite_eq_right (not_lt.mpr hscale)]
  simp

/--
If the exact coefficient sum is not ordinary, the kernel returns quire NaR. The theorem assumes
nothing about the accumulator or the alignment of the increment, because those cases return NaR
before the sum is formed. NaR accumulators and misaligned increments give NaR unconditionally:
see `addDyadic_nar` and `addDyadic_eq_nar_of_exponent_lt`.
-/
theorem addDyadic_eq_nar_of_not_ordinary
    (accumulator : Model format)
    (increment : FloatLib.Numerics.Dyadic)
    (hresult :
      ¬OrdinaryCoefficient format
        (accumulator.coefficient +
          coefficientOfDyadic format increment)) :
    addDyadic accumulator increment = nar format := by
  unfold addDyadic
  split_ifs
  · rfl
  · rfl
  · exact ofCoefficient_eq_nar_of_not_ordinary hresult

/-- Successful dyadic accumulation stores the exact coefficient sum. -/
theorem coefficient_addDyadic_of_ordinary
    (accumulator : Model format)
    (increment : FloatLib.Numerics.Dyadic)
    (haccumulator :
      OrdinaryCoefficient format accumulator.coefficient)
    (hscale : scaleExponent format ≤ increment.exponent)
    (hresult :
      OrdinaryCoefficient format
        (accumulator.coefficient +
          coefficientOfDyadic format increment)) :
    (addDyadic accumulator increment).coefficient =
      accumulator.coefficient + coefficientOfDyadic format increment := by
  rw [addDyadic_eq_ofCoefficient accumulator increment haccumulator hscale]
  exact coefficient_ofCoefficient_of_ordinary hresult

/--
The shared dyadic accumulation kernel refines exact rational addition whenever the dyadic aligns
to the quire scale and the resulting coefficient is ordinary.
-/
theorem toRat?_addDyadic_of_ordinary
    (accumulator : Model format)
    (increment : FloatLib.Numerics.Dyadic)
    (haccumulator :
      OrdinaryCoefficient format accumulator.coefficient)
    (hscale : scaleExponent format ≤ increment.exponent)
    (hresult :
      OrdinaryCoefficient format
        (accumulator.coefficient +
          coefficientOfDyadic format increment)) :
    (addDyadic accumulator increment).toRat? =
      some
        (Rat.ofInt accumulator.coefficient *
            (2 : Rat) ^ scaleExponent format +
          increment.toRat) := by
  rw [addDyadic_eq_ofCoefficient accumulator increment haccumulator hscale,
    toRat?_ofCoefficient_of_ordinary hresult,
    ← coefficientOfDyadic_denotes format increment hscale]
  simp only [Rat.ofInt_eq_cast, Int.cast_add]
  rw [add_mul]

/--
Accumulating the negation of an aligned increment refines exact rational subtraction whenever
the resulting coefficient is ordinary. Negation keeps the exponent, so the increment's own
alignment suffices.
-/
theorem toRat?_addDyadic_neg_of_ordinary
    (accumulator : Model format)
    (increment : FloatLib.Numerics.Dyadic)
    (haccumulator :
      OrdinaryCoefficient format accumulator.coefficient)
    (hscale : scaleExponent format ≤ increment.exponent)
    (hresult :
      OrdinaryCoefficient format
        (accumulator.coefficient +
          coefficientOfDyadic format increment.neg)) :
    (addDyadic accumulator increment.neg).toRat? =
      some
        (Rat.ofInt accumulator.coefficient *
            (2 : Rat) ^ scaleExponent format -
          increment.toRat) := by
  rw [toRat?_addDyadic_of_ordinary accumulator increment.neg haccumulator hscale hresult,
    FloatLib.Numerics.Dyadic.neg_toRat, sub_eq_add_neg]

/--
Adding an ordinary posit to an ordinary quire refines exact rational addition whenever the
resulting fixed-point coefficient remains ordinary.

Decoded posits satisfy the scale condition automatically. The remaining range hypothesis excludes
overflow and the reserved NaR coefficient.
-/
theorem toRat?_qAddP_of_ordinary
    (accumulator : Model format)
    (addend : FloatLib.Floats.Formats.Posit.Model format)
    (dyadic : FloatLib.Numerics.Dyadic)
    (haddend : addend.toDyadic? = some dyadic)
    (haccumulator :
      OrdinaryCoefficient format accumulator.coefficient)
    (hresult :
      OrdinaryCoefficient format
        (accumulator.coefficient +
          coefficientOfDyadic format dyadic)) :
    (qAddP accumulator addend).toRat? =
      some
        (Rat.ofInt accumulator.coefficient *
            (2 : Rat) ^ scaleExponent format +
          dyadic.toRat) := by
  unfold qAddP
  rw [haddend]
  exact
    toRat?_addDyadic_of_ordinary accumulator dyadic haccumulator
      (scaleExponent_le_exponent_of_toDyadic?_eq_some
        addend dyadic haddend)
      hresult

/-- Successful posit accumulation stores the exact coefficient sum. -/
theorem coefficient_qAddP_of_ordinary
    (accumulator : Model format)
    (addend : FloatLib.Floats.Formats.Posit.Model format)
    (dyadic : FloatLib.Numerics.Dyadic)
    (haddend : addend.toDyadic? = some dyadic)
    (haccumulator :
      OrdinaryCoefficient format accumulator.coefficient)
    (hresult :
      OrdinaryCoefficient format
        (accumulator.coefficient +
          coefficientOfDyadic format dyadic)) :
    (qAddP accumulator addend).coefficient =
      accumulator.coefficient + coefficientOfDyadic format dyadic := by
  unfold qAddP
  rw [haddend]
  exact
    coefficient_addDyadic_of_ordinary accumulator dyadic haccumulator
      (scaleExponent_le_exponent_of_toDyadic?_eq_some addend dyadic haddend)
      hresult

/--
Adding a finite posit whose exact coefficient sum is not ordinary produces quire NaR. The
accumulator is not assumed ordinary; a NaR accumulator gives NaR unconditionally
(`qAddP_nar_accumulator`).
-/
theorem qAddP_eq_nar_of_not_ordinary
    (accumulator : Model format)
    (addend : FloatLib.Floats.Formats.Posit.Model format)
    (dyadic : FloatLib.Numerics.Dyadic)
    (haddend : addend.toDyadic? = some dyadic)
    (hresult :
      ¬OrdinaryCoefficient format
        (accumulator.coefficient +
          coefficientOfDyadic format dyadic)) :
    qAddP accumulator addend = nar format := by
  unfold qAddP
  rw [haddend]
  exact addDyadic_eq_nar_of_not_ordinary accumulator dyadic hresult

/--
Subtracting an ordinary posit from an ordinary quire refines exact rational subtraction whenever
the resulting fixed-point coefficient remains ordinary.

As for addition, decoded posits align with the associated quire. The remaining range hypothesis
excludes overflow and the reserved NaR coefficient.
-/
theorem toRat?_qSubP_of_ordinary
    (accumulator : Model format)
    (subtrahend : FloatLib.Floats.Formats.Posit.Model format)
    (dyadic : FloatLib.Numerics.Dyadic)
    (hsubtrahend : subtrahend.toDyadic? = some dyadic)
    (haccumulator :
      OrdinaryCoefficient format accumulator.coefficient)
    (hresult :
      OrdinaryCoefficient format
        (accumulator.coefficient +
          coefficientOfDyadic format dyadic.neg)) :
    (qSubP accumulator subtrahend).toRat? =
      some
        (Rat.ofInt accumulator.coefficient *
            (2 : Rat) ^ scaleExponent format -
          dyadic.toRat) := by
  unfold qSubP
  rw [hsubtrahend]
  exact toRat?_addDyadic_neg_of_ordinary accumulator dyadic haccumulator
    (scaleExponent_le_exponent_of_toDyadic?_eq_some subtrahend dyadic hsubtrahend) hresult

/-- Successful posit subtraction stores the exact coefficient difference. -/
theorem coefficient_qSubP_of_ordinary
    (accumulator : Model format)
    (subtrahend : FloatLib.Floats.Formats.Posit.Model format)
    (dyadic : FloatLib.Numerics.Dyadic)
    (hsubtrahend : subtrahend.toDyadic? = some dyadic)
    (haccumulator :
      OrdinaryCoefficient format accumulator.coefficient)
    (hresult :
      OrdinaryCoefficient format
        (accumulator.coefficient +
          coefficientOfDyadic format dyadic.neg)) :
    (qSubP accumulator subtrahend).coefficient =
      accumulator.coefficient + coefficientOfDyadic format dyadic.neg := by
  unfold qSubP
  rw [hsubtrahend]
  exact
    coefficient_addDyadic_of_ordinary accumulator dyadic.neg haccumulator
      (scaleExponent_le_exponent_of_toDyadic?_eq_some subtrahend dyadic hsubtrahend)
      hresult

/--
Subtracting a finite posit whose exact coefficient difference is not ordinary produces quire NaR.
A NaR accumulator gives NaR unconditionally (`qSubP_nar_accumulator`).
-/
theorem qSubP_eq_nar_of_not_ordinary
    (accumulator : Model format)
    (subtrahend : FloatLib.Floats.Formats.Posit.Model format)
    (dyadic : FloatLib.Numerics.Dyadic)
    (hsubtrahend : subtrahend.toDyadic? = some dyadic)
    (hresult :
      ¬OrdinaryCoefficient format
        (accumulator.coefficient +
          coefficientOfDyadic format dyadic.neg)) :
    qSubP accumulator subtrahend = nar format := by
  unfold qSubP
  rw [hsubtrahend]
  exact addDyadic_eq_nar_of_not_ordinary accumulator dyadic.neg hresult

/--
Every ordinary posit dyadic lies at or above the smallest positive posit exponent.

Zero uses the exact carrier's conventional exponent zero. A finite nonzero value uses the global
representation bound proved from the mandatory negative-regime terminator.
-/
theorem minPositive_exponent_le_exponent_of_toDyadic?_eq_some
    (value : FloatLib.Floats.Formats.Posit.Model format)
    (dyadic : FloatLib.Numerics.Dyadic)
    (hvalue : value.toDyadic? = some dyadic) :
    (FloatLib.Floats.Formats.Posit.Model.DyadicRounding.minPositive format).exponent ≤
      dyadic.exponent := by
  rcases toDyadic?_eq_some_cases hvalue with rfl | ⟨hnar, hzero, rfl⟩
  · rw [FloatLib.Floats.Formats.Posit.Model.DyadicRounding.minPositive_eq_fields]
    simp only [FloatLib.Numerics.Dyadic.zero]
    apply neg_nonpos.mpr
    exact
      mul_nonneg (by norm_num)
        (Int.natCast_nonneg (format.payloadBits - 1))
  · exact
      FloatLib.Floats.Formats.Posit.Model.DyadicRounding.minPositive_exponent_le_scale_of_not_special
        value hzero hnar

/-- The associated quire scale is twice the smallest positive posit exponent. -/
theorem scaleExponent_eq_two_mul_minPositive_exponent (format : Format) :
    scaleExponent format =
      2 *
        (FloatLib.Floats.Formats.Posit.Model.DyadicRounding.minPositive format).exponent := by
  rw [FloatLib.Floats.Formats.Posit.Model.DyadicRounding.minPositive_eq_fields]
  unfold scaleExponent Format.payloadBits
  have hbits := format.bits_ge_two
  simp only [Int.ofNat_eq_natCast]
  omega

/-- Every exact product of two ordinary posits aligns with the associated quire scale. -/
theorem scaleExponent_le_mul_exponent_of_toDyadic?_eq_some
    (left right : FloatLib.Floats.Formats.Posit.Model format)
    (leftDyadic rightDyadic : FloatLib.Numerics.Dyadic)
    (hleft : left.toDyadic? = some leftDyadic)
    (hright : right.toDyadic? = some rightDyadic) :
    scaleExponent format ≤
      (FloatLib.Numerics.Dyadic.mul leftDyadic rightDyadic).exponent := by
  have hleftExponent :=
    minPositive_exponent_le_exponent_of_toDyadic?_eq_some
      left leftDyadic hleft
  have hrightExponent :=
    minPositive_exponent_le_exponent_of_toDyadic?_eq_some
      right rightDyadic hright
  rw [scaleExponent_eq_two_mul_minPositive_exponent]
  simp only [FloatLib.Numerics.Dyadic.mul,
    FloatLib.Numerics.Dyadic.mulFields]
  omega

/--
Exact fused product accumulation refines rational multiplication followed by exact quire
addition whenever the resulting coefficient is ordinary.
-/
theorem toRat?_qMulAdd_of_ordinary
    (accumulator : Model format)
    (left right : FloatLib.Floats.Formats.Posit.Model format)
    (leftDyadic rightDyadic : FloatLib.Numerics.Dyadic)
    (hleft : left.toDyadic? = some leftDyadic)
    (hright : right.toDyadic? = some rightDyadic)
    (haccumulator : OrdinaryCoefficient format accumulator.coefficient)
    (hresult :
      OrdinaryCoefficient format
        (accumulator.coefficient +
          coefficientOfDyadic format
            (FloatLib.Numerics.Dyadic.mul leftDyadic rightDyadic))) :
    (qMulAdd accumulator left right).toRat? =
      some
        (Rat.ofInt accumulator.coefficient *
            (2 : Rat) ^ scaleExponent format +
          leftDyadic.toRat * rightDyadic.toRat) := by
  unfold qMulAdd
  rw [hleft, hright,
    toRat?_addDyadic_of_ordinary accumulator
      (FloatLib.Numerics.Dyadic.mul leftDyadic rightDyadic)
      haccumulator
      (scaleExponent_le_mul_exponent_of_toDyadic?_eq_some
        left right leftDyadic rightDyadic hleft hright)
      hresult,
    FloatLib.Numerics.Dyadic.mul_toRat]

/-- Successful fused product accumulation stores the exact coefficient sum. -/
theorem coefficient_qMulAdd_of_ordinary
    (accumulator : Model format)
    (left right : FloatLib.Floats.Formats.Posit.Model format)
    (leftDyadic rightDyadic : FloatLib.Numerics.Dyadic)
    (hleft : left.toDyadic? = some leftDyadic)
    (hright : right.toDyadic? = some rightDyadic)
    (haccumulator : OrdinaryCoefficient format accumulator.coefficient)
    (hresult :
      OrdinaryCoefficient format
        (accumulator.coefficient +
          coefficientOfDyadic format
            (FloatLib.Numerics.Dyadic.mul leftDyadic rightDyadic))) :
    (qMulAdd accumulator left right).coefficient =
      accumulator.coefficient +
        coefficientOfDyadic format
          (FloatLib.Numerics.Dyadic.mul leftDyadic rightDyadic) := by
  unfold qMulAdd
  rw [hleft, hright]
  exact
    coefficient_addDyadic_of_ordinary accumulator
      (FloatLib.Numerics.Dyadic.mul leftDyadic rightDyadic)
      haccumulator
      (scaleExponent_le_mul_exponent_of_toDyadic?_eq_some
        left right leftDyadic rightDyadic hleft hright)
      hresult

/--
Accumulating the exact product of two finite posits whose coefficient sum is not ordinary
produces quire NaR.

For an ordinary accumulator and two finite posits, this theorem and `toRat?_qMulAdd_of_ordinary`
together determine `qMulAdd`: the result is exact while the coefficient stays ordinary and NaR as
soon as it does not. NaR inputs give NaR unconditionally (`qMulAdd_nar_accumulator`,
`qMulAdd_nar_left`, `qMulAdd_nar_right`).
-/
theorem qMulAdd_eq_nar_of_not_ordinary
    (accumulator : Model format)
    (left right : FloatLib.Floats.Formats.Posit.Model format)
    (leftDyadic rightDyadic : FloatLib.Numerics.Dyadic)
    (hleft : left.toDyadic? = some leftDyadic)
    (hright : right.toDyadic? = some rightDyadic)
    (hresult :
      ¬OrdinaryCoefficient format
        (accumulator.coefficient +
          coefficientOfDyadic format
            (FloatLib.Numerics.Dyadic.mul leftDyadic rightDyadic))) :
    qMulAdd accumulator left right = nar format := by
  unfold qMulAdd
  rw [hleft, hright]
  exact
    addDyadic_eq_nar_of_not_ordinary accumulator
      (FloatLib.Numerics.Dyadic.mul leftDyadic rightDyadic) hresult

/--
Exact fused product subtraction refines rational subtraction whenever the resulting coefficient
is ordinary.
-/
theorem toRat?_qMulSub_of_ordinary
    (accumulator : Model format)
    (left right : FloatLib.Floats.Formats.Posit.Model format)
    (leftDyadic rightDyadic : FloatLib.Numerics.Dyadic)
    (hleft : left.toDyadic? = some leftDyadic)
    (hright : right.toDyadic? = some rightDyadic)
    (haccumulator : OrdinaryCoefficient format accumulator.coefficient)
    (hresult :
      OrdinaryCoefficient format
        (accumulator.coefficient +
          coefficientOfDyadic format
            (FloatLib.Numerics.Dyadic.mul leftDyadic rightDyadic).neg)) :
    (qMulSub accumulator left right).toRat? =
      some
        (Rat.ofInt accumulator.coefficient *
            (2 : Rat) ^ scaleExponent format -
          leftDyadic.toRat * rightDyadic.toRat) := by
  unfold qMulSub
  rw [hleft, hright,
    toRat?_addDyadic_neg_of_ordinary accumulator
      (FloatLib.Numerics.Dyadic.mul leftDyadic rightDyadic) haccumulator
      (scaleExponent_le_mul_exponent_of_toDyadic?_eq_some
        left right leftDyadic rightDyadic hleft hright)
      hresult,
    FloatLib.Numerics.Dyadic.mul_toRat]

/-- Successful fused product subtraction stores the exact coefficient difference. -/
theorem coefficient_qMulSub_of_ordinary
    (accumulator : Model format)
    (left right : FloatLib.Floats.Formats.Posit.Model format)
    (leftDyadic rightDyadic : FloatLib.Numerics.Dyadic)
    (hleft : left.toDyadic? = some leftDyadic)
    (hright : right.toDyadic? = some rightDyadic)
    (haccumulator : OrdinaryCoefficient format accumulator.coefficient)
    (hresult :
      OrdinaryCoefficient format
        (accumulator.coefficient +
          coefficientOfDyadic format
            (FloatLib.Numerics.Dyadic.mul leftDyadic rightDyadic).neg)) :
    (qMulSub accumulator left right).coefficient =
      accumulator.coefficient +
        coefficientOfDyadic format
          (FloatLib.Numerics.Dyadic.mul leftDyadic rightDyadic).neg := by
  unfold qMulSub
  rw [hleft, hright]
  exact
    coefficient_addDyadic_of_ordinary accumulator
      (FloatLib.Numerics.Dyadic.mul leftDyadic rightDyadic).neg
      haccumulator
      (scaleExponent_le_mul_exponent_of_toDyadic?_eq_some
        left right leftDyadic rightDyadic hleft hright)
      hresult

/--
Subtracting the exact product of two finite posits whose coefficient difference is not ordinary
produces quire NaR. NaR inputs give NaR unconditionally (`qMulSub_nar_accumulator`,
`qMulSub_nar_left`, `qMulSub_nar_right`).
-/
theorem qMulSub_eq_nar_of_not_ordinary
    (accumulator : Model format)
    (left right : FloatLib.Floats.Formats.Posit.Model format)
    (leftDyadic rightDyadic : FloatLib.Numerics.Dyadic)
    (hleft : left.toDyadic? = some leftDyadic)
    (hright : right.toDyadic? = some rightDyadic)
    (hresult :
      ¬OrdinaryCoefficient format
        (accumulator.coefficient +
          coefficientOfDyadic format
            (FloatLib.Numerics.Dyadic.mul leftDyadic rightDyadic).neg)) :
    qMulSub accumulator left right = nar format := by
  unfold qMulSub
  rw [hleft, hright]
  exact
    addDyadic_eq_nar_of_not_ordinary accumulator
      (FloatLib.Numerics.Dyadic.mul leftDyadic rightDyadic).neg hresult

/--
Posit-to-quire conversion preserves exact rational meaning for every Posit Standard (2022) value.

NaR maps to quire NaR. Every ordinary value is proved to align with the standard quire scale and
to lie strictly inside its signed coefficient range, so this theorem has no caller-supplied side
conditions.
-/
theorem toRat?_pToQ
    (value : FloatLib.Floats.Formats.Posit.Model format) :
    (pToQ value).toRat? = value.toRat? := by
  cases hvalue : value.toDyadic? with
  | none =>
      rw [FloatLib.Floats.Formats.Posit.Model.toRat?_eq_toDyadic?_map,
        hvalue]
      simp [pToQ, hvalue]
  | some dyadic =>
      unfold pToQ
      rw [hvalue,
        toRat?_ofCoefficient_of_ordinary (coefficientOfDyadic_ordinary value dyadic hvalue),
        coefficientOfDyadic_denotes format dyadic
          (scaleExponent_le_exponent_of_toDyadic?_eq_some value dyadic hvalue),
        FloatLib.Floats.Formats.Posit.Model.toRat?_eq_toDyadic?_map, hvalue]
      rfl

/--
Quire-to-posit conversion agrees with Posit Standard (2022) rational rounding.

An ordinary quire rounds its exact rational value once; the reserved quire NaR maps to the unique
posit NaR instead of being assigned a finite or infinite numerical value.
-/
theorem qToP_eq_roundRat (value : Model format) :
    qToP value =
      match value.toRat? with
      | some rational =>
          FloatLib.Floats.Formats.Posit.Model.roundRat format rational
      | none =>
          FloatLib.Floats.Formats.Posit.Model.nar format := by
  rw [toRat?_eq_toDyadic?_map]
  cases hvalue : value.toDyadic? with
  | none =>
      simp [qToP, hvalue]
  | some dyadic =>
      simp [qToP, hvalue,
        FloatLib.Floats.Formats.Posit.Model.DyadicRounding.round_eq_roundRat]

end FloatLib.Floats.Formats.Posit.Quire.Model
