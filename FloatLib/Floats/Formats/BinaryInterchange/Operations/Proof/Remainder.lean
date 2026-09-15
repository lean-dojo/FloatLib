/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Model.RealSemantics
import FloatLib.Numerics.Exact.Dyadic.Order
import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Proof
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Exact
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Signed
import FloatLib.Numerics.Exact.Dyadic.Arithmetic.Runtime

/-!
# IEEE remainder contracts

IEEE remainder subtracts the nearest integer multiple of the divisor, with ties going to an even
quotient. Reducing an aligned numerator modulo twice the divisor preserves both the remainder
and the quotient parity needed to resolve a tie.

The finite kernel has this exact rational semantics. For finite inputs and a nonzero divisor in
an IEEE encoding, the resulting dyadic is representable, so its final encoding loses no precision.
Separate equations specify the value and status for zero divisors and infinities.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Numerics
open FloatLib.Floats.Formats.Flocq

/-! ## Nearest-even quotient arithmetic -/

private theorem remainderFromDivision_toRat
    (negative : Bool) (numerator denominator : Nat)
    (exponent : Int) (hdenominator : denominator ≠ 0) :
    let quotient := roundQuotientEven numerator denominator
    let coefficient :=
      Int.ofNat numerator - Int.ofNat (quotient * denominator)
    (Operations.Internal.remainderFromDivision
        negative (numerator / denominator % 2 == 1)
        (numerator % denominator) denominator exponent).toRat =
      Rat.ofInt (if negative then -coefficient else coefficient) *
        (2 : Rat) ^ exponent := by
  dsimp only
  rw [roundQuotientEven_eq_quotient_add]
  have hdecompose := Nat.div_add_mod' numerator denominator
  have hremainderLt := Nat.mod_lt numerator (Nat.pos_of_ne_zero hdenominator)
  simp only [Operations.Internal.remainderFromDivision, Numerics.Dyadic.toRat,
    Numerics.Dyadic.signedSignificand]
  congr 2
  cases negative <;> split_ifs <;> simp only [Nat.add_mul, Nat.one_mul, Nat.add_zero, beq_iff_eq,
    Int.ofNat_eq_natCast, Bool.not_false, Bool.not_true, Bool.false_eq_true, not_true_eq_false,
    not_false_eq_true] at * <;> omega

private theorem quotient_odd_iff_mod_twice_ge
    (numerator denominator : Nat) (hdenominator : denominator ≠ 0) :
    (numerator / denominator % 2 == 1) =
      decide (denominator ≤ numerator % (2 * denominator)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  rw [← Nat.mod_mul_right_div_self numerator denominator 2]
  rw [Nat.mul_comm denominator 2]
  constructor
  · intro hquotient
    have honeLe :
        1 ≤ numerator % (2 * denominator) / denominator := by
      omega
    simpa using
      (Nat.le_div_iff_mul_le
        (Nat.pos_of_ne_zero hdenominator)).mp honeLe
  · intro hlower
    apply Nat.div_eq_of_lt_le
    · simpa using hlower
    · exact Nat.mod_lt _ (by omega)

private theorem modular_scaled_residue
    (value shift denominator : Nat) (hdenominator : denominator ≠ 0) :
    (value % (2 * denominator) *
        modularPow 2 shift (2 * denominator)) %
      (2 * denominator) =
        Nat.shiftLeft value shift % (2 * denominator) := by
  have hmodulus : 2 * denominator ≠ 0 := by omega
  rw [modularPow_eq_pow_mod 2 shift (2 * denominator) hmodulus]
  rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq]
  exact (Nat.mul_mod value (2 ^ shift) (2 * denominator)).symm

private theorem remainderDyadic_toRat_of_exponent_le
    (dividend divisor : Numerics.Dyadic)
    (hdivisor : divisor.significand ≠ 0)
    (hexponents : divisor.exponent ≤ dividend.exponent) :
    (remainderDyadic dividend divisor hdivisor).toRat =
      let shift := Int.toNat (dividend.exponent - divisor.exponent)
      let numerator := Nat.shiftLeft dividend.significand shift
      let quotient := roundQuotientEven numerator divisor.significand
      let coefficient :=
        Int.ofNat numerator -
          Int.ofNat (quotient * divisor.significand)
      Rat.ofInt
          (if dividend.negative then -coefficient else coefficient) *
        (2 : Rat) ^ divisor.exponent := by
  dsimp only
  by_cases hzero : dividend.significand = 0
  · have hroundZero :
        roundQuotientEven 0 divisor.significand = 0 := by
      simp [roundQuotientEven]
    rw [remainderDyadic,
      ite_eq_left (by simpa only [beq_iff_eq] using hzero)]
    simp [hzero, hroundZero]
  · let shift := Int.toNat (dividend.exponent - divisor.exponent)
    let modulus := 2 * divisor.significand
    let scaledResidue :=
      (dividend.significand % modulus *
          modularPow 2 shift modulus) %
        modulus
    have hscaledResidue :
        scaledResidue =
          Nat.shiftLeft dividend.significand shift % modulus := by
      simpa [scaledResidue, modulus] using
        modular_scaled_residue
          dividend.significand shift divisor.significand hdivisor
    have hremainder :
        scaledResidue % divisor.significand =
          Nat.shiftLeft dividend.significand shift %
            divisor.significand := by
      rw [hscaledResidue]
      simp [modulus]
    have hquotientOdd :
        decide (divisor.significand ≤ scaledResidue) =
          (Nat.shiftLeft dividend.significand shift /
              divisor.significand % 2 == 1) := by
      rw [hscaledResidue]
      exact
        (quotient_odd_iff_mod_twice_ge
          (Nat.shiftLeft dividend.significand shift)
          divisor.significand hdivisor).symm
    rw [remainderDyadic, ite_eq_right (by simpa only [beq_iff_eq] using hzero),
      ite_eq_left hexponents]
    change
      (Operations.Internal.remainderFromDivision
          dividend.negative
          (decide (divisor.significand ≤ scaledResidue))
          (scaledResidue % divisor.significand)
          divisor.significand divisor.exponent).toRat =
        _
    rw [hremainder, hquotientOdd]
    exact
      remainderFromDivision_toRat
        dividend.negative
        (Nat.shiftLeft dividend.significand shift)
        divisor.significand divisor.exponent hdivisor

private theorem roundQuotientEven_eq_zero_of_twice_lt
    (numerator denominator : Nat)
    (hbelow : 2 * numerator < denominator) :
    roundQuotientEven numerator denominator = 0 := by
  have hnumerator : numerator < denominator := by omega
  simp [roundQuotientEven, Nat.div_eq_of_lt hnumerator,
    Nat.mod_eq_of_lt hnumerator, hbelow]

private theorem remainderDyadic_toRat_of_exponent_lt
    (dividend divisor : Numerics.Dyadic)
    (hdivisor : divisor.significand ≠ 0)
    (hexponents : dividend.exponent < divisor.exponent) :
    (remainderDyadic dividend divisor hdivisor).toRat =
      let shift := Int.toNat (divisor.exponent - dividend.exponent)
      let denominator := Nat.shiftLeft divisor.significand shift
      let quotient := roundQuotientEven dividend.significand denominator
      let coefficient :=
        Int.ofNat dividend.significand -
          Int.ofNat (quotient * denominator)
      Rat.ofInt
          (if dividend.negative then -coefficient else coefficient) *
        (2 : Rat) ^ dividend.exponent := by
  dsimp only
  by_cases hzero : dividend.significand = 0
  · rw [remainderDyadic,
      ite_eq_left (by simpa only [beq_iff_eq] using hzero)]
    simp [hzero, roundQuotientEven]
  · let shift := Int.toNat (divisor.exponent - dividend.exponent)
    let scaledDivisor := Nat.shiftLeft divisor.significand shift
    have hscaledDivisor : scaledDivisor ≠ 0 := by
      simp [scaledDivisor, Nat.shiftLeft_eq', Nat.shiftLeft_eq, hdivisor]
    by_cases hlarge : (2 * dividend.significand).log2 < shift
    · have htwiceLtPow :
          2 * dividend.significand < 2 ^ shift := by
        exact
          Nat.lt_of_lt_of_le Nat.lt_log2_self
            (Nat.pow_le_pow_right (by decide) (by omega))
      have hpowLeScaled :
          2 ^ shift ≤ scaledDivisor := by
        dsimp [scaledDivisor]
        rw [Nat.shiftLeft_eq]
        have honeLe : 1 ≤ divisor.significand :=
          Nat.one_le_iff_ne_zero.mpr hdivisor
        simpa only [one_mul] using
          Nat.mul_le_mul_right (2 ^ shift) honeLe
      have htwiceLt :
          2 * dividend.significand < scaledDivisor :=
        htwiceLtPow.trans_le hpowLeScaled
      have hroundZero :
          roundQuotientEven dividend.significand scaledDivisor = 0 :=
        roundQuotientEven_eq_zero_of_twice_lt
          dividend.significand scaledDivisor htwiceLt
      rw [remainderDyadic,
        ite_eq_right (by simpa only [beq_iff_eq] using hzero),
        ite_eq_right (not_le_of_gt hexponents), ite_eq_left hlarge]
      change
        dividend.toRat =
          Rat.ofInt
              (if dividend.negative then
                -(Int.ofNat dividend.significand -
                  Int.ofNat
                    (roundQuotientEven dividend.significand
                      scaledDivisor * scaledDivisor))
              else
                Int.ofNat dividend.significand -
                  Int.ofNat
                    (roundQuotientEven dividend.significand
                      scaledDivisor * scaledDivisor)) *
            (2 : Rat) ^ dividend.exponent
      rw [hroundZero]
      rw [zero_mul, show Int.ofNat 0 = (0 : Int) by rfl, sub_zero]
      rfl
    · rw [remainderDyadic,
        ite_eq_right (by simpa only [beq_iff_eq] using hzero),
        ite_eq_right (not_le_of_gt hexponents)]
      change
        (if (2 * dividend.significand).log2 < shift then
            dividend
          else
            Operations.Internal.remainderFromDivision
              dividend.negative
              (dividend.significand / scaledDivisor % 2 == 1)
              (dividend.significand % scaledDivisor)
              scaledDivisor dividend.exponent).toRat =
          _
      rw [ite_eq_right hlarge]
      exact
        remainderFromDivision_toRat
          dividend.negative dividend.significand scaledDivisor
          dividend.exponent hscaledDivisor

/-! ## Exact finite remainder -/

/--
The optimized finite remainder kernel has the exact unbounded nearest-even quotient semantics.

When the dividend exponent is larger, modular exponentiation recovers the aligned numerator's
quotient parity and remainder without constructing it. In the other direction, a sufficiently
large exponent gap guarantees that the nearest quotient is zero, allowing an early return.
Both paths agree with the unbounded aligned calculation below.
-/
theorem remainderDyadic_toRat
    (dividend divisor : Numerics.Dyadic)
    (hdivisor : divisor.significand ≠ 0) :
    (remainderDyadic dividend divisor hdivisor).toRat =
      if divisor.exponent ≤ dividend.exponent then
        let shift :=
          Int.toNat (dividend.exponent - divisor.exponent)
        let numerator :=
          Nat.shiftLeft dividend.significand shift
        let quotient :=
          roundQuotientEven numerator divisor.significand
        let coefficient :=
          Int.ofNat numerator -
            Int.ofNat (quotient * divisor.significand)
        Rat.ofInt
            (if dividend.negative then -coefficient else coefficient) *
          (2 : Rat) ^ divisor.exponent
      else
        let shift :=
          Int.toNat (divisor.exponent - dividend.exponent)
        let denominator :=
          Nat.shiftLeft divisor.significand shift
        let quotient :=
          roundQuotientEven dividend.significand denominator
        let coefficient :=
          Int.ofNat dividend.significand -
            Int.ofNat (quotient * denominator)
        Rat.ofInt
            (if dividend.negative then -coefficient else coefficient) *
          (2 : Rat) ^ dividend.exponent := by
  by_cases hexponents : divisor.exponent ≤ dividend.exponent
  · rw [ite_eq_left hexponents]
    exact
      remainderDyadic_toRat_of_exponent_le
        dividend divisor hdivisor hexponents
  · rw [ite_eq_right hexponents]
    exact
      remainderDyadic_toRat_of_exponent_lt
        dividend divisor hdivisor (lt_of_not_ge hexponents)

/-- Zero has zero IEEE remainder against every nonzero finite divisor. -/
@[simp] theorem remainderDyadic_of_significand_eq_zero
    (dividend divisor : Numerics.Dyadic)
    (hzero : dividend.significand = 0)
    (hdivisor : divisor.significand ≠ 0) :
    remainderDyadic dividend divisor hdivisor = dividend := by
  simp [remainderDyadic, hzero]

/-- `remainder` is exactly the value component of its status-bearing operation. -/
@[simp] theorem remainder_eq_value {fmt : FloatFormat}
    (dividend divisor : Model fmt) :
    remainder dividend divisor = (remainderWithStatus dividend divisor).value :=
  rfl

/-! ## Status-bearing exceptional branches -/

/--
For two finite operands with a nonzero divisor, the runtime encodes the selected dyadic remainder
and returns clear status. A zero result uses the dividend's sign, subject to the format's zero
policy.
-/
theorem remainderWithStatus_of_finite
    {fmt : FloatFormat} (dividend divisor : Model fmt)
    (exactDividend exactDivisor : Numerics.Dyadic)
    (hdividend : exactValue dividend = .finite exactDividend)
    (hdivisor : exactValue divisor = .finite exactDivisor)
    (hnonzero : exactDivisor.significand ≠ 0) :
    remainderWithStatus dividend divisor =
      let exact := remainderDyadic exactDividend exactDivisor hnonzero
      let value :=
        if exact.significand == 0 then
          zero fmt exactDividend.negative
        else
          roundDyadic fmt exact
      { value, status := .clear } := by
  simp [remainderWithStatus, hdividend, hdivisor, hnonzero, outcomeWithInvalid]

/-- A finite zero divisor makes IEEE remainder invalid. -/
theorem remainderWithStatus_of_zero_divisor
    {fmt : FloatFormat} (dividend divisor : Model fmt)
    (exactDividend exactDivisor : Numerics.Dyadic)
    (hdividend : exactValue dividend = .finite exactDividend)
    (hdivisor : exactValue divisor = .finite exactDivisor)
    (hzero : exactDivisor.significand = 0) :
    remainderWithStatus dividend divisor =
      { value := invalidResult fmt, status := { invalid := true } } := by
  simp [remainderWithStatus, hdividend, hdivisor, hzero, outcomeWithInvalid]

/-- A finite dividend is unchanged when the divisor is infinite. -/
theorem remainderWithStatus_of_finite_of_infinity
    {fmt : FloatFormat} (dividend divisor : Model fmt)
    (exact : Numerics.Dyadic) (negative : Bool)
    (hdividend : exactValue dividend = .finite exact)
    (hdivisor : exactValue divisor = .infinity negative) :
    remainderWithStatus dividend divisor =
      { value := dividend, status := .clear } := by
  simp [remainderWithStatus, hdividend, hdivisor, outcomeWithInvalid]

/-- An infinite dividend and finite divisor make IEEE remainder invalid. -/
theorem remainderWithStatus_of_infinity_of_finite
    {fmt : FloatFormat} (dividend divisor : Model fmt)
    (dividendNegative : Bool) (exactDivisor : Numerics.Dyadic)
    (hdividend : exactValue dividend = .infinity dividendNegative)
    (hdivisor : exactValue divisor = .finite exactDivisor) :
    remainderWithStatus dividend divisor =
      { value := invalidResult fmt, status := { invalid := true } } := by
  simp [remainderWithStatus, hdividend, hdivisor, outcomeWithInvalid]

/-- Two infinite operands make IEEE remainder invalid. -/
theorem remainderWithStatus_of_infinity_of_infinity
    {fmt : FloatFormat} (dividend divisor : Model fmt)
    (dividendNegative divisorNegative : Bool)
    (hdividend : exactValue dividend = .infinity dividendNegative)
    (hdivisor : exactValue divisor = .infinity divisorNegative) :
    remainderWithStatus dividend divisor =
      { value := invalidResult fmt, status := { invalid := true } } := by
  simp [remainderWithStatus, hdividend, hdivisor, outcomeWithInvalid]

/-! ## Exactness of the encoded remainder -/

/-- The selected remainder magnitude never exceeds the denominator once the raw remainder does. -/
private theorem remainderFromDivision_significand_le_denominator
    (negative quotientOdd : Bool) (remainder denominator : Nat) (exponent : Int)
    (hrem : remainder ≤ denominator) :
    (Operations.Internal.remainderFromDivision
      negative quotientOdd remainder denominator exponent).significand ≤ denominator := by
  simp only [Operations.Internal.remainderFromDivision]
  split_ifs <;> omega

/--
With the ordinary quotient parity and remainder of `numerator / denominator`, the selected
magnitude never exceeds the numerator: a nonzero quotient bounds it by the denominator, and a zero
quotient rounds up only when the numerator is more than half the denominator.
-/
private theorem remainderFromDivision_significand_le_numerator
    (negative : Bool) (numerator denominator : Nat) (exponent : Int) :
    (Operations.Internal.remainderFromDivision negative (numerator / denominator % 2 == 1)
      (numerator % denominator) denominator exponent).significand ≤ numerator := by
  have hmod : numerator % denominator ≤ numerator := Nat.mod_le _ _
  by_cases hlt : numerator < denominator
  · have hq : numerator / denominator = 0 := Nat.div_eq_of_lt hlt
    have hr : numerator % denominator = numerator := Nat.mod_eq_of_lt hlt
    have hround :
        Numerics.nearestEvenRoundsUp (numerator / denominator % 2 == 1)
            (numerator % denominator) denominator =
          decide (denominator < 2 * numerator) := by
      simp [Numerics.nearestEvenRoundsUp, hq, hr]
    simp only [Operations.Internal.remainderFromDivision]
    rw [hround, hr]
    split_ifs with h
    · have h' := of_decide_eq_true h
      omega
    · exact le_rfl
  · have hge : denominator ≤ numerator := not_lt.mp hlt
    simp only [Operations.Internal.remainderFromDivision]
    split_ifs <;> omega

/--
The exact remainder is either the dividend itself or a dyadic at the exponent of one operand whose
significand is no larger than that operand's. These bounds establish representability in
`remainderWithStatus_exact`.
-/
theorem remainderDyadic_eq_or_le
    (dividend divisor : Numerics.Dyadic) (hdivisor : divisor.significand ≠ 0) :
    remainderDyadic dividend divisor hdivisor = dividend ∨
      ((remainderDyadic dividend divisor hdivisor).exponent = divisor.exponent ∧
        (remainderDyadic dividend divisor hdivisor).significand ≤ divisor.significand) ∨
      ((remainderDyadic dividend divisor hdivisor).exponent = dividend.exponent ∧
        (remainderDyadic dividend divisor hdivisor).significand ≤ dividend.significand) := by
  by_cases hzero : dividend.significand = 0
  · exact Or.inl (remainderDyadic_of_significand_eq_zero dividend divisor hzero hdivisor)
  · unfold remainderDyadic
    simp only [beq_iff_eq, hzero, ite_false]
    by_cases hexp : divisor.exponent ≤ dividend.exponent
    · rw [ite_eq_left hexp]
      refine Or.inr (Or.inl ⟨rfl, ?_⟩)
      exact remainderFromDivision_significand_le_denominator _ _ _ _ _
        (Nat.mod_lt _ (Nat.pos_of_ne_zero hdivisor)).le
    · rw [ite_eq_right hexp]
      by_cases hgap :
          (2 * dividend.significand).log2 <
            Int.toNat (divisor.exponent - dividend.exponent)
      · rw [ite_eq_left hgap]
        exact Or.inl rfl
      · rw [ite_eq_right hgap]
        exact Or.inr (Or.inr ⟨rfl, remainderFromDivision_significand_le_numerator _ _ _ _⟩)

/-- At a fixed exponent, magnitude is monotone in the significand. -/
private theorem abs_toReal_le_of_significand_le (r d : Numerics.Dyadic)
    (hexp : r.exponent = d.exponent) (hsig : r.significand ≤ d.significand) :
    |r.toReal| ≤ |d.toReal| := by
  rw [Dyadic.abs_toReal, Dyadic.abs_toReal, hexp]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hsig) (bpow_nonneg _)

/--
With a nonzero divisor, the remainder of two finite operands is exactly representable in an IEEE
encoding. The final rounding preserves the exact dyadic's real value and produces a finite
result, justifying the clear status on this branch.
-/
theorem remainderWithStatus_exact
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true) (dividend divisor : Model fmt)
    (exactDividend exactDivisor : Numerics.Dyadic)
    (hdividend : exactValue dividend = .finite exactDividend)
    (hdivisor : exactValue divisor = .finite exactDivisor)
    (hnonzero : exactDivisor.significand ≠ 0) :
    isFinite (remainder dividend divisor) = true ∧
      toReal (remainder dividend divisor) =
        (remainderDyadic exactDividend exactDivisor hnonzero).toReal := by
  have hda : toDyadic? dividend = some exactDividend := exactValue_eq_finite_iff.mp hdividend
  have hdb : toDyadic? divisor = some exactDivisor := exactValue_eq_finite_iff.mp hdivisor
  have hfinA := isFinite_eq_true_of_toDyadic?_some hda
  have hfinB := isFinite_eq_true_of_toDyadic?_some hdb
  have hboundA : |exactDividend.toReal| ≤ toReal (posMaxFinite fmt) := by
    have := abs_toReal_le_posMaxFinite_of_isIEEE_of_isFinite dividend hfmt hfinA
    simpa [toReal_eq, hda] using this
  have hboundB : |exactDivisor.toReal| ≤ toReal (posMaxFinite fmt) := by
    have := abs_toReal_le_posMaxFinite_of_isIEEE_of_isFinite divisor hfmt hfinB
    simpa [toReal_eq, hdb] using this
  have hsigA := toDyadic?_significand_lt dividend hda
  have hsigB := toDyadic?_significand_lt divisor hdb
  have hexpA := minSubnormalExponent_le_toDyadic? dividend hda
  have hexpB := minSubnormalExponent_le_toDyadic? divisor hdb
  rw [remainder_eq_value,
    remainderWithStatus_of_finite dividend divisor exactDividend exactDivisor hdividend hdivisor
      hnonzero]
  dsimp only
  by_cases hzero : (remainderDyadic exactDividend exactDivisor hnonzero).significand = 0
  · have hbeq : ((remainderDyadic exactDividend exactDivisor hnonzero).significand == 0) = true := by
      simp [hzero]
    simp only [hbeq, ite_true]
    refine ⟨isFinite_eq_true_of_isZero_eq_true _ (isZero_zero fmt exactDividend.negative), ?_⟩
    rw [toReal_zero]
    simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, hzero]
  · have hbeq :
        ((remainderDyadic exactDividend exactDivisor hnonzero).significand == 0) = false := by
      simp [hzero]
    simp only [hbeq, Bool.false_eq_true, ite_false]
    have hrep :
        (remainderDyadic exactDividend exactDivisor hnonzero).significand <
            2 ^ (fmt.fracWidth + 1) ∧
          fmt.minSubnormalExponent ≤ (remainderDyadic exactDividend exactDivisor hnonzero).exponent ∧
          |(remainderDyadic exactDividend exactDivisor hnonzero).toReal| ≤
            toReal (posMaxFinite fmt) := by
      rcases remainderDyadic_eq_or_le exactDividend exactDivisor hnonzero with
        heq | ⟨hexp, hsig⟩ | ⟨hexp, hsig⟩
      · rw [heq]
        exact ⟨hsigA, hexpA, hboundA⟩
      · exact ⟨lt_of_le_of_lt hsig hsigB, by rw [hexp]; exact hexpB,
          (abs_toReal_le_of_significand_le _ _ hexp hsig).trans hboundB⟩
      · exact ⟨lt_of_le_of_lt hsig hsigA, by rw [hexp]; exact hexpA,
          (abs_toReal_le_of_significand_le _ _ hexp hsig).trans hboundA⟩
    exact roundDyadic_of_representable fmt hfmt _ _ 0 (by simp) hrep.1 hrep.2.1 hrep.2.2

end Model
end FloatLib.Floats.Formats.BinaryInterchange
