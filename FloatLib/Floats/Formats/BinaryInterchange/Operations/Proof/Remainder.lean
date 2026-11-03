/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Model.RealSemantics
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Exact
import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Semantics

/-!
# IEEE remainder contracts

IEEE remainder subtracts the nearest integer multiple of the divisor, with ties going to an even
quotient. Reducing an aligned numerator modulo twice the divisor preserves both the remainder
and the quotient parity needed to resolve a tie.

The finite kernel has this exact rational semantics. For finite inputs and a nonzero divisor in
an IEEE encoding, the resulting dyadic is representable, so its final encoding loses no precision.
Zero divisors and infinities have their own value and status equations.

For finite operands and a nonzero divisor, the remainder is the dividend minus an integer
multiple of the divisor and at most half the divisor in magnitude.

When a nonzero remainder and the dividend have opposite signs, C's `fmod` adds the divisor with
the dividend's sign; `remainder_add_copySign_exact` proves that this addition is finite and exact.
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
large exponent gap guarantees that the nearest quotient is zero, so the kernel returns early.
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

/-- Remainder with `status := true` delivers the value of remainder. -/
@[simp] theorem value_remainder {fmt : FloatFormat}
    (dividend divisor : Model fmt) :
    (remainder dividend divisor (status := true)).value = remainder dividend divisor :=
  rfl

/-! ## Status-bearing exceptional branches -/

/--
For two finite operands with a nonzero divisor, the runtime encodes the selected dyadic remainder
and returns clear status and the ternary value `.eq`. A zero result uses the dividend's sign,
subject to the format's zero policy.
-/
theorem remainder_status_of_finite
    {fmt : FloatFormat} (dividend divisor : Model fmt)
    (exactDividend exactDivisor : Numerics.Dyadic)
    (hdividend : exactValue dividend = .finite exactDividend)
    (hdivisor : exactValue divisor = .finite exactDivisor)
    (hnonzero : exactDivisor.significand ≠ 0) :
    remainder dividend divisor (status := true) =
      let exact := remainderDyadic exactDividend exactDivisor hnonzero
      let value :=
        if exact.significand == 0 then
          zero fmt exactDividend.negative
        else
          roundDyadic fmt exact
      { value, status := .clear, ternary := .eq } := by
  simp [remainder, Internal.Status.remainder, hdividend, hdivisor, hnonzero, outcomeWithInvalid]

/-- A finite zero divisor makes IEEE remainder invalid. -/
theorem remainder_status_of_zero_divisor
    {fmt : FloatFormat} (dividend divisor : Model fmt)
    (exactDividend exactDivisor : Numerics.Dyadic)
    (hdividend : exactValue dividend = .finite exactDividend)
    (hdivisor : exactValue divisor = .finite exactDivisor)
    (hzero : exactDivisor.significand = 0) :
    remainder dividend divisor (status := true) =
      { value := invalidResult fmt, status := { invalid := true }, ternary := .eq } := by
  simp [remainder, Internal.Status.remainder, hdividend, hdivisor, hzero, outcomeWithInvalid]

/-- A finite dividend is unchanged when the divisor is infinite. -/
theorem remainder_status_of_finite_of_infinity
    {fmt : FloatFormat} (dividend divisor : Model fmt)
    (exact : Numerics.Dyadic) (negative : Bool)
    (hdividend : exactValue dividend = .finite exact)
    (hdivisor : exactValue divisor = .infinity negative) :
    remainder dividend divisor (status := true) =
      { value := dividend, status := .clear, ternary := .eq } := by
  simp [remainder, Internal.Status.remainder, hdividend, hdivisor, outcomeWithInvalid]

/-- An infinite dividend and finite divisor make IEEE remainder invalid. -/
theorem remainder_status_of_infinity_of_finite
    {fmt : FloatFormat} (dividend divisor : Model fmt)
    (dividendNegative : Bool) (exactDivisor : Numerics.Dyadic)
    (hdividend : exactValue dividend = .infinity dividendNegative)
    (hdivisor : exactValue divisor = .finite exactDivisor) :
    remainder dividend divisor (status := true) =
      { value := invalidResult fmt, status := { invalid := true }, ternary := .eq } := by
  simp [remainder, Internal.Status.remainder, hdividend, hdivisor, outcomeWithInvalid]

/-- Two infinite operands make IEEE remainder invalid. -/
theorem remainder_status_of_infinity_of_infinity
    {fmt : FloatFormat} (dividend divisor : Model fmt)
    (dividendNegative divisorNegative : Bool)
    (hdividend : exactValue dividend = .infinity dividendNegative)
    (hdivisor : exactValue divisor = .infinity divisorNegative) :
    remainder dividend divisor (status := true) =
      { value := invalidResult fmt, status := { invalid := true }, ternary := .eq } := by
  simp [remainder, Internal.Status.remainder, hdividend, hdivisor, outcomeWithInvalid]

/-! ## Exactness of the encoded remainder -/

/--
When the raw remainder is at most the denominator, so is the selected magnitude, `remainder` or
`denominator - remainder`.
-/
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
`remainder_exact`.
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
theorem remainder_exact
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
  have hboundA := abs_toReal_le_posMaxFinite_of_toDyadic?_some dividend hda
  have hboundB := abs_toReal_le_posMaxFinite_of_toDyadic?_some divisor hdb
  have hsigA := toDyadic?_significand_lt dividend hda
  have hsigB := toDyadic?_significand_lt divisor hdb
  have hexpA := minSubnormalExponent_le_toDyadic? dividend hda
  have hexpB := minSubnormalExponent_le_toDyadic? divisor hdb
  rw [← value_remainder,
    remainder_status_of_finite dividend divisor exactDividend exactDivisor hdividend hdivisor
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


/-! ## The truncating remainder -/

/-- The exact remainder differs from the dividend by an integer multiple of the divisor. -/
private theorem remainderDyadic_toRat_eq_sub (dividend divisor : Numerics.Dyadic)
    (h : divisor.significand ≠ 0) :
    ∃ k : ℤ, (remainderDyadic dividend divisor h).toRat = dividend.toRat - k * divisor.toRat := by
  rw [remainderDyadic_toRat]
  have sgn (d : Numerics.Dyadic) : (Rat.ofInt d.signedSignificand) =
      (if d.negative then -1 else 1) * (d.significand : ℚ) := by
    cases hd : d.negative <;> simp [Numerics.Dyadic.signedSignificand, hd]
  let sx : ℤ := if dividend.negative then -1 else 1
  let sy : ℤ := if divisor.negative then -1 else 1
  by_cases hexp : divisor.exponent ≤ dividend.exponent
  · rw [ite_eq_left hexp]
    dsimp only
    set n := Int.toNat (dividend.exponent - divisor.exponent) with hn
    have hsh : Nat.shiftLeft dividend.significand n = dividend.significand * 2 ^ n :=
      Nat.shiftLeft_eq _ _
    rw [hsh]
    set q := roundQuotientEven (dividend.significand * 2 ^ n) divisor.significand
    refine ⟨sx * sy * q, ?_⟩
    have hshift : (n : ℤ) = dividend.exponent - divisor.exponent := Int.toNat_of_nonneg (by omega)
    have hpow : (2 : ℚ) ^ dividend.exponent = (2 : ℚ) ^ n * 2 ^ divisor.exponent := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num), hshift]; congr 1; ring
    simp only [Numerics.Dyadic.toRat, sgn, hpow, sx, sy]
    cases dividend.negative <;> cases divisor.negative <;> simp [Rat.ofInt_eq_cast] <;> ring
  · rw [ite_eq_right hexp]
    dsimp only
    set n := Int.toNat (divisor.exponent - dividend.exponent) with hn
    have hsh : Nat.shiftLeft divisor.significand n = divisor.significand * 2 ^ n :=
      Nat.shiftLeft_eq _ _
    rw [hsh]
    set q := roundQuotientEven dividend.significand (divisor.significand * 2 ^ n)
    refine ⟨sx * sy * q, ?_⟩
    have hshift : (n : ℤ) = divisor.exponent - dividend.exponent := Int.toNat_of_nonneg (by omega)
    have hpow : (2 : ℚ) ^ divisor.exponent = (2 : ℚ) ^ n * 2 ^ dividend.exponent := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num), hshift]; congr 1; ring
    simp only [Numerics.Dyadic.toRat, sgn, hpow, sx, sy]
    cases dividend.negative <;> cases divisor.negative <;> simp [Rat.ofInt_eq_cast] <;> ring

/--
When the divisor exponent is at most the dividend's, the exact remainder of a nonzero dividend has
the divisor's exponent and a significand no larger than the divisor's.
-/
private theorem remainderDyadic_of_exponent_le
    (dividend divisor : Numerics.Dyadic) (hdivisor : divisor.significand ≠ 0)
    (hdividend : dividend.significand ≠ 0) (hexp : divisor.exponent ≤ dividend.exponent) :
    (remainderDyadic dividend divisor hdivisor).exponent = divisor.exponent ∧
      (remainderDyadic dividend divisor hdivisor).significand ≤ divisor.significand := by
  unfold remainderDyadic
  simp only [beq_iff_eq, hdividend, ite_false]
  rw [ite_eq_left hexp]
  exact ⟨rfl, remainderFromDivision_significand_le_denominator _ _ _ _ _
    (Nat.mod_lt _ (Nat.pos_of_ne_zero hdivisor)).le⟩

/-- A binary power in Flocq's radix-two notation is the real power of two. -/
private theorem bpow_binaryRadix (exponent : ℤ) :
    FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent = (2 : ℝ) ^ exponent := by
  simp [FloatLib.Floats.Formats.Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal]

/--
An integer multiple `m * 2^e` with `|m| < 2^(fracWidth + 1)` and `e` at least the minimum subnormal
exponent belongs to the descriptor's grid.
-/
private theorem genericFormat_int_mul_zpow (fmt : FloatFormat) (m e : ℤ)
    (hm : m.natAbs < 2 ^ (fmt.fracWidth + 1)) (he : fmt.minSubnormalExponent ≤ e) :
    genericFormat Numerics.binaryRadix (fexpOf fmt) ((m : ℝ) * (2 : ℝ) ^ e) := by
  have h := Dyadic.genericFormat_of_eq_mul_pow2 fmt ⟨decide (m < 0), m.natAbs, e⟩ m.natAbs 0
    (by simp) hm he
  rw [Dyadic.toReal_mk, bpow_binaryRadix, Nat.cast_natAbs, Int.cast_abs] at h
  convert h using 2
  rcases lt_or_ge m 0 with hneg | hnonneg
  · have : (m : ℝ) < 0 := by exact_mod_cast hneg
    simp [hneg, abs_of_neg this]
  · have : (0 : ℝ) ≤ m := by exact_mod_cast hnonneg
    simp [not_lt.mpr hnonneg, abs_of_nonneg this]

/-- Nearest-even quotient rounding leaves a residue of at most half the denominator. -/
private theorem abs_sub_roundQuotientEven_mul_le (numerator denominator : Nat)
    (h : denominator ≠ 0) :
    |((Int.ofNat numerator - Int.ofNat (roundQuotientEven numerator denominator * denominator) :
        ℤ) : ℚ)| ≤ (denominator : ℚ) / 2 := by
  have herr := roundQuotientEven_error_le_half numerator denominator h
  have hpos : (0 : ℚ) < denominator := by exact_mod_cast Nat.pos_of_ne_zero h
  have heq : ((Int.ofNat numerator -
      Int.ofNat (roundQuotientEven numerator denominator * denominator) : ℤ) : ℚ) =
      -(((roundQuotientEven numerator denominator : Nat) : ℚ) - (numerator : ℚ) / denominator) *
        denominator := by
    simp only [Int.ofNat_eq_natCast]
    push_cast
    field_simp
    ring
  rw [heq, abs_mul, abs_neg, abs_of_pos hpos]
  calc _ ≤ (1 / 2 : ℚ) * denominator := mul_le_mul_of_nonneg_right herr hpos.le
    _ = _ := by ring

/-- The exact remainder is at most half the divisor in magnitude. -/
private theorem remainderDyadic_abs_toRat_le (dividend divisor : Numerics.Dyadic)
    (h : divisor.significand ≠ 0) :
    |(remainderDyadic dividend divisor h).toRat| ≤ |divisor.toRat| / 2 := by
  have hpow (e : ℤ) : (0 : ℚ) < (2 : ℚ) ^ e := zpow_pos (by norm_num) e
  have habs (negative : Bool) (c e : ℤ) :
      |Rat.ofInt (if negative then -c else c) * (2 : ℚ) ^ e| = |(c : ℚ)| * (2 : ℚ) ^ e := by
    rw [abs_mul, abs_of_pos (hpow e)]
    cases negative <;> simp [Rat.ofInt_eq_cast]
  have hdivisor : |divisor.toRat| = (divisor.significand : ℚ) * (2 : ℚ) ^ divisor.exponent := by
    simp only [Numerics.Dyadic.toRat, Numerics.Dyadic.signedSignificand]
    rw [abs_mul, abs_of_pos (hpow _)]
    cases divisor.negative <;> simp [Rat.ofInt_eq_cast]
  rw [remainderDyadic_toRat, hdivisor]
  by_cases hexp : divisor.exponent ≤ dividend.exponent
  · rw [ite_eq_left hexp]
    dsimp only
    rw [habs]
    have hres := abs_sub_roundQuotientEven_mul_le
      (Nat.shiftLeft dividend.significand (Int.toNat (dividend.exponent - divisor.exponent)))
      divisor.significand h
    calc _ ≤ (divisor.significand : ℚ) / 2 * (2 : ℚ) ^ divisor.exponent :=
          mul_le_mul_of_nonneg_right hres (hpow _).le
      _ = _ := by ring
  · rw [ite_eq_right hexp]
    dsimp only
    rw [habs]
    set n := Int.toNat (divisor.exponent - dividend.exponent) with hn
    have hsh : Nat.shiftLeft divisor.significand n = divisor.significand * 2 ^ n :=
      Nat.shiftLeft_eq _ _
    rw [hsh]
    have hres := abs_sub_roundQuotientEven_mul_le dividend.significand
      (divisor.significand * 2 ^ n) (Nat.mul_ne_zero h (pow_ne_zero n (by norm_num)))
    have hshift : (n : ℤ) = divisor.exponent - dividend.exponent := Int.toNat_of_nonneg (by omega)
    have hpow' : (2 : ℚ) ^ divisor.exponent = (2 : ℚ) ^ n * 2 ^ dividend.exponent := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num), hshift]; congr 1; ring
    rw [hpow']
    calc _ ≤ ((divisor.significand * 2 ^ n : ℕ) : ℚ) / 2 * (2 : ℚ) ^ dividend.exponent :=
          mul_le_mul_of_nonneg_right hres (hpow _).le
      _ = _ := by push_cast; ring

/--
The IEEE remainder of finite operands with a nonzero divisor is the dividend minus an integer
multiple of the divisor.
-/
theorem exists_toReal_remainder_eq_sub
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true) (dividend divisor : Model fmt)
    (hdividend : isFinite dividend = true) (hdivisor : isFinite divisor = true)
    (hnonzero : isZero divisor = false) :
    ∃ k : ℤ, toReal (remainder dividend divisor) = toReal dividend - k * toReal divisor := by
  obtain ⟨X, hX⟩ := exists_toDyadic?_of_isFinite hdividend
  obtain ⟨Y, hY⟩ := exists_toDyadic?_of_isFinite hdivisor
  have hYsig : Y.significand ≠ 0 :=
    significand_ne_zero_of_toDyadic?_some_of_isZero_eq_false hY hnonzero
  obtain ⟨-, hrval⟩ := remainder_exact hfmt dividend divisor X Y
    (exactValue_eq_finite_iff.mpr hX) (exactValue_eq_finite_iff.mpr hY) hYsig
  obtain ⟨k, hk⟩ := remainderDyadic_toRat_eq_sub X Y hYsig
  refine ⟨k, ?_⟩
  rw [hrval, show toReal dividend = X.toReal by simp [toReal_eq, hX],
    show toReal divisor = Y.toReal by simp [toReal_eq, hY]]
  have h := congrArg (fun q : ℚ => (q : ℝ)) hk
  simpa using h

/--
The IEEE remainder of finite operands with a nonzero divisor is at most half the divisor in
magnitude.
-/
theorem abs_toReal_remainder_le
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true) (dividend divisor : Model fmt)
    (hdividend : isFinite dividend = true) (hdivisor : isFinite divisor = true)
    (hnonzero : isZero divisor = false) :
    |toReal (remainder dividend divisor)| ≤ |toReal divisor| / 2 := by
  obtain ⟨X, hX⟩ := exists_toDyadic?_of_isFinite hdividend
  obtain ⟨Y, hY⟩ := exists_toDyadic?_of_isFinite hdivisor
  have hYsig : Y.significand ≠ 0 :=
    significand_ne_zero_of_toDyadic?_some_of_isZero_eq_false hY hnonzero
  obtain ⟨-, hrval⟩ := remainder_exact hfmt dividend divisor X Y
    (exactValue_eq_finite_iff.mpr hX) (exactValue_eq_finite_iff.mpr hY) hYsig
  rw [hrval, show toReal divisor = Y.toReal by simp [toReal_eq, hY]]
  have h := (Rat.cast_le (K := ℝ)).mpr (remainderDyadic_abs_toRat_le X Y hYsig)
  push_cast at h
  simpa using h

/--
If the IEEE remainder of finite operands with a nonzero divisor is nonzero and its sign differs
from the dividend's, adding the divisor with the dividend's sign is finite and exact.
-/
theorem remainder_add_copySign_exact
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true) (dividend divisor : Model fmt)
    (hdividend : isFinite dividend = true) (hdivisor : isFinite divisor = true)
    (hnonzero : isZero divisor = false)
    (hzero : isZero (remainder dividend divisor) = false)
    (hsign : signBit (remainder dividend divisor) ≠ signBit dividend) :
    isFinite (add (remainder dividend divisor) (copySign divisor dividend)) = true ∧
      toReal (add (remainder dividend divisor) (copySign divisor dividend)) =
        toReal (remainder dividend divisor) + toReal (copySign divisor dividend) := by
  obtain ⟨X, hX⟩ := exists_toDyadic?_of_isFinite hdividend
  obtain ⟨Y, hY⟩ := exists_toDyadic?_of_isFinite hdivisor
  have hYsig : Y.significand ≠ 0 :=
    significand_ne_zero_of_toDyadic?_some_of_isZero_eq_false hY hnonzero
  obtain ⟨hrfin, hrval⟩ := remainder_exact hfmt dividend divisor X Y
    (exactValue_eq_finite_iff.mpr hX) (exactValue_eq_finite_iff.mpr hY) hYsig
  obtain ⟨Dr, hDr⟩ := exists_toDyadic?_of_isFinite hrfin
  have hDrsig : Dr.significand ≠ 0 :=
    significand_ne_zero_of_toDyadic?_some_of_isZero_eq_false hDr hzero
  have hDrval : Dr.toReal = (remainderDyadic X Y hYsig).toReal := by
    rw [← hrval]; simp [toReal_eq, hDr]
  set R := remainderDyadic X Y hYsig with hR
  have hRsig : R.significand ≠ 0 := by
    intro h
    apply hDrsig
    rw [← Dyadic.toReal_eq_zero_iff] at h ⊢
    rw [hDrval]
    exact h
  have hXsig : X.significand ≠ 0 := by
    intro h
    apply hRsig
    rw [hR, remainderDyadic_of_significand_eq_zero X Y h hYsig]
    exact h
  have hXneg : X.negative = signBit dividend := sign_eq_signBit_of_toDyadic?_some hX
  have hYneg : Y.negative = signBit divisor := sign_eq_signBit_of_toDyadic?_some hY
  have hDrneg : Dr.negative = !X.negative := by
    rw [sign_eq_signBit_of_toDyadic?_some hDr, hXneg]
    revert hsign
    cases signBit (remainder dividend divisor) <;> cases signBit dividend <;> simp
  have hsigns : (X.negative = true ∧ X.toReal < 0 ∧ 0 < R.toReal) ∨
      (X.negative = false ∧ 0 < X.toReal ∧ R.toReal < 0) := by
    cases hx : X.negative
    · have hd : Dr.negative = true := by rw [hDrneg, hx]; rfl
      refine Or.inr ⟨rfl, Dyadic.toReal_pos_of_negative_eq_false hx hXsig, ?_⟩
      rw [← hDrval]
      exact Dyadic.toReal_lt_zero_of_negative_eq_true hd hDrsig
    · have hd : Dr.negative = false := by rw [hDrneg, hx]; rfl
      refine Or.inl ⟨rfl, Dyadic.toReal_lt_zero_of_negative_eq_true hx hXsig, ?_⟩
      rw [← hDrval]
      exact Dyadic.toReal_pos_of_negative_eq_false hd hDrsig
  have hsigned := FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt hfmt
  have hb : toReal divisor = Y.toReal := by simp [toReal_eq, hY]
  have hcfin : isFinite (copySign divisor dividend) = true := by
    rw [isFinite_copySign]; exact hdivisor
  have hc : toReal (copySign divisor dividend) =
      (if X.negative then -1 else 1) * |Y.toReal| := by
    have htoggle : toReal (toggleSign divisor) = -Y.toReal := by
      rw [← neg_eq_toggleSign_of_supportsSignedZero divisor hsigned, toReal_neg divisor hdivisor,
        hb]
    have hYabs : |Y.toReal| = if Y.negative then -Y.toReal else Y.toReal := by
      cases hy : Y.negative
      · exact abs_of_nonneg (Dyadic.toReal_nonneg_of_negative_eq_false hy)
      · exact abs_of_nonpos (Dyadic.toReal_nonpos_of_negative_eq_true hy)
    unfold copySign
    rw [hsigned, ← hXneg, ← hYneg, hYabs]
    cases X.negative <;> cases Y.negative <;> simp [hb, htoggle]
  have hboundA := abs_toReal_le_posMaxFinite_of_toDyadic?_some dividend hX
  have hboundB := abs_toReal_le_posMaxFinite_of_toDyadic?_some divisor hY
  have hsigA := toDyadic?_significand_lt dividend hX
  have hsigB := toDyadic?_significand_lt divisor hY
  have hexpA := minSubnormalExponent_le_toDyadic? dividend hX
  have hexpB := minSubnormalExponent_le_toDyadic? divisor hY
  -- On the divisor's grid the corrected magnitude `|y| - |r|` has a smaller significand than `y`.
  have divisorGrid : R.exponent = Y.exponent → R.significand ≤ Y.significand →
      genericFormat Numerics.binaryRadix (fexpOf fmt) (|Y.toReal| - |R.toReal|) ∧
        |(|Y.toReal| - |R.toReal|)| ≤ toReal (posMaxFinite fmt) := by
    intro hRe hRs
    have ht : |Y.toReal| - |R.toReal| =
        (((Y.significand : ℤ) - R.significand : ℤ) : ℝ) * (2 : ℝ) ^ Y.exponent := by
      rw [Dyadic.abs_toReal, Dyadic.abs_toReal, hRe, bpow_binaryRadix]; push_cast; ring
    have hle : |R.toReal| ≤ |Y.toReal| := abs_toReal_le_of_significand_le R Y hRe hRs
    refine ⟨?_, ?_⟩
    · rw [ht]
      exact genericFormat_int_mul_zpow fmt _ _ (by omega) hexpB
    · rw [abs_of_nonneg (by linarith)]
      linarith [abs_nonneg R.toReal]
  have key : genericFormat Numerics.binaryRadix (fexpOf fmt) (|Y.toReal| - |R.toReal|) ∧
      |(|Y.toReal| - |R.toReal|)| ≤ toReal (posMaxFinite fmt) := by
    by_cases hexp : Y.exponent ≤ X.exponent
    · obtain ⟨hRe, hRs⟩ := remainderDyadic_of_exponent_le X Y hYsig hXsig hexp
      rw [← hR] at hRe hRs
      exact divisorGrid hRe hRs
    rcases remainderDyadic_eq_or_le X Y hYsig with heq | ⟨hRe, hRs⟩ | ⟨hRe, hRs⟩
    · have hRX : R.toReal = X.toReal := by rw [hR, heq]
      exfalso
      rcases hsigns with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> linarith
    · rw [← hR] at hRe hRs
      exact divisorGrid hRe hRs
    rw [← hR] at hRe hRs
    -- On the dividend's finer grid, `x = k * y + r` with `k ≠ 0` bounds `|y| - |r|` by `|x|`.
    have hlt : X.exponent < Y.exponent := lt_of_not_ge hexp
    obtain ⟨k, hk⟩ := remainderDyadic_toRat_eq_sub X Y hYsig
    rw [← hR] at hk
    have hkR : R.toReal = X.toReal - k * Y.toReal := by
      have h := congrArg (fun q : ℚ => (q : ℝ)) hk
      simpa using h
    have hRX : |R.toReal| ≤ |X.toReal| := abs_toReal_le_of_significand_le R X hRe hRs
    have hsum : |Y.toReal| ≤ |X.toReal| + |R.toReal| := by
      have hk0 : k ≠ 0 := by
        rintro rfl
        simp only [Int.cast_zero, zero_mul, sub_zero] at hkR
        rcases hsigns with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> linarith
      have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk0
      have hdiff : |X.toReal| + |R.toReal| = |(k : ℝ)| * |Y.toReal| := by
        rw [← abs_mul]
        have hxr : (k : ℝ) * Y.toReal = X.toReal - R.toReal := by linarith
        rw [hxr]
        rcases hsigns with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
        · rw [abs_of_neg h1, abs_of_pos h2, abs_of_neg (by linarith)]; ring
        · rw [abs_of_pos h1, abs_of_neg h2, abs_of_pos (by linarith)]; ring
      rw [hdiff]
      exact le_mul_of_one_le_left (abs_nonneg _) hk1
    have htX : |(|Y.toReal| - |R.toReal|)| ≤ |X.toReal| := by
      rw [abs_le]; constructor <;> linarith [abs_nonneg Y.toReal]
    set n := (Y.exponent - X.exponent).toNat with hn
    have hn' : (n : ℤ) = Y.exponent - X.exponent := Int.toNat_of_nonneg (by omega)
    have hpow : (2 : ℝ) ^ Y.exponent = (2 : ℝ) ^ n * (2 : ℝ) ^ X.exponent := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num), hn']; congr 1; ring
    set m : ℤ := ((Y.significand * 2 ^ n : ℕ) : ℤ) - R.significand with hm
    have ht : |Y.toReal| - |R.toReal| = (m : ℝ) * (2 : ℝ) ^ X.exponent := by
      rw [Dyadic.abs_toReal, Dyadic.abs_toReal, hRe, bpow_binaryRadix, bpow_binaryRadix, hpow,
        hm]
      push_cast; ring
    have hmX : m.natAbs ≤ X.significand := by
      have hpos : (0 : ℝ) < (2 : ℝ) ^ X.exponent := zpow_pos (by norm_num) _
      rw [ht, abs_mul, abs_of_pos hpos, Dyadic.abs_toReal, bpow_binaryRadix] at htX
      have h := le_of_mul_le_mul_right htX hpos
      rw [← Int.cast_abs, ← Nat.cast_natAbs] at h
      exact_mod_cast h
    refine ⟨?_, htX.trans hboundA⟩
    rw [ht]
    exact genericFormat_int_mul_zpow fmt m _ (lt_of_le_of_lt hmX hsigA) hexpA
  have hsum : toReal (remainder dividend divisor) + toReal (copySign divisor dividend) =
      (if X.negative then -1 else 1) * (|Y.toReal| - |R.toReal|) := by
    rw [hrval, hc]
    rcases hsigns with ⟨hx, -, h2⟩ | ⟨hx, -, h2⟩
    · rw [hx, abs_of_pos h2]; simp only [ite_true]; ring
    · rw [hx, abs_of_neg h2]; simp only [Bool.false_eq_true, ite_false]; ring
  have hgen : genericFormat Numerics.binaryRadix (fexpOf fmt)
      (toReal (remainder dividend divisor) + toReal (copySign divisor dividend)) := by
    rw [hsum]
    split_ifs
    · rw [neg_one_mul]; exact generic_format_neg _ key.1
    · rw [one_mul]; exact key.1
  have habs : |toReal (remainder dividend divisor) + toReal (copySign divisor dividend)| ≤
      toReal (posMaxFinite fmt) := by
    rw [hsum, abs_mul]
    split_ifs <;> simpa using key.2
  have hfin := isFinite_add_of_abs_toReal_add_le_posMaxFinite _ _ hfmt hrfin hcfin habs
  refine ⟨hfin, ?_⟩
  rw [toReal_add_eq_roundAt _ _ hfmt hfin]
  exact round_preserves_generic nearestEven _ hgen

end Model
end FloatLib.Floats.Formats.BinaryInterchange
