/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Deterministic.ShiftRight
import Mathlib.Tactic.Ring

/-!
# Magnitude rounding rules

Rounding a signed value to a binary grid reduces, once its sign is known, to rounding a
nonnegative magnitude to one of the two integers around it. Four rules cover the IEEE 754
rounding directions and MPFR's rounding away from zero: truncation, rounding up, and the two
nearest rules, which differ only at an exact tie.

`MagnitudeRounding` names the four rules, and `MagnitudeRounding.increment` decides each of them
from the three rounding bits: the least retained bit, the guard bit, and the sticky bit.
`roundShiftRight` applies a rule to a division by a power of two and `roundQuotient` to a division
by any natural number. Their nearest-even rules call `roundShiftRightEven` and
`roundQuotientEven`, so each division keeps one nearest-even implementation. The other rules use
shifts in `roundShiftRight` and a single division in `roundQuotient`.

The `@[csimp]` machine-word replacements of `roundShiftRightEven` and `roundQuotientEven` apply
where those functions are called by name. A call through `roundShiftRight` or `roundQuotient` is
compiled from the definitions here, where those replacements are not yet registered, so it runs
the arbitrary-precision definition.

The theorems give each rule in guard-and-sticky form, relate the shift and quotient forms, express
nearest-away as nearest-even with ties sent to the ceiling, and read the ternary value (whether the
delivered value is below, equal to, or above the exact one) off the rounding bits.
-/

@[expose] public section

namespace FloatLib.Numerics

/-- Rule for rounding a nonnegative quotient to one of the two integers around it. -/
inductive MagnitudeRounding where
  /-- Keep the integer part. -/
  | down
  /-- Take the next integer whenever the quotient is not an integer. -/
  | up
  /-- Take the nearer integer, and the even one at an exact tie. -/
  | nearestEven
  /-- Take the nearer integer, and the larger one at an exact tie. -/
  | nearestAway
  deriving DecidableEq, Repr

namespace MagnitudeRounding

/--
Whether `rule` adds one to the truncated quotient.

`lsb` is the least significant retained bit, `guard` the most significant discarded bit, and
`sticky` whether any discarded bit below the guard bit is set. When neither `guard` nor `sticky`
is set the quotient is exact and no rule increments it.
-/
@[inline] def increment (rule : MagnitudeRounding) (lsb guard sticky : Bool) : Bool :=
  match rule with
  | .down => false
  | .up => guard || sticky
  | .nearestEven => guard && (sticky || lsb)
  | .nearestAway => guard

/-- No rule increments an exact quotient. -/
@[simp] theorem increment_false_false (rule : MagnitudeRounding) (lsb : Bool) :
    rule.increment lsb false false = false := by
  cases rule <;> rfl

end MagnitudeRounding

/-! ## Shift rounding -/

/--
`⌈value / 2^shift⌉` for natural numbers.

One shift gives the truncated quotient, and shifting it back decides whether a nonzero remainder
carries the result to the next integer.
-/
@[inline] def shiftRightCeil (value shift : Nat) : Nat :=
  if shift == 0 then
    value
  else
    let quotient := Nat.shiftRight value shift
    let remainder := value - Nat.shiftLeft quotient shift
    if remainder == 0 then quotient else quotient + 1

/--
Whether the bits that a right shift by `shift` discards are exactly one half of a retained unit.

That is the case when the guard bit is set and every lower discarded bit is clear. A clear guard
bit settles the answer before any remainder is formed, so a shift far beyond the width of `value`
costs one shift.
-/
@[inline] def shiftRightIsTie (value shift : Nat) : Bool :=
  shift != 0 && value.testBit (shift - 1) && shiftRightRemainder value (shift - 1) == 0

/--
Round `value / 2^shift` to an integer under `rule`.

Truncation is a right shift and rounding up is `shiftRightCeil`. Nearest-even is
`roundShiftRightEven`, run through its arbitrary-precision definition. Nearest-away keeps the guard
bit in a first shift, adds one, and drops it in a second, so the guard bit alone decides. A zero
shift returns `value` under every rule.
-/
@[inline] def roundShiftRight (rule : MagnitudeRounding) (value shift : Nat) : Nat :=
  match rule with
  | .down => Nat.shiftRight value shift
  | .up => shiftRightCeil value shift
  | .nearestEven => roundShiftRightEven value shift
  | .nearestAway =>
      if shift == 0 then value else Nat.shiftRight (Nat.shiftRight value (shift - 1) + 1) 1

/-! ## Quotient rounding -/

/--
Round `numerator / denominator` to an integer under `rule`.

Nearest-even is `roundQuotientEven`, again through its arbitrary-precision definition. The other
rules use one division each: rounding up divides `numerator - 1`, and nearest-away divides
`2 * numerator + denominator` by `2 * denominator`.

A zero denominator has no quotient. Truncation, rounding up, and nearest-away return `0` there.
Nearest-even keeps the convention of `roundQuotientEven`, which returns `0` for a zero numerator and
`1` otherwise.
-/
@[inline] def roundQuotient (rule : MagnitudeRounding) (numerator denominator : Nat) : Nat :=
  match rule with
  | .down => numerator / denominator
  | .up =>
      if numerator == 0 || denominator == 0 then 0 else (numerator - 1) / denominator + 1
  | .nearestEven => roundQuotientEven numerator denominator
  | .nearestAway => (2 * numerator + denominator) / (2 * denominator)

/-! ## Unfolding lemmas -/

/-- Truncating shift rounding is a right shift. -/
@[simp] theorem roundShiftRight_down (value shift : Nat) :
    roundShiftRight .down value shift = Nat.shiftRight value shift :=
  rfl

/-- Upward shift rounding is `shiftRightCeil`. -/
@[simp] theorem roundShiftRight_up (value shift : Nat) :
    roundShiftRight .up value shift = shiftRightCeil value shift :=
  rfl

/-- Nearest-even shift rounding is `roundShiftRightEven`. -/
@[simp] theorem roundShiftRight_nearestEven (value shift : Nat) :
    roundShiftRight .nearestEven value shift = roundShiftRightEven value shift :=
  rfl

/-- Truncating quotient rounding is natural division. -/
@[simp] theorem roundQuotient_down (numerator denominator : Nat) :
    roundQuotient .down numerator denominator = numerator / denominator :=
  rfl

/-- Nearest-even quotient rounding is `roundQuotientEven`. -/
@[simp] theorem roundQuotient_nearestEven (numerator denominator : Nat) :
    roundQuotient .nearestEven numerator denominator =
      roundQuotientEven numerator denominator :=
  rfl

/-- A ceiling shift by zero returns its argument. -/
@[simp] theorem shiftRightCeil_zero (value : Nat) : shiftRightCeil value 0 = value := by
  simp [shiftRightCeil]

/-- A zero shift is exact under every rule. -/
@[simp] theorem roundShiftRight_zero (rule : MagnitudeRounding) (value : Nat) :
    roundShiftRight rule value 0 = value := by
  cases rule <;> simp [roundShiftRight]

/-- Rounding up with a zero denominator returns zero. -/
@[simp] theorem roundQuotient_up_zero_right (numerator : Nat) :
    roundQuotient .up numerator 0 = 0 := by
  simp [roundQuotient]

/-- Nearest-away rounding with a zero denominator returns zero. -/
@[simp] theorem roundQuotient_nearestAway_zero_right (numerator : Nat) :
    roundQuotient .nearestAway numerator 0 = 0 := by
  simp [roundQuotient]

/-- A denominator of one is exact under every rule. -/
@[simp] theorem roundQuotient_one_right (rule : MagnitudeRounding) (numerator : Nat) :
    roundQuotient rule numerator 1 = numerator := by
  cases rule with
  | down => simp [roundQuotient]
  | up =>
      by_cases hzero : numerator = 0
      · simp [roundQuotient, hzero]
      · simp [roundQuotient, hzero]
        omega
  | nearestEven => simp [roundQuotient, roundQuotientEven, Nat.mod_one]
  | nearestAway => simp only [roundQuotient, Nat.mul_one]; omega

/-! ## Rounding bits -/

/--
A shift by a positive amount is inexact exactly when its guard bit or its sticky bit is set.
-/
theorem mod_two_pow_ne_zero_iff_guard_or_sticky (value shift : Nat) (hshift : 0 < shift) :
    value % 2 ^ shift ≠ 0 ↔
      (value.testBit (shift - 1) || decide (value % 2 ^ (shift - 1) ≠ 0)) = true := by
  obtain ⟨t, rfl⟩ : ∃ t, shift = t + 1 := ⟨shift - 1, by omega⟩
  rw [Nat.add_sub_cancel, mod_two_pow_succ_eq]
  cases value.testBit t <;> simp

/-- A positive shift is a tie exactly when it discards half of a retained unit. -/
theorem shiftRightIsTie_eq_true_iff (value shift : Nat) :
    shiftRightIsTie value shift = true ↔ 0 < shift ∧ value % 2 ^ shift = 2 ^ (shift - 1) := by
  cases shift with
  | zero => simp [shiftRightIsTie]
  | succ t =>
      have hlow : value % 2 ^ t < 2 ^ t := Nat.mod_lt _ (Nat.two_pow_pos t)
      simp only [shiftRightIsTie, Nat.add_sub_cancel, shiftRightRemainder_eq_mod,
        mod_two_pow_succ_eq]
      cases value.testBit t
      · simp
        omega
      · simp

/-- A tie is a set guard bit with a clear sticky bit. -/
theorem shiftRightIsTie_eq_guard_and_not_sticky (value shift : Nat) (hshift : 0 < shift) :
    shiftRightIsTie value shift =
      (value.testBit (shift - 1) && !decide (value % 2 ^ (shift - 1) ≠ 0)) := by
  obtain ⟨t, rfl⟩ : ∃ t, shift = t + 1 := ⟨shift - 1, by omega⟩
  simp only [shiftRightIsTie, Nat.add_sub_cancel, shiftRightRemainder_eq_mod]
  by_cases hsticky : value % 2 ^ t = 0 <;> cases value.testBit t <;> simp [hsticky]

/-- The ceiling shift is the truncated quotient plus one for a nonzero remainder. -/
theorem shiftRightCeil_eq (value shift : Nat) :
    shiftRightCeil value shift =
      value / 2 ^ shift + if value % 2 ^ shift = 0 then 0 else 1 := by
  by_cases hshift : shift = 0
  · subst shift
    simp [Nat.mod_one]
  · have hremainder :
        value - Nat.shiftLeft (Nat.shiftRight value shift) shift = value % 2 ^ shift := by
      simpa [shiftRightRemainder] using shiftRightRemainder_eq_mod value shift
    simp only [shiftRightCeil, beq_iff_eq, hshift, ite_false]
    rw [hremainder]
    simp only [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
    by_cases hzero : value % 2 ^ shift = 0 <;> simp [hzero]

/-- Nearest-away shift rounding adds the guard bit to the truncated quotient. -/
private theorem nearestAway_shiftRight_eq (value t : Nat) :
    Nat.shiftRight (Nat.shiftRight value t + 1) 1 =
      value / 2 ^ (t + 1) + if value.testBit t then 1 else 0 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  change (value >>> t + 1) >>> 1 = _
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, pow_one, pow_succ,
    ← Nat.div_div_eq_div_mul]
  have hmod : value / 2 ^ t % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases hodd : value / 2 ^ t % 2 = 1
  · simp only [hodd, decide_true, ite_true]
    omega
  · simp only [hodd, decide_false, Bool.false_eq_true, ite_false]
    omega

/--
Every rule in guard-and-sticky form.

For a positive shift, the rounded value is the truncated quotient, plus one exactly when the rule
increments it given the least retained bit `value.testBit shift`, the guard bit
`value.testBit (shift - 1)`, and the sticky bit `value % 2^(shift - 1) ≠ 0`.
-/
theorem roundShiftRight_eq_guard_sticky (rule : MagnitudeRounding) (value shift : Nat)
    (hshift : 0 < shift) :
    roundShiftRight rule value shift =
      value / 2 ^ shift +
        if rule.increment (value.testBit shift) (value.testBit (shift - 1))
            (decide (value % 2 ^ (shift - 1) ≠ 0)) then 1 else 0 := by
  cases rule with
  | down =>
      simp [roundShiftRight, MagnitudeRounding.increment, Nat.shiftRight_eq_div_pow]
  | up =>
      have hinexact := mod_two_pow_ne_zero_iff_guard_or_sticky value shift hshift
      simp only [roundShiftRight, MagnitudeRounding.increment, shiftRightCeil_eq]
      by_cases hzero : value % 2 ^ shift = 0
      · have hbits :
            (value.testBit (shift - 1) || decide (value % 2 ^ (shift - 1) ≠ 0)) = false := by
          cases hbits : (value.testBit (shift - 1) || decide (value % 2 ^ (shift - 1) ≠ 0))
          · rfl
          · exact absurd hzero (hinexact.mpr hbits)
        simp only [hbits]
        simp [hzero]
      · have hbits :
            (value.testBit (shift - 1) || decide (value % 2 ^ (shift - 1) ≠ 0)) = true :=
          hinexact.mp hzero
        simp only [hbits]
        simp [hzero]
  | nearestEven =>
      exact roundShiftRightEven_eq_guard_sticky value shift hshift
  | nearestAway =>
      obtain ⟨t, rfl⟩ : ∃ t, shift = t + 1 := ⟨shift - 1, by omega⟩
      simp only [roundShiftRight, MagnitudeRounding.increment, Nat.add_one_ne_zero,
        beq_iff_eq, ite_false, Nat.add_sub_cancel]
      exact nearestAway_shiftRight_eq value t

/--
Rounding up is the ceiling of the quotient: the truncated quotient when the remainder is zero and
its successor otherwise, with `0` for a zero denominator.
-/
theorem roundQuotient_up_eq (numerator denominator : Nat) :
    roundQuotient .up numerator denominator =
      if denominator = 0 then
        0
      else if numerator % denominator = 0 then
        numerator / denominator
      else
        numerator / denominator + 1 := by
  by_cases hdenominator : denominator = 0
  · simp [roundQuotient, hdenominator]
  by_cases hnumerator : numerator = 0
  · simp [roundQuotient, hnumerator]
  have hpos : 0 < denominator := Nat.pos_of_ne_zero hdenominator
  have hremainder := Nat.mod_lt numerator hpos
  have hsplit := Nat.div_add_mod numerator denominator
  simp only [roundQuotient, hnumerator, hdenominator, beq_iff_eq, Bool.or_eq_true, or_self,
    ite_false]
  by_cases hexact : numerator % denominator = 0
  · have hquotientPos : 0 < numerator / denominator := by
      rcases Nat.eq_zero_or_pos (numerator / denominator) with hzero | hpos'
      · rw [hzero, hexact] at hsplit
        omega
      · exact hpos'
    have hquotient : (numerator - 1) / denominator = numerator / denominator - 1 := by
      apply Nat.div_eq_of_lt_le
      · rw [Nat.sub_mul, Nat.one_mul]
        have := Nat.mul_comm denominator (numerator / denominator)
        omega
      · rw [Nat.sub_add_cancel hquotientPos]
        have := Nat.mul_comm denominator (numerator / denominator)
        omega
    simp only [hexact, ite_true, hquotient]
    omega
  · have hquotient : (numerator - 1) / denominator = numerator / denominator := by
      apply Nat.div_eq_of_lt_le
      · have := Nat.mul_comm denominator (numerator / denominator)
        omega
      · rw [Nat.add_mul, Nat.one_mul]
        have := Nat.mul_comm denominator (numerator / denominator)
        omega
    simp [hexact, hquotient]

/--
Nearest-away quotient rounding with a nonzero denominator increments the truncated quotient
exactly when twice the remainder reaches the denominator.
-/
theorem roundQuotient_nearestAway_eq_div_add (numerator denominator : Nat)
    (hdenominator : denominator ≠ 0) :
    roundQuotient .nearestAway numerator denominator =
      numerator / denominator + if denominator ≤ 2 * (numerator % denominator) then 1 else 0 := by
  have hpos : 0 < denominator := Nat.pos_of_ne_zero hdenominator
  have hremainder := Nat.mod_lt numerator hpos
  have hsplit := Nat.div_add_mod numerator denominator
  have hnumerator : 2 * numerator + denominator =
      (2 * (numerator % denominator) + denominator) +
        2 * denominator * (numerator / denominator) := by
    rw [Nat.mul_assoc]
    omega
  simp only [roundQuotient]
  rw [hnumerator, Nat.add_mul_div_left _ _ (by omega : 0 < 2 * denominator), Nat.add_comm]
  congr 1
  split_ifs with hhalf
  · exact Nat.div_eq_of_lt_le (by omega) (by omega)
  · exact Nat.div_eq_of_lt_le (by omega) (by omega)

/--
Nearest-away quotient rounding exceeds a bound exactly when the quotient reaches the bound plus
one half.
-/
theorem lt_roundQuotient_nearestAway_iff (bound numerator denominator : Nat)
    (hdenominator : denominator ≠ 0) :
    bound < roundQuotient .nearestAway numerator denominator ↔
      (2 * bound + 1) * denominator ≤ 2 * numerator := by
  simp only [roundQuotient]
  rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le (by omega : 0 < 2 * denominator)]
  have hleft : (bound + 1) * (2 * denominator) =
      2 * (bound * denominator) + 2 * denominator := by
    ring
  have hright : (2 * bound + 1) * denominator = 2 * (bound * denominator) + denominator := by
    ring
  rw [hleft, hright]
  omega

/--
Nearest-away quotient rounding is nearest-even rounding with an exact tie sent up.

With a nonzero denominator the two rules differ only when twice the remainder equals the
denominator, where nearest-away always takes the larger integer.
-/
theorem roundQuotient_nearestAway_eq (numerator denominator : Nat)
    (hdenominator : denominator ≠ 0) :
    roundQuotient .nearestAway numerator denominator =
      if 2 * (numerator % denominator) = denominator then
        numerator / denominator + 1
      else
        roundQuotientEven numerator denominator := by
  rw [roundQuotient_nearestAway_eq_div_add numerator denominator hdenominator]
  unfold roundQuotientEven
  simp only
  by_cases htie : 2 * (numerator % denominator) = denominator
  · simp [htie]
  · rw [ite_eq_right htie]
    by_cases hbelow : 2 * (numerator % denominator) < denominator
    · simp [hbelow, Nat.not_le.mpr hbelow]
    · have habove : denominator < 2 * (numerator % denominator) := by omega
      simp [hbelow, habove, habove.le]

/-- Twice the remainder is the denominator iff twice the numerator is an odd multiple of it. -/
private theorem two_mul_mod_eq_iff_exists (numerator denominator : Nat)
    (hdenominator : denominator ≠ 0) :
    2 * (numerator % denominator) = denominator ↔
      ∃ k, 2 * numerator = (2 * k + 1) * denominator := by
  have hsplit := Nat.div_add_mod numerator denominator
  constructor
  · intro htie
    refine ⟨numerator / denominator, ?_⟩
    have hproduct : (2 * (numerator / denominator) + 1) * denominator =
        2 * (denominator * (numerator / denominator)) + denominator := by
      ring
    omega
  · rintro ⟨k, hk⟩
    have hproduct : (2 * k + 1) * denominator = 2 * (k * denominator) + denominator := by
      ring
    have hnumerator : numerator = denominator / 2 + k * denominator := by
      omega
    have hhalf : denominator / 2 < denominator := by
      omega
    rw [hnumerator, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hhalf]
    omega

/--
Whether a quotient is an exact tie depends only on the rational it represents.

Two quotients with nonzero denominators and equal cross products are ties together: twice the
remainder equals the denominator for both or for neither.
-/
theorem two_mul_mod_eq_iff_of_mul_eq (numerator denominator numerator' denominator' : Nat)
    (hdenominator : denominator ≠ 0) (hdenominator' : denominator' ≠ 0)
    (hcross : numerator * denominator' = numerator' * denominator) :
    2 * (numerator % denominator) = denominator ↔
      2 * (numerator' % denominator') = denominator' := by
  rw [two_mul_mod_eq_iff_exists _ _ hdenominator, two_mul_mod_eq_iff_exists _ _ hdenominator']
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hdenominator) ?_⟩
    calc
      denominator * (2 * numerator') = 2 * (numerator' * denominator) := by ring
      _ = 2 * numerator * denominator' := by rw [← hcross]; ring
      _ = denominator * ((2 * k + 1) * denominator') := by rw [hk]; ring
  · rintro ⟨k, hk⟩
    refine ⟨k, Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hdenominator') ?_⟩
    calc
      denominator' * (2 * numerator) = 2 * (numerator * denominator') := by ring
      _ = 2 * numerator' * denominator := by rw [hcross]; ring
      _ = denominator' * ((2 * k + 1) * denominator) := by rw [hk]; ring

/-- Shift rounding under every rule is quotient rounding by the corresponding power of two. -/
theorem roundShiftRight_eq_roundQuotient (rule : MagnitudeRounding) (value shift : Nat) :
    roundShiftRight rule value shift = roundQuotient rule value (2 ^ shift) := by
  have hpow : 2 ^ shift ≠ 0 := Nat.ne_of_gt (Nat.two_pow_pos shift)
  cases rule with
  | down => simp [Nat.shiftRight_eq_div_pow]
  | up =>
      rw [roundShiftRight_up, shiftRightCeil_eq, roundQuotient_up_eq]
      by_cases hzero : value % 2 ^ shift = 0 <;> simp [hzero]
  | nearestEven =>
      exact roundShiftRightEven_eq_roundQuotientEven value shift
  | nearestAway =>
      cases shift with
      | zero =>
          simp only [roundShiftRight_zero, pow_zero, roundQuotient]
          omega
      | succ t =>
          rw [roundShiftRight_eq_guard_sticky .nearestAway value (t + 1) (by omega),
            roundQuotient_nearestAway_eq_div_add value (2 ^ (t + 1)) hpow]
          simp only [MagnitudeRounding.increment, Nat.add_sub_cancel]
          congr 1
          rw [mod_two_pow_succ_eq]
          have hlow : value % 2 ^ t < 2 ^ t := Nat.mod_lt _ (Nat.two_pow_pos t)
          rw [pow_succ]
          cases value.testBit t <;> simp <;> omega

/--
Nearest-away shift rounding is nearest-even shift rounding with an exact tie sent to the ceiling.
-/
theorem roundShiftRight_nearestAway_eq (value shift : Nat) :
    roundShiftRight .nearestAway value shift =
      if shiftRightIsTie value shift then
        shiftRightCeil value shift
      else
        roundShiftRightEven value shift := by
  by_cases hshift : shift = 0
  · subst shift
    simp [shiftRightIsTie]
  have hpos : 0 < shift := Nat.pos_of_ne_zero hshift
  have haway := roundShiftRight_eq_guard_sticky .nearestAway value shift hpos
  have hup := roundShiftRight_eq_guard_sticky .up value shift hpos
  have heven := roundShiftRight_eq_guard_sticky .nearestEven value shift hpos
  rw [roundShiftRight_up] at hup
  rw [roundShiftRight_nearestEven] at heven
  rw [shiftRightIsTie_eq_guard_and_not_sticky value shift hpos, haway]
  simp only [MagnitudeRounding.increment] at hup heven ⊢
  cases hguard : value.testBit (shift - 1) <;>
    cases hsticky : decide (value % 2 ^ (shift - 1) ≠ 0) <;>
    simp_all

/-! ## Ternary value -/

/--
Compare a shift-rounded magnitude, scaled back, with the exact magnitude.

The result is equal exactly when no guard or sticky bit is set. Otherwise it is above the exact
magnitude when the rule increments the truncated quotient and below it when the rule truncates.
-/
theorem compare_roundShiftRight_mul_two_pow (rule : MagnitudeRounding) (value shift : Nat)
    (hshift : 0 < shift) :
    compare (roundShiftRight rule value shift * 2 ^ shift) value =
      if value.testBit (shift - 1) || decide (value % 2 ^ (shift - 1) ≠ 0) then
        if rule.increment (value.testBit shift) (value.testBit (shift - 1))
            (decide (value % 2 ^ (shift - 1) ≠ 0)) then .gt else .lt
      else
        .eq := by
  have hinexact := mod_two_pow_ne_zero_iff_guard_or_sticky value shift hshift
  have hsplit := Nat.div_add_mod value (2 ^ shift)
  have hlow : value % 2 ^ shift < 2 ^ shift := Nat.mod_lt _ (Nat.two_pow_pos shift)
  rw [roundShiftRight_eq_guard_sticky rule value shift hshift]
  have hmul : value / 2 ^ shift * 2 ^ shift = 2 ^ shift * (value / 2 ^ shift) :=
    Nat.mul_comm _ _
  by_cases hbits : (value.testBit (shift - 1) || decide (value % 2 ^ (shift - 1) ≠ 0)) = true
  · have hnonzero : value % 2 ^ shift ≠ 0 := hinexact.mpr hbits
    rw [ite_eq_left hbits]
    split_ifs with hincrement
    · rw [compare_gt_iff_gt, Nat.add_mul, Nat.one_mul]
      omega
    · rw [compare_lt_iff_lt, Nat.add_zero]
      omega
  · have hzero : value % 2 ^ shift = 0 := by
      by_contra hne
      exact hbits (hinexact.mp hne)
    have hguard : value.testBit (shift - 1) = false := by
      cases h : value.testBit (shift - 1) <;> simp_all
    have hsticky : decide (value % 2 ^ (shift - 1) ≠ 0) = false := by
      cases h : decide (value % 2 ^ (shift - 1) ≠ 0) <;> simp_all
    rw [ite_eq_right hbits, hguard, hsticky, MagnitudeRounding.increment_false_false]
    simp only [Bool.false_eq_true, ite_false, Nat.add_zero, compare_eq_iff_eq]
    omega

/--
The ternary value of a signed shift rounding, read off its rounding bits.

For a negative value both the delivered and the exact value change sign, so their comparison is
the magnitude comparison swapped. The delivered value equals the exact one when no guard or sticky
bit is set. Otherwise it is above the exact value exactly when the increment decision differs from
the sign: incrementing a positive magnitude, or truncating a negative one.
-/
theorem compare_roundShiftRight_mul_two_pow_signed (rule : MagnitudeRounding) (negative : Bool)
    (value shift : Nat) (hshift : 0 < shift) :
    (if negative then (compare (roundShiftRight rule value shift * 2 ^ shift) value).swap
      else compare (roundShiftRight rule value shift * 2 ^ shift) value) =
      if value.testBit (shift - 1) || decide (value % 2 ^ (shift - 1) ≠ 0) then
        if rule.increment (value.testBit shift) (value.testBit (shift - 1))
            (decide (value % 2 ^ (shift - 1) ≠ 0)) != negative then .gt else .lt
      else
        .eq := by
  rw [compare_roundShiftRight_mul_two_pow rule value shift hshift]
  cases negative <;> split_ifs <;> simp_all

end FloatLib.Numerics
