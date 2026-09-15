/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Prefix.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Rounding.GuardSticky.Spec.Midpoint

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact quotient comparisons preserved by jamming

Jamming a nonzero discarded suffix into the low bit relates the retained prefix to the original
Euclidean quotient and remainder. The comparison lemmas show that the exact fraction and its
jammed prefix make the same comparisons at the even boundaries used by posit rounding, including
scaled tails and stream midpoints.

These lemmas concern the exact quotient and retained prefix, independently of storage width.
`Direct.PrefixProof` uses them after normalizing significands to prove the executable prefix
correct; `Direct.Proof` then connects that prefix to the posit encoding and final rounding.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.DirectDyadicQuotient

open FloatLib.Numerics
open FloatLib.Floats.Formats.Posit.Model.GuardStickyRounding
open FloatLib.Floats.Formats.Posit.Model.StickyPrefix

/-! ## Quotient fractions and jamming -/

/-- A Euclidean quotient plus its proper remainder lies in its unit interval. -/
theorem quotientFraction_bounds
    (quotient remainder denominator : Nat)
    (hdenominator : 0 < denominator)
    (hremainder : remainder < denominator) :
    (quotient : Rat) ≤
        (quotient : Rat) + (remainder : Rat) / (denominator : Rat) ∧
      (quotient : Rat) + (remainder : Rat) / (denominator : Rat) <
        (quotient : Rat) + 1 := by
  have hdenominatorRat : (0 : Rat) < (denominator : Rat) := by
    exact_mod_cast hdenominator
  have hremainderNonnegative : (0 : Rat) ≤ (remainder : Rat) :=
    Nat.cast_nonneg remainder
  have hremainderRat : (remainder : Rat) < (denominator : Rat) := by
    exact_mod_cast hremainder
  have hfractionNonnegative :
      (0 : Rat) ≤ (remainder : Rat) / (denominator : Rat) :=
    div_nonneg hremainderNonnegative hdenominatorRat.le
  have hfractionLt :
      (remainder : Rat) / (denominator : Rat) < 1 :=
    (div_lt_one hdenominatorRat).2 hremainderRat
  constructor <;> linarith

/-- A nonzero Euclidean remainder places the exact quotient strictly above its prefix. -/
theorem quotient_lt_quotientFraction
    (quotient remainder denominator : Nat)
    (hdenominator : 0 < denominator)
    (hremainder : remainder ≠ 0) :
    (quotient : Rat) <
      (quotient : Rat) + (remainder : Rat) / (denominator : Rat) := by
  have hdenominatorRat : (0 : Rat) < (denominator : Rat) := by
    exact_mod_cast hdenominator
  have hremainderRat : (0 : Rat) < (remainder : Rat) := by
    exact_mod_cast Nat.pos_of_ne_zero hremainder
  have hfractionPositive :
      (0 : Rat) < (remainder : Rat) / (denominator : Rat) :=
    div_pos hremainderRat hdenominatorRat
  linarith

/--
A Euclidean quotient plus its proper remainder lies below a natural boundary exactly when the
quotient does.
-/
theorem quotientFraction_lt_natCast_iff
    (quotient remainder denominator boundary : Nat)
    (hdenominator : 0 < denominator)
    (hremainder : remainder < denominator) :
    (quotient : Rat) + (remainder : Rat) / (denominator : Rat) < (boundary : Rat) ↔
      quotient < boundary := by
  have hbounds :=
    quotientFraction_bounds quotient remainder denominator hdenominator hremainder
  constructor
  · intro hexact
    exact_mod_cast hbounds.1.trans_lt hexact
  · intro hquotient
    have hsuccessor : (quotient : Rat) + 1 ≤ boundary := by
      exact_mod_cast hquotient
    linarith [hbounds.2]

/--
A natural boundary lies below a Euclidean quotient plus its proper remainder exactly when it lies
below the quotient, or equals the quotient and the remainder is nonzero.
-/
theorem natCast_lt_quotientFraction_iff
    (quotient remainder denominator boundary : Nat)
    (hdenominator : 0 < denominator)
    (hremainder : remainder < denominator) :
    (boundary : Rat) < (quotient : Rat) + (remainder : Rat) / (denominator : Rat) ↔
      boundary < quotient ∨ (boundary = quotient ∧ remainder ≠ 0) := by
  have hbounds :=
    quotientFraction_bounds quotient remainder denominator hdenominator hremainder
  rcases lt_trichotomy boundary quotient with hlt | rfl | hgt
  · exact iff_of_true
      ((by exact_mod_cast hlt : (boundary : Rat) < quotient).trans_le hbounds.1) (Or.inl hlt)
  · simp only [lt_self_iff_false, true_and, false_or]
    constructor
    · rintro hexact rfl
      simp at hexact
    · exact quotient_lt_quotientFraction _ _ _ hdenominator
  · have hsuccessor : (quotient : Rat) + 1 ≤ boundary := by
      exact_mod_cast hgt
    exact iff_of_false (by linarith [hbounds.2]) (by omega)

/--
Jamming and the exact quotient fraction lie on the same lower side of every even integer
boundary. A stream threshold with at least one zero padding bit has this form.
-/
theorem quotientFraction_lt_even_iff_jam_lt
    (quotient remainder denominator boundary : Nat)
    (hdenominator : 0 < denominator)
    (hremainder : remainder < denominator)
    (hboundary : boundary % 2 = 0) :
    (quotient : Rat) + (remainder : Rat) / (denominator : Rat) <
        (boundary : Rat) ↔
      jamRemainder quotient remainder < boundary := by
  rw [quotientFraction_lt_natCast_iff _ _ _ _ hdenominator hremainder, jamRemainder_eq]
  split_ifs <;> omega

/--
Jamming and the exact quotient fraction lie on the same upper side of every even integer
boundary.
-/
theorem even_lt_quotientFraction_iff_lt_jam
    (quotient remainder denominator boundary : Nat)
    (hdenominator : 0 < denominator)
    (hremainder : remainder < denominator)
    (hboundary : boundary % 2 = 0) :
    (boundary : Rat) <
        (quotient : Rat) + (remainder : Rat) / (denominator : Rat) ↔
      boundary < jamRemainder quotient remainder := by
  rw [natCast_lt_quotientFraction_iff _ _ _ _ hdenominator hremainder, jamRemainder_eq]
  split_ifs <;> omega

/--
Jamming a normalized significand is the same operation as jamming its complete exponent/fraction
tail. The leading bit position is positive for every Posit payload, so the exponent contribution
and removed hidden bit are both even.
-/
theorem exactTailRaw_jamRemainder
    (exponentField quotient remainder leading : Nat)
    (hleading : 0 < leading)
    (hlower : 2 ^ leading ≤ quotient) :
    exactTailRaw exponentField
        (jamRemainder quotient remainder) leading =
      jamRemainder
        (exactTailRaw exponentField quotient leading) remainder := by
  have hpowerEven : 2 ^ leading % 2 = 0 := by
    obtain ⟨preceding, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : leading ≠ 0)
    simp [pow_succ]
  have hrawParity :
      exactTailRaw exponentField quotient leading % 2 =
        quotient % 2 := by
    have hdecompose :
        2 ^ leading + (quotient - 2 ^ leading) = quotient :=
      Nat.add_sub_of_le hlower
    have hfractionParity :
        (quotient - 2 ^ leading) % 2 = quotient % 2 := by
      have hmod :=
        congrArg (fun value : Nat => value % 2) hdecompose
      simpa [Nat.add_mod, hpowerEven] using hmod
    simp [exactTailRaw, fractionRaw, Nat.add_mod, Nat.mul_mod,
      hpowerEven, hfractionParity]
  rw [jamRemainder_eq, jamRemainder_eq, hrawParity]
  by_cases hremainder : remainder = 0
  · simp [hremainder]
  · rw [ite_eq_right hremainder, ite_eq_right hremainder]
    by_cases hquotientEven : quotient % 2 = 0
    · rw [ite_eq_left hquotientEven, ite_eq_left hquotientEven]
      unfold exactTailRaw fractionRaw
      omega
    · rw [ite_eq_right hquotientEven, ite_eq_right hquotientEven]

/-- A zero-padded midpoint is even whenever at least one padding bit remains. -/
theorem streamMidpointRaw_mod_two
    (raw width retained : Nat)
    (hpadding : retained + 1 < width) :
    streamMidpointRaw raw width retained % 2 = 0 := by
  have hexponent :
      width - retained - 1 =
        (width - retained - 2) + 1 := by
    omega
  unfold streamMidpointRaw
  rw [hexponent, pow_succ]
  simp [Nat.mul_mod]

/--
Padding a retained jammed prefix back to the complete stream width never exceeds the unjammed
integer prefix.

The only nontrivial case is a nonzero remainder after an even quotient. Jamming then adds one,
but the padded retained prefix is even, so it cannot equal that odd successor.
-/
theorem paddedStreamPrefix_jamRemainder_le
    (quotient remainder width retained : Nat)
    (hretained : retained < width) :
    streamPrefix (jamRemainder quotient remainder) width retained *
        2 ^ (width - retained) ≤
      quotient := by
  have hshift : 0 < width - retained := by
    omega
  have hpowerEven : 2 ^ (width - retained) % 2 = 0 := by
    obtain ⟨preceding, hshiftEq⟩ :=
      Nat.exists_eq_succ_of_ne_zero (by omega : width - retained ≠ 0)
    rw [hshiftEq, pow_succ]
    simp
  unfold streamPrefix
  rw [ite_eq_left hretained.le, jamRemainder_eq]
  by_cases hremainder : remainder = 0
  · rw [ite_eq_left hremainder]
    exact Nat.div_mul_le_self quotient (2 ^ (width - retained))
  · rw [ite_eq_right hremainder]
    by_cases hquotientEven : quotient % 2 = 0
    · rw [ite_eq_left hquotientEven]
      have hle :=
        Nat.div_mul_le_self (quotient + 1) (2 ^ (width - retained))
      have hleftEven :
          (((quotient + 1) / 2 ^ (width - retained)) *
              2 ^ (width - retained)) % 2 = 0 := by
        simp [Nat.mul_mod, hpowerEven]
      have hsuccessorOdd : (quotient + 1) % 2 = 1 := by
        omega
      omega
    · rw [ite_eq_right hquotientEven]
      exact Nat.div_mul_le_self quotient (2 ^ (width - retained))

/--
The exact quotient fraction lies strictly below the successor of its retained jammed prefix.

This is the upper half of the general local bracket. It needs only a proper Euclidean remainder
and discards at least one stream bit; no Posit width, storage tier, or candidate decoder appears.
-/
theorem quotientFraction_lt_paddedStreamPrefix_jamRemainder_succ
    (quotient remainder denominator width retained : Nat)
    (hdenominator : 0 < denominator)
    (hremainder : remainder < denominator)
    (hretained : retained < width) :
    (quotient : Rat) + (remainder : Rat) / (denominator : Rat) <
      (((streamPrefix (jamRemainder quotient remainder) width retained + 1) *
          2 ^ (width - retained) : Nat) : Rat) := by
  let jammed := jamRemainder quotient remainder
  let shift := width - retained
  have hshiftPositive : 0 < 2 ^ shift :=
    Nat.two_pow_pos shift
  have hjammedUpper :
      jammed <
        (jammed / 2 ^ shift + 1) * 2 ^ shift := by
    have hremainderBound :
        jammed % 2 ^ shift < 2 ^ shift :=
      Nat.mod_lt jammed hshiftPositive
    have hdecompose :=
      Nat.mod_add_div jammed (2 ^ shift)
    calc
      jammed =
          jammed % 2 ^ shift +
            2 ^ shift * (jammed / 2 ^ shift) := hdecompose.symm
      _ <
          2 ^ shift +
            2 ^ shift * (jammed / 2 ^ shift) :=
        Nat.add_lt_add_right hremainderBound _
      _ = (jammed / 2 ^ shift + 1) * 2 ^ shift := by
        ring
  have hquotientLeJammed : quotient ≤ jammed := by
    dsimp [jammed]
    rw [jamRemainder_eq]
    by_cases hremainderZero : remainder = 0
    · simp [hremainderZero]
    · rw [ite_eq_right hremainderZero]
      by_cases hquotientEven : quotient % 2 = 0
      · simp [hquotientEven]
      · simp [hquotientEven]
  have hquotientSuccessorLe :
      quotient + 1 ≤
        (jammed / 2 ^ shift + 1) * 2 ^ shift := by
    omega
  have hfractionLtOne :
      (remainder : Rat) / (denominator : Rat) < 1 := by
    exact (div_lt_one (by exact_mod_cast hdenominator)).2
      (by exact_mod_cast hremainder)
  have hquotientSuccessorLeRat :
      (quotient : Rat) + 1 ≤
        (((jammed / 2 ^ shift + 1) * 2 ^ shift : Nat) : Rat) := by
    exact_mod_cast hquotientSuccessorLe
  unfold streamPrefix
  rw [ite_eq_left hretained.le]
  dsimp [jammed, shift] at *
  linarith

/--
An exact quotient fraction and its jammed finite tail lie on the same lower side of every
zero-padded stream midpoint.
-/
theorem quotientTailFraction_lt_midpoint_iff_jammed
    (exponentField quotient remainder denominator leading retained : Nat)
    (hleading : 0 < leading)
    (hlower : 2 ^ leading ≤ quotient)
    (hdenominator : 0 < denominator)
    (hremainder : remainder < denominator)
    (hpadding : retained + 1 < leading + 2) :
    (exactTailRaw exponentField quotient leading : Rat) +
          (remainder : Rat) / (denominator : Rat) <
        streamMidpointRaw
          (exactTailRaw exponentField
            (jamRemainder quotient remainder) leading)
          (leading + 2) retained ↔
      exactTailRaw exponentField
          (jamRemainder quotient remainder) leading <
        streamMidpointRaw
          (exactTailRaw exponentField
            (jamRemainder quotient remainder) leading)
          (leading + 2) retained := by
  rw [exactTailRaw_jamRemainder
    exponentField quotient remainder leading hleading hlower]
  apply quotientFraction_lt_even_iff_jam_lt
  · exact hdenominator
  · exact hremainder
  · exact streamMidpointRaw_mod_two _ _ _ hpadding

/--
An exact quotient fraction and its jammed finite tail lie on the same upper side of every
zero-padded stream midpoint.
-/
theorem midpoint_lt_quotientTailFraction_iff_jammed
    (exponentField quotient remainder denominator leading retained : Nat)
    (hleading : 0 < leading)
    (hlower : 2 ^ leading ≤ quotient)
    (hdenominator : 0 < denominator)
    (hremainder : remainder < denominator)
    (hpadding : retained + 1 < leading + 2) :
    (streamMidpointRaw
          (exactTailRaw exponentField
            (jamRemainder quotient remainder) leading)
          (leading + 2) retained : Rat) <
        (exactTailRaw exponentField quotient leading : Rat) +
          (remainder : Rat) / (denominator : Rat) ↔
      streamMidpointRaw
          (exactTailRaw exponentField
            (jamRemainder quotient remainder) leading)
          (leading + 2) retained <
        exactTailRaw exponentField
          (jamRemainder quotient remainder) leading := by
  rw [exactTailRaw_jamRemainder
    exponentField quotient remainder leading hleading hlower]
  apply even_lt_quotientFraction_iff_lt_jam
  · exact hdenominator
  · exact hremainder
  · exact streamMidpointRaw_mod_two _ _ _ hpadding

/-!
## Interpreting finite stream words

The unjammed quotient is an integer tail word followed by one proper rational remainder. The
closing lemmas `quotientFraction_lt_trailingRat_iff` and `trailingRat_lt_quotientFraction_iff`
compare that fractional position with any bounded integer tail boundary. They use only
monotonicity of `trailingRat`, so quotient rounding does not duplicate Posit regime layout or
decoder proofs.
-/

/--
Advancing one finite tail word advances a normalized significand by one unit in its stored
leading position, including a carry into the next exponent within the bounded tail.
-/
theorem trailingRat_exactTailRaw_succ
    (exponentField significand leading : Nat)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ significand)
    (hupper : significand < 2 ^ (leading + 1))
    (hsuccessor :
      exactTailRaw exponentField significand leading + 1 <
        2 ^ (leading + 2)) :
    Model.trailingRat (leading + 2)
        (exactTailRaw exponentField significand leading + 1) =
      ((significand : Rat) + 1) / (2 ^ leading : Nat) *
        (2 : Rat) ^ Int.ofNat exponentField := by
  by_cases hsignificandSuccessor : significand + 1 < 2 ^ (leading + 1)
  · have hrawSuccessor :
        exactTailRaw exponentField significand leading + 1 =
          exactTailRaw exponentField (significand + 1) leading := by
      unfold exactTailRaw fractionRaw
      omega
    rw [hrawSuccessor]
    simpa [Nat.cast_add] using
      trailingRat_exactTailRaw exponentField (significand + 1) leading
        hexponent (by omega) hsignificandSuccessor
  · have hpower : 2 ^ (leading + 1) = 2 * 2 ^ leading := by
      rw [pow_succ]
      omega
    have hpowerWidth : 2 ^ (leading + 2) = 4 * 2 ^ leading := by
      rw [pow_add]
      omega
    have hsignificandMax : significand + 1 = 2 * 2 ^ leading := by
      omega
    have hrawSuccessor :
        exactTailRaw exponentField significand leading + 1 =
          exactTailRaw (exponentField + 1) (2 ^ leading) leading := by
      unfold exactTailRaw fractionRaw
      have := Nat.two_pow_pos leading
      rw [Nat.add_mul, Nat.one_mul]
      omega
    have hexponentSuccessor : exponentField + 1 < 4 := by
      rw [hrawSuccessor] at hsuccessor
      unfold exactTailRaw fractionRaw at hsuccessor
      rw [hpowerWidth] at hsuccessor
      have := Nat.two_pow_pos leading
      nlinarith
    rw [hrawSuccessor, trailingRat_exactTailRaw (exponentField + 1) (2 ^ leading) leading
      hexponentSuccessor le_rfl (by omega)]
    have hsignificandMaxRat : (significand : Rat) + 1 = 2 * (2 ^ leading : Nat) := by
      exact_mod_cast hsignificandMax
    rw [hsignificandMaxRat, Int.ofNat_eq_natCast, Int.ofNat_eq_natCast, Nat.cast_add,
      Nat.cast_one, zpow_add₀ (by norm_num : (2 : Rat) ≠ 0)]
    have hnonzero : ((2 ^ leading : Nat) : Rat) ≠ 0 := by positivity
    field_simp

/--
The exact fractional quotient lies between the values of its finite-stream prefix and the next
normalized significand. This is the shared local bracket behind both strict comparison
directions.
-/
private theorem quotientFraction_scaled_bounds
    (exponentField quotient remainder denominator leading : Nat)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ quotient)
    (hupper : quotient < 2 ^ (leading + 1))
    (hdenominator : 0 < denominator)
    (hremainder : remainder < denominator) :
    exactTailRaw exponentField quotient leading < 2 ^ (leading + 2) ∧
      Model.trailingRat (leading + 2)
          (exactTailRaw exponentField quotient leading) ≤
        ((quotient : Rat) + (remainder : Rat) / (denominator : Rat)) /
            (2 ^ leading : Nat) *
          (2 : Rat) ^ Int.ofNat exponentField ∧
      ((quotient : Rat) + (remainder : Rat) / (denominator : Rat)) /
            (2 ^ leading : Nat) *
          (2 : Rat) ^ Int.ofNat exponentField <
        ((quotient : Rat) + 1) / (2 ^ leading : Nat) *
          (2 : Rat) ^ Int.ofNat exponentField := by
  have hbounds :=
    quotientFraction_bounds quotient remainder denominator hdenominator hremainder
  refine ⟨exactTailRaw_lt_two_pow exponentField quotient leading hexponent hlower hupper, ?_, ?_⟩
  · rw [trailingRat_exactTailRaw exponentField quotient leading hexponent hlower hupper]
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hbounds.1 (by positivity)) (zpow_pos (by norm_num) _).le
  · exact mul_lt_mul_of_pos_right
      (div_lt_div_of_pos_right hbounds.2 (by positivity)) (zpow_pos (by norm_num) _)

/-- Every finite-stream word up to the exact quotient word denotes at most the exact quotient. -/
private theorem trailingRat_le_quotientFraction_of_le
    (exponentField quotient remainder denominator leading boundary : Nat)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ quotient)
    (hupper : quotient < 2 ^ (leading + 1))
    (hdenominator : 0 < denominator)
    (hremainder : remainder < denominator)
    (hboundary : boundary < 2 ^ (leading + 2))
    (hle : boundary ≤ exactTailRaw exponentField quotient leading) :
    Model.trailingRat (leading + 2) boundary ≤
      ((quotient : Rat) + (remainder : Rat) / (denominator : Rat)) /
          (2 ^ leading : Nat) * (2 : Rat) ^ Int.ofNat exponentField := by
  have hbounds := quotientFraction_scaled_bounds
    exponentField quotient remainder denominator leading
    hexponent hlower hupper hdenominator hremainder
  rcases hle.lt_or_eq with hlt | rfl
  · exact (Model.trailingRat_lt_of_lt hboundary hbounds.1 hlt).le.trans hbounds.2.1
  · exact hbounds.2.1

/-- Every bounded finite-stream word above the exact quotient word exceeds the exact quotient. -/
private theorem quotientFraction_lt_trailingRat_of_lt
    (exponentField quotient remainder denominator leading boundary : Nat)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ quotient)
    (hupper : quotient < 2 ^ (leading + 1))
    (hdenominator : 0 < denominator)
    (hremainder : remainder < denominator)
    (hboundary : boundary < 2 ^ (leading + 2))
    (hlt : exactTailRaw exponentField quotient leading < boundary) :
    ((quotient : Rat) + (remainder : Rat) / (denominator : Rat)) /
          (2 ^ leading : Nat) * (2 : Rat) ^ Int.ofNat exponentField <
      Model.trailingRat (leading + 2) boundary := by
  have hbounds := quotientFraction_scaled_bounds
    exponentField quotient remainder denominator leading
    hexponent hlower hupper hdenominator hremainder
  have hsuccessor : exactTailRaw exponentField quotient leading + 1 < 2 ^ (leading + 2) := by
    omega
  rw [← trailingRat_exactTailRaw_succ exponentField quotient leading
    hexponent hlower hupper hsuccessor] at hbounds
  rcases (Nat.succ_le_of_lt hlt).lt_or_eq with hlt' | heq
  · exact hbounds.2.2.trans (Model.trailingRat_lt_of_lt hsuccessor hboundary hlt')
  · exact heq ▸ hbounds.2.2

/-- The exact quotient word denotes strictly less than the exact quotient exactly when the
remainder is nonzero. -/
private theorem trailingRat_exactTailRaw_lt_quotientFraction_iff
    (exponentField quotient remainder denominator leading : Nat)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ quotient)
    (hupper : quotient < 2 ^ (leading + 1))
    (hdenominator : 0 < denominator) :
    Model.trailingRat (leading + 2) (exactTailRaw exponentField quotient leading) <
        ((quotient : Rat) + (remainder : Rat) / (denominator : Rat)) /
            (2 ^ leading : Nat) * (2 : Rat) ^ Int.ofNat exponentField ↔
      remainder ≠ 0 := by
  rw [trailingRat_exactTailRaw exponentField quotient leading hexponent hlower hupper,
    mul_lt_mul_iff_of_pos_right (zpow_pos (by norm_num) _),
    div_lt_div_iff_of_pos_right (by positivity), lt_add_iff_pos_right,
    div_pos_iff_of_pos_right (by exact_mod_cast hdenominator), Nat.cast_pos]
  exact Nat.pos_iff_ne_zero

/--
A quotient plus proper remainder is below a bounded finite-stream word exactly when its
normalized rational value is below the value denoted by that word.
-/
theorem quotientFraction_lt_trailingRat_iff
    (exponentField quotient remainder denominator leading boundary : Nat)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ quotient)
    (hupper : quotient < 2 ^ (leading + 1))
    (hdenominator : 0 < denominator)
    (hremainder : remainder < denominator)
    (hboundary : boundary < 2 ^ (leading + 2)) :
    (((quotient : Rat) +
          (remainder : Rat) / (denominator : Rat)) /
        (2 ^ leading : Nat) *
          (2 : Rat) ^ Int.ofNat exponentField <
      Model.trailingRat (leading + 2) boundary) ↔
    (exactTailRaw exponentField quotient leading : Rat) +
          (remainder : Rat) / (denominator : Rat) <
        (boundary : Rat) := by
  rw [quotientFraction_lt_natCast_iff _ _ _ _ hdenominator hremainder]
  rcases lt_or_ge (exactTailRaw exponentField quotient leading) boundary with hlt | hge
  · exact iff_of_true (quotientFraction_lt_trailingRat_of_lt _ _ _ _ _ _
      hexponent hlower hupper hdenominator hremainder hboundary hlt) hlt
  · exact iff_of_false (not_lt.2 (trailingRat_le_quotientFraction_of_le _ _ _ _ _ _
      hexponent hlower hupper hdenominator hremainder hboundary hge)) (not_lt.2 hge)

/-- The reverse bounded finite-stream comparison has the corresponding fractional meaning. -/
theorem trailingRat_lt_quotientFraction_iff
    (exponentField quotient remainder denominator leading boundary : Nat)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ quotient)
    (hupper : quotient < 2 ^ (leading + 1))
    (hdenominator : 0 < denominator)
    (hremainder : remainder < denominator)
    (hboundary : boundary < 2 ^ (leading + 2)) :
    (Model.trailingRat (leading + 2) boundary <
      ((quotient : Rat) +
          (remainder : Rat) / (denominator : Rat)) /
        (2 ^ leading : Nat) *
          (2 : Rat) ^ Int.ofNat exponentField) ↔
    (boundary : Rat) <
      (exactTailRaw exponentField quotient leading : Rat) +
        (remainder : Rat) / (denominator : Rat) := by
  rw [natCast_lt_quotientFraction_iff _ _ _ _ hdenominator hremainder]
  have hraw := exactTailRaw_lt_two_pow exponentField quotient leading hexponent hlower hupper
  rcases lt_trichotomy boundary (exactTailRaw exponentField quotient leading) with hlt | rfl | hgt
  · exact iff_of_true ((Model.trailingRat_lt_of_lt hboundary hraw hlt).trans_le
      (trailingRat_le_quotientFraction_of_le _ _ _ _ _ _
        hexponent hlower hupper hdenominator hremainder hraw le_rfl)) (Or.inl hlt)
  · simpa using trailingRat_exactTailRaw_lt_quotientFraction_iff exponentField quotient remainder
      denominator leading hexponent hlower hupper hdenominator
  · exact iff_of_false (not_lt.2 (quotientFraction_lt_trailingRat_of_lt _ _ _ _ _ _
      hexponent hlower hupper hdenominator hremainder hboundary hgt).le) (by omega)

end FloatLib.Floats.Formats.Posit.Model.DirectDyadicQuotient
