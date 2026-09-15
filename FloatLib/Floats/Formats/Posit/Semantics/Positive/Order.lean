/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Semantics.Positive.Trailing
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
public import FloatLib.Floats.Formats.Posit.Semantics.Positive.BitRuns

/-!
# Order of positive Posit encodings

Regime order and exponent/fraction-tail order imply that unsigned codes below the sign mask are
strictly ordered by their exact rational meanings. Crossing a variable-length regime boundary
changes how many bits remain for exponent and fraction, so ordinary fixed-field lexicographic
reasoning is not enough.

The theorem justifies native unsigned comparison for positive finite posits and supports the signed
order development without decoding both operands again.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

variable {format : Format}

/-- Equal quotients turn strict natural order into strict order of the corresponding remainders. -/
private theorem mod_lt_of_lt_of_div_eq
    {left right divisor : Nat}
    (hlt : left < right)
    (hquotient : left / divisor = right / divisor) :
    left % divisor < right % divisor := by
  have hleft := Nat.mod_add_div left divisor
  have hright := Nat.mod_add_div right divisor
  rw [← hleft, ← hright, hquotient] at hlt
  omega

/-- The exact rational lookup maps the zero code to rational zero. -/
@[simp] theorem nonnegativeRatAt_zero (format : Format) :
    nonnegativeRatAt format 0 = 0 := by
  have hzero :
      ofNatBits (format := format) 0 = zero format :=
    rfl
  simp [nonnegativeRatAt, decodeExact, hzero]

/--
A positive code below the sign mask denotes its exponent/fraction tail scaled by the regime power.

The exponent factor `4` is the Posit Standard (2022)'s regime step `2 ^ exponentBits`.
-/
theorem nonnegativeRatAt_eq_trailingRat_mul_regime
    (format : Format) {code : Nat}
    (hpos : 0 < code) (hcode : code < format.signMaskNat) :
    nonnegativeRatAt format code =
      trailingRat (ofNatBits (format := format) code).trailingBits code *
        (2 : Rat) ^ ((ofNatBits (format := format) code).regimeValue * 4) := by
  rw [nonnegativeRatAt_of_pos_lt_signMask format hpos hcode,
    decodeFields_toRat_eq_trailingRat_mul_regime _ (signBit_ofNatBits_eq_false format code hcode),
    magnitudeBits_ofNatBits_of_lt_signMask format code hcode]
  rfl

/--
Appending a zero low bit while increasing the posit width preserves the exact finite value.

This is the even half of the standard's `(n + 1)`-bit rounding construction: an `n`-bit code `U`
is embedded as `U0`, while the adjacent boundary is `U1`. The theorem holds for every valid static
width, including the zero code.
-/
theorem nonnegativeRatAt_nextPrecision_two_mul
    (format : Format) {code : Nat}
    (hcode : code < format.signMaskNat) :
    nonnegativeRatAt format.nextPrecision (2 * code) =
      nonnegativeRatAt format code := by
  rcases Nat.eq_zero_or_pos code with rfl | hpos
  · simp
  have hpayload := format.payloadBits_pos
  have hwideCode : 2 * code < format.nextPrecision.signMaskNat := by
    rw [Format.nextPrecision_signMaskNat]
    omega
  have hbit : (ofNatBits (format := format.nextPrecision) (2 * code)).regimeBit =
      (ofNatBits (format := format) code).regimeBit := by
    rw [regimeBit_ofNatBits _ hwideCode, regimeBit_ofNatBits _ hcode,
      Format.nextPrecision_payloadBits, Nat.add_sub_cancel,
      show format.payloadBits = (format.payloadBits - 1) + 1 by omega, Nat.testBit_succ]
    norm_num
  have hrun : (ofNatBits (format := format.nextPrecision) (2 * code)).regimeRunLength =
      (ofNatBits (format := format) code).regimeRunLength := by
    rw [regimeRunLength_ofNatBits _ hwideCode, regimeRunLength_ofNatBits _ hcode,
      Format.nextPrecision_payloadBits, Nat.add_sub_cancel]
    exact countLeadingRun_two_mul hpos hcode
  have hregime : (ofNatBits (format := format.nextPrecision) (2 * code)).regimeValue =
      (ofNatBits (format := format) code).regimeValue := by
    unfold regimeValue
    rw [hbit, hrun]
  rw [nonnegativeRatAt_eq_trailingRat_mul_regime _ (by omega) hwideCode,
    nonnegativeRatAt_eq_trailingRat_mul_regime format hpos hcode, hregime]
  congr 1
  set run := (ofNatBits (format := format) code).regimeRunLength with hrunDef
  have hrunLe : run ≤ format.payloadBits := regimeRunLength_le_payload _
  unfold trailingBits hasRegimeTerminator
  rw [← hrunDef, hrun, Format.nextPrecision_payloadBits]
  rcases hrunLe.lt_or_eq with hrunLt | hrunEq
  · simp only [hrunLt, Nat.lt_succ_of_lt hrunLt, decide_true, ↓reduceIte]
    rw [show format.payloadBits + 1 - run - 1 = format.payloadBits - run - 1 + 1 by omega]
    exact trailingRat_succ_two_mul _ _
  · simp [hrunEq, trailingRat, natToRat_eq_cast, Nat.mod_one]

/--
Within one regime block, increasing a positive unsigned code strictly increases its exact value.

Division by the trailing-field modulus yields equal regime prefixes; taking remainders removes
them. Code order is then exactly order of the bounded exponent/fraction remainder, whose rational
interpretation is strictly monotone.
-/
theorem nonnegativeRatAt_lt_of_regimeValue_eq
    (format : Format) {left right : Nat}
    (hleftPos : 0 < left)
    (hlt : left < right)
    (hright : right < format.signMaskNat)
    (hregime :
      (ofNatBits (format := format) left).regimeValue =
        (ofNatBits (format := format) right).regimeValue) :
    nonnegativeRatAt format left <
      nonnegativeRatAt format right := by
  have hleft : left < format.signMaskNat := hlt.trans hright
  have hleftMagnitude := magnitudeBits_ofNatBits_of_lt_signMask format left hleft
  have hrightMagnitude := magnitudeBits_ofNatBits_of_lt_signMask format right hright
  obtain ⟨htrailing, hprefix⟩ :=
    trailingBits_eq_and_prefix_eq_of_regimeValue_eq
      (ofNatBits (format := format) left) (ofNatBits (format := format) right)
      (by rw [hleftMagnitude]; exact hleft) (by rw [hrightMagnitude]; exact hright) hregime
  rw [hleftMagnitude, hrightMagnitude, htrailing] at hprefix
  rw [nonnegativeRatAt_eq_trailingRat_mul_regime format hleftPos hleft,
    nonnegativeRatAt_eq_trailingRat_mul_regime format (hleftPos.trans hlt) hright,
    hregime, htrailing]
  refine mul_lt_mul_of_pos_right ?_ (zpow_pos two_pos _)
  rw [← trailingRat_mod_twoPow _ left, ← trailingRat_mod_twoPow _ right]
  exact trailingRat_lt_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _))
    (Nat.mod_lt _ (Nat.two_pow_pos _)) (mod_lt_of_lt_of_div_eq hlt hprefix)

/--
Two adjacent regime blocks are strictly separated because every tail lies in `[1, 16)` and the
Posit Standard (2022) advances the binary scale by exactly four at each regime step.
-/
private theorem mul_zpow_lt_of_regime_lt
    {leftTail rightTail : Rat}
    {leftRegime rightRegime : Int}
    (hleftTailUpper : leftTail < 16)
    (hrightTailLower : 1 ≤ rightTail)
    (hregime : leftRegime < rightRegime) :
    leftTail * (2 : Rat) ^ (leftRegime * 4) <
      rightTail * (2 : Rat) ^ (rightRegime * 4) := by
  have hleftPowerPos : (0 : Rat) < (2 : Rat) ^ (leftRegime * 4) := zpow_pos two_pos _
  have hblock :
      (16 : Rat) * (2 : Rat) ^ (leftRegime * 4) = (2 : Rat) ^ ((leftRegime + 1) * 4) := by
    rw [show (16 : Rat) = (2 : Rat) ^ (4 : Int) by norm_num, ← zpow_add₀ two_ne_zero]
    ring_nf
  have hpowers : (2 : Rat) ^ ((leftRegime + 1) * 4) ≤ (2 : Rat) ^ (rightRegime * 4) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  nlinarith

/-- Every positive unsigned code below the sign mask denotes a strictly positive rational. -/
theorem nonnegativeRatAt_pos
    (format : Format) {code : Nat}
    (hpos : 0 < code)
    (hcode : code < format.signMaskNat) :
    0 < nonnegativeRatAt format code := by
  rw [nonnegativeRatAt_eq_trailingRat_mul_regime format hpos hcode]
  exact mul_pos (lt_of_lt_of_le one_pos (trailingRat_bounds _ _).1) (zpow_pos two_pos _)

/-- Strictly increasing regime values strictly separate the corresponding positive codes. -/
theorem nonnegativeRatAt_lt_of_regimeValue_lt
    (format : Format) {left right : Nat}
    (hleftPos : 0 < left)
    (hlt : left < right)
    (hright : right < format.signMaskNat)
    (hregime :
      (ofNatBits (format := format) left).regimeValue <
        (ofNatBits (format := format) right).regimeValue) :
    nonnegativeRatAt format left <
      nonnegativeRatAt format right := by
  rw [nonnegativeRatAt_eq_trailingRat_mul_regime format hleftPos (hlt.trans hright),
    nonnegativeRatAt_eq_trailingRat_mul_regime format (hleftPos.trans hlt) hright]
  exact mul_zpow_lt_of_regime_lt (trailingRat_bounds _ _).2 (trailingRat_bounds _ _).1 hregime

/--
Unsigned posit codes below the sign mask are strictly ordered by their exact rational meanings.

This is the width-independent ordering theorem used by bisection, rounding, comparison, and every
certified execution backend.
-/
theorem nonnegativeRatAt_lt_of_lt
    (format : Format) {left right : Nat}
    (hlt : left < right)
    (hright : right < format.signMaskNat) :
    nonnegativeRatAt format left <
      nonnegativeRatAt format right := by
  by_cases hleftZero : left = 0
  · subst left
    rw [nonnegativeRatAt_zero]
    exact nonnegativeRatAt_pos format (by omega) hright
  · have hleftPos : 0 < left :=
      Nat.pos_of_ne_zero hleftZero
    rcases (regimeValue_ofNatBits_le_of_le format hlt.le hright).eq_or_lt with
      hregimeEq | hregimeLt
    · exact nonnegativeRatAt_lt_of_regimeValue_eq format hleftPos hlt hright hregimeEq
    · exact nonnegativeRatAt_lt_of_regimeValue_lt format hleftPos hlt hright hregimeLt

/-- Exact rational lookup is strictly monotone on the complete nonnegative finite code interval. -/
theorem nonnegativeRatAt_strictMonoOn (format : Format) :
    StrictMonoOn (nonnegativeRatAt format)
      (Set.Iio format.signMaskNat) := by
  intro left hleft right hright hlt
  exact nonnegativeRatAt_lt_of_lt format hlt hright

/-- On nonnegative finite codes, rational-value comparison is exactly unsigned-code comparison. -/
theorem nonnegativeRatAt_le_iff
    (format : Format) {left right : Nat}
    (hleft : left < format.signMaskNat)
    (hright : right < format.signMaskNat) :
    nonnegativeRatAt format left ≤
        nonnegativeRatAt format right ↔
      left ≤ right := by
  constructor
  · intro hvalue
    by_contra hcode
    have hrightLeft : right < left :=
      Nat.lt_of_not_ge hcode
    have hstrict :=
      nonnegativeRatAt_lt_of_lt
        format hrightLeft hleft
    exact (not_lt_of_ge hvalue) hstrict
  · intro hcode
    rcases hcode.eq_or_lt with hcodeEq | hcodeLt
    · rw [hcodeEq]
    · exact
        (nonnegativeRatAt_lt_of_lt
          format hcodeLt hright).le

/-- Equality of exact nonnegative finite values is equality of their unsigned posit codes. -/
theorem nonnegativeRatAt_injOn (format : Format) :
    Set.InjOn (nonnegativeRatAt format)
      (Set.Iio format.signMaskNat) := by
  exact (nonnegativeRatAt_strictMonoOn format).injOn


end FloatLib.Floats.Formats.Posit.Model
