/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Rounding.GuardSticky.Spec.Fields
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Rounding.GuardSticky.Spec.Stream
public import FloatLib.Floats.Formats.Posit.Semantics.Positive.BitRuns
public import FloatLib.Floats.Formats.Posit.Semantics.Positive.Trailing
public import FloatLib.Floats.Formats.Posit.Semantics.Positive.Order

/-!
# Exact semantics of finite guard-and-sticky streams

Normalized exponent/significand fields and retained stream prefixes denote the exact rational
tail used in Posit rounding. These representation-independent lemmas are shared by native-word
and fixed-limb Posit packers.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.GuardStickyRounding

/-- The explicit fraction of a normalized significand fits below its leading bit. -/
theorem fractionRaw_lt_two_pow
    (significand leading : Nat)
    (hlower : 2 ^ leading ≤ significand)
    (hupper : significand < 2 ^ (leading + 1)) :
    fractionRaw significand leading < 2 ^ leading := by
  unfold fractionRaw
  rw [pow_succ] at hupper
  omega

/-- A valid exponent and normalized significand fit in the complete finite tail width. -/
theorem exactTailRaw_lt_two_pow
    (exponentField significand leading : Nat)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ significand)
    (hupper : significand < 2 ^ (leading + 1)) :
    exactTailRaw exponentField significand leading <
      2 ^ (leading + 2) := by
  have hfraction :=
    fractionRaw_lt_two_pow significand leading hlower hupper
  unfold exactTailRaw
  calc
    exponentField * 2 ^ leading +
          fractionRaw significand leading <
        (exponentField + 1) * 2 ^ leading := by
      rw [Nat.add_mul]
      simpa using
        Nat.add_lt_add_left hfraction
          (exponentField * 2 ^ leading)
    _ ≤ 4 * 2 ^ leading :=
      Nat.mul_le_mul_right (2 ^ leading) (by omega)
    _ = 2 ^ (leading + 2) := by
      rw [show (4 : Nat) = 2 ^ 2 by decide, ← Nat.pow_add]
      congr 1
      omega

/-- Removing the explicit fraction from a normalized tail recovers its two-bit exponent field. -/
theorem exactTailRaw_div_two_pow
    (exponentField significand leading : Nat)
    (hlower : 2 ^ leading ≤ significand)
    (hupper : significand < 2 ^ (leading + 1)) :
    exactTailRaw exponentField significand leading / 2 ^ leading =
      exponentField := by
  have hfraction :=
    fractionRaw_lt_two_pow significand leading hlower hupper
  unfold exactTailRaw
  rw [mul_comm exponentField (2 ^ leading)]
  rw [Nat.mul_add_div (Nat.two_pow_pos leading)]
  rw [Nat.div_eq_of_lt hfraction, Nat.add_zero]

/-- The low normalized-significand bits are precisely its explicit fraction. -/
theorem significand_mod_two_pow
    (significand leading : Nat)
    (hlower : 2 ^ leading ≤ significand)
    (hupper : significand < 2 ^ (leading + 1)) :
    significand % 2 ^ leading =
      fractionRaw significand leading := by
  have hfraction :=
    fractionRaw_lt_two_pow significand leading hlower hupper
  have hdecompose :
      2 ^ leading + fractionRaw significand leading =
        significand := by
    unfold fractionRaw
    omega
  calc
    significand % 2 ^ leading =
        (2 ^ leading + fractionRaw significand leading) %
          2 ^ leading := by
      rw [hdecompose]
    _ = fractionRaw significand leading := by
      simp only [Nat.add_mod, Nat.mod_self,
        Nat.mod_eq_of_lt hfraction, zero_add]

/-- The low `leading` bits of the complete tail are its explicit fraction. -/
theorem exactTailRaw_mod_two_pow
    (exponentField significand leading : Nat)
    (hlower : 2 ^ leading ≤ significand)
    (hupper : significand < 2 ^ (leading + 1)) :
    exactTailRaw exponentField significand leading % 2 ^ leading =
      fractionRaw significand leading := by
  have hfraction :=
    fractionRaw_lt_two_pow significand leading hlower hupper
  unfold exactTailRaw
  rw [mul_comm exponentField (2 ^ leading)]
  simp only [Nat.add_mod, Nat.mul_mod_right,
    Nat.mod_eq_of_lt hfraction, zero_add]

/--
Every suffix contained in the explicit fraction is shared by the complete tail and significand.

The exponent contribution is a multiple of `2 ^ leading`, so reducing either value modulo a
smaller power of two observes exactly the same fraction suffix.
-/
theorem exactTailRaw_mod_eq_significand_mod
    (exponentField significand leading suffix : Nat)
    (hsuffix : suffix ≤ leading)
    (hlower : 2 ^ leading ≤ significand)
    (hupper : significand < 2 ^ (leading + 1)) :
    exactTailRaw exponentField significand leading % 2 ^ suffix =
      significand % 2 ^ suffix := by
  have hdivisor : 2 ^ suffix ∣ 2 ^ leading :=
    Nat.pow_dvd_pow 2 hsuffix
  calc
    exactTailRaw exponentField significand leading % 2 ^ suffix =
        (exactTailRaw exponentField significand leading %
          2 ^ leading) % 2 ^ suffix := by
      exact (Nat.mod_mod_of_dvd _ hdivisor).symm
    _ = (fractionRaw significand leading) % 2 ^ suffix := by
      rw [exactTailRaw_mod_two_pow
        exponentField significand leading hlower hupper]
    _ = (significand % 2 ^ leading) % 2 ^ suffix := by
      rw [significand_mod_two_pow significand leading hlower hupper]
    _ = significand % 2 ^ suffix :=
      Nat.mod_mod_of_dvd significand hdivisor

/--
The Posit exponent/fraction prefix is ordinary truncation of the complete finite tail.

This identity is the central bridge between field-oriented packing and generic binary rounding.
-/
theorem tailPrefix_eq_streamPrefix
    (exponentField significand leading count : Nat)
    (hlower : 2 ^ leading ≤ significand)
    (hupper : significand < 2 ^ (leading + 1)) :
    DirectDyadicPacking.tailPrefix
        exponentField significand leading count =
      streamPrefix
        (exactTailRaw exponentField significand leading)
        (leading + 2) count := by
  have hfraction :
      fractionRaw significand leading < 2 ^ leading :=
    fractionRaw_lt_two_pow significand leading hlower hupper
  by_cases hcountTwo : count ≤ 2
  · have hcountWidth : count ≤ leading + 2 := by
      omega
    simp only [DirectDyadicPacking.tailPrefix, ite_eq_left hcountTwo,
      streamPrefix, ite_eq_left hcountWidth, Nat.shiftRight_eq_div_pow]
    have hpower :
        2 ^ (leading + 2 - count) =
          2 ^ leading * 2 ^ (2 - count) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [hpower, ← Nat.div_div_eq_div_mul]
    have hrawDiv :
        exactTailRaw exponentField significand leading /
            2 ^ leading =
          exponentField := by
      unfold exactTailRaw
      rw [mul_comm exponentField (2 ^ leading)]
      rw [Nat.mul_add_div (Nat.two_pow_pos leading)]
      rw [Nat.div_eq_of_lt hfraction, Nat.add_zero]
    rw [hrawDiv]
  · have hcountLarge : 2 < count := by
      omega
    simp only [DirectDyadicPacking.tailPrefix, ite_eq_right hcountTwo,
      Nat.shiftLeft_eq]
    by_cases hcountWidth : count ≤ leading + 2
    · have hfractionCount : count - 2 ≤ leading := by
        omega
      simp only [DirectDyadicPacking.fractionPrefix,
        ite_eq_left hfractionCount, Nat.shiftRight_eq_div_pow,
        streamPrefix, ite_eq_left hcountWidth]
      have hpower :
          2 ^ leading =
            2 ^ (leading - (count - 2)) *
              2 ^ (count - 2) := by
        rw [← Nat.pow_add]
        congr 1
        omega
      have hwidth :
          leading + 2 - count =
            leading - (count - 2) := by
        omega
      rw [hwidth]
      unfold exactTailRaw
      rw [hpower]
      have hreassociate :
          exponentField *
              (2 ^ (leading - (count - 2)) * 2 ^ (count - 2)) =
            2 ^ (leading - (count - 2)) *
              (exponentField * 2 ^ (count - 2)) := by
        ac_rfl
      rw [hreassociate]
      rw [Nat.mul_add_div (Nat.two_pow_pos _)]
      simp only [fractionRaw, Nat.shiftLeft_eq, one_mul]
    · have hfractionCount : ¬count - 2 ≤ leading := by
        omega
      simp only [DirectDyadicPacking.fractionPrefix,
        ite_eq_right hfractionCount, Nat.shiftLeft_eq,
        streamPrefix, ite_eq_right hcountWidth]
      have hpower :
          2 ^ leading * 2 ^ (count - (leading + 2)) =
            2 ^ (count - 2) := by
        rw [← Nat.pow_add]
        congr 1
        omega
      have hremaining :
          count - (leading + 2) =
            count - 2 - leading := by
        omega
      unfold exactTailRaw
      rw [Nat.add_mul]
      rw [mul_assoc exponentField, hpower, hremaining]
      simp only [fractionRaw, one_mul]

/-- Reading beyond the complete finite exponent/fraction stream returns zero. -/
theorem tailBit_eq_false_of_le
    (exponentField significand leading index : Nat)
    (hindex : leading + 2 ≤ index) :
    tailBit exponentField significand leading index = false := by
  unfold tailBit
  rw [ite_eq_right (by omega)]
  dsimp only
  rw [ite_eq_right (by omega)]

/-- No sticky information remains after the complete finite tail has been consumed. -/
theorem tailHasNonzeroAfter_eq_false_of_le
    (exponentField significand leading consumed : Nat)
    (hconsumed : leading + 2 ≤ consumed) :
    tailHasNonzeroAfter exponentField significand leading consumed = false := by
  unfold tailHasNonzeroAfter
  rw [ite_eq_right (by omega)]
  dsimp only
  rw [ite_eq_right (by omega)]

/-- The field-oriented bit reader is the guard bit of the complete finite stream. -/
theorem tailBit_eq_streamGuard
    (exponentField significand leading index : Nat)
    (hlower : 2 ^ leading ≤ significand)
    (hupper : significand < 2 ^ (leading + 1)) :
    tailBit exponentField significand leading index =
      streamGuard
        (exactTailRaw exponentField significand leading)
        (leading + 2) index := by
  by_cases hindex : index < leading + 2
  · unfold streamGuard
    rw [ite_eq_left hindex]
    unfold tailBit
    by_cases hexponent : index < 2
    · rw [ite_eq_left hexponent]
      have hposition :
          leading + 2 - index - 1 =
            (1 - index) + leading := by
        omega
      rw [hposition, Nat.testBit_add]
      rw [exactTailRaw_div_two_pow
        exponentField significand leading hlower hupper]
    · rw [ite_eq_right hexponent]
      dsimp only
      have hfraction : index - 2 < leading := by
        omega
      rw [ite_eq_left hfraction]
      let bit := leading - (index - 2) - 1
      have hbitLt : bit < leading := by
        dsimp [bit]
        omega
      have hposition :
          leading + 2 - index - 1 = bit := by
        dsimp [bit]
        omega
      have hrawBit :=
        Nat.testBit_mod_two_pow
          (exactTailRaw exponentField significand leading)
          leading bit
      have hsignificandBit :=
        Nat.testBit_mod_two_pow significand leading bit
      simp only [hbitLt, decide_true, Bool.true_and] at hrawBit hsignificandBit
      rw [hposition]
      calc
        significand.testBit bit =
            (significand % 2 ^ leading).testBit bit :=
          hsignificandBit.symm
        _ = (fractionRaw significand leading).testBit bit := by
          rw [significand_mod_two_pow
            significand leading hlower hupper]
        _ =
            (exactTailRaw exponentField significand leading %
              2 ^ leading).testBit bit := by
          rw [exactTailRaw_mod_two_pow
            exponentField significand leading hlower hupper]
        _ =
            (exactTailRaw exponentField significand leading).testBit bit :=
          hrawBit
  · have hindexLe : leading + 2 ≤ index :=
      Nat.le_of_not_gt hindex
    rw [tailBit_eq_false_of_le
      exponentField significand leading index hindexLe]
    simp [streamGuard, hindex]

/--
The field-oriented suffix test is the sticky bit of the complete finite stream.

The caller supplies the number of retained bits, while `tailHasNonzeroAfter` receives the number
of bits consumed through the guard. Splitting on a zero or positive retained prefix isolates the
only case where one exponent bit remains; every later suffix lies wholly inside the explicit
fraction.
-/
theorem tailHasNonzeroAfter_succ_eq_streamSticky
    (exponentField significand leading retained : Nat)
    (hlower : 2 ^ leading ≤ significand)
    (hupper : significand < 2 ^ (leading + 1)) :
    tailHasNonzeroAfter exponentField significand leading (retained + 1) =
      streamSticky
        (exactTailRaw exponentField significand leading)
        (leading + 2) retained := by
  cases retained with
  | zero =>
      have hfraction :
          fractionRaw significand leading < 2 ^ leading :=
        fractionRaw_lt_two_pow significand leading hlower hupper
      have hpowerPos : 0 < 2 ^ leading :=
        Nat.two_pow_pos leading
      have hexponentModLt : exponentField % 2 < 2 :=
        Nat.mod_lt exponentField (by decide)
      have hexponentModLe : exponentField % 2 ≤ 1 := by
        omega
      have hscaled :
          (exponentField % 2) * 2 ^ leading ≤ 2 ^ leading := by
        simpa using
          Nat.mul_le_mul_right (2 ^ leading) hexponentModLe
      have hcandidateLt :
          (exponentField % 2) * 2 ^ leading +
              fractionRaw significand leading <
            2 * 2 ^ leading := by
        omega
      have hraw :
          exactTailRaw exponentField significand leading =
            ((exponentField % 2) * 2 ^ leading +
                fractionRaw significand leading) +
              (2 * 2 ^ leading) * (exponentField / 2) := by
        unfold exactTailRaw
        nth_rewrite 1 [← Nat.mod_add_div exponentField 2]
        simp only [Nat.add_mul, Nat.mul_assoc]
        ac_rfl
      have hpower :
          2 ^ (leading + 1) = 2 * 2 ^ leading := by
        rw [Nat.pow_succ]
        omega
      have hrawMod :
          exactTailRaw exponentField significand leading %
              2 ^ (leading + 1) =
            (exponentField % 2) * 2 ^ leading +
              fractionRaw significand leading := by
        rw [hpower, hraw, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt hcandidateLt]
      unfold tailHasNonzeroAfter streamSticky
      change
        (exponentField % 2 != 0 ||
            significand % 2 ^ leading != 0) =
          (exactTailRaw exponentField significand leading %
              2 ^ (leading + 1) != 0)
      rw [significand_mod_two_pow
        significand leading hlower hupper, hrawMod]
      have hexponentMod :
          exponentField % 2 = 0 ∨ exponentField % 2 = 1 := by
        omega
      rcases hexponentMod with hexponentMod | hexponentMod
      · simp [hexponentMod]
      · simp [hexponentMod]
  | succ retained =>
      unfold tailHasNonzeroAfter streamSticky
      rw [ite_eq_right (by omega)]
      dsimp only
      have hconsumedFraction :
          retained + 1 + 1 - 2 = retained := by
        omega
      rw [hconsumedFraction]
      have hshift :
          leading + 2 - Nat.succ retained - 1 =
            leading - retained := by
        omega
      rw [hshift]
      by_cases hretained : retained < leading
      · rw [ite_eq_left hretained]
        rw [exactTailRaw_mod_eq_significand_mod
          exponentField significand leading (leading - retained)
          (by omega) hlower hupper]
      · rw [ite_eq_right hretained]
        have hzero : leading - retained = 0 := by
          omega
        rw [hzero, Nat.pow_zero, Nat.mod_one]
        rfl

/--
Direct field inspection and the concatenated-stream specification select the same interior code.

The normalization hypotheses are the only semantic facts needed to identify the two views of the
tail. Executable backends can therefore optimize representation without changing the rounding
argument.
-/
theorem roundInteriorCodeFromFields_eq_roundInteriorCode
    (format : Format) (regime : Int)
    (exponentField significand leading regimeFieldBits : Nat)
    (hlower : 2 ^ leading ≤ significand)
    (hupper : significand < 2 ^ (leading + 1)) :
    roundInteriorCodeFromFields format regime exponentField significand
        leading regimeFieldBits =
      roundInteriorCode format regime exponentField significand
        leading regimeFieldBits := by
  unfold roundInteriorCodeFromFields roundInteriorCode
  dsimp only
  rw [tailBit_eq_streamGuard
    exponentField significand leading
    (format.payloadBits - regimeFieldBits) hlower hupper]
  rw [tailHasNonzeroAfter_succ_eq_streamSticky
    exponentField significand leading
    (format.payloadBits - regimeFieldBits) hlower hupper]

/-- Consuming the complete finite stream reproduces its packed natural-number value. -/
theorem tailPrefix_full
    (exponentField significand leading : Nat)
    (hlower : 2 ^ leading ≤ significand)
    (hupper : significand < 2 ^ (leading + 1)) :
    DirectDyadicPacking.tailPrefix exponentField significand leading
        (leading + 2) =
      exactTailRaw exponentField significand leading := by
  cases leading with
  | zero =>
      have hsignificand : significand = 1 := by
        norm_num at hlower hupper
        omega
      subst significand
      simp [DirectDyadicPacking.tailPrefix,
        exactTailRaw, fractionRaw]
  | succ leading =>
      unfold DirectDyadicPacking.tailPrefix
      rw [ite_eq_right (by omega)]
      unfold DirectDyadicPacking.fractionPrefix
      rw [ite_eq_left (by omega)]
      simp [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
        exactTailRaw, fractionRaw]

/--
The finite exponent/fraction stream denotes the normalized significand scaled by its exponent.

This is the semantic bridge from bit-oriented guard/sticky inspection to the rational model used
by the Posit decoder.
-/
theorem trailingRat_exactTailRaw
    (exponentField significand leading : Nat)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ significand)
    (hupper : significand < 2 ^ (leading + 1)) :
    Model.trailingRat (leading + 2)
        (exactTailRaw exponentField significand leading) =
      (significand : Rat) / (2 ^ leading : Nat) *
        (2 : Rat) ^ Int.ofNat exponentField := by
  have hdiv :=
    exactTailRaw_div_two_pow
      exponentField significand leading hlower hupper
  have hmod :=
    exactTailRaw_mod_two_pow
      exponentField significand leading hlower hupper
  have hexponentMod : exponentField % 2 ^ 2 = exponentField := by
    simpa using Nat.mod_eq_of_lt hexponent
  have hfractionCast :
      ((significand - 2 ^ leading : Nat) : Rat) =
        (significand : Rat) - (2 ^ leading : Nat) := by
    rw [Nat.cast_sub hlower]
  unfold Model.trailingRat
  simp only [
    show min 2 (leading + 2) = 2 by omega,
    show leading + 2 - 2 = leading by omega,
    show 2 - 2 = 0 by omega,
    pow_zero, Nat.mul_one]
  rw [hdiv, hexponentMod, hmod]
  unfold fractionRaw Model.natToRat
  change
    (1 + ((significand - 2 ^ leading : Nat) : Rat) /
        ((2 ^ leading : Nat) : Rat)) *
        (2 : Rat) ^ Int.ofNat exponentField =
      (significand : Rat) / ((2 ^ leading : Nat) : Rat) *
        (2 : Rat) ^ Int.ofNat exponentField
  rw [hfractionCast]
  field_simp
  ring

/--
A normalized exact value factors into the finite tail value and its Posit regime scale.

Arithmetic kernels establish `hscale` while normalizing their intermediate. The rounding proof
can then reason only about the finite tail stream and reattach the positive regime scale once.
-/
theorem normalizedValue_eq_trailingRat_mul_regime
    (targetExponent regime : Int)
    (exponentField significand leading : Nat)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ significand)
    (hupper : significand < 2 ^ (leading + 1))
    (hscale :
      targetExponent + Int.ofNat leading =
        regime * 4 + Int.ofNat exponentField) :
    (significand : Rat) * (2 : Rat) ^ targetExponent =
      Model.trailingRat (leading + 2)
          (exactTailRaw exponentField significand leading) *
        (2 : Rat) ^ (regime * 4) := by
  rw [trailingRat_exactTailRaw
    exponentField significand leading
    hexponent hlower hupper]
  calc
    (significand : Rat) * (2 : Rat) ^ targetExponent =
        ((significand : Rat) / (2 : Rat) ^ Int.ofNat leading) *
          (2 : Rat) ^
            (targetExponent + Int.ofNat leading) := by
      rw [zpow_add₀ (by norm_num : (2 : Rat) ≠ 0)]
      field_simp
    _ =
        ((significand : Rat) / (2 : Rat) ^ Int.ofNat leading) *
          (2 : Rat) ^
            (regime * 4 + Int.ofNat exponentField) := by
      rw [hscale]
    _ =
        ((significand : Rat) / (2 ^ leading : Nat)) *
            (2 : Rat) ^ Int.ofNat exponentField *
          (2 : Rat) ^ (regime * 4) := by
      rw [zpow_add₀ (by norm_num : (2 : Rat) ≠ 0)]
      simp only [Int.ofNat_eq_natCast, zpow_natCast]
      norm_num [Nat.cast_pow, div_eq_mul_inv, inv_pow]
      ring

/-- Appending zero bits preserves the rational value represented by a finite tail. -/
theorem trailingRat_mul_two_pow
    (trailing raw extra : Nat) :
    Model.trailingRat (trailing + extra) (raw * 2 ^ extra) =
      Model.trailingRat trailing raw := by
  induction extra with
  | zero =>
      simp
  | succ extra inductionHypothesis =>
      have hwidth :
          trailing + (extra + 1) =
            (trailing + extra) + 1 := by
        omega
      rw [hwidth, Nat.pow_succ]
      calc
        Model.trailingRat ((trailing + extra) + 1)
            (raw * (2 ^ extra * 2)) =
          Model.trailingRat ((trailing + extra) + 1)
            (2 * (raw * 2 ^ extra)) := by
            congr 1
            ring
        _ =
          Model.trailingRat (trailing + extra)
            (raw * 2 ^ extra) :=
          Model.trailingRat_succ_two_mul
            (trailing + extra) (raw * 2 ^ extra)
        _ = Model.trailingRat trailing raw :=
          inductionHypothesis

/--
Truncating a bounded exponent/fraction stream cannot increase its exact value.

The retained prefix is padded back to the complete stream width before applying strict
monotonicity. This formulation also covers tails with zero retained bits.
-/
theorem trailingRat_streamPrefix_le
    {raw width retained : Nat}
    (hraw : raw < 2 ^ width)
    (hretained : retained ≤ width) :
    Model.trailingRat retained (streamPrefix raw width retained) ≤
      Model.trailingRat width raw := by
  let shift := width - retained
  let pfx := streamPrefix raw width retained
  have hprefix :
      pfx = raw / 2 ^ shift := by
    dsimp [pfx, shift]
    unfold streamPrefix
    rw [ite_eq_left hretained]
  have hwidth : retained + shift = width := by
    dsimp [shift]
    omega
  have hprefixBound :
      pfx < 2 ^ retained := by
    dsimp [pfx]
    unfold streamPrefix
    rw [ite_eq_left hretained, Nat.div_lt_iff_lt_mul
      (Nat.two_pow_pos (width - retained))]
    rw [← Nat.pow_add, Nat.add_comm,
      Nat.sub_add_cancel hretained]
    exact hraw
  have hpaddedBound :
      pfx * 2 ^ shift < 2 ^ width := by
    rw [← hwidth, Nat.pow_add]
    exact (Nat.mul_lt_mul_right (Nat.two_pow_pos shift)).2
      hprefixBound
  have hpaddedLe : pfx * 2 ^ shift ≤ raw := by
    rw [hprefix]
    exact Nat.div_mul_le_self raw (2 ^ shift)
  rw [← trailingRat_mul_two_pow retained pfx shift, hwidth]
  by_cases hequal : pfx * 2 ^ shift = raw
  · rw [hequal]
  · exact (Model.trailingRat_lt_of_lt
      hpaddedBound hraw (lt_of_le_of_ne hpaddedLe hequal)).le

/--
Retaining at least the complete finite stream is exact.

Extra requested positions are zero padding, so this theorem is the representable-value branch of
the guard/sticky proof.
-/
theorem trailingRat_streamPrefix_eq_of_width_le
    (raw width retained : Nat)
    (hwidth : width ≤ retained) :
    Model.trailingRat retained (streamPrefix raw width retained) =
      Model.trailingRat width raw := by
  have hprefix :
      streamPrefix raw width retained =
        raw * 2 ^ (retained - width) := by
    unfold streamPrefix
    by_cases hequal : retained = width
    · subst retained
      simp
    · rw [ite_eq_right (by omega)]
  rw [hprefix]
  have hsum : width + (retained - width) = retained :=
    Nat.add_sub_of_le hwidth
  calc
    Model.trailingRat retained
        (raw * 2 ^ (retained - width)) =
      Model.trailingRat (width + (retained - width))
        (raw * 2 ^ (retained - width)) := by rw [hsum]
    _ = Model.trailingRat width raw :=
      trailingRat_mul_two_pow width raw (retained - width)

/-- Retaining an arbitrary number of leading stream bits never increases the exact value. -/
theorem trailingRat_streamPrefix_le_total
    {raw width retained : Nat}
    (hraw : raw < 2 ^ width) :
    Model.trailingRat retained (streamPrefix raw width retained) ≤
      Model.trailingRat width raw := by
  by_cases hretained : retained ≤ width
  · exact trailingRat_streamPrefix_le hraw hretained
  · exact (trailingRat_streamPrefix_eq_of_width_le
      raw width retained (by omega)).le

/--
When the retained prefix has an in-regime successor, the exact stream lies strictly below it.

The successor is padded to the complete width and compared there. Regime-boundary carry is
intentionally excluded and handled once by the Posit layout layer.
-/
theorem trailingRat_lt_streamPrefix_succ
    {raw width retained : Nat}
    (hraw : raw < 2 ^ width)
    (hretained : retained < width)
    (hprefixSucc :
      streamPrefix raw width retained + 1 < 2 ^ retained) :
    Model.trailingRat width raw <
      Model.trailingRat retained
        (streamPrefix raw width retained + 1) := by
  let shift := width - retained
  let pfx := streamPrefix raw width retained
  have hprefix :
      pfx = raw / 2 ^ shift := by
    dsimp [pfx, shift]
    unfold streamPrefix
    rw [ite_eq_left hretained.le]
  have hwidth : retained + shift = width := by
    dsimp [shift]
    omega
  have hrawUpper :
      raw < (pfx + 1) * 2 ^ shift := by
    have hmodLt :
        raw % 2 ^ shift < 2 ^ shift :=
      Nat.mod_lt raw (Nat.two_pow_pos shift)
    have hdecompose :=
      Nat.mod_add_div raw (2 ^ shift)
    rw [hprefix]
    calc
      raw = raw % 2 ^ shift +
          2 ^ shift * (raw / 2 ^ shift) := hdecompose.symm
      _ < 2 ^ shift +
          2 ^ shift * (raw / 2 ^ shift) :=
        Nat.add_lt_add_right hmodLt _
      _ = (raw / 2 ^ shift + 1) * 2 ^ shift := by
        ring
  have hpaddedBound :
      (pfx + 1) * 2 ^ shift < 2 ^ width := by
    rw [← hwidth, Nat.pow_add]
    exact (Nat.mul_lt_mul_right
      (Nat.two_pow_pos shift)).2 hprefixSucc
  rw [← trailingRat_mul_two_pow retained
    (pfx + 1) shift, hwidth]
  exact Model.trailingRat_lt_of_lt hraw hpaddedBound hrawUpper

/-- Bounded raw-tail order is equivalent to exact rational-tail order. -/
theorem trailingRat_lt_iff_of_bounded
    {width left right : Nat}
    (hleft : left < 2 ^ width)
    (hright : right < 2 ^ width) :
    Model.trailingRat width left <
        Model.trailingRat width right ↔
      left < right := by
  constructor
  · intro hrat
    by_contra hnot
    have hrightLe : right ≤ left :=
      Nat.le_of_not_gt hnot
    rcases hrightLe.eq_or_lt with hequal | hlt
    · subst right
      exact (lt_irrefl _ hrat)
    · have hreverse :=
        Model.trailingRat_lt_of_lt hright hleft hlt
      exact (not_lt_of_ge hreverse.le) hrat
  · exact Model.trailingRat_lt_of_lt hleft hright


end FloatLib.Floats.Formats.Posit.Model.GuardStickyRounding
