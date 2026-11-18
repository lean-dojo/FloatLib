/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Proof

import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

/-!
# Order of positive finite IEEE P3109 codes

Positive finite codes are ordered by their unsigned natural-number representation, so in
`binary8p4se` code `0x08`, the first normal value, sits above `0x07`, the last subnormal one. This
module proves that the exact decoder preserves that order for every valid descriptor, across the
subnormal-to-normal boundary and in the `P = 1` case.

Reference: P3109 Interim Report v4.1 (unapproved draft), §§3.1 and 4.7.2–4.7.6.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109
namespace Format

/-- The spacing exponent is constant within each row, including canonical zero. -/
theorem decodeQuantum_add_mul (format : Format) (trailing row : Nat)
    (htrailing : trailing < 2 ^ format.trailingBits) :
    format.decodeQuantum (trailing + row * 2 ^ format.trailingBits) =
      if row = 0 then format.minimumQuantumExponent
      else (row : Int) - format.exponentBias + 1 - format.precision := by
  have hunit : 0 < 2 ^ format.trailingBits := Nat.two_pow_pos _
  have hdiv :
      (trailing + row * 2 ^ format.trailingBits) / 2 ^ format.trailingBits = row := by
    rw [Nat.add_mul_div_right _ _ hunit, Nat.div_eq_of_lt htrailing, Nat.zero_add]
  by_cases hrow : row = 0
  · subst row
    by_cases hzero : trailing = 0 <;>
      simp [decodeQuantum, decodePositiveFinite, hzero, Nat.div_eq_of_lt htrailing]
  · simp [decodeQuantum, decodePositiveFinite, hdiv, hrow]

/-- Positive decoding is its stored significand times the spacing quantum, including zero. -/
theorem decodePositiveFinite_toRat_eq_significand_mul (format : Format) (bits : Nat) :
    (format.decodePositiveFinite bits).toRat =
      ((format.decodePositiveFinite bits).significand : Rat) *
        2 ^ format.decodeQuantum bits := by
  by_cases hzero : bits = 0
  · simp [hzero, decodeQuantum]
  · simp [decodeQuantum, hzero, Numerics.Dyadic.toRat, Numerics.Dyadic.signedSignificand]

/-- Consecutive positive codes differ by exactly one quantum, also across exponent rows. -/
theorem decodePositiveFinite_succ_toRat
    (format : Format) (bits : Nat) :
    (format.decodePositiveFinite (bits + 1)).toRat =
      (format.decodePositiveFinite bits).toRat + 2 ^ format.decodeQuantum bits := by
  have hunit : 0 < 2 ^ format.trailingBits := Nat.two_pow_pos _
  obtain ⟨row, trailing, htrailing, rfl⟩ :
      ∃ row trailing, trailing < 2 ^ format.trailingBits ∧
        bits = trailing + row * 2 ^ format.trailingBits :=
    ⟨bits / 2 ^ format.trailingBits, bits % 2 ^ format.trailingBits, Nat.mod_lt _ hunit,
      by rw [Nat.mul_comm]; exact (Nat.mod_add_div bits _).symm⟩
  rw [format.decodeQuantum_add_mul trailing row htrailing]
  by_cases hcarry : trailing + 1 = 2 ^ format.trailingBits
  · rw [show trailing + row * 2 ^ format.trailingBits + 1 =
        0 + (row + 1) * 2 ^ format.trailingBits by
      rw [Nat.add_mul, Nat.one_mul]; omega,
      format.decodePositiveFinite_toRat_add_mul 0 (row + 1) hunit (Nat.succ_ne_zero row)]
    rcases Nat.eq_zero_or_pos row with rfl | hrow
    · simp only [ite_true, Nat.zero_mul, Nat.add_zero]
      rw [format.decodePositiveFinite_toRat_of_lt trailing htrailing,
        show (((0 + 1 : Nat) : Int) - format.exponentBias + 1 - format.precision) =
          format.minimumQuantumExponent by
        unfold minimumQuantumExponent
        simp only [Int.ofNat_eq_natCast]
        push_cast
        ring]
      have hc : ((2 ^ format.trailingBits : Nat) : Rat) = trailing + 1 := by
        exact_mod_cast hcarry.symm
      rw [hc]
      ring
    · simp only [hrow.ne', ite_false]
      rw [format.decodePositiveFinite_toRat_add_mul trailing row htrailing hrow.ne',
        show (((row + 1 : Nat) : Int) - format.exponentBias + 1 - format.precision) =
          ((row : Nat) : Int) - format.exponentBias + 1 - format.precision + 1 by
        push_cast
        omega,
        zpow_add_one₀ (by norm_num : (2 : Rat) ≠ 0)]
      have hcoefficient :
          ((2 ^ format.trailingBits + 0 : Nat) : Rat) * 2 =
            ((2 ^ format.trailingBits + trailing : Nat) : Rat) + 1 := by
        exact_mod_cast (by omega :
          (2 ^ format.trailingBits + 0) * 2 = 2 ^ format.trailingBits + trailing + 1)
      calc
        _ = (((2 ^ format.trailingBits + 0 : Nat) : Rat) * 2) *
            2 ^ ((row : Int) - format.exponentBias + 1 - format.precision) := by ring
        _ = _ := by rw [hcoefficient]; ring
  · have hsucc : trailing + 1 < 2 ^ format.trailingBits := by omega
    rw [show trailing + row * 2 ^ format.trailingBits + 1 =
      (trailing + 1) + row * 2 ^ format.trailingBits by omega]
    rcases Nat.eq_zero_or_pos row with rfl | hrow
    · simp only [ite_true, Nat.zero_mul, Nat.add_zero]
      rw [
        format.decodePositiveFinite_toRat_of_lt trailing htrailing,
        format.decodePositiveFinite_toRat_of_lt (trailing + 1) hsucc]
      push_cast
      ring
    · simp only [hrow.ne', ite_false]
      rw [format.decodePositiveFinite_toRat_add_mul trailing row htrailing hrow.ne',
        format.decodePositiveFinite_toRat_add_mul (trailing + 1) row hsucc hrow.ne']
      push_cast
      ring

/--
Increasing a positive finite P3109 code strictly increases its exact numerical value.

The theorem is parameterized by the descriptor and enumerates no named width, precision, or
format profile.

Reference: P3109 Interim Report v4.1 (unapproved draft), §§3.1 and 4.7.2–4.7.6.
-/
theorem decodePositiveFinite_strictMono (format : Format) :
    StrictMono (fun bits => (format.decodePositiveFinite bits).toRat) := by
  apply strictMono_nat_of_lt_succ
  intro bits
  rw [format.decodePositiveFinite_succ_toRat]
  exact lt_add_of_pos_right _ (zpow_pos (by norm_num) _)

end Format
end FloatLib.Floats.Formats.P3109
