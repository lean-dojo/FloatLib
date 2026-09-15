/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Proof
public import FloatLib.Numerics.Exact.Dyadic.Order
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Order of positive finite IEEE P3109 codes

Positive finite codes are ordered by their unsigned natural-number representation. This module
proves that the exact decoder preserves that order for every valid descriptor, including the
subnormal-to-normal boundary and the `P = 1` case.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109
namespace Format

/-- Adjacent positive finite codes decode to strictly increasing values. -/
private theorem decodePositiveFinite_succ_lt
    (format : Format) (bits : Nat) :
    (format.decodePositiveFinite bits).toRat <
      (format.decodePositiveFinite (bits + 1)).toRat := by
  have hunit : 0 < 2 ^ format.trailingBits := Nat.two_pow_pos _
  have hquantum : (0 : Rat) < 2 ^ format.minimumQuantumExponent :=
    zpow_pos (by norm_num) _
  obtain ⟨row, trailing, htrailing, rfl⟩ :
      ∃ row trailing, trailing < 2 ^ format.trailingBits ∧
        bits = trailing + row * 2 ^ format.trailingBits :=
    ⟨bits / 2 ^ format.trailingBits, bits % 2 ^ format.trailingBits, Nat.mod_lt _ hunit,
      by rw [Nat.mul_comm]; exact (Nat.mod_add_div bits _).symm⟩
  by_cases hcarry : trailing + 1 = 2 ^ format.trailingBits
  · rw [show trailing + row * 2 ^ format.trailingBits + 1 =
        0 + (row + 1) * 2 ^ format.trailingBits by
      rw [Nat.add_mul, Nat.one_mul]; omega,
      format.decodePositiveFinite_toRat_add_mul 0 (row + 1) hunit (Nat.succ_ne_zero row)]
    rcases Nat.eq_zero_or_pos row with rfl | hrow
    · rw [Nat.zero_mul, Nat.add_zero, format.decodePositiveFinite_toRat_of_lt trailing htrailing,
        show (((0 + 1 : Nat) : Int) - format.exponentBias + 1 - format.precision) =
          format.minimumQuantumExponent by
        unfold minimumQuantumExponent
        simp only [Int.ofNat_eq_natCast]
        push_cast
        ring]
      exact mul_lt_mul_of_pos_right
        (by exact_mod_cast (by omega : trailing < 2 ^ format.trailingBits + 0)) hquantum
    · rw [format.decodePositiveFinite_toRat_add_mul trailing row htrailing hrow.ne',
        show (((row + 1 : Nat) : Int) - format.exponentBias + 1 - format.precision) =
          ((row : Nat) : Int) - format.exponentBias + 1 - format.precision + 1 by
        push_cast
        ring,
        zpow_add_one₀ (by norm_num : (2 : Rat) ≠ 0)]
      have hpow := zpow_pos (by norm_num : (0 : Rat) < 2)
        (((row : Nat) : Int) - format.exponentBias + 1 - format.precision)
      have hcoefficient :
          ((2 ^ format.trailingBits + trailing : Nat) : Rat) <
            ((2 ^ format.trailingBits + 0 : Nat) : Rat) * 2 := by
        exact_mod_cast
          (by omega : 2 ^ format.trailingBits + trailing < (2 ^ format.trailingBits + 0) * 2)
      calc
        ((2 ^ format.trailingBits + trailing : Nat) : Rat) *
            2 ^ (((row : Nat) : Int) - format.exponentBias + 1 - format.precision) <
          ((2 ^ format.trailingBits + 0 : Nat) : Rat) * 2 *
            2 ^ (((row : Nat) : Int) - format.exponentBias + 1 - format.precision) :=
          mul_lt_mul_of_pos_right hcoefficient hpow
        _ = _ := by ring
  · have hsucc : trailing + 1 < 2 ^ format.trailingBits := by omega
    rw [show trailing + row * 2 ^ format.trailingBits + 1 =
      (trailing + 1) + row * 2 ^ format.trailingBits by omega]
    rcases Nat.eq_zero_or_pos row with rfl | hrow
    · rw [Nat.zero_mul, Nat.add_zero, Nat.add_zero,
        format.decodePositiveFinite_toRat_of_lt trailing htrailing,
        format.decodePositiveFinite_toRat_of_lt (trailing + 1) hsucc]
      exact mul_lt_mul_of_pos_right (by exact_mod_cast Nat.lt_succ_self trailing) hquantum
    · rw [format.decodePositiveFinite_toRat_add_mul trailing row htrailing hrow.ne',
        format.decodePositiveFinite_toRat_add_mul (trailing + 1) row hsucc hrow.ne']
      exact mul_lt_mul_of_pos_right
        (by exact_mod_cast (by omega :
          2 ^ format.trailingBits + trailing < 2 ^ format.trailingBits + (trailing + 1)))
        (zpow_pos (by norm_num) _)

/--
Increasing a positive finite P3109 code strictly increases its exact numerical value.

The theorem is parameterized by the descriptor; no named width, precision, or format profile is
enumerated.
-/
theorem decodePositiveFinite_strictMono (format : Format) :
    StrictMono (fun bits => (format.decodePositiveFinite bits).toRat) :=
  strictMono_nat_of_lt_succ format.decodePositiveFinite_succ_lt

end Format
end FloatLib.Floats.Formats.P3109
