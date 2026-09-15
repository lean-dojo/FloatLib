/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Remainder.Proof
import Mathlib.Tactic.Linarith

/-!
# Midpoint parity of the delivered remainder

The exact-value identity and half-divisor bound establish the nearest integer
quotient. If the returned remainder has half the divisor's magnitude, the quotient
in the exact-value identity is even.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange
namespace Arithmetic

/-- The delivered magnitude is the unrounded integer residual on the common grid. -/
theorem remainder_magnitude (f : Format) (sx sy : Bool) (cx cy : Nat) (qx qy : Int)
    (hc : cy ≠ 0) (v : ℚ)
    (hv : (remainder f (.finite sx cx qx) (.finite sy cy qy)).value.toRat? = some v) :
    |v| = (remainderCoefficient (cx * 10 ^ (qx - min qx qy).toNat)
      (cy * 10 ^ (qy - min qx qy).toNat) : ℚ) * (10 : ℚ) ^ min qx qy := by
  simp only [remainder, if_neg hc, remainderFinite, Datum.toRat?_eq, Option.some.injEq] at hv
  rw [← hv]
  simp only [abs_mul]
  have hs : |(if (if remainderRoundUp (cx * 10 ^ (qx - min qx qy).toNat)
        (cy * 10 ^ (qy - min qx qy).toNat) then !sx else sx) then (-1 : ℚ) else 1)| = 1 := by
    cases (if remainderRoundUp (cx * 10 ^ (qx - min qx qy).toNat)
      (cy * 10 ^ (qy - min qx qy).toNat) then !sx else sx) <;> norm_num
  rw [hs, one_mul, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_pos (zpow_pos (by norm_num) _)]

/-- If the delivered remainder has exactly half the divisor's magnitude, its quotient is even. -/
theorem remainder_even_at_midpoint (f : Format) (sx sy : Bool) (cx cy : Nat) (qx qy : Int)
    (hc : cy ≠ 0) (v : ℚ)
    (hv : (remainder f (.finite sx cx qx) (.finite sy cy qy)).value.toRat? = some v)
    (htie : 2 * |v| = (cy : ℚ) * (10 : ℚ) ^ qy) :
    remainderInteger sx sy cx cy qx qy % 2 = 0 := by
  let q := min qx qy
  let a := cx * 10 ^ (qx - q).toNat
  let b := cy * 10 ^ (qy - q).toNat
  have hb : b ≠ 0 := Nat.mul_ne_zero hc (pow_ne_zero _ (by decide))
  have hm := remainder_magnitude f sx sy cx cy qx qy hc v hv
  have hy := remainder_align_value cy qy q (min_le_right ..)
  have hp : 0 < (10 : ℚ) ^ q := zpow_pos (by norm_num) _
  have hm' : |v| = (remainderCoefficient a b : ℚ) * (10 : ℚ) ^ q := hm
  have hy' : (b : ℚ) * (10 : ℚ) ^ q = (cy : ℚ) * (10 : ℚ) ^ qy := hy
  have he : (2 : ℚ) * (remainderCoefficient a b : ℚ) = (b : ℚ) := by
    rw [hm', ← hy'] at htie
    nlinarith [htie]
  have he' : 2 * remainderCoefficient a b = b := by exact_mod_cast he
  have hparity := remainderQuotient_even_at_tie a b hb he'
  change (if sx ^^ sy then -(remainderQuotient a b : Int)
    else (remainderQuotient a b : Int)) % 2 = 0
  split <;> omega

end Arithmetic
end FloatLib.Floats.Formats.DecimalInterchange
