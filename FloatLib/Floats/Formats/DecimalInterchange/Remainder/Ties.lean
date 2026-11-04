/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Remainder.Proof

/-!
# Midpoint parity of the delivered remainder

The exact-value identity and the half-divisor bound make the quotient a nearest integer, and this
file handles the tie. If the returned remainder has half the divisor's magnitude, the quotient in
the exact-value identity is even, as with `7` by `2`, where the remainder `-1` goes with the even
quotient `4`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange
namespace Arithmetic

/-- If a finite delivered remainder has half the divisor's magnitude, its quotient is even.
A zero divisor gives a NaN, so a finite result has a nonzero divisor. -/
theorem remainder_even_at_midpoint (f : Format) (sx sy : Bool) (cx cy : Nat) (qx qy : Int)
    (v : ℚ)
    (hv : (remainder f (.finite sx cx qx) (.finite sy cy qy)).value.toRat? = some v)
    (htie : 2 * |v| = (cy : ℚ) * (10 : ℚ) ^ qy) :
    remainderInteger sx sy cx cy qx qy % 2 = 0 := by
  have hc : cy ≠ 0 := by
    rintro rfl
    simp [remainder, invalidResult, Datum.toRat?_eq] at hv
  let q := min qx qy
  let a := cx * 10 ^ (qx - q).toNat
  let b := cy * 10 ^ (qy - q).toNat
  have hb : b ≠ 0 := Nat.mul_ne_zero hc (pow_ne_zero _ (by decide))
  have hm := remainder_magnitude f sx sy cx cy qx qy v hv
  have hy := finer_grid_value cy qy q (min_le_right ..)
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
