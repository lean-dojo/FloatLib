/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Remainder.Integer
public import FloatLib.Floats.Formats.DecimalInterchange.Arithmetic.Proof

/-!
# Remainder representability and exact value

On the finer operand grid, either the dividend or the divisor has an original
bounded coefficient. The integer remainder is no larger than either. Hence the
exact result fits at the preferred quantum, including subnormal results.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange
namespace Arithmetic

/-- Moving to a finer grid changes the coefficient by an integral radix power. -/
theorem remainder_align_value (c : Nat) (q r : Int) (hr : r ≤ q) :
    ((c * 10 ^ (q - r).toNat : Nat) : ℚ) * (10 : ℚ) ^ r =
      (c : ℚ) * (10 : ℚ) ^ q := by
  have he : r + ((q - r).toNat : Int) = q := by omega
  conv_rhs => rw [← he, zpow_add₀ (by norm_num), zpow_natCast]
  push_cast
  ring

/-- The exact remainder coefficient fits the original precision at the smaller quantum. -/
theorem remainder_coefficient_lt (f : Format) (cx cy : Nat) (qx qy : Int)
    (hx : cx < f.coefficientBound) (hy : cy < f.coefficientBound) (hc : cy ≠ 0) :
    remainderCoefficient (cx * 10 ^ (qx - min qx qy).toNat)
      (cy * 10 ^ (qy - min qx qy).toNat) < f.coefficientBound := by
  by_cases hq : qx ≤ qy
  · simp only [min_eq_left hq, sub_self, Int.toNat_zero, pow_zero, mul_one]
    exact (remainderCoefficient_le cx _).trans_lt hx
  · have hq' : qy ≤ qx := by omega
    simp only [min_eq_right hq', sub_self, Int.toNat_zero, pow_zero, mul_one]
    have h := remainderCoefficient_twice_le (cx * 10 ^ (qx - qy).toNat) cy hc
    omega

theorem remainderFinite_valid (f : Format) (sx sy : Bool) (cx cy : Nat) (qx qy : Int)
    (hx : (Datum.finite sx cx qx).Valid f) (hy : (Datum.finite sy cy qy).Valid f)
    (hc : cy ≠ 0) : (remainderFinite sx cx qx cy qy).Valid f := by
  have hx' := (Datum.valid_quantum_iff ..).mp hx
  have hy' := (Datum.valid_quantum_iff ..).mp hy
  apply (Datum.valid_quantum_iff ..).mpr
  exact ⟨remainder_coefficient_lt f cx cy qx qy hx'.1 hy'.1 hc,
    le_min hx'.2.1 hy'.2.1, (min_le_left qx qy).trans hx'.2.2⟩

theorem remainder_valid (f : Format) (x y : Datum)
    (hx : x.Valid f) (hy : y.Valid f) : (remainder f x y).value.Valid f := by
  cases x <;> cases y <;> simp only [remainder]
  all_goals first
    | exact nanResult_valid ..
    | exact invalidResult_valid f
    | exact hx
    | (split
       · exact invalidResult_valid f
       · exact remainderFinite_valid f _ _ _ _ _ _ hx hy ‹_›)

/-- Finite, nonzero-divisor remainder raises no default exceptions. -/
theorem remainder_status (f : Format) (sx sy : Bool) (cx cy : Nat) (qx qy : Int)
    (hc : cy ≠ 0) :
    (remainder f (.finite sx cx qx) (.finite sy cy qy)).status = {} := by
  simp [remainder, hc]

/-- Every finite ordinary result uses exactly the preferred quantum. -/
theorem remainder_quantum (f : Format) (sx sy : Bool) (cx cy : Nat) (qx qy : Int)
    (hc : cy ≠ 0) :
    ∃ s c, (remainder f (.finite sx cx qx) (.finite sy cy qy)).value =
      .finite s c (min qx qy) := by
  simp [remainder, hc, remainderFinite]

/-- Signed integer quotient used in the exact remainder identity. -/
def remainderInteger (sx sy : Bool) (cx cy : Nat) (qx qy : Int) : Int :=
  let n := remainderQuotient (cx * 10 ^ (qx - min qx qy).toNat)
    (cy * 10 ^ (qy - min qx qy).toNat)
  if sx ^^ sy then -(n : Int) else (n : Int)

theorem remainder_value (f : Format) (sx sy : Bool) (cx cy : Nat) (qx qy : Int)
    (hc : cy ≠ 0) :
    (remainder f (.finite sx cx qx) (.finite sy cy qy)).value.toRat? =
      some (Datum.finiteValue sx cx qx -
        (remainderInteger sx sy cx cy qx qy : ℚ) * Datum.finiteValue sy cy qy) := by
  let q := min qx qy
  let a := cx * 10 ^ (qx - q).toNat
  let b := cy * 10 ^ (qy - q).toNat
  have hb : b ≠ 0 := Nat.mul_ne_zero hc (pow_ne_zero _ (by decide))
  have hx := remainder_align_value cx qx q (min_le_left ..)
  have hy := remainder_align_value cy qy q (min_le_right ..)
  change (a : ℚ) * (10 : ℚ) ^ q = _ at hx
  change (b : ℚ) * (10 : ℚ) ^ q = _ at hy
  have he := remainderCoefficient_signed a b hb
  simp only [remainder, ite_eq_right hc, remainderFinite, Datum.toRat?_eq]
  apply congrArg some
  change (if (if remainderRoundUp a b then !sx else sx) then (-1 : ℚ) else 1) *
      (remainderCoefficient a b : ℚ) * (10 : ℚ) ^ q = _
  unfold Datum.finiteValue remainderInteger
  change _ = (if sx then (-1 : ℚ) else 1) * (cx : ℚ) * (10 : ℚ) ^ qx -
    ((if sx ^^ sy then -(remainderQuotient a b : Int)
      else (remainderQuotient a b : Int)) : Int) *
      ((if sy then (-1 : ℚ) else 1) * (cy : ℚ) * (10 : ℚ) ^ qy)
  rw [mul_assoc (if sx then (-1 : ℚ) else 1), ← hx,
    mul_assoc (if sy then (-1 : ℚ) else 1), ← hy]
  cases sx <;> cases sy <;>
    simp only [Bool.false_xor, Bool.true_xor, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, Int.cast_natCast, Int.cast_neg]
  all_goals
    split at he <;> rename_i h
    all_goals
      simp only [h, ↓reduceIte, Bool.false_eq_true]
      have he' := congrArg (fun t : ℚ => t * (10 : ℚ) ^ q) he
      nlinarith [he']

/-- The actual delivered remainder is at most half the divisor in magnitude. -/
theorem remainder_error_le_half_divisor (f : Format) (sx sy : Bool)
    (cx cy : Nat) (qx qy : Int) (hc : cy ≠ 0) :
    ∃ v, (remainder f (.finite sx cx qx) (.finite sy cy qy)).value.toRat? = some v ∧
      2 * |v| ≤ (cy : ℚ) * (10 : ℚ) ^ qy := by
  let q := min qx qy
  let a := cx * 10 ^ (qx - q).toNat
  let b := cy * 10 ^ (qy - q).toNat
  have hb : b ≠ 0 := Nat.mul_ne_zero hc (pow_ne_zero _ (by decide))
  have he : 2 * (remainderCoefficient a b : ℚ) ≤ (b : ℚ) := by
    exact_mod_cast remainderCoefficient_twice_le a b hb
  have hp : 0 < (10 : ℚ) ^ q := zpow_pos (by norm_num) _
  have hy := remainder_align_value cy qy q (min_le_right ..)
  have hh := mul_le_mul_of_nonneg_right he hp.le
  simp only [remainder, ite_eq_right hc, remainderFinite, Datum.toRat?_eq]
  refine ⟨_, rfl, ?_⟩
  change 2 * |(if (if remainderRoundUp a b then !sx else sx) then (-1 : ℚ) else 1) *
      (remainderCoefficient a b : ℚ) * (10 : ℚ) ^ q| ≤ _
  simp only [abs_mul]
  have hs : |(if (if remainderRoundUp a b then !sx else sx) then (-1 : ℚ) else 1)| = 1 := by
    cases (if remainderRoundUp a b then !sx else sx) <;> norm_num
  rw [hs, one_mul, abs_of_nonneg (Nat.cast_nonneg (remainderCoefficient a b)),
    abs_of_pos hp, ← hy]
  nlinarith

/-- A zero remainder retains the dividend's sign, for either sign of divisor. -/
theorem remainder_zero_sign (sx : Bool) (cx cy : Nat) (qx qy : Int) (hc : cy ≠ 0)
    (s : Bool) (q : Int) (hz : remainderFinite sx cx qx cy qy = .finite s 0 q) :
    s = sx := by
  let a := cx * 10 ^ (qx - min qx qy).toNat
  let b := cy * 10 ^ (qy - min qx qy).toNat
  have hb : b ≠ 0 := Nat.mul_ne_zero hc (pow_ne_zero _ (by decide))
  have h := Datum.finite.inj hz
  have he : remainderCoefficient a b = 0 := h.2.1
  have hs := remainderRoundUp_eq_false_of_zero a b hb he
  have hsign : (if remainderRoundUp a b then !sx else sx) = s := h.1
  simpa [hs] using hsign.symm

end Arithmetic
end FloatLib.Floats.Formats.DecimalInterchange
