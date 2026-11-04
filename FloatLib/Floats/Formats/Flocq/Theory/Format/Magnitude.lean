/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Flocq.Theory.Core
public import Mathlib.Data.Int.Log
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Radix Magnitude

The magnitude of a nonzero real $x$ is the unique integer $e$ for which
$\beta^{e-1}\le|x|<\beta^e$. In radix 10 the magnitude of `314` is `3`, and in radix 2 the
magnitude of `0.75` is `0`. These bounds are the basic bridge between logarithmic magnitude,
canonical exponents, and generic-format rounding.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

/-- Flocq magnitude is Mathlib's integer logarithm plus one away from zero. -/
theorem magnitude_eq_int_log_add_one (β : Numerics.Radix) (x : ℝ) (hx : x ≠ 0) :
    magnitude β x = Int.log β.base |x| + 1 := by
  simpa [magnitude, hx, Real.logb, Numerics.Radix.toReal] using
    congrArg (fun n : ℤ ↦ n + 1)
      (Real.floor_logb_natCast (b := β.base) (abs_nonneg x))

/-- The logarithmic definition of `magnitude` satisfies the standard Flocq magnitude bounds. -/
theorem magnitude_spec (β : Numerics.Radix) (x : ℝ) (hx : x ≠ 0) :
    bpow β (magnitude β x - 1) ≤ abs x ∧
      abs x < bpow β (magnitude β x) := by
  rw [magnitude_eq_int_log_add_one β x hx]
  have hb : 1 < β.base := β.base_valid
  simpa [bpow, Numerics.Radix.toReal] using
    And.intro (Int.zpow_log_le_self hb (abs_pos.mpr hx))
      (Int.lt_zpow_succ_log_self hb |x|)

/-- Lower magnitude bound for a nonzero real. -/
theorem bpow_magnitude_sub_one_le (β : Numerics.Radix) (x : ℝ) (hx : x ≠ 0) :
    bpow β (magnitude β x - 1) ≤ abs x :=
  (magnitude_spec β x hx).1

/-- Strict upper magnitude bound. It also holds at zero, since radix powers are positive. -/
theorem abs_lt_bpow_magnitude (β : Numerics.Radix) (x : ℝ) :
    abs x < bpow β (magnitude β x) := by
  by_cases hx : x = 0
  · simpa [hx] using bpow.pos β (magnitude β 0)
  · exact (magnitude_spec β x hx).2

/-- The magnitude of $\beta^e$ is $e+1$. -/
@[simp] theorem magnitude_bpow (β : Numerics.Radix) (e : ℤ) :
    magnitude β (bpow β e) = e + 1 := by
  rw [magnitude_eq_int_log_add_one β _ (bpow.ne_zero β e),
    abs_of_pos (bpow.pos β e)]
  simpa only [bpow, Numerics.Radix.toReal] using
    congrArg (fun n : ℤ ↦ n + 1) (Int.log_zpow β.base_valid e)

/-- Radix powers preserve and reflect exponent order. -/
@[simp] theorem bpow_le_bpow_iff (β : Numerics.Radix) (e₁ e₂ : ℤ) :
    bpow β e₁ ≤ bpow β e₂ ↔ e₁ ≤ e₂ := by
  change β.toReal ^ e₁ ≤ β.toReal ^ e₂ ↔ e₁ ≤ e₂
  exact zpow_le_zpow_iff_right₀ (G₀ := ℝ) (a := β.toReal)
    (m := e₁) (n := e₂) (Numerics.Radix.gt_one β)

/-- Radix powers preserve and reflect strict exponent order. -/
@[simp] theorem bpow_lt_bpow_iff (β : Numerics.Radix) (e₁ e₂ : ℤ) :
    bpow β e₁ < bpow β e₂ ↔ e₁ < e₂ := by
  change β.toReal ^ e₁ < β.toReal ^ e₂ ↔ e₁ < e₂
  exact zpow_lt_zpow_iff_right₀ (G₀ := ℝ) (a := β.toReal)
    (m := e₁) (n := e₂) (Numerics.Radix.gt_one β)

/-- Any strict radix-power upper bound is also an upper bound on magnitude. -/
theorem magnitude_le_of_abs_lt_bpow (β : Numerics.Radix) (x : ℝ) (e : ℤ)
    (hx : x ≠ 0) (hupper : abs x < bpow β e) : magnitude β x ≤ e := by
  have hlower := bpow_magnitude_sub_one_le β x hx
  have hexp : magnitude β x - 1 < e :=
    (bpow_lt_bpow_iff β (magnitude β x - 1) e).mp
      (hlower.trans_lt hupper)
  linarith

/-- Radix-power bounds uniquely determine magnitude. -/
theorem magnitude_eq_of_bpow_bounds (β : Numerics.Radix) (x : ℝ) (e : ℤ)
    (hlower : bpow β (e - 1) ≤ abs x)
    (hupper : abs x < bpow β e) : magnitude β x = e := by
  have hx : x ≠ 0 := abs_pos.mp ((bpow.pos β (e - 1)).trans_le hlower)
  have hleft : e - 1 < magnitude β x :=
    (bpow_lt_bpow_iff β (e - 1) (magnitude β x)).mp
      (hlower.trans_lt (magnitude_spec β x hx).2)
  have hright := magnitude_le_of_abs_lt_bpow β x e hx hupper
  omega

/-- Magnitude is monotone with respect to absolute value for nonzero inputs. -/
theorem magnitude_mono_abs (β : Numerics.Radix) {x y : ℝ}
    (hx : x ≠ 0) (hxy : abs x ≤ abs y) :
    magnitude β x ≤ magnitude β y := by
  have hy : y ≠ 0 := abs_pos.mp ((abs_pos.mpr hx).trans_le hxy)
  rw [magnitude_eq_int_log_add_one β x hx, magnitude_eq_int_log_add_one β y hy]
  exact add_le_add (Int.log_mono_right (b := β.base) (abs_pos.mpr hx) hxy) le_rfl

/-- Magnitude is monotone on positive real inputs. -/
theorem magnitude_mono_pos (β : Numerics.Radix) {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) : magnitude β x ≤ magnitude β y :=
  magnitude_mono_abs β hx.ne' (by rwa [abs_of_pos hx, abs_of_pos (hx.trans_le hxy)])

/--
A monotone exponent format preserves absolute-value order at canonical exponents of nonzero inputs.
-/
theorem cexp_mono_abs (β : Numerics.Radix)
    {fexp : ℤ → ℤ} [ValidExp fexp] [MonotoneExp fexp]
    {x y : ℝ} (hx : x ≠ 0) (hxy : abs x ≤ abs y) :
    cexp β fexp x ≤ cexp β fexp y := by
  apply MonotoneExp.monotone
  exact magnitude_mono_abs β hx hxy

/-- The magnitude of a nonzero product is at most the sum of operand magnitudes. -/
theorem magnitude_mul_le_add (β : Numerics.Radix) {x y : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    magnitude β (x * y) ≤ magnitude β x + magnitude β y := by
  apply magnitude_le_of_abs_lt_bpow β (x * y)
  · exact mul_ne_zero hx hy
  · rw [abs_mul, bpow.add_exp]
    exact mul_lt_mul
      (abs_lt_bpow_magnitude β x)
      (abs_lt_bpow_magnitude β y).le
      (abs_pos.mpr hy)
      (bpow.nonneg β _)

/-- Multiplication by a radix power shifts magnitude by its exponent. -/
theorem magnitude_mul_bpow (β : Numerics.Radix) (x : ℝ) (e : ℤ) (hx : x ≠ 0) :
    magnitude β (x * bpow β e) = magnitude β x + e := by
  apply magnitude_eq_of_bpow_bounds β
  · rw [abs_mul, abs_of_pos (bpow.pos β e)]
    calc
      bpow β (magnitude β x + e - 1) =
          bpow β (magnitude β x - 1) * bpow β e := by
        rw [← bpow.add_exp]
        congr 1
        ring
      _ ≤ abs x * bpow β e := mul_le_mul_of_nonneg_right
        (bpow_magnitude_sub_one_le β x hx) (bpow.nonneg β e)
  · rw [abs_mul, abs_of_pos (bpow.pos β e)]
    calc
      abs x * bpow β e <
          bpow β (magnitude β x) * bpow β e :=
        mul_lt_mul_of_pos_right
          (abs_lt_bpow_magnitude β x) (bpow.pos β e)
      _ = bpow β (magnitude β x + e) :=
        (bpow.add_exp β _ _).symm

/-- A radix power with nonnegative exponent is the cast of a natural number. -/
theorem bpow_eq_natCast_of_nonneg (β : Numerics.Radix) (e : ℤ) (he : 0 ≤ e) :
    ∃ n : ℕ, bpow β e = n := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le he
  exact ⟨β.base ^ n, by simp [bpow, Numerics.Radix.toReal]⟩

/-- A radix power is an integer multiple of every radix power with a smaller or equal exponent. -/
theorem exists_bpow_eq_int_mul_bpow (β : Numerics.Radix) {e e' : ℤ} (h : e' ≤ e) :
    ∃ N : ℤ, bpow β e = (N : ℝ) * bpow β e' := by
  obtain ⟨N, hN⟩ := bpow_eq_natCast_of_nonneg β (e - e') (sub_nonneg.mpr h)
  exact ⟨N, by rw [Int.cast_natCast, ← hN, ← bpow.add_exp, sub_add_cancel]⟩

/--
An integer multiple of a radix power is an integer multiple of every radix power with a smaller or
equal exponent: a value on a coarser grid also lies on every finer one.
-/
theorem exists_int_mul_bpow_of_le (β : Numerics.Radix) (n : ℤ) {e e' : ℤ} (h : e' ≤ e) :
    ∃ m : ℤ, (n : ℝ) * bpow β e = (m : ℝ) * bpow β e' := by
  obtain ⟨N, hN⟩ := exists_bpow_eq_int_mul_bpow β h
  exact ⟨n * N, by rw [hN]; push_cast; ring⟩

end FloatLib.Floats.Formats.Flocq
