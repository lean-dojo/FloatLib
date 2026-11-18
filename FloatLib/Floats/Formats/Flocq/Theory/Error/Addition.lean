/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Flocq.Theory.Error.Exactness
public import FloatLib.Floats.Formats.Flocq.Theory.Format.Theorems
public import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Order
import Mathlib.Tactic.Abel

/-!
# Exactness of Addition Errors

Add two representable values, round to nearest, and the error is itself representable, as long as
the exponent function is valid and monotone. The proof puts both operands on the smaller canonical
grid, represents the rounded result on that same grid, and uses nearestness to keep the canonical
exponent of the error under control.

Nearestness matters. With directed rounding the statement fails: in radix `2` with three digits of
precision, rounding `1 - 2^(-10)` downward gives `7/8`, and the error `2^(-3) - 2^(-10)` needs
seven digits.

That representable error is the mathematical content of the TwoSum and FastTwoSum error-free
transformations, `x + y = round (x + y) + e` with `e` in the format. We don't formalize the
step-by-step exactness of the floating-point operations that compute `e` in those algorithms.

The source counterpart is Flocq 4.2.2, `src/Prop/Plus_error.v`, theorem `plus_error`,
which states representability of `round (x + y) - (x + y)` under nearest rounding:
<https://flocq.gitlabpages.inria.fr/releases/flocq-4.2.2.tar.gz>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

variable {β : Numerics.Radix} {fexp : ℤ → ℤ}
  [ValidExp fexp] [MonotoneExp fexp]

/-- Addition-error exactness when the first operand has the smaller canonical exponent. -/
private theorem add_round_error_generic_aux {rnd : ℝ → ℤ} [ValidRndToNearest rnd] {x y : ℝ}
    (hxy : cexp β fexp x ≤ cexp β fexp y)
    (hx : GenericRepresentable β fexp x) (hy : GenericRepresentable β fexp y) :
    GenericRepresentable β fexp
      (round (β := β) (fexp := fexp) rnd (x + y) - (x + y)) := by
  let ex := cexp β fexp x
  -- Both operands lie on the grid of the smaller canonical exponent `ex`.
  obtain ⟨mx, hxrepr⟩ := exists_int_mul_bpow_cexp_of_generic hx
  obtain ⟨my, hyrepr⟩ := exists_int_mul_bpow_of_le_cexp hy hxy
  let commonMantissa : ℤ := mx + my
  let common : FloatRep β := { mantissa := commonMantissa, exponent := ex }
  have hsum : x + y = toReal common := by
    rw [hxrepr, hyrepr]
    unfold common commonMantissa toReal
    push_cast
    ring
  obtain ⟨mr, hrounded⟩ :=
    round_toReal_exists_same_exponent
      (β := β) (fexp := fexp) rnd common
  let errorMantissa : ℤ := mr - commonMantissa
  let errorFloat : FloatRep β := { mantissa := errorMantissa, exponent := ex }
  let err := round (β := β) (fexp := fexp) rnd (x + y) - (x + y)
  have herr : err = toReal errorFloat := by
    unfold err errorFloat errorMantissa toReal
    rw [hsum, hrounded]
    unfold common
    simp only [toReal]
    push_cast
    ring
  by_cases herr0 : err = 0
  · change GenericRepresentable β fexp err
    rw [herr0]
    exact genericRepresentable_zero
  have hnear := (round_toNearest_point
    (β := β) (fexp := fexp) rnd (x + y)).2 y hy
  have herrLe : abs err ≤ abs x := by
    simpa [err] using hnear
  have hcexp : cexp β fexp err ≤ ex := by
    exact cexp_mono_abs β herr0 herrLe
  apply genericRepresentable_of_toReal_of_cexp_le errorFloat err herr
  exact hcexp

/--
The addition error of two representable values under any nearest rounding rule is representable.

The rounding rule is implicit because the conclusion determines it, and `nearestEven` is the
usual instance. The statement needs a monotone exponent function and fails for directed rounding.
-/
theorem add_round_error_generic {rnd : ℝ → ℤ} [ValidRndToNearest rnd] {x y : ℝ}
    (hx : GenericRepresentable β fexp x) (hy : GenericRepresentable β fexp y) :
    GenericRepresentable β fexp
      (round (β := β) (fexp := fexp) rnd (x + y) - (x + y)) := by
  rcases le_total (cexp β fexp x) (cexp β fexp y) with hxy | hyx
  · exact add_round_error_generic_aux hxy hx hy
  · simpa [add_comm] using
      (add_round_error_generic_aux (β := β) (fexp := fexp) (rnd := rnd) hyx hy hx)

/--
Error-free transformation of addition: the exact sum of two representable values is the rounded
sum plus a representable error term.

This is the specification met by the TwoSum and FastTwoSum algorithms.  The term `e` is
`x + y - round (x + y)`, and its representability is `add_round_error_generic` up to sign.
-/
theorem add_round_exact_error {rnd : ℝ → ℤ} [ValidRndToNearest rnd] {x y : ℝ}
    (hx : GenericRepresentable β fexp x) (hy : GenericRepresentable β fexp y) :
    ∃ e : ℝ, GenericRepresentable β fexp e ∧
      x + y = round (β := β) (fexp := fexp) rnd (x + y) + e := by
  refine ⟨x + y - round (β := β) (fexp := fexp) rnd (x + y), ?_, by abel⟩
  have herr := add_round_error_generic (β := β) (fexp := fexp) (rnd := rnd) hx hy
  simpa [neg_sub] using genericRepresentable_neg (β := β) (fexp := fexp) _ herr

/-- Every FLT value lies on its minimum-exponent FIX grid. -/
theorem genericRepresentable_flt_to_fix (emin prec : ℤ) (hprec : 0 < prec) {x : ℝ}
    (hx : @GenericRepresentable β (fltExp emin prec) (validExp_flt emin prec hprec) x) :
    GenericRepresentable β (fixExp emin) x := by
  let : ValidExp (fltExp emin prec) := validExp_flt emin prec hprec
  let : ValidExp (fixExp emin) := fixValidExp emin
  obtain ⟨m, hxf⟩ := exists_int_mul_bpow_of_le_cexp hx (e := emin)
    (by simp [cexp, fltExp])
  apply genericRepresentable_of_toReal_of_cexp_le
    ({ mantissa := m, exponent := emin } : FloatRep β) x hxf
  simp [cexp, fixExp]

/-- A bounded FIX value is FLT-representable, including the radix-power boundary. -/
theorem genericRepresentable_fix_to_flt_of_abs_le (emin prec : ℤ) (hprec : 0 < prec)
    {x : ℝ} (hx : GenericRepresentable β (fixExp emin) x)
    (hbound : abs x ≤ bpow β (prec + emin)) :
    @GenericRepresentable β (fltExp emin prec) (validExp_flt emin prec hprec) x := by
  let : ValidExp (fixExp emin) := fixValidExp emin
  let : ValidExp (fltExp emin prec) := validExp_flt emin prec hprec
  by_cases hx0 : x = 0
  · subst x
    exact genericRepresentable_zero
  rcases hbound.eq_or_lt with heq | hlt
  · have habsFmt : GenericRepresentable β (fltExp emin prec) (abs x) := by
      rw [heq]
      apply genericRepresentable_bpow
      unfold fltExp
      rw [max_eq_left (by omega)]
      omega
    exact (genericRepresentable_abs_iff (β := β) (fexp := fltExp emin prec) x).mp habsFmt
  · obtain ⟨f, hxf, hfe⟩ :=
      (genericRepresentable_fix_iff (β := β) emin x).mp hx
    apply genericRepresentable_of_toReal_of_cexp_le f x hxf
    have hmag : magnitude β x ≤ prec + emin :=
      magnitude_le_of_abs_lt_bpow β x (prec + emin) hx0 hlt
    rw [hfe]
    simp only [cexp, fltExp, sup_le_iff, tsub_le_iff_right, Std.le_refl, and_true, ge_iff_le]
    omega

/-- A small enough sum of two FLT values is itself FLT-representable. -/
theorem genericRepresentable_flt_add_small (emin prec : ℤ) (hprec : 0 < prec)
    {x y : ℝ}
    (hx : @GenericRepresentable β (fltExp emin prec) (validExp_flt emin prec hprec) x)
    (hy : @GenericRepresentable β (fltExp emin prec) (validExp_flt emin prec hprec) y)
    (hbound : abs (x + y) ≤ bpow β (prec + emin)) :
    @GenericRepresentable β (fltExp emin prec) (validExp_flt emin prec hprec) (x + y) := by
  exact genericRepresentable_fix_to_flt_of_abs_le (β := β) emin prec hprec
    (genericRepresentable_fix_add emin (genericRepresentable_flt_to_fix emin prec hprec hx)
      (genericRepresentable_flt_to_fix emin prec hprec hy)) hbound

end FloatLib.Floats.Formats.Flocq
