/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Flocq.Theory.Format.Magnitude
public import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Core

/-!
# Generic format properties

Before you pick a concrete FIX, FLX, or FLT family, a Flocq-style generic format already says which
reals are representable, through a radix and a canonical exponent function. This module proves the
closure and representation facts the rounding theory builds on, such as `x` being representable if
and only if `-x` is.

None of it runs. It's the common real-valued specification that binary-interchange and other format
implementations prove their exact integer algorithms against.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

variable {β : Numerics.Radix} {fexp : ℤ → ℤ} [ValidExp fexp]

/-- Magnitude is invariant under negation. -/
@[simp] theorem magnitude_neg (x : ℝ) : magnitude β (-x) = magnitude β x := by
  simp [magnitude]

/-- The canonical exponent is invariant under negation. -/
@[simp] theorem cexp_neg (x : ℝ) : cexp β fexp (-x) = cexp β fexp x := by
  simp [cexp]

/-- Negation negates the canonical scaled mantissa. -/
@[simp] theorem scaledMantissa_neg (x : ℝ) :
    scaledMantissa β fexp (-x) = -scaledMantissa β fexp x := by
  simp [scaledMantissa]

/-- Zero belongs to every valid generic format. -/
@[simp] theorem generic_format_zero : genericFormat β fexp 0 := by
  apply generic_format_of_scaled_mantissa_int (n := 0)
  simp [scaledMantissa]

/-- Generic formats are closed under negation. -/
theorem generic_format_neg (x : ℝ) (hx : genericFormat β fexp x) :
    genericFormat β fexp (-x) := by
  obtain ⟨n, hn⟩ :=
    (generic_format_iff_scaled_mantissa_int (β := β) (fexp := fexp) x).mp hx
  apply generic_format_of_scaled_mantissa_int (n := -n)
  simp [hn]

/-- A value is representable if and only if its negation is representable. -/
@[simp] theorem generic_format_neg_iff (x : ℝ) :
    genericFormat β fexp (-x) ↔ genericFormat β fexp x := by
  constructor
  · intro hx
    simpa using generic_format_neg (β := β) (fexp := fexp) (-x) hx
  · exact generic_format_neg (β := β) (fexp := fexp) x

/-- A value is representable if and only if its absolute value is representable. -/
theorem generic_format_abs_iff (x : ℝ) :
    genericFormat β fexp (abs x) ↔ genericFormat β fexp x := by
  rcases le_total 0 x with hx | hx
  · simp [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, generic_format_neg_iff]

/-- A radix power is representable whenever its canonical exponent is no larger than its exponent. -/
theorem generic_format_bpow (e : ℤ) (h : fexp (e + 1) ≤ e) :
    genericFormat β fexp (bpow β e) := by
  obtain ⟨m, hm⟩ := exists_bpow_eq_int_mul_bpow β h
  apply generic_format_of_scaled_mantissa_int (n := m)
  rw [scaledMantissa_eq_div, div_eq_iff (bpow.ne_zero β _)]
  simpa [cexp] using hm

/--
A mantissa/exponent representation is generic when its stored exponent is at least the canonical
exponent selected for its value.
-/
theorem generic_format_of_toReal_of_cexp_le (f : FloatRep β) (x : ℝ)
    (hxf : x = toReal f) (he : cexp β fexp x ≤ f.exponent) :
    genericFormat β fexp x := by
  obtain ⟨m, hm⟩ := exists_int_mul_bpow_of_le β f.mantissa he
  apply generic_format_of_scaled_mantissa_int (n := m)
  rw [scaledMantissa_eq_div, div_eq_iff (bpow.ne_zero β _)]
  exact hxf.trans hm

/-- A generic-format value is an integer multiple of the radix power at its canonical exponent. -/
theorem exists_int_mul_bpow_cexp_of_generic {x : ℝ} (hx : genericFormat β fexp x) :
    ∃ n : ℤ, x = (n : ℝ) * bpow β (cexp β fexp x) :=
  ⟨_, hx⟩

/--
A generic-format value is an integer multiple of every radix power at or below its canonical
exponent, so values with different canonical exponents can be aligned on the finer grid.
-/
theorem exists_int_mul_bpow_of_le_cexp {x : ℝ} (hx : genericFormat β fexp x) {e : ℤ}
    (he : e ≤ cexp β fexp x) : ∃ m : ℤ, x = (m : ℝ) * bpow β e := by
  obtain ⟨n, hxn⟩ := exists_int_mul_bpow_cexp_of_generic hx
  obtain ⟨m, hm⟩ := exists_int_mul_bpow_of_le β n he
  exact ⟨m, hxn.trans hm⟩

/-- A grid point at exponent `fexp E` in the magnitude bin `[β^(E-1), β^E)` is representable. -/
theorem generic_format_of_mul_bpow_of_mem_bin {y : ℝ} {E : ℤ} (m : ℤ)
    (hy : y = (m : ℝ) * bpow β (fexp E))
    (hlower : bpow β (E - 1) ≤ y) (hupper : y < bpow β E) :
    genericFormat β fexp y := by
  have hypos : 0 < y := (bpow.pos β (E - 1)).trans_le hlower
  have hmag : magnitude β y = E :=
    magnitude_eq_of_bpow_bounds β y E
      (by simpa [abs_of_pos hypos] using hlower)
      (by simpa [abs_of_pos hypos] using hupper)
  apply generic_format_of_toReal_of_cexp_le
    ({ mantissa := m, exponent := fexp E } : FloatRep β) y hy
  simp [cexp, hmag]

/-- A positive representable value uses a canonical exponent strictly below its magnitude. -/
theorem cexp_lt_magnitude_of_pos_generic {x : ℝ} (hx : 0 < x)
    (hfmt : genericFormat β fexp x) :
    cexp β fexp x < magnitude β x := by
  obtain ⟨n, hn⟩ := scaled_mantissa_int_of_generic
    (β := β) (fexp := fexp) x hfmt
  have hbpos := bpow.pos β (cexp β fexp x)
  have hspos : 0 < scaledMantissa β fexp x := by
    rw [scaledMantissa_eq_div]
    positivity
  have hnpos : 0 < n := by
    exact_mod_cast (show (0 : ℝ) < n by simpa [hn] using hspos)
  by_contra hnot
  have hmagle : magnitude β x ≤ cexp β fexp x := le_of_not_gt hnot
  have hxUpper : x < bpow β (magnitude β x) := by
    simpa [abs_of_pos hx] using (magnitude_spec β x hx.ne').2
  have hslt : scaledMantissa β fexp x < 1 := by
    rw [scaledMantissa_eq_div, div_lt_one hbpos]
    exact hxUpper.trans_le ((bpow_le_bpow_iff β _ _).2 hmagle)
  have hnlt : n < 1 := by exact_mod_cast (show (n : ℝ) < 1 by simpa [hn] using hslt)
  exact (not_lt_of_ge (Int.add_one_le_iff.mpr hnpos)) hnlt

/-- Representability of `β^e` forces its canonical exponent to be at most `e`. -/
theorem fexp_succ_le_of_generic_bpow (e : ℤ)
    (hfmt : genericFormat β fexp (bpow β e)) : fexp (e + 1) ≤ e := by
  have h := cexp_lt_magnitude_of_pos_generic
    (β := β) (fexp := fexp) (bpow.pos β e) hfmt
  simp [cexp] at h
  linarith

/-- If `β^e` is representable, the exponent selected for the bin below it is at most `e`. -/
theorem fexp_le_of_generic_bpow (e : ℤ)
    (hfmt : genericFormat β fexp (bpow β e)) : fexp e ≤ e := by
  have hnext := fexp_succ_le_of_generic_bpow (β := β) (fexp := fexp) e hfmt
  by_contra hnot
  have heLt : e < fexp e := lt_of_not_ge hnot
  have heSucc : e + 1 ≤ fexp e := Int.add_one_le_iff.mpr heLt
  have hconst := ((ValidExp.flocq_valid (fexp := fexp) e).2 heLt.le).2 (e + 1) heSucc
  linarith

/--
A value representable with `fexp₁` remains representable with `fexp₂` when the second canonical
exponent is no larger at that value's magnitude.  The condition is local because representability
of `x` only depends on the exponent selected at `magnitude x`.
-/
theorem generic_inclusion_mag {fexp₁ fexp₂ : ℤ → ℤ}
    [ValidExp fexp₁] [ValidExp fexp₂] {x : ℝ}
    (hexp : x ≠ 0 → fexp₂ (magnitude β x) ≤ fexp₁ (magnitude β x))
    (hx : genericFormat β fexp₁ x) : genericFormat β fexp₂ x := by
  by_cases hx0 : x = 0
  · subst x
    exact generic_format_zero
  -- `hx` is the canonical representation of `x` at the exponent selected by `fexp₁`.
  apply generic_format_of_toReal_of_cexp_le _ x hx
  change fexp₂ (magnitude β x) ≤ fexp₁ (magnitude β x)
  exact hexp hx0

/-- Pointwise-smaller exponent selection defines a containing generic format. -/
theorem generic_inclusion {fexp₁ fexp₂ : ℤ → ℤ}
    [ValidExp fexp₁] [ValidExp fexp₂]
    (hexp : ∀ e, fexp₂ e ≤ fexp₁ e) {x : ℝ}
    (hx : genericFormat β fexp₁ x) : genericFormat β fexp₂ x :=
  generic_inclusion_mag (fun _ => hexp _) hx

/-- No generic-format value lies strictly between consecutive points on its canonical grid. -/
theorem generic_format_discrete (x : ℝ) (m : ℤ)
    (hlower : (m : ℝ) * bpow β (cexp β fexp x) < x)
    (hupper : x < ((m + 1 : ℤ) : ℝ) * bpow β (cexp β fexp x)) :
    ¬genericFormat β fexp x := by
  intro hx
  obtain ⟨n, hrepr⟩ := exists_int_mul_bpow_cexp_of_generic hx
  have hb : 0 < bpow β (cexp β fexp x) := bpow.pos β _
  have hlower' : (m : ℝ) * bpow β (cexp β fexp x) <
      (n : ℝ) * bpow β (cexp β fexp x) := hlower.trans_eq hrepr
  have hupper' : (n : ℝ) * bpow β (cexp β fexp x) <
      ((m + 1 : ℤ) : ℝ) * bpow β (cexp β fexp x) := hrepr.symm.trans_lt hupper
  have hmnR : (m : ℝ) < (n : ℝ) := by
    nlinarith [hlower']
  have hnmR : (n : ℝ) < ((m + 1 : ℤ) : ℝ) := by
    nlinarith [hupper']
  have hmn : m < n := by exact_mod_cast hmnR
  have hnm : n < m + 1 := by exact_mod_cast hnmR
  linarith

/-- Every generic-format value has a canonical mantissa/exponent representation. -/
theorem canonical_exists_of_generic {x : ℝ} (hx : genericFormat β fexp x) :
    ∃ f : FloatRep β, x = toReal f ∧ Canonical β fexp f := by
  let f : FloatRep β :=
    { mantissa := ⌊scaledMantissa β fexp x⌋
      exponent := cexp β fexp x }
  refine ⟨f, hx, ?_⟩
  unfold Canonical
  change cexp β fexp x = cexp β fexp (toReal f)
  rw [← hx]

/-- The real value of a canonical representation belongs to its generic format. -/
theorem generic_format_of_canonical (f : FloatRep β)
    (hf : Canonical β fexp f) :
    genericFormat β fexp (toReal f) := by
  apply generic_format_of_toReal_of_cexp_le f (toReal f) rfl
  exact hf.ge

/-- Canonical representations of the same real value are equal. -/
theorem canonical_unique {f g : FloatRep β}
    (hf : Canonical β fexp f) (hg : Canonical β fexp g)
    (hval : toReal f = toReal g) : f = g := by
  have hexp : f.exponent = g.exponent := by
    rw [hf, hg, hval]
  have hmant : f.mantissa = g.mantissa := by
    have hb : 0 < bpow β f.exponent := bpow.pos β _
    have hreal : (f.mantissa : ℝ) * bpow β f.exponent =
        (g.mantissa : ℝ) * bpow β f.exponent := by
      simpa [toReal, hexp] using hval
    have hcast : (f.mantissa : ℝ) = (g.mantissa : ℝ) := by nlinarith
    exact_mod_cast hcast
  cases f
  cases g
  simp_all

end FloatLib.Floats.Formats.Flocq
