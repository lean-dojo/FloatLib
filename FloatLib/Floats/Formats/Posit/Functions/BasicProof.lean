/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.Posit.Functions.Basic
public import FloatLib.Floats.Formats.Posit.Cast.Widening

/-!
# Exact absolute value and sign

Posit Standard (2022), §5.2: signed-word absolute value and sign have their exact
rational meanings at every standard width. The argument shares signed-magnitude
decoding with integer rounding and obtains the exact unit from widening.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

variable {format : Format}

/-- Comparing a whole posit word below zero reads precisely its sign bit, including NaR. -/
theorem compareLess_zero (value : Model format) :
    compareLess value (zero format) = value.signBit := by
  exact BitVec.slt_zero_eq_msb

/-- The standard absolute value is the positive magnitude word, also at zero and NaR. -/
theorem abs_eq_magnitude (value : Model format) :
    abs value = ofNatBits value.magnitudeBits := by
  rw [abs, compareLess_zero]
  have h := ofNatBits_magnitudeBits value
  cases hs : value.signBit
  · simpa only [hs, Bool.false_eq_true, ite_false] using h.symm
  · simp only [hs, ite_true] at h ⊢
    exact (congrArg Model.negate h.symm).trans (Model.neg_neg _)

/-- Exact rational semantics of absolute value, with unavailable values propagated as NaR. -/
@[simp] theorem toRat?_abs (value : Model format) :
    (abs value).toRat? = value.toRat?.map (fun q => |q|) := by
  by_cases hn : value = nar format
  · subst value
    simp
  have hc := magnitudeBits_lt_signMask_of_ne_nar value hn
  have hq := nonnegativeRatAt_nonneg format hc
  rw [abs_eq_magnitude, toRat?_eq_signed_magnitude value hn]
  have hd := toRat?_signed_code format value.magnitudeBits hc false
  simp only [Bool.false_eq_true, ite_false] at hd
  rw [hd]
  cases value.signBit <;> simp [abs_of_nonneg hq]

/-- For a finite decoded value, comparison below zero agrees with rational negativity. -/
theorem compareLess_zero_iff {value : Model format} {q : ℚ}
    (hq : value.toRat? = some q) :
    compareLess value (zero format) = true ↔ q < 0 := by
  have hn : value ≠ nar format := by
    intro h
    simp [h] at hq
  by_cases hz : value = zero format
  · subst value
    simp at hq
    simp [← hq]
  have hc := magnitudeBits_lt_signMask_of_ne_nar value hn
  have hp := nonnegativeRatAt_pos format
    (Nat.pos_of_ne_zero (magnitudeBits_ne_zero_of_ne_zero value hz)) hc
  rw [toRat?_eq_signed_magnitude value hn, Option.some.injEq] at hq
  rw [compareLess_zero, ← hq]
  cases value.signBit <;> simp [hp, hp.not_gt]

/-- The exact rational decoder identifies zero uniquely. -/
theorem toRat?_eq_zero_iff (value : Model format) :
    value.toRat? = some 0 ↔ value = zero format := by
  constructor
  · intro h
    simpa using (roundRat_toRat? value 0 h).symm
  · rintro rfl
    simp

/-- For a finite decoded value, comparison above zero agrees with rational positivity. -/
theorem zero_compareLess_iff {value : Model format} {q : ℚ}
    (hq : value.toRat? = some q) :
    compareLess (zero format) value = true ↔ 0 < q := by
  have hn := compareLess_zero_iff hq
  have hz : value = zero format ↔ q = 0 := by
    rw [← toRat?_eq_zero_iff value, hq, Option.some.injEq]
  simp only [compareLess_eq_true_iff] at hn ⊢
  constructor
  · intro h
    have hnonneg : ¬q < 0 := fun hneg => (not_lt_of_gt h) (hn.mpr hneg)
    have hnonzero : q ≠ 0 := fun hzero => (ne_of_gt h) (hz.mpr hzero)
    exact lt_of_le_of_ne (le_of_not_gt hnonneg) (Ne.symm hnonzero)
  · intro h
    apply lt_of_le_of_ne
    · exact le_of_not_gt (fun hneg => (not_lt_of_gt h) (hn.mp hneg))
    · exact fun hzero => (ne_of_gt h) (hz.mp hzero.symm)

/-- Rounding the unit produces an exact unit at every standard precision. -/
@[simp] theorem toRat?_roundRat_one (format : Format) :
    (roundRat format 1).toRat? = some 1 := by
  have h := toRat?_signed_code format format.oneCodeNat
    format.oneCodeNat_lt_signMaskNat false
  simp only [Bool.false_eq_true, ite_false, nonnegativeRatAt_oneCodeNat] at h
  rw [roundRat_toRat? _ 1 h]
  exact h

/-- Rounding minus one produces exact minus one at every standard precision. -/
@[simp] theorem toRat?_roundRat_neg_one (format : Format) :
    (roundRat format (-1)).toRat? = some (-1) := by
  have h := toRat?_signed_code format format.oneCodeNat
    format.oneCodeNat_lt_signMaskNat true
  simp only [ite_true, nonnegativeRatAt_oneCodeNat] at h
  rw [roundRat_toRat? _ (-1) h]
  exact h

/-- Posit Standard §5.2 sign has exact rational values −1, 0 and 1 and propagates NaR. -/
@[simp] theorem toRat?_sign (value : Model format) :
    (sign value).toRat? =
      value.toRat?.map (fun q => if q < 0 then -1 else if q = 0 then 0 else 1) := by
  cases hq : value.toRat? with
  | none =>
      have hn : value = nar format := by
        simpa using (toRat?_eq_none_iff value).mp hq
      subst value
      simp
  | some q =>
      have hn : value.isNaR = false := by
        apply Bool.eq_false_iff.mpr
        intro h
        have := (toRat?_eq_none_iff value).mpr h
        simp [hq] at this
      have hl := compareLess_zero_iff hq
      have hg := zero_compareLess_iff hq
      simp only [sign, hn, Bool.false_eq_true, ite_false, Option.map_some]
      by_cases hpos : 0 < q
      · simp [hg.mpr hpos, hpos.not_gt, ne_of_gt hpos]
      · by_cases hneg : q < 0
        · simp [show compareLess (zero format) value = false from
            Bool.eq_false_iff.mpr (fun h => hpos (hg.mp h)), hl.mpr hneg, hneg]
        · have hz : q = 0 := le_antisymm (le_of_not_gt hpos) (le_of_not_gt hneg)
          have hv := (toRat?_eq_zero_iff value).mp (by simpa [hz] using hq)
          subst value
          simp [hz]

end FloatLib.Floats.Formats.Posit.Model
