/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Flocq.Theory.Analysis.Ulp

/-!
# Successor and Predecessor

The neighboring values follow Flocq's `Core/Ulp.v`.  At a positive radix boundary, the spacing
below the value can differ from the spacing above it, so `predPos` uses the preceding
magnitude's exponent in that case.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

variable {β : Numerics.Radix} {fexp : ℤ → ℤ} [ValidExp fexp]

/-- Previous-value formula for a nonnegative input. -/
noncomputable def predPos (x : ℝ) : ℝ :=
  if x = bpow β (magnitude β x - 1) then
    x - bpow β (fexp (magnitude β x - 1))
  else
    x - ulp β fexp x

/-- Successor in the generic format, defined by positive spacing and sign symmetry. -/
noncomputable def succ (x : ℝ) : ℝ :=
  if 0 ≤ x then x + ulp β fexp x else -predPos (β := β) (fexp := fexp) (-x)

/-- Predecessor, defined as the negated successor of the negated input. -/
noncomputable def pred (x : ℝ) : ℝ :=
  -succ (β := β) (fexp := fexp) (-x)

/-- On nonnegative inputs, successor adds one ULP. -/
theorem succ_eq_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    succ (β := β) (fexp := fexp) x = x + ulp β fexp x := by
  simp [succ, hx]

/-- Successor and predecessor are exchanged by negation. -/
@[simp] theorem succ_neg (x : ℝ) :
    succ (β := β) (fexp := fexp) (-x) = -pred (β := β) (fexp := fexp) x := by
  simp [pred]

/-- Predecessor and successor are exchanged by negation. -/
@[simp] theorem pred_neg (x : ℝ) :
    pred (β := β) (fexp := fexp) (-x) = -succ (β := β) (fexp := fexp) x := by
  simp [pred]

/-- The successor of zero is the format's zero ULP. -/
theorem succ_zero :
    succ (β := β) (fexp := fexp) 0 = ulp β fexp 0 := by
  simp [succ]

/-- The predecessor of zero is the negated zero ULP. -/
theorem pred_zero :
    pred (β := β) (fexp := fexp) 0 = -ulp β fexp 0 := by
  rw [pred, neg_zero, succ_zero]

/-- On nonnegative inputs, the symmetric predecessor agrees with `predPos`. -/
theorem pred_eq_pos {x : ℝ} (hx : 0 ≤ x) :
    pred (β := β) (fexp := fexp) x = predPos (β := β) (fexp := fexp) x := by
  by_cases hx0 : x = 0
  · subst x
    rw [pred_zero]
    have hb : (0 : ℝ) ≠ bpow β (-1) := (bpow.ne_zero β (-1)).symm
    simp [predPos, magnitude, hb]
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have hnx : ¬0 ≤ -x := not_le.mpr (neg_neg_of_pos hxpos)
    simp [pred, succ, hnx]

/-- The predecessor of a radix power uses the spacing from the bin immediately below it. -/
theorem pred_bpow (e : ℤ) :
    pred (β := β) (fexp := fexp) (bpow β e) =
      bpow β e - bpow β (fexp e) := by
  rw [pred_eq_pos (bpow.nonneg β e)]
  simp [predPos]

/-- The positive predecessor formula never exceeds its input. -/
theorem predPos_le (x : ℝ) : predPos (β := β) (fexp := fexp) x ≤ x := by
  unfold predPos
  split
  · exact sub_le_self x (bpow.nonneg β _)
  · exact sub_le_self x (ulp.nonneg β fexp x)

/-- Away from zero, the positive predecessor formula is strictly smaller than its input. -/
theorem predPos_lt {x : ℝ} (hx : x ≠ 0) :
    predPos (β := β) (fexp := fexp) x < x := by
  unfold predPos
  split
  · exact sub_lt_self x (bpow.pos β _)
  · exact sub_lt_self x (ulp.pos_of_ne_zero β fexp x hx)

/-- Successor never falls below its input. -/
theorem le_succ (x : ℝ) : x ≤ succ (β := β) (fexp := fexp) x := by
  by_cases hx : 0 ≤ x
  · rw [succ_eq_of_nonneg hx]
    exact le_add_of_nonneg_right (ulp.nonneg β fexp x)
  · simp only [succ, hx, if_false]
    simpa only [neg_neg] using
      neg_le_neg (predPos_le (β := β) (fexp := fexp) (-x))

/-- Predecessor never exceeds its input. -/
theorem pred_le (x : ℝ) : pred (β := β) (fexp := fexp) x ≤ x := by
  rw [← neg_le_neg_iff]
  simpa using le_succ (β := β) (fexp := fexp) (-x)

/-- Successor is strictly larger away from zero. -/
theorem lt_succ {x : ℝ} (hx : x ≠ 0) :
    x < succ (β := β) (fexp := fexp) x := by
  by_cases hnonneg : 0 ≤ x
  · rw [succ_eq_of_nonneg hnonneg]
    exact lt_add_of_pos_right x (ulp.pos_of_ne_zero β fexp x hx)
  · have hnegne : -x ≠ 0 := neg_ne_zero.mpr hx
    simp only [succ, hnonneg, if_false]
    simpa only [neg_neg] using
      neg_lt_neg (predPos_lt (β := β) (fexp := fexp) hnegne)

/-- Predecessor is strictly smaller away from zero. -/
theorem pred_lt {x : ℝ} (hx : x ≠ 0) :
    pred (β := β) (fexp := fexp) x < x := by
  rw [← neg_lt_neg_iff]
  simpa using lt_succ (β := β) (fexp := fexp) (neg_ne_zero.mpr hx)

/-- A positive representable value's successor does not exceed its magnitude boundary. -/
theorem succ_le_magnitude_bpow_of_pos {x : ℝ} (hx : 0 < x)
    (hfmt : genericFormat β fexp x) :
    succ (β := β) (fexp := fexp) x ≤ bpow β (magnitude β x) := by
  let ex := magnitude β x
  let e := fexp ex
  let s := scaledMantissa β fexp x
  obtain ⟨n, hn⟩ := scaled_mantissa_int_of_generic
    (β := β) (fexp := fexp) x hfmt
  have hx0 : x ≠ 0 := hx.ne'
  have hbpos : 0 < bpow β e := bpow.pos β e
  have hcexp : cexp β fexp x = e := rfl
  have hsdiv : s = x / bpow β e := by
    simpa [s, hcexp] using scaledMantissa_eq_div (β := β) (fexp := fexp) x
  have hlarge : e < ex := by
    simpa [e, ex, cexp] using
      cexp_lt_magnitude_of_pos_generic (β := β) (fexp := fexp) hx hfmt
  have hulp : ulp β fexp x = bpow β e := by
    rw [ulp.of_ne_zero β fexp x hx0]
    rfl
  have hd : 0 ≤ ex - e := sub_nonneg.mpr hlarge.le
  obtain ⟨N, hN⟩ := bpow_eq_natCast_of_nonneg β (ex - e) hd
  have hsUpper : s < bpow β (ex - e) := by
    rw [hsdiv]
    calc
      x / bpow β e < bpow β ex / bpow β e :=
        (div_lt_div_iff_of_pos_right hbpos).2
          (by simpa [ex, abs_of_pos hx] using (magnitude_spec β x hx0).2)
      _ = bpow β (ex - e) := (bpow.sub_exp β ex e).symm
  have hnN : n < (N : ℤ) := by
    exact_mod_cast (show (n : ℝ) < N by simpa [s, hn, hN] using hsUpper)
  have hnSuccR : ((n + 1 : ℤ) : ℝ) ≤ N := by
    exact_mod_cast (Int.add_one_le_iff.mpr hnN)
  rw [succ_eq_of_nonneg hx.le, hulp]
  have hrepr := scaled_mantissa_mul_bpow (β := β) (fexp := fexp) x
  rw [hn, hcexp] at hrepr
  calc
    x + bpow β e = (n : ℝ) * bpow β e + bpow β e := by
      rw [hrepr]
    _ =
        ((n + 1 : ℤ) : ℝ) * bpow β e := by push_cast; ring
    _ ≤ (N : ℝ) * bpow β e :=
      mul_le_mul_of_nonneg_right hnSuccR hbpos.le
    _ = bpow β (ex - e) * bpow β e := by rw [hN]
    _ = bpow β ex := by
      rw [← bpow.add_exp, sub_add_cancel]
    _ = bpow β (magnitude β x) := rfl

/-- The successor of a positive representable value is representable. -/
theorem generic_format_succ_of_pos {x : ℝ} (hx : 0 < x)
    (hfmt : genericFormat β fexp x) :
    genericFormat β fexp (succ (β := β) (fexp := fexp) x) := by
  let ex := magnitude β x
  let e := fexp ex
  obtain ⟨n, hn⟩ := scaled_mantissa_int_of_generic
    (β := β) (fexp := fexp) x hfmt
  have hx0 : x ≠ 0 := hx.ne'
  have hcexp : cexp β fexp x = e := rfl
  have hlarge : e < ex := by
    simpa [e, ex, cexp] using
      cexp_lt_magnitude_of_pos_generic (β := β) (fexp := fexp) hx hfmt
  have hulp : ulp β fexp x = bpow β e := by
    rw [ulp.of_ne_zero β fexp x hx0]
    rfl
  let y := succ (β := β) (fexp := fexp) x
  change genericFormat β fexp y
  have hy : y = ((n + 1 : ℤ) : ℝ) * bpow β e := by
    dsimp [y]
    rw [succ_eq_of_nonneg hx.le, hulp]
    have hrepr := scaled_mantissa_mul_bpow (β := β) (fexp := fexp) x
    rw [hn, hcexp] at hrepr
    rw [← hrepr]
    push_cast
    ring
  have hyUpper : y ≤ bpow β ex := succ_le_magnitude_bpow_of_pos hx hfmt
  rcases hyUpper.eq_or_lt with heq | hlt
  · rw [heq]
    exact generic_format_bpow ex
      (((ValidExp.flocq_valid (fexp := fexp) ex).1 hlarge))
  · have hxy : x ≤ y := by
      simpa [y] using le_succ (β := β) (fexp := fexp) x
    have hypos : 0 < y := hx.trans_le hxy
    have hyLower : bpow β (ex - 1) ≤ y := by
      have hxLower : bpow β (ex - 1) ≤ x := by
        simpa [ex, abs_of_pos hx] using (magnitude_spec β x hx0).1
      exact hxLower.trans hxy
    have hmagY : magnitude β y = ex :=
      magnitude_eq_of_bpow_bounds β y ex hypos.ne'
        (by simpa [abs_of_pos hypos] using hyLower)
        (by simpa [abs_of_pos hypos] using hlt)
    apply generic_format_of_toReal_of_cexp_le
      ({ mantissa := n + 1, exponent := e } : FloatRep β) y
    · simpa [toReal] using hy
    · simp [cexp, hmagY, e]

/--
Subtracting one ULP from a positive representable value that is not a radix boundary remains
representable in the same magnitude bin.
-/
theorem generic_format_sub_ulp_of_pos {x : ℝ} (hx : 0 < x)
    (hfmt : genericFormat β fexp x)
    (hboundary : x ≠ bpow β (magnitude β x - 1)) :
    genericFormat β fexp (x - ulp β fexp x) := by
  let ex := magnitude β x
  let e := fexp ex
  let s := scaledMantissa β fexp x
  obtain ⟨n, hn⟩ := scaled_mantissa_int_of_generic
    (β := β) (fexp := fexp) x hfmt
  have hx0 : x ≠ 0 := hx.ne'
  have hbpos : 0 < bpow β e := bpow.pos β e
  have hcexp : cexp β fexp x = e := rfl
  have hsdiv : s = x / bpow β e := by
    simpa [s, hcexp] using scaledMantissa_eq_div (β := β) (fexp := fexp) x
  have hlarge : e < ex := by
    simpa [e, ex, cexp] using
      cexp_lt_magnitude_of_pos_generic (β := β) (fexp := fexp) hx hfmt
  have hulp : ulp β fexp x = bpow β e := by
    rw [ulp.of_ne_zero β fexp x hx0]
    rfl
  have hd : 0 ≤ ex - 1 - e := by linarith
  obtain ⟨N, hN⟩ := bpow_eq_natCast_of_nonneg β (ex - 1 - e) hd
  have hxLower : bpow β (ex - 1) < x := by
    have hle : bpow β (ex - 1) ≤ x := by
      simpa [ex, abs_of_pos hx] using (magnitude_spec β x hx0).1
    exact lt_of_le_of_ne hle (Ne.symm (by simpa [ex] using hboundary))
  have hsLower : bpow β (ex - 1 - e) < s := by
    rw [hsdiv]
    calc
      bpow β (ex - 1 - e) =
          bpow β (ex - 1) / bpow β e := bpow.sub_exp β _ _
      _ < x / bpow β e := (div_lt_div_iff_of_pos_right hbpos).2 hxLower
  have hNn : (N : ℤ) < n := by
    exact_mod_cast (show (N : ℝ) < n by simpa [s, hn, hN] using hsLower)
  have hNpred : (N : ℤ) ≤ n - 1 := by linarith
  let y := x - ulp β fexp x
  change genericFormat β fexp y
  have hy : y = ((n - 1 : ℤ) : ℝ) * bpow β e := by
    dsimp [y]
    rw [hulp]
    have hrepr := scaled_mantissa_mul_bpow (β := β) (fexp := fexp) x
    rw [hn, hcexp] at hrepr
    rw [← hrepr]
    push_cast
    ring
  have hyLower : bpow β (ex - 1) ≤ y := by
    have hNpredR : (N : ℝ) ≤ (n - 1 : ℤ) := by exact_mod_cast hNpred
    calc
      bpow β (ex - 1) =
          bpow β (ex - 1 - e) * bpow β e := by
        rw [← bpow.add_exp]
        congr 1
        linarith
      _ = (N : ℝ) * bpow β e := by rw [hN]
      _ ≤ ((n - 1 : ℤ) : ℝ) * bpow β e :=
        mul_le_mul_of_nonneg_right hNpredR hbpos.le
      _ = y := hy.symm
  have hyUpper : y < bpow β ex := by
    have hyltx : y < x := by
      dsimp [y]
      exact sub_lt_self x (ulp.pos_of_ne_zero β fexp x hx0)
    exact hyltx.trans (by simpa [ex, abs_of_pos hx] using (magnitude_spec β x hx0).2)
  have hypos : 0 < y := (bpow.pos β (ex - 1)).trans_le hyLower
  have hmagY : magnitude β y = ex :=
    magnitude_eq_of_bpow_bounds β y ex hypos.ne'
      (by simpa [abs_of_pos hypos] using hyLower)
      (by simpa [abs_of_pos hypos] using hyUpper)
  apply generic_format_of_toReal_of_cexp_le
    ({ mantissa := n - 1, exponent := e } : FloatRep β) y
  · simpa [toReal] using hy
  · simp [cexp, hmagY, e]

/-- Subtracting the preceding-bin spacing from a representable radix power is representable. -/
theorem generic_format_bpow_sub_prev_spacing (k : ℤ)
    (hfmt : genericFormat β fexp (bpow β k)) :
    genericFormat β fexp (bpow β k - bpow β (fexp k)) := by
  let ef := fexp k
  have hef : ef ≤ k := by
    simpa [ef] using fexp_le_of_generic_bpow (β := β) (fexp := fexp) k hfmt
  rcases hef.eq_or_lt with heq | hlt
  · have hy0 : bpow β k - bpow β ef = 0 := by rw [heq]; ring
    rw [hy0]
    exact generic_format_zero
  · let d := k - ef
    have hd1 : 1 ≤ d := by simp [d]; linarith
    have hd0 : 0 ≤ d := le_trans (by norm_num) hd1
    have hdsub : 0 ≤ d - 1 := by linarith
    have hpowOne : (1 : ℝ) ≤ bpow β (d - 1) := by
      change (1 : ℝ) ≤ β.toReal ^ (d - 1)
      exact one_le_zpow₀ (le_of_lt (Numerics.Radix.gt_one β)) hdsub
    have hbaseTwo : (2 : ℝ) ≤ β.toReal := by
      change (2 : ℝ) ≤ (β.base : ℝ)
      exact_mod_cast β.base_valid
    have hstep : bpow β d = β.toReal * bpow β (d - 1) := by
      calc
        bpow β d = bpow β (1 + (d - 1)) := by congr 1; linarith
        _ = bpow β 1 * bpow β (d - 1) := bpow.add_exp β _ _
        _ = β.toReal * bpow β (d - 1) := by simp [bpow]
    have hdouble : 2 * bpow β (d - 1) ≤
        β.toReal * bpow β (d - 1) :=
      mul_le_mul_of_nonneg_right hbaseTwo (bpow.nonneg β _)
    have hgap : bpow β (d - 1) ≤ bpow β d - 1 := by
      rw [hstep]
      linarith
    let y := bpow β k - bpow β ef
    change genericFormat β fexp y
    have hypos : 0 < y := by
      dsimp [y]
      exact sub_pos.mpr ((bpow_lt_bpow_iff β ef k).2 hlt)
    have hyUpper : y < bpow β k := by
      dsimp [y]
      exact sub_lt_self _ (bpow.pos β ef)
    have hyLower : bpow β (k - 1) ≤ y := by
      have hb := bpow.nonneg β ef
      calc
        bpow β (k - 1) =
            bpow β (d - 1) * bpow β ef := by
          rw [← bpow.add_exp]
          congr 1
          dsimp [d]
          ring
        _ ≤ (bpow β d - 1) * bpow β ef :=
          mul_le_mul_of_nonneg_right hgap hb
        _ = y := by
          dsimp [y]
          rw [sub_mul, one_mul, ← bpow.add_exp]
          congr 1
          simp [d]
    have hmagY : magnitude β y = k :=
      magnitude_eq_of_bpow_bounds β y k hypos.ne'
        (by simpa [abs_of_pos hypos] using hyLower)
        (by simpa [abs_of_pos hypos] using hyUpper)
    obtain ⟨N, hN⟩ := bpow_eq_natCast_of_nonneg β d hd0
    apply generic_format_of_toReal_of_cexp_le
      ({ mantissa := Int.ofNat N - 1, exponent := ef } : FloatRep β) y
    · dsimp [y]
      simp only [toReal]
      calc
        bpow β k - bpow β ef =
            bpow β d * bpow β ef - 1 * bpow β ef := by
          rw [← bpow.add_exp]
          congr 2
          · dsimp [d]
            ring
          · ring
        _ = (bpow β d - 1) * bpow β ef := by ring
        _ = ((N : ℝ) - 1) * bpow β ef := by rw [hN]
        _ = ((Int.ofNat N - 1 : ℤ) : ℝ) * bpow β ef := by norm_num
    · simp [cexp, hmagY, ef]

/-- The predecessor formula for a positive representable input yields a representable value. -/
theorem generic_format_predPos_of_pos {x : ℝ} (hx : 0 < x)
    (hfmt : genericFormat β fexp x) :
    genericFormat β fexp (predPos (β := β) (fexp := fexp) x) := by
  unfold predPos
  split_ifs with hboundary
  · let k := magnitude β x - 1
    have hpowFmt : genericFormat β fexp (bpow β k) := by
      rw [← hboundary]
      exact hfmt
    rw [hboundary]
    simpa [k] using generic_format_bpow_sub_prev_spacing
      (β := β) (fexp := fexp) k hpowFmt
  · exact generic_format_sub_ulp_of_pos hx hfmt hboundary

/-- The successor of every representable value is representable. -/
theorem generic_format_succ {x : ℝ} (hfmt : genericFormat β fexp x) :
    genericFormat β fexp (succ (β := β) (fexp := fexp) x) := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hnegpos : 0 < -x := neg_pos.mpr hx
    have hnegfmt : genericFormat β fexp (-x) := generic_format_neg x hfmt
    have hpred := generic_format_predPos_of_pos
      (β := β) (fexp := fexp) hnegpos hnegfmt
    have hsucc : succ (β := β) (fexp := fexp) x =
        -predPos (β := β) (fexp := fexp) (-x) := by
      simp [succ, not_le.mpr hx]
    rw [hsucc]
    exact generic_format_neg _ hpred
  · subst x
    rw [succ_zero]
    exact generic_format_ulp_zero
  · exact generic_format_succ_of_pos hx hfmt

/-- The predecessor of every representable value is representable. -/
theorem generic_format_pred {x : ℝ} (hfmt : genericFormat β fexp x) :
    genericFormat β fexp (pred (β := β) (fexp := fexp) x) := by
  rw [pred]
  apply generic_format_neg
  exact generic_format_succ (generic_format_neg x hfmt)

/-- No representable value lies strictly between a positive grid point and its successor. -/
theorem succ_le_of_lt_pos {x y : ℝ} (hx : 0 < x)
    (hxfmt : genericFormat β fexp x) (hyfmt : genericFormat β fexp y)
    (hxy : x < y) : succ (β := β) (fexp := fexp) x ≤ y := by
  have hy : 0 < y := hx.trans hxy
  let ex := magnitude β x
  let ey := magnitude β y
  have hmag : ex ≤ ey := by
    have hxLower := (magnitude_spec β x hx.ne').1
    have hyUpper := (magnitude_spec β y hy.ne').2
    have hpowers : bpow β (ex - 1) < bpow β ey := by
      exact hxLower.trans (by simpa [abs_of_pos hx, abs_of_pos hy] using hxy.le) |>.trans_lt hyUpper
    have : ex - 1 < ey := (bpow_lt_bpow_iff β _ _).mp hpowers
    linarith
  rcases hmag.eq_or_lt with heq | hlt
  · let e := fexp ex
    obtain ⟨nx, hnx⟩ := scaled_mantissa_int_of_generic
      (β := β) (fexp := fexp) x hxfmt
    obtain ⟨ny, hny⟩ := scaled_mantissa_int_of_generic
      (β := β) (fexp := fexp) y hyfmt
    have hcexpX : cexp β fexp x = e := by simp [cexp, ex, e]
    have hcexpY : cexp β fexp y = e := by simp [cexp, ey, ex, heq, e]
    have hmant : nx < ny := by
      have hbpos := bpow.pos β e
      have hsxy : scaledMantissa β fexp x < scaledMantissa β fexp y := by
        rw [scaledMantissa_eq_div, scaledMantissa_eq_div, hcexpX, hcexpY]
        exact (div_lt_div_iff_of_pos_right hbpos).2 hxy
      exact_mod_cast (show (nx : ℝ) < ny by simpa [hnx, hny] using hsxy)
    have hsuccMant : nx + 1 ≤ ny := Int.add_one_le_iff.mpr hmant
    rw [succ_eq_of_nonneg hx.le,
      ulp.of_ne_zero β fexp x hx.ne', hcexpX]
    have hxrepr := scaled_mantissa_mul_bpow (β := β) (fexp := fexp) x
    have hyrepr := scaled_mantissa_mul_bpow (β := β) (fexp := fexp) y
    rw [hnx, hcexpX] at hxrepr
    rw [hny, hcexpY] at hyrepr
    rw [← hxrepr, ← hyrepr]
    have hsuccMantR : ((nx + 1 : ℤ) : ℝ) ≤ ny := by exact_mod_cast hsuccMant
    calc
      (nx : ℝ) * bpow β e + bpow β e =
          ((nx + 1 : ℤ) : ℝ) * bpow β e := by push_cast; ring
      _ ≤ (ny : ℝ) * bpow β e :=
        mul_le_mul_of_nonneg_right hsuccMantR (bpow.nonneg β e)
  · have hsuccBound := succ_le_magnitude_bpow_of_pos
      (β := β) (fexp := fexp) hx hxfmt
    have hboundary : bpow β ex ≤ bpow β (ey - 1) :=
      (bpow_le_bpow_iff β _ _).2 (by linarith)
    have hyLower : bpow β (ey - 1) ≤ y := by
      simpa [ey, abs_of_pos hy] using (magnitude_spec β y hy.ne').1
    exact hsuccBound.trans (hboundary.trans hyLower)

end FloatLib.Floats.Formats.Flocq
