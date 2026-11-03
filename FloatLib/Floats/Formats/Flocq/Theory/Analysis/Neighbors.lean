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

/--
The symmetric predecessor agrees with `predPos` on every input. Below zero, the radix-boundary
branch of `predPos` never applies and both subtract one ULP.
-/
theorem pred_eq_pos (x : ℝ) :
    pred (β := β) (fexp := fexp) x = predPos (β := β) (fexp := fexp) x := by
  rcases lt_or_ge x 0 with hneg | hx
  · have hboundary : x ≠ bpow β (magnitude β x - 1) := (hneg.trans (bpow.pos β _)).ne
    rw [pred, succ_eq_of_nonneg (neg_nonneg.mpr hneg.le), ulp_neg, predPos, ite_eq_right hboundary]
    ring
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
  rw [pred_eq_pos]
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
  · simp only [succ, hx, ite_false]
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
    simp only [succ, hnonneg, ite_false]
    simpa only [neg_neg] using
      neg_lt_neg (predPos_lt (β := β) (fexp := fexp) hnegne)

/-- Predecessor is strictly smaller away from zero. -/
theorem pred_lt {x : ℝ} (hx : x ≠ 0) :
    pred (β := β) (fexp := fexp) x < x := by
  rw [← neg_lt_neg_iff]
  simpa using lt_succ (β := β) (fexp := fexp) (neg_ne_zero.mpr hx)

/--
A positive representable value is an integer number of ULPs, and its ULP is the radix power at an
exponent strictly below its magnitude.
-/
private theorem exists_int_mul_ulp_of_pos {x : ℝ} (hx : 0 < x)
    (hfmt : genericFormat β fexp x) :
    ∃ n : ℤ, x = (n : ℝ) * bpow β (fexp (magnitude β x)) ∧
      ulp β fexp x = bpow β (fexp (magnitude β x)) ∧
      fexp (magnitude β x) < magnitude β x := by
  obtain ⟨n, hxn⟩ := exists_int_mul_bpow_cexp_of_generic hfmt
  exact ⟨n, hxn, ulp.of_ne_zero β fexp x hx.ne',
    cexp_lt_magnitude_of_pos_generic hx hfmt⟩

/-- Strictly ordered integer multiples of a positive spacing are at least one spacing apart. -/
private theorem int_mul_add_le_of_lt {p q : ℤ} {u : ℝ} (hu : 0 < u)
    (h : (p : ℝ) * u < (q : ℝ) * u) : (p : ℝ) * u + u ≤ (q : ℝ) * u := by
  have hpq : p < q := by exact_mod_cast lt_of_mul_lt_mul_right h hu.le
  have hle : (p : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr hpq
  nlinarith

/-- A radix power is at least twice the next lower one, since every radix is at least two. -/
private theorem two_mul_bpow_sub_one_le (e : ℤ) : 2 * bpow β (e - 1) ≤ bpow β e := by
  have hbase : (2 : ℝ) ≤ β.toReal := by
    change (2 : ℝ) ≤ (β.base : ℝ)
    exact_mod_cast β.base_valid
  calc
    2 * bpow β (e - 1) ≤ β.toReal * bpow β (e - 1) :=
      mul_le_mul_of_nonneg_right hbase (bpow.nonneg β _)
    _ = bpow β e := by
      rw [show bpow β e = bpow β (1 + (e - 1)) by congr 1; ring, bpow.add_exp]
      simp [bpow]

/-- A positive representable value's successor does not exceed its magnitude boundary. -/
theorem succ_le_magnitude_bpow_of_pos {x : ℝ} (hx : 0 < x)
    (hfmt : genericFormat β fexp x) :
    succ (β := β) (fexp := fexp) x ≤ bpow β (magnitude β x) := by
  let ex := magnitude β x
  let e := fexp ex
  obtain ⟨n, hxn, hulp, hlarge⟩ :
      ∃ n : ℤ, x = (n : ℝ) * bpow β e ∧ ulp β fexp x = bpow β e ∧ e < ex :=
    exists_int_mul_ulp_of_pos hx hfmt
  obtain ⟨N, hN⟩ := exists_bpow_eq_int_mul_bpow β hlarge.le
  have hxUpper : x < bpow β ex := by
    simpa [ex, abs_of_pos hx] using (magnitude_spec β x hx.ne').2
  rw [succ_eq_of_nonneg hx.le, hulp]
  change x + bpow β e ≤ bpow β ex
  rw [hN, hxn]
  apply int_mul_add_le_of_lt (bpow.pos β e)
  rw [← hxn, ← hN]
  exact hxUpper

/-- The successor of a positive representable value is representable. -/
private theorem generic_format_succ_of_pos {x : ℝ} (hx : 0 < x)
    (hfmt : genericFormat β fexp x) :
    genericFormat β fexp (succ (β := β) (fexp := fexp) x) := by
  let ex := magnitude β x
  let e := fexp ex
  obtain ⟨n, hxn, hulp, hlarge⟩ :
      ∃ n : ℤ, x = (n : ℝ) * bpow β e ∧ ulp β fexp x = bpow β e ∧ e < ex :=
    exists_int_mul_ulp_of_pos hx hfmt
  let y := succ (β := β) (fexp := fexp) x
  change genericFormat β fexp y
  have hy : y = ((n + 1 : ℤ) : ℝ) * bpow β e := by
    dsimp [y]
    rw [succ_eq_of_nonneg hx.le, hulp, hxn]
    push_cast
    ring
  have hyUpper : y ≤ bpow β ex := succ_le_magnitude_bpow_of_pos hx hfmt
  rcases hyUpper.eq_or_lt with heq | hlt
  · rw [heq]
    exact generic_format_bpow ex
      (((ValidExp.flocq_valid (fexp := fexp) ex).1 hlarge))
  · have hxy : x ≤ y := by
      simpa [y] using le_succ (β := β) (fexp := fexp) x
    have hyLower : bpow β (ex - 1) ≤ y := by
      have hxLower : bpow β (ex - 1) ≤ x := by
        simpa [ex, abs_of_pos hx] using (magnitude_spec β x hx.ne').1
      exact hxLower.trans hxy
    exact generic_format_of_mul_bpow_of_mem_bin (n + 1) hy hyLower hlt

/--
Subtracting one ULP from a positive representable value that is not a radix boundary remains
representable in the same magnitude bin.
-/
private theorem generic_format_sub_ulp_of_pos {x : ℝ} (hx : 0 < x)
    (hfmt : genericFormat β fexp x)
    (hboundary : x ≠ bpow β (magnitude β x - 1)) :
    genericFormat β fexp (x - ulp β fexp x) := by
  let ex := magnitude β x
  let e := fexp ex
  obtain ⟨n, hxn, hulp, hlarge⟩ :
      ∃ n : ℤ, x = (n : ℝ) * bpow β e ∧ ulp β fexp x = bpow β e ∧ e < ex :=
    exists_int_mul_ulp_of_pos hx hfmt
  have hx0 : x ≠ 0 := hx.ne'
  obtain ⟨N, hN⟩ := exists_bpow_eq_int_mul_bpow β (show e ≤ ex - 1 by omega)
  have hxLower : bpow β (ex - 1) < x := by
    have hle : bpow β (ex - 1) ≤ x := by
      simpa [ex, abs_of_pos hx] using (magnitude_spec β x hx0).1
    exact lt_of_le_of_ne hle (Ne.symm (by simpa [ex] using hboundary))
  let y := x - ulp β fexp x
  change genericFormat β fexp y
  have hy : y = ((n - 1 : ℤ) : ℝ) * bpow β e := by
    dsimp [y]
    rw [hulp, hxn]
    push_cast
    ring
  have hyLower : bpow β (ex - 1) ≤ y := by
    have hgap := int_mul_add_le_of_lt (bpow.pos β e)
      (show (N : ℝ) * bpow β e < (n : ℝ) * bpow β e by rw [← hN, ← hxn]; exact hxLower)
    rw [hN, hy, Int.cast_sub, Int.cast_one, sub_mul, one_mul]
    linarith
  have hyUpper : y < bpow β ex := by
    have hyltx : y < x := by
      dsimp [y]
      exact sub_lt_self x (ulp.pos_of_ne_zero β fexp x hx0)
    exact hyltx.trans (by simpa [ex, abs_of_pos hx] using (magnitude_spec β x hx0).2)
  exact generic_format_of_mul_bpow_of_mem_bin (n - 1) hy hyLower hyUpper

/--
Subtracting one ULP from a representable value that is not a positive radix boundary remains
representable. Positive values stay in their magnitude bin. For zero and negative values the
difference is the negated successor of `-x`.
-/
theorem generic_format_sub_ulp {x : ℝ} (hfmt : genericFormat β fexp x)
    (hboundary : x ≠ bpow β (magnitude β x - 1)) :
    genericFormat β fexp (x - ulp β fexp x) := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hneg : x - ulp β fexp x = -succ (β := β) (fexp := fexp) (-x) := by
      rw [succ_eq_of_nonneg (neg_nonneg.mpr hx.le), ulp_neg]
      ring
    rw [hneg]
    exact generic_format_neg _
      (generic_format_succ_of_pos (neg_pos.mpr hx) (generic_format_neg x hfmt))
  · subst x
    simpa using generic_format_neg _ (generic_format_ulp_zero (β := β) (fexp := fexp))
  · exact generic_format_sub_ulp_of_pos hx hfmt hboundary

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
    have hdsub : 0 ≤ d - 1 := by linarith
    have hpowOne : (1 : ℝ) ≤ bpow β (d - 1) := by
      change (1 : ℝ) ≤ β.toReal ^ (d - 1)
      exact one_le_zpow₀ (le_of_lt (Numerics.Radix.gt_one β)) hdsub
    have hgap : bpow β (d - 1) ≤ bpow β d - 1 := by
      linarith [two_mul_bpow_sub_one_le (β := β) d]
    let y := bpow β k - bpow β ef
    change genericFormat β fexp y
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
    obtain ⟨N, hN⟩ := exists_bpow_eq_int_mul_bpow β hlt.le
    have hy : y = ((N - 1 : ℤ) : ℝ) * bpow β ef := by
      dsimp [y]
      rw [hN]
      push_cast
      ring
    exact generic_format_of_mul_bpow_of_mem_bin (N - 1) hy hyLower hyUpper

/-- The predecessor formula yields a representable value for every representable input. -/
theorem generic_format_predPos {x : ℝ} (hfmt : genericFormat β fexp x) :
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
  · exact generic_format_sub_ulp hfmt hboundary

/-- The successor of every representable value is representable. -/
theorem generic_format_succ {x : ℝ} (hfmt : genericFormat β fexp x) :
    genericFormat β fexp (succ (β := β) (fexp := fexp) x) := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hnegfmt : genericFormat β fexp (-x) := generic_format_neg x hfmt
    have hpred := generic_format_predPos (β := β) (fexp := fexp) hnegfmt
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
private theorem succ_le_of_lt_pos {x y : ℝ} (hx : 0 < x)
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
    have hcexpX : cexp β fexp x = e := by simp [cexp, ex, e]
    have hcexpY : cexp β fexp y = e := by simp [cexp, ey, ex, heq, e]
    -- In the same bin, both values are integer multiples of the same ULP.
    obtain ⟨nx, hxrepr⟩ := exists_int_mul_bpow_cexp_of_generic hxfmt
    obtain ⟨ny, hyrepr⟩ := exists_int_mul_bpow_cexp_of_generic hyfmt
    rw [hcexpX] at hxrepr
    rw [hcexpY] at hyrepr
    rw [succ_eq_of_nonneg hx.le,
      ulp.of_ne_zero β fexp x hx.ne', hcexpX]
    rw [hxrepr, hyrepr]
    apply int_mul_add_le_of_lt (bpow.pos β e)
    rw [← hxrepr, ← hyrepr]
    exact hxy
  · have hsuccBound := succ_le_magnitude_bpow_of_pos
      (β := β) (fexp := fexp) hx hxfmt
    have hboundary : bpow β ex ≤ bpow β (ey - 1) :=
      (bpow_le_bpow_iff β _ _).2 (by linarith)
    have hyLower : bpow β (ey - 1) ≤ y := by
      simpa [ey, abs_of_pos hy] using (magnitude_spec β y hy.ne').1
    exact hsuccBound.trans (hboundary.trans hyLower)

/-- The zero ULP is no larger than any positive representable value. -/
private theorem ulp_zero_le_of_pos {y : ℝ} (hy : 0 < y) (hyfmt : genericFormat β fexp y) :
    ulp β fexp 0 ≤ y := by
  rw [ulp.zero]
  cases hopt : negligibleExp fexp with
  | none => exact hy.le
  | some n =>
      have hn : n ≤ fexp n := negligibleExp_spec hopt
      change bpow β (fexp n) ≤ y
      by_cases hsmall : magnitude β y ≤ fexp n
      · have hconst := ((ValidExp.flocq_valid (fexp := fexp) n).2 hn).2 _ hsmall
        have hcexp : cexp β fexp y = fexp n := by simp [cexp, hconst]
        simpa [hcexp, abs_of_pos hy] using bpow_cexp_le_abs_of_generic hy.ne' hyfmt
      · have hle : bpow β (fexp n) ≤ bpow β (magnitude β y - 1) :=
          (bpow_le_bpow_iff β _ _).2 (by omega)
        exact hle.trans (by simpa [abs_of_pos hy] using bpow_magnitude_sub_one_le β y hy.ne')

/-- The predecessor formula of a positive representable value is nonnegative. -/
private theorem predPos_nonneg {a : ℝ} (ha : 0 < a) (hfmt : genericFormat β fexp a) :
    0 ≤ predPos (β := β) (fexp := fexp) a := by
  unfold predPos
  split_ifs with hboundary
  · have hpow : genericFormat β fexp (bpow β (magnitude β a - 1)) := by
      rw [← hboundary]
      exact hfmt
    have hle := fexp_le_of_generic_bpow (β := β) (fexp := fexp) _ hpow
    rw [sub_nonneg]
    calc
      bpow β (fexp (magnitude β a - 1)) ≤ bpow β (magnitude β a - 1) :=
        (bpow_le_bpow_iff β _ _).2 hle
      _ = a := hboundary.symm
  · rw [sub_nonneg]
    simpa [abs_of_pos ha] using ulp_le_abs_of_generic ha.ne' hfmt

/-- A positive representable value below a representable `a` is at most `predPos a`. -/
private theorem le_predPos_of_lt {a b : ℝ} (hb : 0 < b) (hba : b < a)
    (hafmt : genericFormat β fexp a) (hbfmt : genericFormat β fexp b) :
    b ≤ predPos (β := β) (fexp := fexp) a := by
  have ha : 0 < a := hb.trans hba
  have hmag : magnitude β b ≤ magnitude β a := magnitude_mono_pos β hb hba.le
  obtain ⟨nb, hnb⟩ := exists_int_mul_bpow_cexp_of_generic hbfmt
  have hcb : cexp β fexp b < magnitude β b := cexp_lt_magnitude_of_pos_generic hb hbfmt
  have hbUpper : b < bpow β (magnitude β b) := by
    simpa [abs_of_pos hb] using abs_lt_bpow_magnitude β b
  unfold predPos
  split_ifs with hboundary
  · set e := magnitude β a - 1 with he
    have hpow : genericFormat β fexp (bpow β e) := by
      rw [← hboundary]
      exact hafmt
    have hfe : fexp e ≤ e := fexp_le_of_generic_bpow (β := β) (fexp := fexp) e hpow
    have hbe : magnitude β b ≤ e := by
      apply magnitude_le_of_abs_lt_bpow β b e hb.ne'
      rw [abs_of_pos hb, ← hboundary]
      exact hba
    calc
      b ≤ bpow β e - bpow β (fexp e) := ?_
      _ = a - bpow β (fexp e) := by rw [← hboundary]
    rcases hbe.eq_or_lt with hbeq | hblt
    · -- Same binade: both values are multiples of `β^(fexp e)`.
      have hcexp : cexp β fexp b = fexp e := by simp [cexp, hbeq]
      rw [hcexp] at hnb
      obtain ⟨M, hpowM⟩ := exists_bpow_eq_int_mul_bpow β hfe
      rw [hnb, hpowM]
      refine le_sub_iff_add_le.mpr (int_mul_add_le_of_lt (bpow.pos β _) ?_)
      rw [← hnb, ← hpowM, ← hboundary]
      exact hba
    · -- Lower binade: `b < β^(e-1) ≤ β^e - β^(fexp e)`.
      have hfe' : fexp e ≤ e - 1 := by
        by_contra hcon
        have hfeq : fexp e = e := by omega
        have hconst := ((ValidExp.flocq_valid (fexp := fexp) e).2 (by omega)).2
          (magnitude β b) (by omega)
        have hcexp : cexp β fexp b = e := by simp [cexp, hconst, hfeq]
        omega
      have h1 : b < bpow β (e - 1) := hbUpper.trans_le ((bpow_le_bpow_iff β _ _).2 (by omega))
      have h2 : bpow β (fexp e) ≤ bpow β (e - 1) := (bpow_le_bpow_iff β _ _).2 hfe'
      have h3 := two_mul_bpow_sub_one_le (β := β) e
      linarith
  · rw [ulp.of_ne_zero β fexp a ha.ne']
    obtain ⟨na, hna⟩ := exists_int_mul_bpow_cexp_of_generic hafmt
    have hca : cexp β fexp a < magnitude β a := cexp_lt_magnitude_of_pos_generic ha hafmt
    have hupos : 0 < bpow β (cexp β fexp a) := bpow.pos β _
    rcases hmag.eq_or_lt with hbeq | hblt
    · -- Same binade: both values are multiples of one ULP of `a`.
      have hcexp : cexp β fexp b = cexp β fexp a := by simp [cexp, hbeq]
      rw [hcexp] at hnb
      have h := int_mul_add_le_of_lt hupos (show (nb : ℝ) * bpow β (cexp β fexp a) <
          (na : ℝ) * bpow β (cexp β fexp a) by rw [← hnb, ← hna]; exact hba)
      rw [← hnb, ← hna] at h
      linarith
    · -- Lower binade: `b < β^(mag a - 1)`, which is at most `a - ulp a`.
      have h1 : b < bpow β (magnitude β a - 1) :=
        hbUpper.trans_le ((bpow_le_bpow_iff β _ _).2 (by omega))
      have haLower : bpow β (magnitude β a - 1) < a :=
        lt_of_le_of_ne (by simpa [abs_of_pos ha] using bpow_magnitude_sub_one_le β a ha.ne')
          (fun h => hboundary h.symm)
      obtain ⟨N, hpowN⟩ :=
        exists_bpow_eq_int_mul_bpow β (show cexp β fexp a ≤ magnitude β a - 1 by omega)
      have h := int_mul_add_le_of_lt hupos (show (N : ℝ) * bpow β (cexp β fexp a) <
          (na : ℝ) * bpow β (cexp β fexp a) by rw [← hpowN, ← hna]; exact haLower)
      rw [← hpowN, ← hna] at h
      linarith

/--
No representable value lies strictly between a representable value and its successor. This is
Flocq's `succ_le_lt`: below zero the successor is the negated predecessor of `-x`.
-/
theorem succ_le_of_lt {x y : ℝ}
    (hxfmt : genericFormat β fexp x) (hyfmt : genericFormat β fexp y)
    (hxy : x < y) : succ (β := β) (fexp := fexp) x ≤ y := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hsucc : succ (β := β) (fexp := fexp) x =
        -predPos (β := β) (fexp := fexp) (-x) := by
      simp [succ, not_le.mpr hx]
    have hafmt := generic_format_neg x hxfmt
    rw [hsucc, neg_le]
    rcases le_or_gt 0 y with hy | hy
    · exact (neg_nonpos.mpr hy).trans (predPos_nonneg (neg_pos.mpr hx) hafmt)
    · exact le_predPos_of_lt (neg_pos.mpr hy) (neg_lt_neg hxy) hafmt
        (generic_format_neg y hyfmt)
  · rw [succ_zero]
    exact ulp_zero_le_of_pos hxy hyfmt
  · exact succ_le_of_lt_pos hx hxfmt hyfmt hxy

end FloatLib.Floats.Formats.Flocq
