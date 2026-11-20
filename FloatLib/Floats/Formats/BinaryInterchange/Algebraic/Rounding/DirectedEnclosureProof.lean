/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Rounding.DirectedEnclosure
public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Rounding.DirectedProof
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.TotalOrder.Encoding
public import FloatLib.Numerics.Enclosure.Rational.Proof

/-!
# An enclosure whose endpoints round alike determines the rounding

For an IEEE descriptor and every rounding direction, if two reals of the same sign round to the
same encoding, every real between them rounds to that encoding (`roundReal_eq_of_mem_Icc`):
rounding is monotone, a finite encoding is determined by its value and its sign, and the overflow
results are the extreme encodings of their sign. So an encoding accepted by `roundEnclosure?` or
`zivRound?` is the correct rounding of every real in the enclosure
(`roundReal_eq_of_roundEnclosure?`, `roundReal_eq_of_zivRound?`).
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Floats.Formats.Flocq FloatLib.Numerics

variable {fmt : FloatFormat}

/-- Finite values with the same real value, and the same sign when it is zero, are equal. -/
theorem eq_of_toReal_eq {x y : Model fmt} (hx : isFinite x = true)
    (hy : isFinite y = true) (hvalue : toReal x = toReal y)
    (hsign : toReal x = 0 → signBit x = signBit y) : x = y := by
  by_cases hzero : toReal x = 0
  · have hxzero := (isZero_eq_true_iff_toReal_eq_zero x hx).mpr hzero
    have hyzero := (isZero_eq_true_iff_toReal_eq_zero y hy).mpr (hvalue ▸ hzero)
    have hdecode := toDyadic?_eq_zero_of_isZero_eq_true y hyzero
    rw [← hsign hzero] at hdecode
    exact eq_of_toDyadic?_eq_some (toDyadic?_eq_zero_of_isZero_eq_true x hxzero) hdecode
  · exact eq_of_toReal_eq_of_nonzero hvalue hzero

/--
For an IEEE descriptor, two reals of the same sign that round to the same encoding in the
direction `mode` enclose only reals that round to it.
-/
theorem roundReal_eq_of_mem_Icc (hfmt : fmt.isIEEE = true) (mode : IEEERoundingMode)
    {lo hi x : ℝ} (hlo : lo ≤ x) (hhi : x ≤ hi) (hsign : 0 < lo ∨ hi < 0)
    (h : roundReal fmt mode lo = roundReal fmt mode hi) :
    roundReal fmt mode x = roundReal fmt mode lo := by
  have hsigned := FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt hfmt
  have hlo0 : lo ≠ 0 := by
    rcases hsign with hs | hs
    · exact hs.ne'
    · exact ((hlo.trans hhi).trans_lt hs).ne
  have hhi0 : hi ≠ 0 := by
    rcases hsign with hs | hs
    · exact (hs.trans_le (hlo.trans hhi)).ne'
    · exact hs.ne
  have hx0 : x ≠ 0 := by
    rcases hsign with hs | hs
    · exact (hs.trans_le hlo).ne'
    · exact (hhi.trans_lt hs).ne
  have ha := roundReal_roundsTo (fmt := fmt) mode hlo0
  have hb := roundReal_roundsTo (fmt := fmt) mode hhi0
  have hxr := roundReal_roundsTo (fmt := fmt) mode hx0
  have hAX := roundAt_mono fmt hlo mode
  have hXB := roundAt_mono fmt hhi mode
  rcases hsign with hpos | hneg
  · have hsx : decide (x < 0) = false := decide_eq_false (not_lt.mpr (hpos.le.trans hlo))
    have hsa : decide (lo < 0) = false := decide_eq_false (not_lt.mpr hpos.le)
    have hsb : decide (hi < 0) = false :=
      decide_eq_false (not_lt.mpr (hpos.le.trans (hlo.trans hhi)))
    have hA0 : 0 ≤ roundAt fmt lo mode := by
      have hmono := roundAt_mono fmt hpos.le mode
      rwa [roundAt_zero fmt mode] at hmono
    have hX0 : 0 ≤ roundAt fmt x mode := hA0.trans hAX
    by_cases hrange : |roundAt fmt x mode| ≤ toReal (posMaxFinite fmt)
    · obtain ⟨hfinite, hvalue⟩ := hxr.finite hrange
      rw [abs_of_nonneg hX0] at hrange
      obtain ⟨hfa, hva⟩ := ha.finite (by rw [abs_of_nonneg hA0]; exact hAX.trans hrange)
      have hvalueLo : toReal (roundReal fmt mode lo) = roundAt fmt x mode := by
        by_cases hBrange : |roundAt fmt hi mode| ≤ toReal (posMaxFinite fmt)
        · obtain ⟨-, hvb⟩ := hb.finite hBrange
          rw [← h] at hvb
          linarith
        · have hov := hb.overflow (not_le.mp hBrange)
          rw [← h, hsb] at hov
          have hmax : toReal (roundReal fmt mode lo) = toReal (posMaxFinite fmt) := by
            cases hflag : mode.overflowRoundsMagnitudeUp false with
            | true => simp [hov, directedOverflow, hflag, isFinite_nativeOverflow hfmt] at hfa
            | false =>
                rw [hov, directedOverflow, hflag]
                simp [toReal_maxFinite]
          linarith
      exact eq_of_toReal_eq hfinite hfa (hvalue.trans hvalueLo.symm)
        (fun _ => by rw [hxr.signBit hsigned, ha.signBit hsigned, hsx, hsa])
    · have hX : toReal (posMaxFinite fmt) < roundAt fmt x mode := by
        have hgt := not_le.mp hrange
        rwa [abs_of_nonneg hX0] at hgt
      have hB : toReal (posMaxFinite fmt) < |roundAt fmt hi mode| := by
        rw [abs_of_nonneg (hX0.trans hXB)]
        exact hX.trans_le hXB
      rw [hxr.overflow (not_le.mp hrange), h, hb.overflow hB, hsx, hsb]
  · have hsx : decide (x < 0) = true := decide_eq_true (hhi.trans_lt hneg)
    have hsa : decide (lo < 0) = true := decide_eq_true ((hlo.trans hhi).trans_lt hneg)
    have hB0 : roundAt fmt hi mode ≤ 0 := by
      have hmono := roundAt_mono fmt hneg.le mode
      rwa [roundAt_zero fmt mode] at hmono
    have hX0 : roundAt fmt x mode ≤ 0 := hXB.trans hB0
    by_cases hrange : |roundAt fmt x mode| ≤ toReal (posMaxFinite fmt)
    · obtain ⟨hfinite, hvalue⟩ := hxr.finite hrange
      rw [abs_of_nonpos hX0] at hrange
      obtain ⟨hfb, hvb⟩ := hb.finite (by rw [abs_of_nonpos hB0]; linarith)
      rw [← h] at hfb hvb
      have hvalueLo : toReal (roundReal fmt mode lo) = roundAt fmt x mode := by
        by_cases hArange : |roundAt fmt lo mode| ≤ toReal (posMaxFinite fmt)
        · obtain ⟨-, hva⟩ := ha.finite hArange
          linarith
        · have hov := ha.overflow (not_le.mp hArange)
          rw [hsa] at hov
          have hmax : toReal (roundReal fmt mode lo) = -toReal (posMaxFinite fmt) := by
            cases hflag : mode.overflowRoundsMagnitudeUp true with
            | true => simp [hov, directedOverflow, hflag, isFinite_nativeOverflow hfmt] at hfb
            | false =>
                rw [hov, directedOverflow, hflag]
                simp [toReal_maxFinite]
          linarith
      exact eq_of_toReal_eq hfinite hfb (hvalue.trans hvalueLo.symm)
        (fun _ => by rw [hxr.signBit hsigned, ha.signBit hsigned, hsx, hsa])
    · have hX : roundAt fmt x mode < -toReal (posMaxFinite fmt) := by
        have hgt := not_le.mp hrange
        rw [abs_of_nonpos hX0] at hgt
        linarith
      have hA : toReal (posMaxFinite fmt) < |roundAt fmt lo mode| := by
        rw [abs_of_nonpos (hAX.trans hX0)]
        linarith
      rw [hxr.overflow (not_le.mp hrange), ha.overflow hA, hsx, hsa]

/-- The sign requested for a zero does not affect the rounding of a nonzero real. -/
theorem roundReal_of_ne_zero (fmt : FloatFormat) (mode : IEEERoundingMode) {x : ℝ} (hx : x ≠ 0)
    (zeroSign : Bool) : roundReal fmt mode x zeroSign = roundReal fmt mode x := by
  unfold roundReal AlgebraicRounding.roundSigned
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have hcmp : cmp x ((0 : Rat) : ℝ) = .lt := (cmp_eq_lt_iff _ _).mpr (by simpa using hneg)
    simp only [hcmp]
  · have hcmp : cmp x ((0 : Rat) : ℝ) = .gt := (cmp_eq_gt_iff _ _).mpr (by simpa using hpos)
    simp only [hcmp]

namespace AlgebraicRounding

/-- `roundRat` is the rounding of the rational as a real. -/
theorem roundRat_eq_roundReal (fmt : FloatFormat) (mode : IEEERoundingMode) (q : Rat) :
    roundRat fmt mode q = roundReal fmt mode (q : ℝ) :=
  roundSigned_eq_roundReal fmt mode fun boundary => by simp only [cmp, cmpUsing, Rat.cast_lt]

/--
For an IEEE descriptor, an encoding accepted by `roundEnclosure?` is the rounding, in the
direction `mode`, of every real in the enclosure.
-/
theorem roundReal_eq_of_roundEnclosure? (hfmt : fmt.isIEEE = true) (mode : IEEERoundingMode)
    {interval : RationalInterval} {x : ℝ} {result : Model fmt} (hx : interval.Contains x)
    (h : roundEnclosure? fmt mode interval = some result) (zeroSign : Bool := false) :
    roundReal fmt mode x zeroSign = result := by
  unfold roundEnclosure? at h
  split at h
  · rename_i hsign
    have hsignReal : (0 : ℝ) < interval.lo ∨ (interval.hi : ℝ) < 0 := by exact_mod_cast hsign
    have hx0 : x ≠ 0 := by
      rcases hsignReal with hs | hs
      · exact (hs.trans_le hx.1).ne'
      · exact (hx.2.trans_lt hs).ne
    rw [roundReal_of_ne_zero fmt mode hx0]
    dsimp only at h
    split at h
    · rename_i hequal
      rw [← Option.some.inj h, roundRat_eq_roundReal]
      refine roundReal_eq_of_mem_Icc hfmt mode hx.1 hx.2 hsignReal ?_
      rw [← roundRat_eq_roundReal, ← roundRat_eq_roundReal, ← ofNatBits_toNatBits (roundRat _ _ _),
        hequal, ofNatBits_toNatBits]
    · simp at h
  · simp at h

/--
For an IEEE descriptor, an encoding accepted by `zivRound?` from sound enclosures of `x` is the
rounding of `x` in the direction `mode`.
-/
theorem roundReal_eq_of_zivRound? (hfmt : fmt.isIEEE = true) (mode : IEEERoundingMode)
    {enclose : Nat → Option RationalInterval} {x : ℝ}
    (henclose : ∀ precision interval, enclose precision = some interval → interval.Contains x)
    {levels precision : Nat} {result : Model fmt}
    (h : zivRound? fmt mode enclose levels precision = some result) (zeroSign : Bool := false) :
    roundReal fmt mode x zeroSign = result := by
  induction levels generalizing precision with
  | zero => simp [zivRound?] at h
  | succ levels ih =>
      rw [zivRound?] at h
      split at h
      · rename_i accepted haccepted
        obtain ⟨interval, hinterval, hround⟩ := Option.bind_eq_some_iff.mp haccepted
        rw [← Option.some.inj h]
        exact roundReal_eq_of_roundEnclosure? hfmt mode (henclose _ _ hinterval) hround zeroSign
      · exact ih h

end AlgebraicRounding

end FloatLib.Floats.Formats.BinaryInterchange.Model
