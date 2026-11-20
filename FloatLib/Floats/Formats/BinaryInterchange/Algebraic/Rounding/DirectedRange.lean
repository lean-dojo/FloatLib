/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Rounding.DirectedProof

/-!
# The rounding of a real outside the range of the format

For every format descriptor and every rounding direction:

* `roundReal_of_upperExponent_le`: a real of magnitude at least `2 ^ upperExponent fmt`, the
  first power of two beyond the largest finite number, rounds to the overflow result of its
  sign;
* `roundReal_of_lt_lowerExponent`: a nonzero real of magnitude below `2 ^ lowerExponent fmt`,
  half the least positive number, rounds to what every such real of its sign rounds to, a zero
  or the least positive number.

Each asks for a bound on one side only. The rounding of a real from an enclosure
(`roundReal_eq_of_mem_Icc`) needs two rational ends, which a value like `exp (2 ^ 100)` does not
have at a usable size.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Floats.Formats.Flocq FloatLib.Numerics AlgebraicRounding

variable {fmt : FloatFormat}

/-- A nonzero real rounds as its magnitude does with its sign. -/
theorem roundReal_signed (mode : IEEERoundingMode) (sign : Bool) {t : ℝ} (ht : 0 < t)
    (zeroSign : Bool := false) :
    roundReal fmt mode (if sign then -t else t) zeroSign =
      roundMagnitude fmt mode sign (fun boundary : Rat => cmp t (boundary : ℝ)) := by
  unfold roundReal roundSigned
  cases sign with
  | false =>
      have hcmp : cmp t ((0 : Rat) : ℝ) = .gt := (cmp_eq_gt_iff _ _).mpr (by simpa using ht)
      simp only [Bool.false_eq_true, ↓reduceIte, hcmp]
  | true =>
      have hcmp : cmp (-t) ((0 : Rat) : ℝ) = .lt := (cmp_eq_lt_iff _ _).mpr (by simpa using ht)
      have hmirror : (fun boundary : Rat => (cmp (-t) ((-boundary : Rat) : ℝ)).swap) =
          fun boundary : Rat => cmp t (boundary : ℝ) := by
        funext boundary
        rw [cmp_swap]
        push_cast
        simp only [cmp, cmpUsing, neg_lt_neg_iff]
      simp only [↓reduceIte, hcmp, hmirror]

/-- A real is its magnitude with its sign. -/
private theorem eq_signed_abs (x : ℝ) : x = if decide (x < 0) = true then -|x| else |x| := by
  by_cases h : x < 0
  · simp [h, abs_of_neg h]
  · simp [h, abs_of_nonneg (not_lt.mp h)]

/--
A real of magnitude at least `2 ^ upperExponent fmt` rounds to the overflow result of its sign
in the direction `mode`, for every format descriptor.
-/
theorem roundReal_of_upperExponent_le (mode : IEEERoundingMode) {x : ℝ}
    (hx : Flocq.bpow binaryRadix (upperExponent fmt) ≤ |x|) (zeroSign : Bool := false) :
    roundReal fmt mode x zeroSign =
      directedOverflow fmt (decide (x < 0))
        (mode.overflowRoundsMagnitudeUp (decide (x < 0))) := by
  have hupper : cmp |x| ((powerOfTwo (upperExponent fmt) : Rat) : ℝ) ≠ .lt := by
    rw [cast_powerOfTwo]
    exact fun h => absurd ((cmp_eq_lt_iff _ _).mp h) (not_lt.mpr hx)
  conv_lhs => rw [eq_signed_abs x]
  rw [roundReal_signed mode (decide (x < 0)) ((Flocq.bpow.pos binaryRadix _).trans_le hx)
      zeroSign,
    roundMagnitude_eq fmt mode (decide (x < 0)) (target := |x|) (fun _ => rfl),
    ite_eq_left hupper]

/--
A nonzero real of magnitude below `2 ^ lowerExponent fmt`, half the least positive number,
rounds in the direction `mode` as a magnitude in the lower half of the first cell of the grid
does, for every format descriptor: to a zero of its sign, or to the least positive number with
its sign where the direction rounds the magnitude up.
-/
theorem roundReal_of_lt_lowerExponent (mode : IEEERoundingMode) {x : ℝ} (hne : x ≠ 0)
    (hx : |x| < Flocq.bpow binaryRadix (lowerExponent fmt)) (zeroSign : Bool := false) :
    roundReal fmt mode x zeroSign =
      roundLocated fmt mode (decide (x < 0)) 0 fmt.minSubnormalExponent false true := by
  have hupper : ¬cmp |x| ((powerOfTwo (upperExponent fmt) : Rat) : ℝ) ≠ .lt := by
    rw [cast_powerOfTwo, not_not, cmp_eq_lt_iff]
    exact hx.trans
      ((Flocq.bpow_lt_bpow_iff binaryRadix _ _).mpr (lowerExponent_lt_upperExponent fmt))
  have hlower : cmp |x| ((powerOfTwo (lowerExponent fmt) : Rat) : ℝ) = .lt := by
    rw [cast_powerOfTwo, cmp_eq_lt_iff]
    exact hx
  conv_lhs => rw [eq_signed_abs x]
  rw [roundReal_signed mode (decide (x < 0)) (abs_pos.mpr hne) zeroSign,
    roundMagnitude_eq fmt mode (decide (x < 0)) (target := |x|) (fun _ => rfl),
    ite_eq_right hupper, ite_eq_left hlower]

end FloatLib.Floats.Formats.BinaryInterchange.Model
