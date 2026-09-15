/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Enclosure.Proof
public import FloatLib.Numerics.Enclosure.Elementary.Convergence
public import Mathlib.NumberTheory.Real.Irrational

/-!
# Eventual acceptance of converging posit enclosures

Every comparison in posit rounding has a rational boundary. Consequently the rounded code is
locally constant at an irrational target, and converging rational endpoints eventually agree.
The result separates two mathematical obligations: the enclosure algorithm converges, and its
target avoids the exact boundaries. A function-specific irrationality theorem or exact-case
handler is still needed before this gives a total elementary operation.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.Enclosure

open Filter FloatLib.Numerics
open scoped Topology

private theorem eventually_decide_rat_le_eq {x : ℝ} (hx : Irrational x) (q : ℚ) :
    ∀ᶠ y in 𝓝 x, decide ((q : ℝ) ≤ y) = decide ((q : ℝ) ≤ x) := by
  rcases lt_or_gt_of_ne (hx.ne_rat q) with hlt | hgt
  · filter_upwards [eventually_lt_nhds hlt] with y hy
    simp [not_le_of_gt hlt, not_le_of_gt hy]
  · filter_upwards [eventually_gt_nhds hgt] with y hy
    simp [hgt.le, hy.le]

private theorem eventually_bisection_eq (format : Format) {x : ℝ} (hx : Irrational x)
    (steps lower upper : Nat) :
    ∀ᶠ y in 𝓝 x,
      Model.lowerCodeByBisection
        (fun code => decide (RealRounding.nonnegativeRealAt format code ≤ y))
        steps lower upper =
      Model.lowerCodeByBisection
        (fun code => decide (RealRounding.nonnegativeRealAt format code ≤ x))
        steps lower upper := by
  induction steps generalizing lower upper with
  | zero => exact Eventually.of_forall fun _ => rfl
  | succ steps ih =>
      by_cases hsplit : lower + 1 < upper
      · have hguard : ∀ᶠ y in 𝓝 x,
            decide (RealRounding.nonnegativeRealAt format ((lower + upper) / 2) ≤ y) =
              decide (RealRounding.nonnegativeRealAt format ((lower + upper) / 2) ≤ x) :=
          eventually_decide_rat_le_eq hx
            (Model.nonnegativeRatAt format ((lower + upper) / 2))
        filter_upwards [hguard, ih ((lower + upper) / 2) upper,
          ih lower ((lower + upper) / 2)] with y hy hleft hright
        simp only [Model.lowerCodeByBisection, if_pos hsplit]
        simp only [hy, hleft, hright]
      · exact Eventually.of_forall fun _ => by
          simp only [Model.lowerCodeByBisection, if_neg hsplit]

/-- The finite lower-code search is locally constant at every irrational target. -/
theorem eventually_lowerCode_eq (format : Format) {x : ℝ} (hx : Irrational x) :
    ∀ᶠ y in 𝓝 x, RealRounding.lowerCode format y = RealRounding.lowerCode format x :=
  eventually_bisection_eq format hx format.bits 0 format.signMaskNat

private theorem eventually_rat_comparisons {x : ℝ} (hx : Irrational x) (q : ℚ) :
    ∀ᶠ y in 𝓝 x,
      (y ≤ (q : ℝ) ↔ x ≤ (q : ℝ)) ∧
      (y < (q : ℝ) ↔ x < (q : ℝ)) ∧
      ((q : ℝ) < y ↔ (q : ℝ) < x) := by
  rcases lt_or_gt_of_ne (hx.ne_rat q) with hlt | hgt
  · filter_upwards [eventually_lt_nhds hlt] with y hy
    simp [hlt, hy, hlt.le, hy.le, not_lt_of_ge hlt.le, not_lt_of_ge hy.le]
  · filter_upwards [eventually_gt_nhds hgt] with y hy
    simp [hgt, hy, not_le_of_gt hgt, not_le_of_gt hy,
      not_lt_of_ge hgt.le, not_lt_of_ge hy.le]

/-- Standard posit rounding is locally constant at every irrational real target. -/
theorem eventually_roundPositiveCode_eq (format : Format) {x : ℝ} (hx : Irrational x) :
    ∀ᶠ y in 𝓝 x,
      RealRounding.roundPositiveCode format y = RealRounding.roundPositiveCode format x := by
  have hzero : ∀ᶠ y in 𝓝 x, (y ≤ 0 ↔ x ≤ 0) := by
    filter_upwards [eventually_rat_comparisons hx 0] with y hy
    simpa only [Rat.cast_zero] using hy.1
  have hminimum : ∀ᶠ y in 𝓝 x,
      (y < RealRounding.minPositive format ↔ x < RealRounding.minPositive format) := by
    filter_upwards [eventually_rat_comparisons hx (Model.minPositiveRat format)] with y hy
    exact hy.2.1
  have hthreshold : ∀ᶠ y in 𝓝 x,
      (y < RealRounding.roundingThreshold format (RealRounding.lowerCode format x) ↔
        x < RealRounding.roundingThreshold format (RealRounding.lowerCode format x)) ∧
      (RealRounding.roundingThreshold format (RealRounding.lowerCode format x) < y ↔
        RealRounding.roundingThreshold format (RealRounding.lowerCode format x) < x) := by
    filter_upwards [eventually_rat_comparisons hx
      (Model.roundingThreshold format (RealRounding.lowerCode format x))] with y hy
    exact hy.2
  filter_upwards [eventually_lowerCode_eq format hx, hzero, hminimum, hthreshold]
    with y hlower hzero hminimum hthreshold
  simp only [RealRounding.roundPositiveCode, hlower, hzero, hminimum,
    hthreshold.1, hthreshold.2]

/--
Converging rational endpoints eventually certify the posit rounding of an irrational target.

Containment is not required for this eventual statement: convergence puts both endpoints in a
neighborhood on which rounding is constant. Containment separately certifies every accepted
result, including any accepted before that neighborhood is reached.
-/
theorem eventually_roundPositive?_eq_some (format : Format)
    {intervals : Nat → RationalInterval} {x : ℝ} (hx : Irrational x)
    (hlo : Tendsto (fun n => ((intervals n).lo : ℝ)) atTop (𝓝 x))
    (hhi : Tendsto (fun n => ((intervals n).hi : ℝ)) atTop (𝓝 x)) :
    ∀ᶠ n in atTop,
      roundPositive? format (intervals n) = some (RealRounding.roundPositive format x) := by
  have hround := eventually_roundPositiveCode_eq format hx
  filter_upwards [hlo.eventually hround, hhi.eventually hround] with n hlower hupper
  rw [RealRounding.roundPositiveCode_ratCast] at hlower hupper
  simp [roundPositive?, hlower, hupper, RealRounding.roundPositive]

/-- An irrational exponential target is eventually resolved by the rational Taylor enclosures. -/
theorem eventually_roundPositive?_exp (format : Format) (x : ℚ)
    (hx : Irrational (Real.exp (x : ℝ))) :
    ∀ᶠ degree in atTop,
      roundPositive? format (FloatLib.Numerics.Enclosure.exp x degree) =
        some (RealRounding.roundPositive format (Real.exp (x : ℝ))) :=
  eventually_roundPositive?_eq_some format hx
    (FloatLib.Numerics.Enclosure.tendsto_exp_lo x)
    (FloatLib.Numerics.Enclosure.tendsto_exp_hi x)

end FloatLib.Floats.Formats.Posit.Model.Enclosure
