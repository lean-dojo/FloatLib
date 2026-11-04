/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Rational.Proof
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.OrderClosed

/-!
# Convergence through rational interval operations

Repeated squaring preserves endpoint convergence to a nonnegative target. With the containment
lemmas, that lets an analytic kernel reduce its argument and keep both soundness and arbitrary
accuracy.
-/

@[expose] public section

namespace FloatLib.Numerics.RationalInterval

open Filter
open scoped Topology

/-- Values within a vanishing radius of a real number converge to it. -/
theorem tendsto_of_abs_sub_le {α : Type*} {l : Filter α} {f radius : α → ℝ} {x : ℝ}
    (hbound : ∀ a, |x - f a| ≤ radius a) (hradius : Tendsto radius l (𝓝 0)) :
    Tendsto f l (𝓝 x) := by
  rw [tendsto_iff_dist_tendsto_zero]
  exact squeeze_zero (fun _ => dist_nonneg)
    (fun a => by simpa only [Real.dist_eq, abs_sub_comm] using hbound a) hradius

/-- The lower endpoints of a repeatedly squared enclosure approach the corresponding power. -/
theorem tendsto_squareRepeat_lo {α : Type*} {l : Filter α}
    {intervals : α → RationalInterval} {x : ℝ}
    (hlo : Tendsto (fun a => ((intervals a).lo : ℝ)) l (𝓝 x))
    (hx : 0 ≤ x) (n : Nat) :
    Tendsto (fun a => ((intervals a |>.squareRepeat n).lo : ℝ)) l
      (𝓝 (x ^ (2 ^ n))) := by
  induction n with
  | zero => simpa [squareRepeat] using hlo
  | succ n ih =>
      have hmax := (tendsto_const_nhds (x := (0 : ℝ))).max ih
      simpa [squareRepeat, squareNonnegative, max_eq_right (pow_nonneg hx _),
        pow_succ, pow_mul] using hmax.pow 2

/-- The upper endpoints of a repeatedly squared enclosure approach the corresponding power. -/
theorem tendsto_squareRepeat_hi {α : Type*} {l : Filter α}
    {intervals : α → RationalInterval} {x : ℝ}
    (hhi : Tendsto (fun a => ((intervals a).hi : ℝ)) l (𝓝 x)) (n : Nat) :
    Tendsto (fun a => ((intervals a |>.squareRepeat n).hi : ℝ)) l
      (𝓝 (x ^ (2 ^ n))) := by
  induction n with
  | zero => simpa [squareRepeat] using hhi
  | succ n ih =>
      simpa [squareRepeat, squareNonnegative, pow_succ, pow_mul] using ih.pow 2

end FloatLib.Numerics.RationalInterval
