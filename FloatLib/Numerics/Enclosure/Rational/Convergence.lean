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

Repeated squaring preserves endpoint convergence to a nonnegative target. Together with the
containment lemmas, this lets an analytic kernel reduce its argument without losing either
soundness or arbitrary accuracy.
-/

@[expose] public section

namespace FloatLib.Numerics.RationalInterval

open Filter
open scoped Topology

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
