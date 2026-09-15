/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Comparison.Runtime
public import FloatLib.Numerics.Enclosure.Rational.Proof
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Order.Basic

/-!
# Correctness and termination of enclosure comparison

Containment proves the ordering at every successful search. Endpoint convergence proves that
the search terminates whenever the target differs from the boundary. Irrationality is one
convenient sufficient condition when the boundaries are rational.
-/

public section

namespace FloatLib.Numerics.Enclosure.Comparison

open Filter
open scoped Topology

/-- Every accepted comparison agrees with the enclosed real value. -/
theorem compare_eq_real (intervals : Nat → RationalInterval) (boundary : ℚ)
    (terminates : ∃ n, Separates (intervals n) boundary) (x : ℝ)
    (contains : ∀ n, (intervals n).Contains x) :
    compare intervals boundary terminates = cmp x (boundary : ℝ) := by
  have hcontains := contains (Nat.find terminates)
  have hseparates := Nat.find_spec terminates
  dsimp only [compare]
  split
  · rename_i hlt
    have hreal : x < (boundary : ℝ) :=
      hcontains.2.trans_lt (by exact_mod_cast hlt)
    simp [cmp, cmpUsing, hreal]
  · rename_i hlt
    have hgt := hseparates.resolve_left hlt
    have hreal : (boundary : ℝ) < x :=
      (show (boundary : ℝ) < ((intervals (Nat.find terminates)).lo : ℝ) by
        exact_mod_cast hgt).trans_le hcontains.1
    simp [cmp, cmpUsing, hreal, not_lt_of_ge hreal.le]

/-- Converging endpoints eventually exclude every boundary different from their limit. -/
theorem exists_separating {intervals : Nat → RationalInterval} {x : ℝ} (boundary : ℚ)
    (hne : x ≠ (boundary : ℝ))
    (hlo : Tendsto (fun n => ((intervals n).lo : ℝ)) atTop (𝓝 x))
    (hhi : Tendsto (fun n => ((intervals n).hi : ℝ)) atTop (𝓝 x)) :
    ∃ n, Separates (intervals n) boundary := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨n, hn⟩ := (hhi.eventually (eventually_lt_nhds hlt)).exists
    exact ⟨n, Or.inl (by exact_mod_cast hn)⟩
  · obtain ⟨n, hn⟩ := (hlo.eventually (eventually_gt_nhds hgt)).exists
    exact ⟨n, Or.inr (by exact_mod_cast hn)⟩

/-- An irrational limit cannot equal a rational comparison boundary. -/
theorem exists_separating_of_irrational {intervals : Nat → RationalInterval}
    {x : ℝ} (hx : Irrational x) (boundary : ℚ)
    (hlo : Tendsto (fun n => ((intervals n).lo : ℝ)) atTop (𝓝 x))
    (hhi : Tendsto (fun n => ((intervals n).hi : ℝ)) atTop (𝓝 x)) :
    ∃ n, Separates (intervals n) boundary :=
  exists_separating boundary (hx.ne_rat boundary) hlo hhi

end FloatLib.Numerics.Enclosure.Comparison
