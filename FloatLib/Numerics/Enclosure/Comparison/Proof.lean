/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Comparison.Cache
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

/--
A prepared comparison sharing a cached enclosure sequence agrees with the real ordering of any
value that every enclosure contains, at every cache size.
-/
theorem Prepared.compare_enclosed_cacheIntervals (intervals : Nat → RationalInterval)
    (count : Nat)
    (terminates : ∀ boundary : ℚ, ∃ n, Separates ((cacheIntervals intervals count).get n) boundary)
    (boundary : ℚ) (x : ℝ) (contains : ∀ n, (intervals n).Contains x) :
    (Prepared.enclosed (cacheIntervals intervals count) terminates).compare boundary =
      cmp x (boundary : ℝ) :=
  compare_eq_real _ _ _ x fun n => by simpa only [cacheIntervals_apply] using contains n

/-- An irrational limit cannot equal a rational comparison boundary. -/
theorem exists_separating_of_irrational {intervals : Nat → RationalInterval}
    {x : ℝ} (hx : Irrational x) (boundary : ℚ)
    (hlo : Tendsto (fun n => ((intervals n).lo : ℝ)) atTop (𝓝 x))
    (hhi : Tendsto (fun n => ((intervals n).hi : ℝ)) atTop (𝓝 x)) :
    ∃ n, Separates (intervals n) boundary :=
  exists_separating boundary (hx.ne_rat boundary) hlo hhi

/-- The degrees `2 ^ n` tend to infinity. -/
private theorem tendsto_two_pow_atTop : Tendsto (fun n : Nat => 2 ^ n) atTop atTop :=
  StrictMono.tendsto_atTop fun _ _ h => Nat.pow_lt_pow_right (by decide) h

/--
Converging endpoints sampled at the doubling degrees `2 ^ n` of the adaptive comparisons
eventually exclude every boundary different from their limit.
-/
theorem exists_separating_two_pow {intervals : Nat → RationalInterval} {x : ℝ} (boundary : ℚ)
    (hne : x ≠ (boundary : ℝ))
    (hlo : Tendsto (fun n => ((intervals n).lo : ℝ)) atTop (𝓝 x))
    (hhi : Tendsto (fun n => ((intervals n).hi : ℝ)) atTop (𝓝 x)) :
    ∃ n, Separates (intervals (2 ^ n)) boundary :=
  exists_separating (intervals := fun n => intervals (2 ^ n)) boundary hne
    (hlo.comp tendsto_two_pow_atTop) (hhi.comp tendsto_two_pow_atTop)

/-- At the doubling degrees, an irrational limit is eventually separated from a rational
boundary. -/
theorem exists_separating_two_pow_of_irrational {intervals : Nat → RationalInterval}
    {x : ℝ} (hx : Irrational x) (boundary : ℚ)
    (hlo : Tendsto (fun n => ((intervals n).lo : ℝ)) atTop (𝓝 x))
    (hhi : Tendsto (fun n => ((intervals n).hi : ℝ)) atTop (𝓝 x)) :
    ∃ n, Separates (intervals (2 ^ n)) boundary :=
  exists_separating_two_pow boundary (hx.ne_rat boundary) hlo hhi

end FloatLib.Numerics.Enclosure.Comparison
