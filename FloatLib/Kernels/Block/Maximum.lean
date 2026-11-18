/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Block.Policy
public import FloatLib.Tactic.KernelOptimize
import FloatLib.Numerics.Kernel.QProof

/-!
# The largest magnitude of a group for Lean's kernel

`Block.amax group y g` folds `max` over the magnitudes `|y i|` of a group. For rational data
Lean's kernel pays about a millisecond per element for the absolute value and the maximum, on
top of the evaluation of the element itself.

`amaxLoop` runs through the indices of `Fin n` once and keeps the largest magnitude as a
numerator and a denominator: it compares `|num| / den` of an element with the fraction so far by
cross products of natural numbers. `amax_eq_loop` proves, for every `n`, grouping and data, that
`amax` is that fraction, and is tagged `@[kernel_optimize]`, so `float_decide` evaluates the
largest magnitude of a group with the loop. The elements themselves are evaluated as written.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Block

/-- The larger of two fractions of natural numbers, by cross products: `a / b` when it is larger
than `best.1 / best.2`, and `best` otherwise. -/
def largerFraction (best : Nat × Nat) (a b : Nat) : Nat × Nat :=
  Bool.casesOn (motive := fun _ => Nat × Nat) (Nat.blt (Nat.mul best.1 b) (Nat.mul a best.2))
    best (a, b)

/-- The largest magnitude among the entries of the group `g` with an index below `k`, as a
numerator and a denominator, and `0 / 1` when there is none. -/
def amaxLoop {n : Nat} {γ : Type*} [DecidableEq γ] (group : Fin n → γ) (y : Fin n → ℚ) (g : γ) :
    Nat → Nat × Nat
  | 0 => (0, 1)
  | k + 1 =>
      if h : k < n then
        if group ⟨k, h⟩ = g then
          largerFraction (amaxLoop group y g k) (y ⟨k, h⟩).num.natAbs (y ⟨k, h⟩).den
        else amaxLoop group y g k
      else amaxLoop group y g k

/-- The loop keeps a positive denominator, bounds every magnitude of the group that it has seen,
and its fraction is zero or one of those magnitudes. -/
theorem amaxLoop_spec {n : Nat} {γ : Type*} [DecidableEq γ] (group : Fin n → γ) (y : Fin n → ℚ)
    (g : γ) : ∀ k,
      0 < (amaxLoop group y g k).2 ∧
        (∀ i : Fin n, i.val < k → group i = g →
          |y i| ≤ ((amaxLoop group y g k).1 : ℚ) / (amaxLoop group y g k).2) ∧
        ((amaxLoop group y g k).1 = 0 ∨
          ∃ i : Fin n, i.val < k ∧ group i = g ∧
            |y i| = ((amaxLoop group y g k).1 : ℚ) / (amaxLoop group y g k).2)
  | 0 => ⟨Nat.one_pos, fun i hi => absurd hi (Nat.not_lt_zero _), Or.inl rfl⟩
  | k + 1 => by
      obtain ⟨hd, hle, hex⟩ := amaxLoop_spec group y g k
      rw [amaxLoop]
      by_cases hk : k < n
      · rw [dite_eq_left hk]
        by_cases hg : group ⟨k, hk⟩ = g
        · rw [ite_eq_left hg]
          generalize amaxLoop group y g k = best at hd hle hex
          obtain ⟨p, d⟩ := best
          have habs := FloatLib.Numerics.Kernel.Q.abs_eq_natAbs_div (y ⟨k, hk⟩)
          have hb : 0 < (y ⟨k, hk⟩).den := (y ⟨k, hk⟩).den_pos
          generalize (y ⟨k, hk⟩).num.natAbs = a at habs
          generalize (y ⟨k, hk⟩).den = b at habs hb
          have hdq : (0 : ℚ) < d := by exact_mod_cast hd
          have hbq : (0 : ℚ) < b := by exact_mod_cast hb
          unfold largerFraction
          cases hlt : Nat.blt (Nat.mul p b) (Nat.mul a d)
          · -- the best stays
            have hge : a * d ≤ p * b := by
              rcases Nat.lt_or_ge (p * b) (a * d) with h | h
              · have : Nat.blt (Nat.mul p b) (Nat.mul a d) = true := by
                  rw [Nat.blt_eq]; exact h
                rw [this] at hlt; cases hlt
              · exact h
            have hfrac : (a : ℚ) / b ≤ (p : ℚ) / d := by
              rw [div_le_div_iff₀ hbq hdq]
              exact_mod_cast hge
            refine ⟨hd, fun i hi hig => ?_, ?_⟩
            · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt' | heq
              · exact hle i hlt' hig
              · have hi' : i = ⟨k, hk⟩ := Fin.ext heq
                rw [hi', habs]
                exact hfrac
            · rcases hex with h0 | ⟨i, hi, hig, heq⟩
              · exact Or.inl h0
              · exact Or.inr ⟨i, Nat.lt_succ_of_lt hi, hig, heq⟩
          · -- the new entry is larger
            have hlt' : p * b < a * d := by rw [← Nat.blt_eq]; exact hlt
            have hfrac : (p : ℚ) / d < (a : ℚ) / b := by
              rw [div_lt_div_iff₀ hdq hbq]
              exact_mod_cast hlt'
            refine ⟨hb, fun i hi hig => ?_, Or.inr ⟨⟨k, hk⟩, Nat.lt_succ_self k, hg, habs⟩⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt'' | heq
            · exact le_trans (hle i hlt'' hig) (le_of_lt hfrac)
            · have hi' : i = ⟨k, hk⟩ := Fin.ext heq
              rw [hi', habs]
        · rw [ite_eq_right hg]
          refine ⟨hd, fun i hi hig => ?_, ?_⟩
          · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | heq
            · exact hle i hlt hig
            · have hi' : i = ⟨k, hk⟩ := Fin.ext heq
              rw [hi'] at hig
              exact absurd hig hg
          · rcases hex with h0 | ⟨i, hi, hig, heq⟩
            · exact Or.inl h0
            · exact Or.inr ⟨i, Nat.lt_succ_of_lt hi, hig, heq⟩
      · rw [dite_eq_right hk]
        refine ⟨hd, fun i hi hig => hle i (by omega) hig, ?_⟩
        rcases hex with h0 | ⟨i, hi, hig, heq⟩
        · exact Or.inl h0
        · exact Or.inr ⟨i, Nat.lt_succ_of_lt hi, hig, heq⟩

/--
The largest magnitude of a group of rational numbers indexed by `Fin n` is the fraction that
one loop over the indices finds on numerators and denominators, for every grouping.
-/
@[kernel_optimize] theorem amax_eq_loop {n : Nat} {γ : Type*} [DecidableEq γ] (group : Fin n → γ)
    (y : Fin n → ℚ)
    (g : γ) :
    amax group y g =
      mkRat (Int.ofNat (amaxLoop group y g n).1) (amaxLoop group y g n).2 := by
  obtain ⟨_, hle, hex⟩ := amaxLoop_spec group y g n
  rw [Rat.mkRat_eq_div]
  change _ = ((amaxLoop group y g n).1 : ℚ) / (amaxLoop group y g n).2
  rcases hex with h0 | ⟨i, -, hig, heq⟩
  · rw [h0, Nat.cast_zero, zero_div]
    refine le_antisymm (amax_le_iff.mpr ⟨le_rfl, fun i hig => ?_⟩) (amax_nonneg group y g)
    have := hle i i.isLt hig
    rwa [h0, Nat.cast_zero, zero_div] at this
  · exact amax_eq (fun i hig => hle i i.isLt hig) ⟨i, hig, heq⟩

end FloatLib.Floats.Formats.Block
