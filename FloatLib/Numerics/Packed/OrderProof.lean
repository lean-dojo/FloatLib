/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Packed.Lanes
public import FloatLib.Numerics.Packed.Order

/-!
# Soundness of the lanewise comparison

`lanesLe_sound`: a passing `lanesLe w n u v` gives `lane w k u ≤ lane w k v` for every `k < n`,
for every width `w ≥ 1`, every number of lanes and every pair of rows.
-/

@[expose] public section

namespace FloatLib.Numerics.Packed

/-- The lanes of a row below `2 ^ (w * n)` that passes the unsigned range check are all below
the bound, the ones from `n` on being zero. -/
private theorem lane_lt_of_guard {w g n u : Nat} (h : guard w g n u (signed := false) = true)
    (j : Nat) : lane w j u < 2 ^ g := by
  obtain ⟨hu, hlanes⟩ := lanes_lt_of_guard h
  rcases Nat.lt_or_ge j n with hj | hj
  · exact hlanes _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)
  · have hbig : u < 2 ^ (w * j) :=
      Nat.lt_of_lt_of_le hu (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left w hj))
    rw [lane_eq, Nat.div_eq_of_lt hbig, Nat.zero_mod]
    exact Nat.two_pow_pos g

/--
A passing `lanesLe w n u v` proves the comparison in every lane: `lane w k u ≤ lane w k v` for
all `k < n`.
-/
theorem lanesLe_sound {w n u v : Nat} (h : lanesLe w n u v = true) (hw : 1 ≤ w) :
    ∀ k < n, lane w k u ≤ lane w k v := by
  unfold lanesLe at h
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.sub_eq, Nat.add_eq, Nat.land_eq] at h
  obtain ⟨hu, hv, heq⟩ := h
  have htop : 2 ^ (w - 1) < 2 ^ w := Nat.pow_lt_pow_right (by decide) (by omega)
  have hdouble : 2 ^ w = 2 ^ (w - 1) + 2 ^ (w - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, w = m + 1 := ⟨w - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.pow_succ]
    omega
  have hbias : ∀ j, lane w j (bias w n) = if j < n then 2 ^ (w - 1) else 0 := by
    intro j
    have : bias w n = ones w n * 2 ^ (w - 1) := by
      simp only [bias, pow2_eq, Nat.mul_eq, Nat.sub_eq, Nat.mul_comm]
    rw [this, lane_const hw htop]
  have hlu := lane_lt_of_guard hu
  have hlv := lane_lt_of_guard hv
  have hadd : ∀ j, lane w j (v + bias w n) = lane w j v + lane w j (bias w n) :=
    lane_add fun j => by
      have := hlv j
      rw [hbias]
      split <;> omega
  have hsub : ∀ j, lane w j (v + bias w n - u) = lane w j (v + bias w n) - lane w j u :=
    lane_sub hw fun j => by
      rw [hadd, hbias]
      have := hlu j
      rcases Nat.lt_or_ge j n with hj | hj
      · rw [ite_eq_left hj]
        omega
      · obtain ⟨hbound, -⟩ := lanes_lt_of_guard hu
        have hbig : u < 2 ^ (w * j) :=
          Nat.lt_of_lt_of_le hbound (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left w hj))
        rw [lane_eq, Nat.div_eq_of_lt hbig, Nat.zero_mod]
        exact Nat.zero_le _
  intro k hk
  have hlane := congrArg (lane w k) heq
  rw [lane_land, hsub, hadd, hbias, ite_eq_left hk] at hlane
  have hle := Nat.and_le_left (n := lane w k v + 2 ^ (w - 1) - lane w k u) (m := 2 ^ (w - 1))
  have := hlu k
  omega

end FloatLib.Numerics.Packed
