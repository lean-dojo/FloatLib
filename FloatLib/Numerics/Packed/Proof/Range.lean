/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Packed.Proof.Digits

/-!
# Range guards for packed signed rows

The bitwise guard bounds every signed lane and excludes nonzero storage beyond the requested row.
The bounds hold for every width and row length satisfying the guard.
-/

@[expose] public section

namespace FloatLib.Numerics.Packed

private theorem eq_of_lanes {j a b x y : Nat} (ha : a < 2 ^ j) (hb : b < 2 ^ j)
    (h : a + 2 ^ j * x = b + 2 ^ j * y) : a = b ∧ x = y := by
  have h1 := congrArg (· % 2 ^ j) h
  have h2 := congrArg (· / 2 ^ j) h
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos j), Nat.div_eq_of_lt ha, Nat.div_eq_of_lt hb,
    Nat.zero_add] at h1 h2
  exact ⟨h1, h2⟩

private theorem land_high_eq_zero {j a : Nat} (ha : a < 2 ^ j) (q : Nat) :
    a &&& (2 ^ j * q) = 0 := by
  have := land_split (x := 0) (y := q) ha (Nat.two_pow_pos j)
  simpa using this

/-- A lane whose bits from `g + 1` up read `100…0` lies in
`[2 ^ (w - 1), 2 ^ (w - 1) + 2 ^ (g + 1))`. -/
private theorem bounds_of_land {w g t : Nat} (hg : g + 1 < w) (ht : t < 2 ^ w)
    (h : t &&& (2 ^ w - 2 ^ (g + 1)) = 2 ^ (w - 1)) :
    2 ^ (w - 1) ≤ t ∧ t < 2 ^ (w - 1) + 2 ^ (g + 1) := by
  obtain ⟨e, he⟩ : ∃ e, w = g + 1 + (e + 1) := ⟨w - g - 2, by omega⟩
  subst he
  have hw : 2 ^ (g + 1 + (e + 1)) = 2 ^ (g + 1) * 2 ^ (e + 1) := Nat.pow_add _ _ _
  have hw1 : 2 ^ (g + 1 + (e + 1) - 1) = 2 ^ (g + 1) * 2 ^ e := by
    rw [show g + 1 + (e + 1) - 1 = g + 1 + e by omega, Nat.pow_add]
  have hm : 2 ^ (g + 1 + (e + 1)) - 2 ^ (g + 1) = 0 + 2 ^ (g + 1) * (2 ^ (e + 1) - 1) := by
    rw [hw, Nat.mul_sub, Nat.mul_one, Nat.zero_add]
  have hq : t / 2 ^ (g + 1) < 2 ^ (e + 1) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_comm, ← hw]; exact ht
  rw [hm, ← Nat.mod_add_div t (2 ^ (g + 1)), land_split (Nat.mod_lt _ (Nat.two_pow_pos _))
    (Nat.two_pow_pos _), Nat.and_zero, Nat.zero_add, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt hq, hw1] at h
  have hq' := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos _) h
  have hr := Nat.mod_lt t (Nat.two_pow_pos (g + 1))
  have ht' := Nat.mod_add_div t (2 ^ (g + 1))
  rw [hq', hw1.symm] at ht'
  rw [hw1]; rw [hw1] at ht'
  omega

private theorem guard_lanes (w g : Nat) (hg : g + 1 < w) :
    ∀ ds : List Nat, (∀ d ∈ ds, d < 2 ^ w) →
    (Nat.ofDigits (2 ^ w : Nat) ds +
        Nat.ofDigits (2 ^ w : Nat) (List.replicate ds.length (2 ^ g))) &&&
        Nat.ofDigits (2 ^ w : Nat) (List.replicate ds.length (2 ^ w - 2 ^ (g + 1))) =
      Nat.ofDigits (2 ^ w : Nat) (List.replicate ds.length (2 ^ (w - 1))) →
    ∀ d ∈ ds, 2 ^ (w - 1) ≤ d + 2 ^ g ∧ d + 2 ^ g < 2 ^ (w - 1) + 2 ^ (g + 1)
  | [], _, _ => by simp
  | d :: ds, hd, h => by
      have hlt : ∀ e ∈ ds, e < 2 ^ w := fun e he => hd e (by simp [he])
      have hd0 := hd d (by simp)
      have hgw : 2 ^ (g + 1) ≤ 2 ^ (w - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      have hw2 : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← Nat.pow_succ']; congr 1; omega
      have hg2 : 2 ^ (g + 1) = 2 * 2 ^ g := Nat.pow_succ'
      have hm : 2 ^ w - 2 ^ (g + 1) < 2 ^ w := by have := Nat.two_pow_pos g; omega
      have ht : 2 ^ (w - 1) < 2 ^ w := by have := Nat.two_pow_pos (w - 1); omega
      simp only [List.length_cons, List.replicate_succ, Nat.ofDigits_cons] at h
      -- peel off the bottom lane: `d + 2 ^ g`, then everything above it times `2 ^ w`
      rw [show d + 2 ^ w * Nat.ofDigits (2 ^ w : Nat) ds +
            (2 ^ g + 2 ^ w * Nat.ofDigits (2 ^ w : Nat) (List.replicate ds.length (2 ^ g))) =
          (d + 2 ^ g) + 2 ^ w *
            (Nat.ofDigits (2 ^ w : Nat) ds +
              Nat.ofDigits (2 ^ w : Nat) (List.replicate ds.length (2 ^ g))) by
            rw [Nat.mul_add]; omega] at h
      by_cases hc : d + 2 ^ g < 2 ^ w
      -- no carry: the mask acts on this lane alone, and its high bits read `100…0`
      · rw [land_split hc hm] at h
        obtain ⟨h0, h1⟩ := eq_of_lanes (Nat.and_lt_two_pow _ hm) ht h
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact bounds_of_land hg hc h0
        · exact guard_lanes w g hg ds hlt h1 e he
      -- a carry leaves this lane below `2 ^ (g + 1)`, so its masked bits are all zero, and the
      -- top bit that the check expects is missing
      · exfalso
        have hs : d + 2 ^ g - 2 ^ w < 2 ^ (g + 1) := by omega
        generalize Nat.ofDigits (2 ^ w : Nat) ds +
          Nat.ofDigits (2 ^ w : Nat) (List.replicate ds.length (2 ^ g)) = X at h
        rw [show d + 2 ^ g + 2 ^ w * X = (d + 2 ^ g - 2 ^ w) + 2 ^ w * (X + 1) by
              rw [Nat.mul_succ]; omega,
          land_split (by omega) hm] at h
        obtain ⟨h0, -⟩ := eq_of_lanes (Nat.and_lt_two_pow _ hm) ht h
        have hm' : 2 ^ w - 2 ^ (g + 1) = 2 ^ (g + 1) * (2 ^ (w - (g + 1)) - 1) := by
          rw [Nat.mul_sub, Nat.mul_one, ← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
        rw [hm', land_high_eq_zero hs] at h0
        have := Nat.two_pow_pos (w - 1)
        omega

/-- A passing range check bounds every signed entry: `-2 ^ g ≤ x < 2 ^ g`. It also says that the row
has no entries beyond `n` and that the bound leaves a spare bit, `g + 1 < w`. -/
theorem guard_sound {w g n u : Nat} (h : guard w g n u = true) :
    g + 1 < w ∧ u < 2 ^ (w * n) ∧ ∀ x ∈ entries w n u, -2 ^ g ≤ x ∧ x < 2 ^ g := by
  simp only [guard, Bool.cond_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, pow2_eq, Nat.add_eq,
    Nat.mul_eq,
    Nat.sub_eq] at h
  obtain ⟨hu, hg, hm⟩ := h
  have hw : 1 ≤ w := by omega
  refine ⟨hg, hu, ?_⟩
  have hds : ∀ d ∈ lanes w n u, d < 2 ^ w := by
    intro d hd
    simp only [lanes, List.mem_map] at hd
    obtain ⟨k, _, rfl⟩ := hd
    exact lane_lt w k u
  -- the one big comparison of `guard` is the lane-by-lane statement of `guard_lanes`
  have key := guard_lanes w g hg (lanes w n u) hds (by
    rw [ofDigits_lanes w n u hu, length_lanes, ofDigits_replicate _ (2 ^ g),
      ofDigits_replicate _ (2 ^ w - 2 ^ (g + 1)),
      ← bias_eq_ofDigits w n hw, ← ones_eq_ofDigits w n hw]
    show (u + 2 ^ g * ones w n) &&& ((2 ^ w - 2 ^ (g + 1)) * ones w n) = bias w n
    exact hm)
  intro x hx
  rw [entries_eq_lanes, List.mem_map] at hx
  obtain ⟨d, hd, rfl⟩ := hx
  have := key d hd
  have e1 := natCast_two_pow (w - 1)
  have e2 := natCast_two_pow g
  omega

end FloatLib.Numerics.Packed
