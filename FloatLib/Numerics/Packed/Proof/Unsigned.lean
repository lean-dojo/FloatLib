/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Packed.Proof.Digits

/-!
# Unsigned packed rows

Unsigned guards bound every natural digit. Packing, lane sums and multiplication recover
nonnegative entries and their Cauchy convolution under explicit width and headroom assumptions.
-/

@[expose] public section

namespace FloatLib.Numerics.Packed

/-- A row below `2 ^ (w * n)` is the value of its lanes in base `2 ^ w`. -/
theorem eval_lanes {w n u : Nat} (hu : u < 2 ^ (w * n)) :
    eval (2 ^ w) ((lanes w n u).map Nat.cast) = u := by
  rw [← natCast_two_pow, eval_natCast, ofDigits_lanes w n u hu]

private theorem land_replicate (w m : Nat) (hm : m < 2 ^ w) :
    ∀ ds : List Nat, (∀ d ∈ ds, d < 2 ^ w) →
      Nat.ofDigits (2 ^ w : Nat) ds &&&
          Nat.ofDigits (2 ^ w : Nat) (List.replicate ds.length m) = 0 →
        ∀ d ∈ ds, d &&& m = 0
  | [], _, _ => by simp
  | d :: ds, hd, h => by
      simp only [List.length_cons, List.replicate_succ, Nat.ofDigits_cons] at h
      rw [land_split (hd d (by simp)) hm] at h
      obtain ⟨h0, h1⟩ := Nat.add_eq_zero_iff.mp h
      have h1 := (Nat.mul_eq_zero.mp h1).resolve_left (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos w))
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact h0
      · exact land_replicate w m hm ds (fun x hx => hd x (by simp [hx])) h1 e he

private theorem lt_of_land_high {w g d : Nat} (hg : g ≤ w) (hd : d < 2 ^ w)
    (h : d &&& (2 ^ w - 2 ^ g) = 0) : d < 2 ^ g := by
  have hm : 2 ^ w - 2 ^ g = 0 + 2 ^ g * (2 ^ (w - g) - 1) := by
    rw [Nat.zero_add, Nat.mul_sub, Nat.mul_one, ← Nat.pow_add, Nat.add_sub_cancel' hg]
  have hq : d / 2 ^ g < 2 ^ (w - g) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos g), ← Nat.pow_add, Nat.sub_add_cancel hg]; exact hd
  rw [hm, ← Nat.mod_add_div d (2 ^ g), land_split (Nat.mod_lt _ (Nat.two_pow_pos g))
    (Nat.two_pow_pos g), Nat.and_zero, Nat.zero_add, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt hq] at h
  have h0 := (Nat.mul_eq_zero.mp h).resolve_left (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos g))
  have := Nat.mod_add_div d (2 ^ g)
  rw [h0, Nat.mul_zero, Nat.add_zero] at this
  rw [← this]; exact Nat.mod_lt _ (Nat.two_pow_pos g)

/-- A passing unsigned range check bounds every lane by `2 ^ g` and rules out lanes beyond `n`. -/
theorem lanes_lt_of_guard {w g n u : Nat} (h : guard w g n u (signed := false) = true) :
    u < 2 ^ (w * n) ∧ ∀ d ∈ lanes w n u, d < 2 ^ g := by
  simp only [guard, Bool.cond_false, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq, pow2_eq,
    Nat.mul_eq, Nat.sub_eq] at h
  obtain ⟨hu, hg, hm⟩ := h
  refine ⟨hu, ?_⟩
  rcases Nat.eq_zero_or_pos w with hw | hw
  · intro d hd
    have hg0 : g = 0 := by omega
    have := lt_of_mem_lanes hd
    rw [hw] at this; rw [hg0]; exact this
  · have hds : ∀ d ∈ lanes w n u, d < 2 ^ w := fun d hd => lt_of_mem_lanes hd
    have hmask : 2 ^ w - 2 ^ g < 2 ^ w := by
      have := Nat.two_pow_pos g; have := Nat.two_pow_pos w; omega
    have key := land_replicate w (2 ^ w - 2 ^ g) hmask (lanes w n u) hds (by
      rw [ofDigits_lanes w n u hu, length_lanes, ofDigits_replicate, ← ones_eq_ofDigits w n hw]
      exact hm)
    intro d hd
    exact lt_of_land_high hg (hds d hd) (key d hd)

/-- One remainder computes the sum of the lanes of a row, when that sum is below `2 ^ w - 1`. -/
theorem laneSum_eq {w n u : Nat} (hu : u < 2 ^ (w * n)) (hs : (lanes w n u).sum < 2 ^ w - 1) :
    laneSum w u = (lanes w n u).sum := by
  have := ofDigits_mod (2 ^ w - 1) (lanes w n u)
  rw [Nat.sub_add_cancel Nat.one_le_two_pow, ofDigits_lanes w n u hu, Nat.mod_eq_of_lt hs] at this
  unfold laneSum
  rw [pow2_eq]
  exact this

private theorem pack_unsigned (w : Nat) :
    ∀ xs : List Int, pack w xs (signed := false) = Nat.ofDigits (2 ^ w : Nat) (xs.map Int.toNat)
  | [] => rfl
  | x :: xs => by
      simp only [pack, Bool.cond_false, List.map_cons, Nat.ofDigits_cons, Nat.add_eq,
        pack_unsigned w xs]
      change (x + 0).toNat + (Nat.ofDigits (α := Nat) _ _ <<< w) = _
      rw [Int.add_zero, Nat.shiftLeft_eq, Nat.mul_comm]

private theorem map_toNat_natCast {xs : List Int} (hx : ∀ x ∈ xs, 0 ≤ x) :
    (xs.map Int.toNat).map Nat.cast = xs := by
  rw [List.map_map]
  conv => rhs; rw [← List.map_id xs]
  apply List.map_congr_left
  intro x hx'
  exact Int.toNat_of_nonneg (hx x hx')

/-- The lanes of an unsigned packed list are its entries, when they lie in `[0, 2 ^ w)`. -/
theorem lanes_pack {w : Nat} {xs : List Int} (hx : ∀ x ∈ xs, 0 ≤ x ∧ x < 2 ^ w) :
    lanes w xs.length (pack w xs (signed := false)) = xs.map Int.toNat := by
  rw [pack_unsigned]
  have := lanes_ofDigits w (xs.map Int.toNat) (by
    intro d hd
    simp only [List.mem_map] at hd
    obtain ⟨x, hx', rfl⟩ := hd
    have := hx x hx'
    have e := natCast_two_pow w
    omega)
  rwa [List.length_map] at this

/-- The product of two unsigned guarded rows. If the lanes of `u` are below `2 ^ gx`, those of `v`
below `2 ^ gy`, and `n * 2 ^ gx * (m * 2 ^ gy) < 2 ^ w`, then the product `u * v` holds the Cauchy
product of their lanes. -/
theorem lanes_mul {w gx gy n m u v : Nat} (hu : guard w gx n u (signed := false) = true)
    (hv : guard w gy m v (signed := false) = true) (hroom : n * 2 ^ gx * (m * 2 ^ gy) < 2 ^ w)
    (hn : 0 < n) (hm : 0 < m) :
    (lanes w (n + m - 1) (u * v)).map Nat.cast =
      conv ((lanes w n u).map Nat.cast) ((lanes w m v).map Nat.cast) := by
  obtain ⟨hu', hbu⟩ := lanes_lt_of_guard hu
  obtain ⟨hv', hbv⟩ := lanes_lt_of_guard hv
  have bound : ∀ {g k t : Nat}, (∀ d ∈ lanes w k t, d < 2 ^ g) →
      ∀ x ∈ (lanes w k t).map (Nat.cast : Nat → Int), -2 ^ g ≤ x ∧ x < 2 ^ g := by
    intro g k t hb x hx
    simp only [List.mem_map] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    have := hb d hd
    have e := natCast_two_pow g
    have : (0 : Int) < 2 ^ g := Int.pow_pos (by decide)
    constructor <;> omega
  have nonneg : ∀ {k t : Nat}, ∀ x ∈ (lanes w k t).map (Nat.cast : Nat → Int), 0 ≤ x := by
    intro k t x hx
    simp only [List.mem_map] at hx
    obtain ⟨d, _, rfl⟩ := hx
    omega
  generalize hX : (lanes w n u).map (Nat.cast : Nat → Int) = X at *
  generalize hY : (lanes w m v).map (Nat.cast : Nat → Int) = Y at *
  have hX0 : ∀ x ∈ X, 0 ≤ x := hX ▸ nonneg
  have hY0 : ∀ y ∈ Y, 0 ≤ y := hY ▸ nonneg
  have hc0 := nonneg_of_mem_conv hX0 hY0
  have hXlen : X.length = n := by rw [← hX, List.length_map, length_lanes]
  have hYlen : Y.length = m := by rw [← hY, List.length_map, length_lanes]
  have hl1 : l1 (conv X Y) < 2 ^ w := by
    have h1 := l1_le_of_bound (hX ▸ bound hbu)
    have h2 := l1_le_of_bound (hY ▸ bound hbv)
    rw [hXlen] at h1
    rw [hYlen] at h2
    have := l1_conv_le X Y
    have := Nat.mul_le_mul h1 h2
    omega
  have hlen : (conv X Y).length = n + m - 1 := by
    rw [length_conv (List.length_pos_iff.mp (by omega)) (List.length_pos_iff.mp (by omega)),
      hXlen, hYlen]
  have hc := map_toNat_natCast hc0
  have hval : Nat.ofDigits (2 ^ w : Nat) ((conv X Y).map Int.toNat) = u * v := by
    have := eval_natCast (2 ^ w) ((conv X Y).map Int.toNat)
    have eX : eval (2 ^ w) X = u := by rw [← hX]; exact eval_lanes hu'
    have eY : eval (2 ^ w) Y = v := by rw [← hY]; exact eval_lanes hv'
    rw [hc, natCast_two_pow, eval_conv, eX, eY] at this
    exact_mod_cast this.symm
  have hlt : ∀ d ∈ (conv X Y).map Int.toNat, d < 2 ^ w := by
    intro d hd
    simp only [List.mem_map] at hd
    obtain ⟨z, hz, rfl⟩ := hd
    have := natAbs_le_l1 hz
    have := hc0 z hz
    omega
  have := lanes_ofDigits w _ hlt
  rw [List.length_map, hlen, hval] at this
  rw [this, hc]

end FloatLib.Numerics.Packed
