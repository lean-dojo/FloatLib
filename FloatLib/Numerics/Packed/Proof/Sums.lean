/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Packed.Proof.Range
public import FloatLib.Numerics.Packed.Proof.Signed

/-!
# Sums and norms of packed rows

Masked remainders compute the sum of positive entries, the signed sum and the l1 norm. The
hypotheses state the headroom needed to prevent modular wraparound, either for an explicit list or
for a guarded stored row.
-/

@[expose] public section

namespace FloatLib.Numerics.Packed

private theorem ub_land_top {w : Nat} (hw : 1 ≤ w) {x : Int} (hx : x.natAbs < 2 ^ (w - 1)) :
    ub w x &&& 2 ^ (w - 1) = 2 ^ (w - 1) * (ub w x / 2 ^ (w - 1)) :=
  land_top (w - 1) _ (by rw [Nat.sub_add_cancel hw]; exact ub_lt hw (fits_of_natAbs hx))

private theorem ub_land_low {w : Nat} {x : Int} (hx : x.natAbs < 2 ^ (w - 1)) :
    ub w x &&& (ub w x / 2 ^ (w - 1) * (2 ^ (w - 1) - 1)) = x.toNat := by
  have hpos := Nat.two_pow_pos (w - 1)
  have e := natCast_two_pow (w - 1)
  by_cases hs : 0 ≤ x
  · have hu : ub w x = x.toNat + 2 ^ (w - 1) * 1 := by simp only [ub]; omega
    have hq : ub w x / 2 ^ (w - 1) = 1 := by
      rw [hu, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt (by omega)]
    rw [hq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod, hu, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by omega)]
  · have hq : ub w x / 2 ^ (w - 1) = 0 := Nat.div_eq_of_lt (by simp only [ub]; omega)
    rw [hq, Nat.zero_mul, Nat.and_zero]; omega

private theorem posSum_len {w : Nat} (hw : 1 ≤ w) (xs : List Int)
    (hx : ∀ x ∈ xs, x.natAbs < 2 ^ (w - 1))
    (hs : (xs.map Int.toNat).sum < 2 ^ w - 1) :
    posSum w xs.length (eval (2 ^ w) xs) = (xs.map Int.toNat).sum := by
  have hfit : ∀ x ∈ xs, Fits w x := fun x h => fits_of_natAbs (hx x h)
  have hub : ∀ x ∈ xs, ub w x < 2 ^ w := fun x h => ub_lt hw (hfit x h)
  have hpos := Nat.two_pow_pos (w - 1)
  have h2 : 2 ^ w = 2 ^ (w - 1) * 2 := by rw [← Nat.pow_succ]; congr 1; omega
  have hcst : List.replicate xs.length (2 ^ (w - 1)) = xs.map fun _ => 2 ^ (w - 1) :=
    List.map_const'.symm
  simp only [posSum, laneSum, ofInt_eval_aux hw xs hfit, pow2_eq, Nat.sub_eq, Nat.mul_eq,
    bias_eq_ofDigits w _ hw]
  change (Nat.ofDigits (2 ^ w : Nat) (xs.map (ub w)) &&&
      ((Nat.ofDigits (2 ^ w : Nat) (xs.map (ub w)) &&&
          Nat.ofDigits (2 ^ w : Nat) (List.replicate xs.length (2 ^ (w - 1))))
        >>> (w - 1) * (2 ^ (w - 1) - 1))) % (2 ^ w - 1) = _
  -- the first mask keeps the sign bit of every lane, which is set exactly for `x ≥ 0`
  rw [hcst, land_ofDigits_map w _ _ xs hub (fun _ _ => by omega)]
  have e1 : (xs.map fun x => ub w x &&& 2 ^ (w - 1)) =
      xs.map fun x => 2 ^ (w - 1) * (ub w x / 2 ^ (w - 1)) :=
    List.map_congr_left (fun x hx' => ub_land_top hw (hx x hx'))
  rw [e1, ofDigits_map_mul, Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel_left _ hpos,
    ← ofDigits_map_mul_right, land_ofDigits_map w _ _ xs hub]
  -- shifted down and spread over the low bits, the sign bits keep `x` where `x ≥ 0` and clear
  -- the lane otherwise, and one remainder adds up what is left
  · have e2 : (xs.map fun x => ub w x &&& (ub w x / 2 ^ (w - 1) * (2 ^ (w - 1) - 1))) =
        xs.map Int.toNat :=
      List.map_congr_left (fun x hx' => ub_land_low (hx x hx'))
    rw [e2]
    have := ofDigits_mod (2 ^ w - 1) (xs.map Int.toNat)
    rw [Nat.sub_add_cancel Nat.one_le_two_pow] at this
    rw [this, Nat.mod_eq_of_lt hs]
  · intro x hx'
    have hq : ub w x / 2 ^ (w - 1) < 2 := by
      rw [Nat.div_lt_iff_lt_mul hpos]; have := hub x hx'; omega
    have hc : ub w x / 2 ^ (w - 1) = 0 ∨ ub w x / 2 ^ (w - 1) = 1 := by
      generalize ub w x / 2 ^ (w - 1) = q at hq; omega
    rcases hc with h | h <;> rw [h] <;> omega

private theorem sum_toNat_append_zeros (xs : List Int) (k : Nat) :
    ((xs ++ List.replicate k 0).map Int.toNat).sum = (xs.map Int.toNat).sum := by
  simp

/-- One masked remainder computes the sum of the positive entries of a row whose entries fit, when
that sum is below `2 ^ w - 1`. -/
theorem posSum_eval {w n : Nat} (hw : 1 ≤ w) {xs : List Int} (hn : xs.length ≤ n)
    (hx : ∀ x ∈ xs, x.natAbs < 2 ^ (w - 1)) (hs : (xs.map Int.toNat).sum < 2 ^ w - 1) :
    posSum w n (eval (2 ^ w) xs) = (xs.map Int.toNat).sum := by
  have hlen : (xs ++ List.replicate (n - xs.length) 0).length = n := by
    simp only [List.length_append, List.length_replicate]; omega
  have hp : ∀ x ∈ xs ++ List.replicate (n - xs.length) 0, x.natAbs < 2 ^ (w - 1) := by
    intro x h
    rcases List.mem_append.mp h with h | h
    · exact hx x h
    · rw [List.eq_of_mem_replicate h]; exact Nat.two_pow_pos _
  have hz : eval (2 ^ w) xs = eval (2 ^ w) (xs ++ List.replicate (n - xs.length) 0) := by
    simp [eval_append]
  rw [hz, ← sum_toNat_append_zeros xs (n - xs.length)]
  rw [← sum_toNat_append_zeros xs (n - xs.length)] at hs
  generalize xs ++ List.replicate (n - xs.length) 0 = ys at hp hlen hs ⊢
  subst hlen
  exact posSum_len hw ys hp hs

private theorem sum_toNat_le_l1 : ∀ xs : List Int, (xs.map Int.toNat).sum ≤ l1 xs
  | [] => by simp [l1]
  | x :: xs => by
      have := sum_toNat_le_l1 xs
      simp only [List.map_cons, List.sum_cons, l1_cons]; omega

private theorem sum_toNat_add (xs : List Int) :
    (xs.map Int.toNat).sum + ((xs.map (fun x => -x)).map Int.toNat).sum = l1 xs := by
  induction xs with
  | nil => simp [l1]
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, l1_cons]; omega

private theorem sum_toNat_sub (xs : List Int) :
    ((xs.map Int.toNat).sum : Int) - ((xs.map (fun x => -x)).map Int.toNat).sum = xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, Int.natCast_add] at *; omega

private theorem posSum_pair {w n : Nat} (hw : 1 ≤ w) {xs : List Int} (hn : xs.length ≤ n)
    (hl : l1 xs < 2 ^ (w - 1)) :
    posSum w n (eval (2 ^ w) xs) = (xs.map Int.toNat).sum ∧
      posSum w n (Int.neg (eval (2 ^ w) xs)) = ((xs.map (fun x => -x)).map Int.toNat).sum := by
  have hx : ∀ x ∈ xs, x.natAbs < 2 ^ (w - 1) := fun x h => Nat.lt_of_le_of_lt (natAbs_le_l1 h) hl
  have h2 : 2 ^ (w - 1) ≤ 2 ^ w - 1 := by
    have : 2 ^ w = 2 ^ (w - 1) * 2 := by rw [← Nat.pow_succ]; congr 1; omega
    have := Nat.two_pow_pos (w - 1); omega
  have hxn : ∀ x ∈ xs.map (fun x => -x), x.natAbs < 2 ^ (w - 1) := by
    intro y hy; simp only [List.mem_map] at hy
    obtain ⟨x, hx', rfl⟩ := hy; simpa using hx x hx'
  have hsum := sum_toNat_add xs
  constructor
  · exact posSum_eval hw hn hx (by have := sum_toNat_le_l1 xs; omega)
  · rw [show Int.neg (eval (2 ^ w) xs) = -eval (2 ^ w) xs from rfl, neg_eval]
    exact posSum_eval hw (by simpa using hn) hxn (by omega)

/-- Two masked remainders compute the `l1` norm of a row whose `l1` norm is below `2 ^ (w - 1)`. -/
theorem absSum_eval {w n : Nat} (hw : 1 ≤ w) {xs : List Int} (hn : xs.length ≤ n)
    (hl : l1 xs < 2 ^ (w - 1)) : absSum w n (eval (2 ^ w) xs) = l1 xs := by
  obtain ⟨h1, h2⟩ := posSum_pair hw hn hl
  simp only [absSum, Nat.add_eq, Kernel.Z.neg_eq_core, h1, h2]
  exact sum_toNat_add xs

/-- Two masked remainders compute the sum of the entries of a row whose `l1` norm is below
`2 ^ (w - 1)`. -/
theorem sum_eval {w n : Nat} (hw : 1 ≤ w) {xs : List Int} (hn : xs.length ≤ n)
    (hl : l1 xs < 2 ^ (w - 1)) : sum w n (eval (2 ^ w) xs) = xs.sum := by
  obtain ⟨h1, h2⟩ := posSum_pair hw hn hl
  simp only [sum, Kernel.Z.subNat_eq, Kernel.Z.neg_eq_core, h1, h2]
  exact sum_toNat_sub xs

/-- The `l1` norm of a guarded row by two masked remainders, when `n * 2 ^ g < 2 ^ (w - 1)`. -/
theorem absSum_toInt {w g n u : Nat} (hu : guard w g n u = true) (hroom : n * 2 ^ g < 2 ^ (w - 1)) :
    absSum w n (toInt w n u) = l1 (entries w n u) := by
  obtain ⟨hgw, hu', hbu⟩ := guard_sound hu
  have hw : 1 ≤ w := by omega
  have h1 := l1_le_of_bound hbu
  rw [length_entries] at h1
  rw [← eval_entries hw hu', absSum_eval hw (Nat.le_of_eq (length_entries w n u)) (by omega)]

/-- The sum of a guarded row by two masked remainders, when `n * 2 ^ g < 2 ^ (w - 1)`. -/
theorem sum_toInt {w g n u : Nat} (hu : guard w g n u = true) (hroom : n * 2 ^ g < 2 ^ (w - 1)) :
    sum w n (toInt w n u) = (entries w n u).sum := by
  obtain ⟨hgw, hu', hbu⟩ := guard_sound hu
  have hw : 1 ≤ w := by omega
  have h1 := l1_le_of_bound hbu
  rw [length_entries] at h1
  rw [← eval_entries hw hu', sum_eval hw (Nat.le_of_eq (length_entries w n u)) (by omega)]

end FloatLib.Numerics.Packed
