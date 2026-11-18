/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Packed.Proof.Signed

/-!
# Reversal of packed rows

The divide-and-conquer reversal program reverses fixed-width lanes and biased signed entries. Its
output fits the same storage width, including empty and one-entry rows.
-/

@[expose] public section

namespace FloatLib.Numerics.Packed

private theorem reverse_of_length_le_one : ∀ {l : List Nat}, l.length ≤ 1 → l.reverse = l
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: _ :: _, h => by simp at h

private theorem revAux_spec (w : Nat) : ∀ d n u, n ≤ d →
    lanes w n (revAux w d n u) = (lanes w n u).reverse ∧ revAux w d n u < 2 ^ (w * n)
  | 0, n, u, h => by
      have : n = 0 := by omega
      subst this; simp [revAux, lanes]
  | d + 1, n, u, hnd => by
      by_cases hn : n ≤ 1
      · have hb : Nat.ble n 1 = true := Nat.ble_eq.mpr hn
        simp only [revAux, hb, Bool.cond_true, pow2_eq, Nat.mul_eq, Nat.sub_eq]
        change lanes w n (u &&& 2 ^ (w * n) - 1) = _ ∧ (u &&& 2 ^ (w * n) - 1) < _
        rw [Nat.and_two_pow_sub_one_eq_mod, lanes_mod]
        exact ⟨(reverse_of_length_le_one (by rw [length_lanes]; exact hn)).symm,
          Nat.mod_lt _ (Nat.two_pow_pos _)⟩
      · have hb : Nat.ble n 1 = false :=
          Bool.eq_false_iff.mpr (fun h' => hn (Nat.le_of_ble_eq_true h'))
        simp only [revAux, hb, Bool.cond_false, pow2_eq]
        change lanes w n
            ((revAux w d (n / 2) (u &&& 2 ^ (w * (n / 2)) - 1) <<< (w * (n - n / 2))) |||
              revAux w d (n - n / 2) (u >>> (w * (n / 2)))) = _ ∧
          ((revAux w d (n / 2) (u &&& 2 ^ (w * (n / 2)) - 1) <<< (w * (n - n / 2))) |||
            revAux w d (n - n / 2) (u >>> (w * (n / 2)))) < _
        rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
        have hh1 : n / 2 ≤ d := by omega
        have hr1 : n - n / 2 ≤ d := by omega
        have hhn : n / 2 ≤ n := Nat.div_le_self n 2
        generalize n / 2 = h at hh1 hr1 hhn ⊢
        obtain ⟨r, rfl⟩ : ∃ r, n = r + h := ⟨n - h, by omega⟩
        rw [Nat.add_sub_cancel] at hr1 ⊢
        obtain ⟨hA, hA'⟩ := revAux_spec w d h (u % 2 ^ (w * h)) hh1
        obtain ⟨hB, hB'⟩ := revAux_spec w d r (u / 2 ^ (w * h)) hr1
        generalize revAux w d h (u % 2 ^ (w * h)) = A at hA hA'
        generalize revAux w d r (u / 2 ^ (w * h)) = B at hB hB'
        -- the two halves occupy disjoint lanes, so the disjunction is a sum, and reversing a
        -- row is reversing each half and swapping them
        rw [← Nat.shiftLeft_add_eq_or_of_lt hB', Nat.shiftLeft_eq, Nat.add_comm (A * _) B,
          Nat.mul_comm A]
        constructor
        · rw [lanes_append w r h hB' A, hA, hB, ← List.reverse_append, Nat.add_comm r h,
            lanes_split w h r u]
        · rw [Nat.mul_add, Nat.pow_add]
          have : A + 1 ≤ 2 ^ (w * h) := hA'
          have := Nat.mul_le_mul_left (2 ^ (w * r)) this
          rw [Nat.mul_succ] at this
          have e := Nat.mul_comm (2 ^ (w * r)) (2 ^ (w * h))
          omega

private theorem lanes_rev_spec (w n u : Nat) :
    lanes w n (rev w n u) = (lanes w n u).reverse ∧ rev w n u < 2 ^ (w * n) :=
  revAux_spec w n n u (Nat.le_refl n)

/-- The lanes of `rev w n u` are the lanes of `u` in reverse order. -/
theorem lanes_rev (w n u : Nat) : lanes w n (rev w n u) = (lanes w n u).reverse :=
  (lanes_rev_spec w n u).1

/-- The entries of `rev w n u` are the entries of `u` in reverse order. -/
theorem entries_rev (w n u : Nat) : entries w n (rev w n u) = (entries w n u).reverse := by
  rw [entries_eq_lanes, entries_eq_lanes, (lanes_rev_spec w n u).1, List.map_reverse]

/-- A reversed row has no lanes beyond `n`. -/
theorem rev_lt (w n u : Nat) : rev w n u < 2 ^ (w * n) := (lanes_rev_spec w n u).2

/-- The autocorrelation is one Kronecker product: the row `x ⋆ reverse x` of the entries `x`. -/
theorem autocorr_eq {w n u : Nat} (hw : 1 ≤ w) (hu : u < 2 ^ (w * n)) :
    autocorr w n u = eval (2 ^ w) (conv (entries w n u) (entries w n u).reverse) := by
  rw [eval_conv, ← entries_rev, eval_entries hw hu, eval_entries hw (rev_lt w n u)]
  exact Kernel.Z.mul_eq _ _

end FloatLib.Numerics.Packed
