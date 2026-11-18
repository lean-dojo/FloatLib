/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Packed.Proof.Digits

/-!
# Signed entries of biased packed rows

Biasing each signed entry gives a natural digit. Evaluation and extraction are inverse when the
entries fit; padding preserves the row's value, and the executable packer produces the same code.
-/

@[expose] public section

namespace FloatLib.Numerics.Packed

private theorem eval_map_sub (w : Nat) (c : Int) : ∀ ds : List Nat,
    eval (2 ^ w) (ds.map fun (d : Nat) => (d : Int) - c) =
      ((Nat.ofDigits (2 ^ w) ds : Nat) : Int) -
        c * ((Nat.ofDigits (2 ^ w) (List.replicate ds.length 1) : Nat) : Int)
  | [] => by simp [eval]
  | d :: ds => by
      have ih := eval_map_sub w c ds
      simp only [List.map_cons, eval, ih, Nat.ofDigits_cons, List.length_cons, List.replicate_succ,
        Int.natCast_add,
        Int.natCast_mul, Int.natCast_pow, Int.cast_ofNat_Int]
      grind

/-- The biased lane of `x`. -/
def ub (w : Nat) (x : Int) : Nat := (x + 2 ^ (w - 1)).toNat

/-- Biasing a signed value that fits produces a digit below the lane radix. -/
theorem ub_lt {w : Nat} (hw : 1 ≤ w) {x : Int} (hx : Fits w x) : ub w x < 2 ^ w := by
  have h2 := two_pow_pred hw
  have : ((ub w x : Nat) : Int) < (2 ^ w : Nat) := by
    rw [natCast_two_pow, h2]; simp only [ub, Fits] at *; omega
  exact_mod_cast this

private theorem ub_sub {w : Nat} {x : Int} (hx : Fits w x) : (ub w x : Int) - 2 ^ (w - 1) = x := by
  simp only [ub, Fits] at *; omega

private theorem ofDigits_ub (w : Nat) : ∀ xs : List Int, (∀ x ∈ xs, Fits w x) →
    ((Nat.ofDigits (2 ^ w) (xs.map (ub w)) : Nat) : Int) =
      eval (2 ^ w) xs +
        ((Nat.ofDigits (2 ^ w) (List.replicate xs.length (2 ^ (w - 1))) : Nat) : Int)
  | [], _ => by simp [eval]
  | x :: xs, h => by
      have ih := ofDigits_ub w xs (fun y hy => h y (by simp [hy]))
      have hx := ub_sub (h x (by simp))
      simp only [List.map_cons, Nat.ofDigits_cons, eval, List.length_cons, List.replicate_succ,
        Int.natCast_add, Int.natCast_mul, Int.natCast_pow, ih]
      push_cast at hx ⊢
      grind

/-- The value of the signed entries of a biased row below `2 ^ (w * n)` is the row's integer. -/
theorem eval_entries {w n u : Nat} (hw : 1 ≤ w) (hu : u < 2 ^ (w * n)) :
    eval (2 ^ w) (entries w n u) = toInt w n u := by
  rw [entries_eq_lanes, eval_map_sub, ofDigits_lanes w n u hu, length_lanes, toInt_eq,
    bias_eq_ofDigits w n hw,
    ofDigits_replicate (2 ^ w) (2 ^ (w - 1))]
  push_cast; rfl

/-- Encoding the value of a fitting signed list gives the Horner value of its biased digits. -/
theorem ofInt_eval_aux {w : Nat} (hw : 1 ≤ w) (xs : List Int) (hx : ∀ x ∈ xs, Fits w x) :
    ofInt w xs.length (eval (2 ^ w) xs) = Nat.ofDigits (2 ^ w : Nat) (xs.map (ub w)) := by
  have := ofDigits_ub w xs hx
  rw [ofInt_eq, bias_eq_ofDigits w _ hw]
  omega

private theorem pad_fits {w : Nat} {xs : List Int} (hx : ∀ x ∈ xs, Fits w x) (k : Nat) :
    ∀ x ∈ xs ++ List.replicate k 0, Fits w x := by
  intro x h
  rcases List.mem_append.mp h with h | h
  · exact hx x h
  · rw [List.eq_of_mem_replicate h]
    have : (0 : Int) < 2 ^ (w - 1) := Int.pow_pos (by decide)
    constructor <;> omega

private theorem entries_ofInt_eval_len {w : Nat} (hw : 1 ≤ w) (ys : List Int)
    (hy : ∀ y ∈ ys, Fits w y) :
    entries w ys.length (ofInt w ys.length (eval (2 ^ w) ys)) = ys ∧
      ofInt w ys.length (eval (2 ^ w) ys) < 2 ^ (w * ys.length) := by
  have hub : ∀ d ∈ ys.map (ub w), d < 2 ^ w := by
    intro d hd
    simp only [List.mem_map] at hd
    obtain ⟨y, hy', rfl⟩ := hd
    exact ub_lt hw (hy y hy')
  rw [ofInt_eval_aux hw _ hy]
  constructor
  · rw [entries_eq_lanes]
    have := lanes_ofDigits w _ hub
    rw [List.length_map] at this
    rw [this, List.map_map]
    conv => rhs; rw [← List.map_id ys]
    apply List.map_congr_left
    intro y hy'
    exact ub_sub (hy y hy')
  · have := ofDigits_lt w _ hub
    rwa [List.length_map] at this

private theorem pad_spec {w n : Nat} (hw : 1 ≤ w) {xs : List Int} (hn : xs.length ≤ n)
    (hx : ∀ x ∈ xs, Fits w x) :
    entries w n (ofInt w n (eval (2 ^ w) xs)) = xs ++ List.replicate (n - xs.length) 0 ∧
      ofInt w n (eval (2 ^ w) xs) < 2 ^ (w * n) := by
  have hp := pad_fits hx (n - xs.length)
  have hlen : (xs ++ List.replicate (n - xs.length) 0).length = n := by
    simp only [List.length_append, List.length_replicate]; omega
  have hz : eval (2 ^ w) xs = eval (2 ^ w) (xs ++ List.replicate (n - xs.length) 0) := by
    simp [eval_append]
  rw [hz]
  generalize xs ++ List.replicate (n - xs.length) 0 = ys at hp hlen ⊢
  subst hlen
  exact entries_ofInt_eval_len hw ys hp

/-- Reading back the signed entries of a row whose entries fit gives the row, padded with zeros to
`n` entries. -/
theorem entries_ofInt_eval {w n : Nat} (hw : 1 ≤ w) {xs : List Int} (hn : xs.length ≤ n)
    (hx : ∀ x ∈ xs, Fits w x) :
    entries w n (ofInt w n (eval (2 ^ w) xs)) = xs ++ List.replicate (n - xs.length) 0 :=
  (pad_spec hw hn hx).1

/-- A row whose entries fit has a biased row below `2 ^ (w * n)`. -/
theorem ofInt_eval_lt {w n : Nat} (hw : 1 ≤ w) {xs : List Int} (hn : xs.length ≤ n)
    (hx : ∀ x ∈ xs, Fits w x) : ofInt w n (eval (2 ^ w) xs) < 2 ^ (w * n) :=
  (pad_spec hw hn hx).2

/-- One entry of a row whose entries fit: entry `k` of its biased row of `n` lanes is
`xs.getD k 0`. -/
theorem entry_ofInt_eval {w n k : Nat} (hw : 1 ≤ w) {xs : List Int} (hn : xs.length ≤ n)
    (hk : k < n)
    (hx : ∀ x ∈ xs, Fits w x) : entry w k (ofInt w n (eval (2 ^ w) xs)) = xs.getD k 0 := by
  have h := entries_ofInt_eval hw hn hx
  have hk' : k < (entries w n (ofInt w n (eval (2 ^ w) xs))).length := by
    rw [length_entries]; exact hk
  rw [← getElem_entries hk', List.getElem_of_eq h, List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_ge k xs.length with hlt | hge
  · rw [List.getElem_append_left hlt, List.getElem?_eq_getElem hlt]; rfl
  · rw [List.getElem_append_right hge, List.getElem_replicate, List.getElem?_eq_none hge]; rfl

private theorem pack_eq_ofDigits (w : Nat) :
    ∀ xs : List Int, pack w xs = Nat.ofDigits (2 ^ w : Nat) (xs.map (ub w))
  | [] => rfl
  | x :: xs => by
      simp only [pack, Bool.cond_true, List.map_cons, Nat.ofDigits_cons, ub, pow2_eq,
        Nat.add_eq, Nat.sub_eq,
        pack_eq_ofDigits w xs, Int.ofNat_eq_natCast, Int.add_def, natCast_two_pow]
      change _ + (Nat.ofDigits (α := Nat) _ _ <<< w) = _
      rw [Nat.shiftLeft_eq, Nat.mul_comm]

/-- Packing a list whose entries fit is the biased row of its value. -/
theorem pack_eq_ofInt {w : Nat} (hw : 1 ≤ w) {xs : List Int} (hx : ∀ x ∈ xs, Fits w x) :
    pack w xs = ofInt w xs.length (eval (2 ^ w) xs) := by
  rw [pack_eq_ofDigits, ofInt_eval_aux hw xs hx]

/-- An absolute value below the signed half-range implies that the value fits. -/
theorem fits_of_natAbs {w : Nat} {x : Int} (hx : x.natAbs < 2 ^ (w - 1)) : Fits w x := by
  have e := natCast_two_pow (w - 1)
  constructor <;> omega

end FloatLib.Numerics.Packed
