/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.ZProof
public import FloatLib.Numerics.Packed.Matrix
public import FloatLib.Numerics.Packed.Proof.Products
public import FloatLib.Numerics.Packed.Proof.Sums
public import FloatLib.Numerics.Packed.Proof.Unsigned

/-!
# Soundness of the packed matrix product check

* `eval_outer`: the value of an outer product is the product of the values, the second one in
  the base raised to the length of the column. This is Kronecker substitution in two variables.
* `eval_sumRows`: the value of a sum of rows is the sum of their values.
* `length_eq_of_matMulCheck`: a passing `matMulCheck` has as many columns as rows.
* `entries_matMul`: after a passing `matMulCheck`, the entries of the product row are the entries
  of `colRowProduct` of the entries of the columns and rows, padded with zeros to `n * p` (the
  padding is the whole row when there is no column). It holds for all sizes, lane widths and data.
-/

@[expose] public section

namespace FloatLib.Numerics.Packed

open FloatLib.Numerics.Kernel

/-- An outer product has one copy of the column for each entry of the row. -/
theorem length_outer (xs : List Int) : ∀ ys : List Int,
    (outer xs ys).length = ys.length * xs.length
  | [] => by simp [outer]
  | y :: ys => by
    have ih := length_outer xs ys
    simp only [outer, List.map_cons, List.flatten_cons, List.length_append, List.length_cons,
      smul, List.length_map] at ih ⊢
    rw [ih]
    rw [add_mul]; ac_rfl

/-- The value of an outer product is the product of the values, with the row read in the base
raised to the length of the column. -/
theorem eval_outer (b : Int) (xs : List Int) : ∀ ys : List Int,
    eval b (outer xs ys) = eval b xs * eval (b ^ xs.length) ys
  | [] => by simp [outer, eval]
  | y :: ys => by
    have ih := eval_outer b xs ys
    simp only [outer, List.map_cons, List.flatten_cons] at ih ⊢
    rw [eval_append, eval_smul, ih, eval]
    simp only [smul, List.length_map]
    rw [mul_add]; ac_rfl

/-- The value of a sum of rows is the sum of their values. -/
theorem eval_sumRows (b : Int) : ∀ rows : List (List Int),
    eval b (sumRows rows) = (rows.map (eval b)).sum
  | [] => by simp [sumRows, eval]
  | row :: rows => by
    simp only [sumRows, eval_add, eval_sumRows b rows, List.map_cons, List.sum_cons]

private theorem natAbs_le_of_mem_add {P Q : Nat} : ∀ {xs ys : List Int},
    (∀ x ∈ xs, x.natAbs ≤ P) → (∀ y ∈ ys, y.natAbs ≤ Q) → ∀ z ∈ add xs ys, z.natAbs ≤ P + Q
  | [], ys, _, hy => fun z hz => by
    have := hy z (by simpa [add] using hz)
    omega
  | x :: xs, [], hx, _ => fun z hz => by
    have := hx z (by simpa [add] using hz)
    omega
  | x :: xs, y :: ys, hx, hy => fun z hz => by
    simp only [add, List.mem_cons] at hz
    rcases hz with rfl | hz
    · have h1 := hx x (by simp)
      have h2 := hy y (by simp)
      have := Int.natAbs_add_le x y
      omega
    · exact natAbs_le_of_mem_add (fun a ha => hx a (by simp [ha])) (fun a ha => hy a (by simp [ha]))
        z hz

private theorem natAbs_le_of_mem_outer {P Q : Nat} {xs ys : List Int}
    (hx : ∀ x ∈ xs, x.natAbs ≤ P) (hy : ∀ y ∈ ys, y.natAbs ≤ Q) :
    ∀ z ∈ outer xs ys, z.natAbs ≤ P * Q := by
  intro z hz
  simp only [outer, List.mem_flatten, List.mem_map, smul] at hz
  obtain ⟨_, ⟨y, hy', rfl⟩, hz⟩ := hz
  simp only [List.mem_map] at hz
  obtain ⟨x, hx', rfl⟩ := hz
  rw [Int.natAbs_mul, Nat.mul_comm]
  exact Nat.mul_le_mul (hx x hx') (hy y hy')

/-- Every entry of a matrix product is at most the number of columns times the product of the
bounds of the two matrices. -/
theorem natAbs_le_of_mem_colRowProduct {P Q : Nat} : ∀ {cols rows : List (List Int)},
    (∀ c ∈ cols, ∀ x ∈ c, x.natAbs ≤ P) → (∀ r ∈ rows, ∀ y ∈ r, y.natAbs ≤ Q) →
      ∀ z ∈ colRowProduct cols rows, z.natAbs ≤ cols.length * (P * Q)
  | [], _, _, _ => fun z hz => by simp [colRowProduct, sumRows] at hz
  | _ :: _, [], _, _ => fun z hz => by simp [colRowProduct, sumRows] at hz
  | c :: cols, r :: rows, hc, hr => fun z hz => by
    have ih := natAbs_le_of_mem_colRowProduct (cols := cols) (rows := rows)
      (fun a ha => hc a (by simp [ha])) (fun a ha => hr a (by simp [ha]))
    have hhead := natAbs_le_of_mem_outer (hc c (by simp)) (hr r (by simp))
    simp only [colRowProduct, List.zipWith_cons_cons, sumRows] at hz
    have := natAbs_le_of_mem_add hhead ih z hz
    simp only [List.length_cons]
    rw [Nat.succ_mul]
    omega

/-- A matrix product of columns with `n` entries and rows with `p` entries has at most `n * p`
entries. -/
theorem length_colRowProduct_le {n p : Nat} : ∀ {cols rows : List (List Int)},
    (∀ c ∈ cols, c.length = n) → (∀ r ∈ rows, r.length = p) →
      (colRowProduct cols rows).length ≤ n * p
  | [], _, _, _ => by simp [colRowProduct, sumRows]
  | _ :: _, [], _, _ => by simp [colRowProduct, sumRows]
  | c :: cols, r :: rows, hc, hr => by
    have ih := length_colRowProduct_le (cols := cols) (rows := rows)
      (fun a ha => hc a (by simp [ha])) (fun a ha => hr a (by simp [ha]))
    simp only [colRowProduct, List.zipWith_cons_cons, sumRows, length_add, length_outer,
      hc c (by simp), hr r (by simp)] at ih ⊢
    rw [Nat.mul_comm p n]
    exact max_le le_rfl ih

private theorem count_eq (us : List Nat) : count us = us.length := by
  induction us with
  | nil => rfl
  | cons u us ih =>
    change Nat.succ (count us) = _
    rw [ih, List.length_cons]

private theorem guardAll_iff (w g n : Nat) (us : List Nat) :
    guardAll w g n us = true ↔ ∀ u ∈ us, guard w g n u = true := by
  induction us with
  | nil => simp [guardAll]
  | cons u us ih =>
    change Bool.and (guard w g n u) (guardAll w g n us) = true ↔ _
    rw [Bool.and_eq_true, ih]
    simp

private theorem outerSum_eq (w n v p : Nat) : ∀ cols rows : List Nat,
    outerSum w n v p cols rows =
      (List.zipWith (fun c r => toInt w n c * toInt v p r) cols rows).sum
  | [], _ => by simp [outerSum]
  | _ :: _, [] => by simp [outerSum]
  | c :: cols, r :: rows => by
    have ih := outerSum_eq w n v p cols rows
    change Z.add (Z.mul (Z.subNat c (bias w n)) (Z.subNat r (bias v p)))
      (outerSum w n v p cols rows) = _
    rw [Z.add_eq, Z.mul_eq, Z.subNat_eq, Z.subNat_eq, ih, List.zipWith_cons_cons, List.sum_cons,
      toInt_eq, toInt_eq]

/-- The sum of the products of the integers of guarded columns and rows is the value of their
matrix product. -/
private theorem sum_toInt_eq_eval {w n p gA gB : Nat} (hw : 1 ≤ w) (hwn : 1 ≤ w * n) :
    ∀ {cols rows : List Nat}, (∀ c ∈ cols, guard w gA n c = true) →
      (∀ r ∈ rows, guard (w * n) gB p r = true) →
      (List.zipWith (fun c r => toInt w n c * toInt (w * n) p r) cols rows).sum =
        eval (2 ^ w) (colRowProduct (cols.map (entries w n)) (rows.map (entries (w * n) p)))
  | [], _, _, _ => by simp [colRowProduct, sumRows, eval]
  | _ :: _, [], _, _ => by simp [colRowProduct, sumRows, eval]
  | c :: cols, r :: rows, hc, hr => by
    have ih := sum_toInt_eq_eval hw hwn (cols := cols) (rows := rows)
      (fun a ha => hc a (by simp [ha])) (fun a ha => hr a (by simp [ha]))
    obtain ⟨-, hcu, -⟩ := guard_sound (hc c (by simp))
    obtain ⟨-, hru, -⟩ := guard_sound (hr r (by simp))
    simp only [List.zipWith_cons_cons, List.sum_cons, List.map_cons, colRowProduct, sumRows,
      eval_add] at ih ⊢
    rw [ih, eval_outer, length_entries, ← Int.pow_mul, eval_entries hw hcu, eval_entries hwn hru]

/-- A passing `matMulCheck` has matching inner dimensions: as many columns of `A` as rows of
`B`. -/
theorem length_eq_of_matMulCheck {w gA gB n p : Nat} {cols rows : List Nat} {prod : Nat}
    (h : matMulCheck w gA gB n p cols rows prod = true) : cols.length = rows.length := by
  unfold matMulCheck at h
  rw [Bool.and_eq_true, Nat.beq_eq, count_eq, count_eq] at h
  exact h.1

/--
After a passing `matMulCheck`, the product row holds the matrix product: its `n * p` entries are
the entries of `colRowProduct` of the entries of the columns and of the rows, followed by zeros
when there are fewer, which happens only without columns. Entry `i + n * j` is
`∑ k, A[i][k] * B[k][j]`, over the common number of columns of `A` and rows of `B`
(`length_eq_of_matMulCheck`).
-/
theorem entries_matMul {w gA gB n p : Nat} {cols rows : List Nat} {prod : Nat}
    (h : matMulCheck w gA gB n p cols rows prod = true) (hw : 1 ≤ w) (hn : 1 ≤ n) :
    entries w (n * p) prod =
      colRowProduct (cols.map (entries w n)) (rows.map (entries (w * n) p)) ++
        List.replicate
          (n * p - (colRowProduct (cols.map (entries w n)) (rows.map (entries (w * n) p))).length)
          0 := by
  unfold matMulCheck at h
  simp only [Bool.and_eq_true, guardAll_iff, Nat.ble_eq, Int.beq'_eq, Z.subNat_eq, pow2_eq,
    Nat.mul_eq, Nat.sub_eq, Nat.succ_eq_add_one, count_eq] at h
  obtain ⟨-, hcols, hrows, hroom, hsum⟩ := h
  have hwn : 1 ≤ w * n := Nat.mul_pos hw hn
  set L := colRowProduct (cols.map (entries w n)) (rows.map (entries (w * n) p))
  -- the integer of the product row is the value of the matrix product
  have hval : toInt w (n * p) prod = eval (2 ^ w) L := by
    rw [toInt_eq, hsum, outerSum_eq, sum_toInt_eq_eval hw hwn hcols hrows]
  -- every entry of the matrix product fits a lane
  have hA : ∀ c ∈ cols.map (entries w n), ∀ x ∈ c, x.natAbs ≤ 2 ^ gA := by
    intro c hc x hx
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hc
    obtain ⟨-, -, hb⟩ := guard_sound (hcols u hu)
    have := hb x hx
    have e := natCast_two_pow gA
    omega
  have hB : ∀ r ∈ rows.map (entries (w * n) p), ∀ y ∈ r, y.natAbs ≤ 2 ^ gB := by
    intro r hr y hy
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hr
    obtain ⟨-, -, hb⟩ := guard_sound (hrows u hu)
    have := hb y hy
    have e := natCast_two_pow gB
    omega
  have hfits : ∀ z ∈ L, Fits w z := by
    intro z hz
    have hz' := natAbs_le_of_mem_colRowProduct hA hB z hz
    rw [List.length_map] at hz'
    have e := natCast_two_pow (w - 1)
    constructor <;> omega
  have hlen : L.length ≤ n * p :=
    length_colRowProduct_le (fun c hc => by
      obtain ⟨u, -, rfl⟩ := List.mem_map.1 hc
      exact length_entries w n u) (fun r hr => by
      obtain ⟨u, -, rfl⟩ := List.mem_map.1 hr
      exact length_entries (w * n) p u)
  have hback : ofInt w (n * p) (toInt w (n * p) prod) = prod := by
    rw [ofInt_eq, toInt_eq]
    omega
  rw [← hback, hval, entries_ofInt_eval hw hlen hfits]

end FloatLib.Numerics.Packed
