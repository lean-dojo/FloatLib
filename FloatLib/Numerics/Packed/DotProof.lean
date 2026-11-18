/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.SeqProof
public import FloatLib.Numerics.Packed.Dot
public import FloatLib.Numerics.Packed.Proof.Products
public import FloatLib.Numerics.Packed.Proof.Sums
public import FloatLib.Numerics.Packed.Proof.Unsigned
public import Mathlib.Algebra.BigOperators.Intervals

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Ring

/-!
# The dot product of two packed rows, proved

* `pack_append`: a packed list with more entries appended is the packed list plus the packed
  entries from the lane `xs.length` on, with or without signs.
* `packRev_eq`, `packFwd_eq`: `packRev w l` is `pack w` of the reversed list and `packFwd w l`
  is `pack w` of the list, both without signs.
* `lanes_packRev`, `lanes_packFwd`: for members below `2 ^ w`, the lanes of the two rows are
  `l.reverse` and `l`.
* `add_getD`, `smul_getD`, `conv_getD`: the entries of a lanewise sum, of a scaled row and of
  the Cauchy product, `(conv X Y)[m] = ∑ i ≤ m, X[i] * Y[m - i]`.
* `dot_eq`: `dot w n (packRev w xs) (packFwd w ws) = ∑ i < n, xs[i] * ws[i]` for a list `xs` of
  length `n` and a list `ws` of at least that length whose rows pass
  `guard w gx n … (signed := false)` and `guard w gy ws.length … (signed := false)` with
  `n * 2 ^ gx * (ws.length * 2 ^ gy) < 2 ^ w`.

All of it holds for every lane width and every list. The product itself is
`FloatLib.Numerics.Packed.lanes_mul`.
-/

@[expose] public section

namespace FloatLib.Numerics.Packed

open FloatLib.Numerics.Kernel Finset

/-- A packed list with more entries appended: the new entries start at the lane `xs.length`. -/
theorem pack_append (w : Nat) (signed : Bool) : ∀ xs ys : List Int,
    pack w (xs ++ ys) signed = pack w xs signed + 2 ^ (w * xs.length) * pack w ys signed
  | [], ys => by
    change pack w ys signed = 0 + 2 ^ (w * 0) * pack w ys signed
    rw [Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
  | x :: xs, ys => by
    change Int.toNat (Int.add x (Int.ofNat (cond signed (pow2 (Nat.sub w 1)) 0))) +
        (pack w (xs ++ ys) signed) <<< w =
      Int.toNat (Int.add x (Int.ofNat (cond signed (pow2 (Nat.sub w 1)) 0))) +
        (pack w xs signed) <<< w + 2 ^ (w * (xs.length + 1)) * pack w ys signed
    rw [pack_append w signed xs ys, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.mul_succ,
      Nat.pow_add]
    ring

/-- The unsigned row of one natural number is the number. -/
private theorem pack_one (w x : Nat) : pack w [Int.ofNat x] (signed := false) = x := by
  change Int.toNat (Int.ofNat x + Int.ofNat 0) + 0 <<< w = x
  rw [Nat.zero_shiftLeft]
  simp

/-- What the steps of `packRev` return. -/
theorem packGo_eq (w : Nat) : ∀ (l : List Nat) (outer inner cnt : Nat),
    packGo w l outer inner cnt =
      pack w (l.reverse.map Int.ofNat) (signed := false) +
        (outer * (2 ^ w) ^ cnt + inner) * (2 ^ w) ^ l.length
  | [], outer, inner, cnt => by
    change outer <<< (cnt * w) + inner = 0 + (outer * (2 ^ w) ^ cnt + inner) * (2 ^ w) ^ 0
    rw [Nat.shiftLeft_eq, ← pow_mul, Nat.mul_comm cnt w, pow_zero, Nat.mul_one, Nat.zero_add]
  | x :: l, outer, inner, cnt => by
    change strict (Nat.add (Nat.shiftLeft inner w) x) (fun inner' =>
      Bool.casesOn (motive := fun _ => Nat) (Nat.beq cnt 63)
        (packGo w l outer inner' (Nat.succ cnt))
        (strict (Nat.add (Nat.shiftLeft outer (Nat.mul 64 w)) inner') fun outer' =>
          packGo w l outer' 0 0)) = _
    rw [strict_eq]
    have hin : Nat.add (Nat.shiftLeft inner w) x = inner * 2 ^ w + x := by
      change inner <<< w + x = _
      rw [Nat.shiftLeft_eq]
    have hx : pack w (List.map Int.ofNat [x]) (signed := false) = x := pack_one w x
    rw [hin, List.reverse_cons, List.map_append, pack_append, List.length_map,
      List.length_reverse, List.length_cons, hx, pow_mul]
    cases hc : Nat.beq cnt 63 with
    | false =>
      change packGo w l outer (inner * 2 ^ w + x) (Nat.succ cnt) = _
      rw [packGo_eq w l]
      simp only [Nat.succ_eq_add_one]
      ring
    | true =>
      have hcnt : cnt = 63 := Nat.eq_of_beq_eq_true hc
      change strict (Nat.add (Nat.shiftLeft outer (Nat.mul 64 w)) (inner * 2 ^ w + x))
        (fun outer' => packGo w l outer' 0 0) = _
      rw [strict_eq]
      have hout : Nat.add (Nat.shiftLeft outer (Nat.mul 64 w)) (inner * 2 ^ w + x) =
          outer * (2 ^ w) ^ 64 + (inner * 2 ^ w + x) := by
        change outer <<< (64 * w) + (inner * 2 ^ w + x) = _
        rw [Nat.shiftLeft_eq, ← pow_mul, Nat.mul_comm 64 w]
      rw [hout, packGo_eq w l, hcnt]
      simp only [Nat.add_zero, pow_zero, Nat.mul_one]
      ring

/-- `packRev w l` is the unsigned row of the reversed list. -/
theorem packRev_eq (w : Nat) (l : List Nat) :
    packRev w l = pack w (l.reverse.map Int.ofNat) (signed := false) := by
  unfold packRev
  rw [packGo_eq]
  simp

/-- `packFwd w l` is the unsigned row of the list. -/
theorem packFwd_eq (w : Nat) (l : List Nat) :
    packFwd w l = pack w (l.map Int.ofNat) (signed := false) := by
  unfold packFwd
  rw [packRev_eq, Seq.reverse_eq, List.reverse_reverse]

/-- The lanes of `packFwd w l` are `l`, for members below `2 ^ w`. -/
theorem lanes_packFwd {w : Nat} {l : List Nat} (h : ∀ d ∈ l, d < 2 ^ w) :
    lanes w l.length (packFwd w l) = l := by
  have hx : ∀ x ∈ l.map Int.ofNat, 0 ≤ x ∧ x < (2 : ℤ) ^ w := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hx
    refine ⟨Int.natCast_nonneg d, ?_⟩
    have := h d hd
    change ((d : ℕ) : ℤ) < (2 : ℤ) ^ w
    exact_mod_cast this
  have h1 := lanes_pack hx
  rw [List.length_map] at h1
  rw [packFwd_eq, h1, List.map_map]
  exact (List.map_congr_left (fun d _ => by simp)).trans (List.map_id l)

/-- The lanes of `packRev w l` are `l.reverse`, for members below `2 ^ w`. -/
theorem lanes_packRev {w : Nat} {l : List Nat} (h : ∀ d ∈ l, d < 2 ^ w) :
    lanes w l.length (packRev w l) = l.reverse := by
  rw [packRev_eq, ← packFwd_eq, ← List.length_reverse]
  exact lanes_packFwd (fun d hd => h d (List.mem_reverse.1 hd))

/-- The lane `k` as an entry of the list of lanes. -/
theorem lanes_getD {w n u k : Nat} (hk : k < n) : (lanes w n u).getD k 0 = lane w k u := by
  simp [lanes, List.getD_eq_getElem?_getD, hk]

/-- An entry of a lanewise sum. -/
theorem add_getD : ∀ (xs ys : List Int) (m : Nat),
    (add xs ys).getD m 0 = xs.getD m 0 + ys.getD m 0
  | [], ys, m => by simp [add]
  | x :: xs, [], m => by simp [add]
  | x :: xs, y :: ys, m => by
    cases m with
    | zero => simp [add]
    | succ m => simpa [add] using add_getD xs ys m

/-- An entry of a scaled row. -/
theorem smul_getD (c : Int) (xs : List Int) (m : Nat) :
    (smul c xs).getD m 0 = c * xs.getD m 0 := by
  simpa only [smul, mul_zero] using List.getD_map xs 0 (n := m) (c * ·)

/-- An entry of the Cauchy product: `∑ i ≤ m, X[i] * Y[m - i]`, with zero beyond the ends. -/
theorem conv_getD : ∀ (X Y : List Int) (m : Nat),
    (conv X Y).getD m 0 = ∑ i ∈ range (m + 1), X.getD i 0 * Y.getD (m - i) 0
  | [], Y, m => by simp [conv]
  | x :: X, Y, m => by
    change (add (smul x Y) (0 :: conv X Y)).getD m 0 = _
    rw [add_getD, smul_getD, sum_range_succ']
    simp only [List.getD_cons_zero, Nat.sub_zero, List.getD_cons_succ]
    rw [add_comm]
    congr 1
    cases m with
    | zero => simp
    | succ m =>
      rw [List.getD_cons_succ, conv_getD X Y m]
      refine sum_congr rfl fun i _ => ?_
      rw [Nat.succ_sub_succ]

/-- The lane `n - 1` of the product of a row packed by `packRev` and a row packed by `packFwd` is
the dot product of the first list with the first `n` members of the second, when the lanes have
room: the `n` members of `xs` below `2 ^ gx`, those of `ws` below `2 ^ gy` (both checked on the
rows by `guard`), and `n * 2 ^ gx * (ws.length * 2 ^ gy) < 2 ^ w`. The second list may be longer
than the first, so one packed row serves every shorter list. -/
theorem dot_eq {w n gx gy : Nat} {xs ws : List Nat} (hn : 0 < n) (hxs : xs.length = n)
    (hws : n ≤ ws.length) (hxw : ∀ d ∈ xs, d < 2 ^ w) (hww : ∀ d ∈ ws, d < 2 ^ w)
    (hga : guard w gx n (packRev w xs) (signed := false) = true)
    (hgb : guard w gy ws.length (packFwd w ws) (signed := false) = true)
    (hroom : n * 2 ^ gx * (ws.length * 2 ^ gy) < 2 ^ w) :
    dot w n (packRev w xs) (packFwd w ws) = ∑ i ∈ range n, xs.getD i 0 * ws.getD i 0 := by
  have hla : lanes w n (packRev w xs) = xs.reverse := by
    rw [← hxs]
    exact lanes_packRev hxw
  have hlb : lanes w ws.length (packFwd w ws) = ws := lanes_packFwd hww
  have hmul := lanes_mul hga hgb hroom hn (lt_of_lt_of_le hn hws)
  rw [hla, hlb] at hmul
  have hlane : ((dot w n (packRev w xs) (packFwd w ws) : ℕ) : ℤ) =
      ((lanes w (n + ws.length - 1) (packRev w xs * packFwd w ws)).map Nat.cast).getD
        (n - 1) 0 := by
    have hlt : n - 1 < n + ws.length - 1 := by omega
    have h := lanes_getD (w := w) (u := packRev w xs * packFwd w ws) hlt
    rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, List.getD_map, h]
    rfl
  have hsum : ((∑ i ∈ range n, xs.getD i 0 * ws.getD i 0 : ℕ) : ℤ) =
      ∑ i ∈ range (n - 1 + 1), (xs.reverse.map Nat.cast).getD i (0 : ℤ) *
        (ws.map Nat.cast).getD (n - 1 - i) (0 : ℤ) := by
    have hn1 : n - 1 + 1 = n := by omega
    rw [hn1, ← sum_range_reflect]
    push_cast
    refine sum_congr rfl fun i hi => ?_
    have hi' : i < n := mem_range.1 hi
    have h1 : (xs.reverse.map (Nat.cast : ℕ → ℤ)).getD i 0 =
        ((xs.getD (n - 1 - i) 0 : ℕ) : ℤ) := by
      rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, List.getD_map,
        List.getD_reverse i (by omega), hxs]
    have h2 : (ws.map (Nat.cast : ℕ → ℤ)).getD (n - 1 - i) 0 =
        ((ws.getD (n - 1 - i) 0 : ℕ) : ℤ) := by
      exact List.getD_map ws 0 (Nat.cast : ℕ → ℤ)
    rw [h1, h2]
  have := conv_getD (xs.reverse.map Nat.cast) (ws.map Nat.cast) (n - 1)
  rw [← hmul, ← hlane, ← hsum] at this
  exact_mod_cast this

end FloatLib.Numerics.Packed
