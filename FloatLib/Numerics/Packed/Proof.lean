/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Packed.Basic

/-!
# Soundness of the packed-row programs

Each theorem here says what a kernel computation on biased rows means for the integer lists they
stand for. The hypotheses are the ones a caller can check with one more operation, so that a
certificate stays a few big-number operations plus a comparison of small numbers.

A biased row `u` of `n` lanes below `2 ^ (w * n)` stands for the value of its entries. In the other
direction a list whose entries fit comes back out of its value, padded with zeros. A range check
then bounds every entry, and the bound is what makes a product readable. Take two rows of `n` and
`m` entries below `2 ^ gx` and `2 ^ gy`. Their `l1` norms are at most `n * 2 ^ gx` and
`m * 2 ^ gy`, so every entry of their Cauchy product is at most `n * 2 ^ gx * (m * 2 ^ gy)`. With
`n = m = 1000` and `gx = gy = 64`, that is below `2 ^ 148`, so lanes of `150` bits hold the
product.

## Main statements

Signed rows:

* `eval_entries`: `toInt w n u = eval (2 ^ w) (entries w n u)` for `u < 2 ^ (w * n)`.
* `entries_ofInt_eval`, `entry_ofInt_eval` and `ofInt_eval_lt`: a list whose entries fit comes
  back out of the biased row of its value, and `pack_eq_ofInt` says `pack` builds the same row.
* `guard_sound`: one range check bounds every entry and rules out lanes beyond the row.
* `entries_mul` and `entries_autocorr`: two guards and the headroom
  `n * 2 ^ gx * (m * 2 ^ gy) < 2 ^ (w - 1)` give the entries of a product row, or of a row times
  its reverse.
* `absSum_eval`, `sum_eval` and `posSum_eval`: masked remainders compute the `l1` norm, the sum
  and the positive part of a row whose `l1` norm is below `2 ^ (w - 1)`, and `absSum_toInt` and
  `sum_toInt` do the same for a guarded row.
* `entries_rev`, `lanes_rev` and `autocorr_eq`: reversal and autocorrelation on the lists.

Rows of natural numbers have the same results without the bias: `eval_lanes`,
`lanes_lt_of_guard`, `laneSum_eq`, `lanes_pack` and `lanes_mul`, where the headroom condition is
`n * 2 ^ gx * (m * 2 ^ gy) < 2 ^ w`.

## Implementation notes

The proofs go through the lanes of a row, a list of digits in base `2 ^ w`, and a private Horner
value `nv` of such digit lists. Adding a constant to every lane, or masking every lane, acts digit
by digit as long as no lane carries, and the range check is arranged so that a carry shows up in
the masked result. That is the usual SWAR overflow test: add a bias that pushes every legal value
into a known window of high bits, then look at those bits all at once.

Every headroom condition is stated as a comparison of small numbers, `n * 2 ^ g < 2 ^ (w - 1)`
and the like, rather than as a property of the row. The kernel decides it in microseconds before it
touches the big numbers, so a caller pays nothing for it.

## References

* Henry S. Warren, Jr., *Hacker's Delight*, second edition, Addison-Wesley (2013), chapter 2,
  whose multibyte addition adds several fields of one word at once,
  <https://www.informit.com/store/hackers-delight-9780321842688>.
* Randall J. Fisher and Henry G. Dietz, *Compiling for SIMD within a register*, LCPC 1998,
  LNCS 1656 (1999), 290–305, <https://doi.org/10.1007/3-540-48319-5_19>.

## Tags

packed row, Kronecker substitution, SWAR, soundness
-/

@[expose] public section

namespace FloatLib.Numerics.Packed

private theorem two_pow_pred {w : Nat} (hw : 1 ≤ w) : (2 : Int) ^ w = 2 * 2 ^ (w - 1) := by
  rw [← Int.pow_succ']; congr 1; omega

/-! ### Digits -/

/-- Horner value of natural lanes. -/
private def nv (b : Nat) : List Nat → Nat
  | [] => 0
  | d :: ds => d + b * nv b ds

private theorem lane_succ (w k u : Nat) : lane w (k + 1) u = lane w k (u / 2 ^ w) := by
  simp only [lane_eq, Nat.div_div_eq_div_mul, ← Nat.pow_add]
  congr 3; rw [Nat.mul_succ, Nat.add_comm]

private theorem lanes_succ (w n u : Nat) :
    lanes w (n + 1) u = lane w 0 u :: lanes w n (u / 2 ^ w) := by
  simp only [lanes, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  exact lane_succ w k u

private theorem lane_zero (w u : Nat) : lane w 0 u = u % 2 ^ w := by simp [lane_eq]

private theorem nv_lanes (w : Nat) : ∀ (n u : Nat), u < 2 ^ (w * n) → nv (2 ^ w) (lanes w n u) = u
  | 0, u, h => by simp at h; simp [lanes, nv, h]
  | n + 1, u, h => by
      rw [lanes_succ, nv, lane_zero, nv_lanes w n (u / 2 ^ w) ?_]
      · exact Nat.mod_add_div u (2 ^ w)
      · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos w), ← Nat.pow_add]
        rwa [Nat.mul_succ] at h

private theorem nv_lt (w : Nat) :
    ∀ ds : List Nat, (∀ d ∈ ds, d < 2 ^ w) → nv (2 ^ w) ds < 2 ^ (w * ds.length)
  | [], _ => by simp [nv]
  | d :: ds, h => by
      have ih := nv_lt w ds (fun e he => h e (by simp [he]))
      have hd := h d (by simp)
      simp only [nv, List.length_cons, Nat.mul_succ, Nat.pow_add]
      have : 2 ^ w * nv (2 ^ w) ds + 2 ^ w ≤ 2 ^ w * 2 ^ (w * ds.length) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ ih
      rw [Nat.mul_comm (2 ^ (w * ds.length))]
      omega

private theorem lanes_nv (w : Nat) : ∀ ds : List Nat, (∀ d ∈ ds, d < 2 ^ w) →
    lanes w ds.length (nv (2 ^ w) ds) = ds
  | [], _ => by simp [lanes]
  | d :: ds, h => by
      have hd := h d (by simp)
      rw [List.length_cons, lanes_succ, lane_zero, nv, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hd,
        Nat.add_mul_div_left _ _ (Nat.two_pow_pos w), Nat.div_eq_of_lt hd, Nat.zero_add,
        lanes_nv w ds (fun e he => h e (by simp [he]))]

/-- The lanes of `b + 2 ^ (w * m) * a` for `b < 2 ^ (w * m)`: those of `b`, then those of `a`. -/
private theorem lanes_append (w m k : Nat) {b : Nat} (hb : b < 2 ^ (w * m)) (a : Nat) :
    lanes w (m + k) (b + 2 ^ (w * m) * a) = lanes w m b ++ lanes w k a := by
  induction m generalizing b with
  | zero => simp at hb; subst hb; simp [lanes]
  | succ m ih =>
      rw [Nat.add_right_comm, lanes_succ, lanes_succ, List.cons_append]
      have hpow : 2 ^ (w * (m + 1)) = 2 ^ w * 2 ^ (w * m) := by
        rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
      congr 1
      · rw [lane_zero, lane_zero, hpow, Nat.mul_assoc, Nat.add_mul_mod_self_left]
      · rw [hpow, Nat.mul_assoc, Nat.add_mul_div_left _ _ (Nat.two_pow_pos w)]
        apply ih
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos w), Nat.mul_comm]
        rwa [← hpow]

/-- The first `m + k` lanes of `u` are the `m` lanes of `u % 2 ^ (w * m)` followed by the `k`
lanes of `u / 2 ^ (w * m)`. -/
theorem lanes_split (w m k u : Nat) :
    lanes w (m + k) u = lanes w m (u % 2 ^ (w * m)) ++ lanes w k (u / 2 ^ (w * m)) := by
  have := lanes_append w m k (Nat.mod_lt u (Nat.two_pow_pos (w * m))) (u / 2 ^ (w * m))
  simpa only [Nat.mod_add_div] using this

/-- Reducing modulo `2 ^ (w * n)` keeps the first `n` lanes. -/
theorem lanes_mod (w n u : Nat) : lanes w n (u % 2 ^ (w * n)) = lanes w n u := by
  have := lanes_split w n 0 u
  simp only [Nat.add_zero] at this
  rw [this]; simp [lanes]

private theorem eval_map_sub (w : Nat) (c : Int) : ∀ ds : List Nat,
    eval (2 ^ w) (ds.map fun (d : Nat) => (d : Int) - c) =
      (nv (2 ^ w) ds : Int) - c * (nv (2 ^ w) (List.replicate ds.length 1) : Int)
  | [] => by simp [eval, nv]
  | d :: ds => by
      have ih := eval_map_sub w c ds
      simp only [List.map_cons, eval, ih, nv, List.length_cons, List.replicate_succ,
        Int.natCast_add,
        Int.natCast_mul, Int.natCast_pow, Int.cast_ofNat_Int]
      grind

private theorem geom (t : Nat) : ∀ n, t * nv (t + 1) (List.replicate n 1) + 1 = (t + 1) ^ n
  | 0 => by simp [nv]
  | n + 1 => by
      have ih := geom t n
      simp only [List.replicate_succ, nv, Nat.pow_succ]
      rw [← ih]; grind

private theorem ones_eq_nv (w n : Nat) (hw : 1 ≤ w) :
    ones w n = nv (2 ^ w) (List.replicate n 1) := by
  have hpos : 1 ≤ 2 ^ w - 1 := by
    have : 2 ≤ 2 ^ w := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw
    omega
  have hg := geom (2 ^ w - 1) n
  rw [Nat.sub_add_cancel (Nat.one_le_two_pow), ← Nat.pow_mul] at hg
  simp only [ones, pow2_eq, Nat.sub_eq, Nat.mul_eq]
  show (2 ^ (w * n) - 1) / (2 ^ w - 1) = _
  rw [← hg, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ (by omega)]

private theorem nv_replicate (b c : Nat) :
    ∀ n, nv b (List.replicate n c) = c * nv b (List.replicate n 1)
  | 0 => by simp [nv]
  | n + 1 => by
      simp only [List.replicate_succ, nv, nv_replicate b c n]
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]

private theorem bias_eq_nv (w n : Nat) (hw : 1 ≤ w) :
    bias w n = nv (2 ^ w) (List.replicate n (2 ^ (w - 1))) := by
  rw [nv_replicate, ← ones_eq_nv w n hw]
  simp [bias, pow2_eq]

/-- A conjunction acts lane by lane. -/
theorem lane_land (w k u v : Nat) : lane w k (u &&& v) = lane w k u &&& lane w k v := by
  simp only [lane, pow2_eq, Nat.sub_eq, Nat.mul_eq]
  show ((u &&& v) >>> (w * k)) &&& (2 ^ w - 1) =
    ((u >>> (w * k)) &&& (2 ^ w - 1)) &&& ((v >>> (w * k)) &&& (2 ^ w - 1))
  rw [Nat.shiftRight_and_distrib]
  generalize u >>> (w * k) = a
  generalize v >>> (w * k) = b
  generalize 2 ^ w - 1 = m
  rw [Nat.and_assoc, Nat.and_assoc, Nat.and_comm m (b &&& m), Nat.and_assoc, Nat.and_self]

/-- The number `c * ones w n` holds `c` in each of its `n` lanes, when `c < 2 ^ w`. -/
theorem lanes_mul_ones {w n c : Nat} (hw : 1 ≤ w) (hc : c < 2 ^ w) :
    lanes w n (c * ones w n) = List.replicate n c ∧ c * ones w n < 2 ^ (w * n) := by
  have hr : ∀ d ∈ List.replicate n c, d < 2 ^ w := fun d hd => List.eq_of_mem_replicate hd ▸ hc
  rw [ones_eq_nv w n hw, ← nv_replicate]
  have h1 := lanes_nv w _ hr
  have h2 := nv_lt w _ hr
  rw [List.length_replicate] at h1 h2
  exact ⟨h1, h2⟩

/-- The biased lane of `x`. -/
private def ub (w : Nat) (x : Int) : Nat := (x + 2 ^ (w - 1)).toNat

private theorem ub_lt {w : Nat} (hw : 1 ≤ w) {x : Int} (hx : Fits w x) : ub w x < 2 ^ w := by
  have h2 := two_pow_pred hw
  have : ((ub w x : Nat) : Int) < (2 ^ w : Nat) := by
    rw [natCast_two_pow, h2]; simp only [ub, Fits] at *; omega
  exact_mod_cast this

private theorem ub_sub {w : Nat} {x : Int} (hx : Fits w x) : (ub w x : Int) - 2 ^ (w - 1) = x := by
  simp only [ub, Fits] at *; omega

private theorem nv_ub (w : Nat) : ∀ xs : List Int, (∀ x ∈ xs, Fits w x) →
    (nv (2 ^ w) (xs.map (ub w)) : Int) =
      eval (2 ^ w) xs + (nv (2 ^ w) (List.replicate xs.length (2 ^ (w - 1))) : Int)
  | [], _ => by simp [nv, eval]
  | x :: xs, h => by
      have ih := nv_ub w xs (fun y hy => h y (by simp [hy]))
      have hx := ub_sub (h x (by simp))
      simp only [List.map_cons, nv, eval, List.length_cons, List.replicate_succ, Int.natCast_add,
        Int.natCast_mul, Int.natCast_pow, ih]
      push_cast at hx ⊢
      grind

/-- The value of the signed entries of a biased row below `2 ^ (w * n)` is the row's integer. -/
theorem eval_entries {w n u : Nat} (hw : 1 ≤ w) (hu : u < 2 ^ (w * n)) :
    eval (2 ^ w) (entries w n u) = toInt w n u := by
  rw [entries_eq_lanes, eval_map_sub, nv_lanes w n u hu, length_lanes, toInt_eq,
    bias_eq_nv w n hw,
    nv_replicate (2 ^ w) (2 ^ (w - 1))]
  push_cast; rfl

private theorem ofInt_eval_aux {w : Nat} (hw : 1 ≤ w) (xs : List Int) (hx : ∀ x ∈ xs, Fits w x) :
    ofInt w xs.length (eval (2 ^ w) xs) = nv (2 ^ w) (xs.map (ub w)) := by
  have := nv_ub w xs hx
  rw [ofInt_eq, bias_eq_nv w _ hw]
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
    have := lanes_nv w _ hub
    rw [List.length_map] at this
    rw [this, List.map_map]
    conv => rhs; rw [← List.map_id ys]
    apply List.map_congr_left
    intro y hy'
    exact ub_sub (hy y hy')
  · have := nv_lt w _ hub
    rwa [List.length_map] at this

private theorem pad_spec {w n : Nat} (hw : 1 ≤ w) {xs : List Int} (hn : xs.length ≤ n)
    (hx : ∀ x ∈ xs, Fits w x) :
    entries w n (ofInt w n (eval (2 ^ w) xs)) = xs ++ List.replicate (n - xs.length) 0 ∧
      ofInt w n (eval (2 ^ w) xs) < 2 ^ (w * n) := by
  have hp := pad_fits hx (n - xs.length)
  have hlen : (xs ++ List.replicate (n - xs.length) 0).length = n := by simp; omega
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

/-! ### Packing -/

private theorem pack_eq_nv (w : Nat) : ∀ xs : List Int, pack w xs = nv (2 ^ w) (xs.map (ub w))
  | [] => rfl
  | x :: xs => by
      simp only [pack, Bool.cond_true, List.map_cons, nv, ub, pow2_eq, Nat.add_eq, Nat.sub_eq,
        pack_eq_nv w xs, Int.ofNat_eq_natCast, Int.add_def, natCast_two_pow]
      show _ + (nv _ _ <<< w) = _
      rw [Nat.shiftLeft_eq, Nat.mul_comm]

/-- Packing a list whose entries fit is the biased row of its value. -/
theorem pack_eq_ofInt {w : Nat} (hw : 1 ≤ w) {xs : List Int} (hx : ∀ x ∈ xs, Fits w x) :
    pack w xs = ofInt w xs.length (eval (2 ^ w) xs) := by
  rw [pack_eq_nv, ofInt_eval_aux hw xs hx]

/-! ### Range checks -/

/-- Lanes split a conjunction when both operands are written lane by lane. -/
private theorem land_split {j a b x y : Nat} (ha : a < 2 ^ j) (hb : b < 2 ^ j) :
    (a + 2 ^ j * x) &&& (b + 2 ^ j * y) = (a &&& b) + 2 ^ j * (x &&& y) := by
  have h1 := Nat.mod_add_div ((a + 2 ^ j * x) &&& (b + 2 ^ j * y)) (2 ^ j)
  rw [Nat.and_mod_two_pow, Nat.and_div_two_pow, Nat.add_mul_mod_self_left,
    Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.add_mul_div_left _ _ (Nat.two_pow_pos j),
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos j), Nat.div_eq_of_lt ha, Nat.div_eq_of_lt hb] at h1
  simpa using h1.symm

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

private theorem guard_lanes (w g : Nat) (hg : g + 1 < w) : ∀ ds : List Nat, (∀ d ∈ ds, d < 2 ^ w) →
    (nv (2 ^ w) ds + nv (2 ^ w) (List.replicate ds.length (2 ^ g))) &&&
        nv (2 ^ w) (List.replicate ds.length (2 ^ w - 2 ^ (g + 1))) =
      nv (2 ^ w) (List.replicate ds.length (2 ^ (w - 1))) →
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
      simp only [List.length_cons, List.replicate_succ, nv] at h
      -- peel off the bottom lane: `d + 2 ^ g`, then everything above it times `2 ^ w`
      rw [show d + 2 ^ w * nv (2 ^ w) ds +
            (2 ^ g + 2 ^ w * nv (2 ^ w) (List.replicate ds.length (2 ^ g))) =
          (d + 2 ^ g) + 2 ^ w * (nv (2 ^ w) ds + nv (2 ^ w) (List.replicate ds.length (2 ^ g))) by
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
        generalize nv (2 ^ w) ds + nv (2 ^ w) (List.replicate ds.length (2 ^ g)) = X at h
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
    rw [nv_lanes w n u hu, length_lanes, nv_replicate _ (2 ^ g),
      nv_replicate _ (2 ^ w - 2 ^ (g + 1)),
      ← bias_eq_nv w n hw, ← ones_eq_nv w n hw]
    show (u + 2 ^ g * ones w n) &&& ((2 ^ w - 2 ^ (g + 1)) * ones w n) = bias w n
    exact hm)
  intro x hx
  rw [entries_eq_lanes, List.mem_map] at hx
  obtain ⟨d, hd, rfl⟩ := hx
  have := key d hd
  have e1 := natCast_two_pow (w - 1)
  have e2 := natCast_two_pow g
  have e3 : ((2 ^ (g + 1) : Nat) : Int) = 2 * 2 ^ g := by rw [natCast_two_pow, Int.pow_succ']
  omega

/-! ### Sums of entries -/

private theorem land_nv_map (w : Nat) (f g : Int → Nat) :
    ∀ xs : List Int, (∀ x ∈ xs, f x < 2 ^ w) → (∀ x ∈ xs, g x < 2 ^ w) →
      nv (2 ^ w) (xs.map f) &&& nv (2 ^ w) (xs.map g) = nv (2 ^ w) (xs.map fun x => f x &&& g x)
  | [], _, _ => by simp [nv]
  | x :: xs, hf, hg => by
      simp only [List.map_cons, nv]
      rw [land_split (hf x (by simp)) (hg x (by simp)),
        land_nv_map w f g xs (fun y hy => hf y (by simp [hy])) (fun y hy => hg y (by simp [hy]))]

private theorem nv_map_mul (b c : Nat) (f : Int → Nat) :
    ∀ xs : List Int, nv b (xs.map fun x => c * f x) = c * nv b (xs.map f)
  | [] => by simp [nv]
  | x :: xs => by
      simp only [List.map_cons, nv, nv_map_mul b c f xs]
      rw [Nat.mul_add, Nat.mul_left_comm]

private theorem nv_map_mul_right (b c : Nat) (f : Int → Nat) (xs : List Int) :
    nv b (xs.map fun x => f x * c) = nv b (xs.map f) * c := by
  have := nv_map_mul b c f xs
  simp only [Nat.mul_comm _ c]; exact this

/-- `2 ^ w ≡ 1 (mod 2 ^ w - 1)`, so a packed row and the sum of its lanes have the same
remainder. -/
private theorem nv_mod (t : Nat) : ∀ ds : List Nat, nv (t + 1) ds % t = ds.sum % t
  | [] => by simp [nv]
  | d :: ds => by
      have ih := nv_mod t ds
      simp only [nv, List.sum_cons]
      rw [show d + (t + 1) * nv (t + 1) ds = (d + nv (t + 1) ds) + t * nv (t + 1) ds by grind,
        Nat.add_mul_mod_self_left, Nat.add_mod, ih, ← Nat.add_mod]

private theorem land_top (m v : Nat) (hv : v < 2 ^ (m + 1)) :
    v &&& 2 ^ m = 2 ^ m * (v / 2 ^ m) := by
  have h := land_split (j := m) (x := v / 2 ^ m) (y := 1) (Nat.mod_lt v (Nat.two_pow_pos m))
    (Nat.two_pow_pos m)
  rw [Nat.mod_add_div, Nat.zero_add, Nat.mul_one, Nat.and_zero, Nat.zero_add] at h
  rw [h]
  have hq : v / 2 ^ m < 2 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos m)]; rw [Nat.pow_succ] at hv; omega
  have hc : v / 2 ^ m = 0 ∨ v / 2 ^ m = 1 := by generalize v / 2 ^ m = q at hq; omega
  rcases hc with e | e <;> rw [e] <;> simp

private theorem fits_of_natAbs {w : Nat} {x : Int} (hx : x.natAbs < 2 ^ (w - 1)) : Fits w x := by
  have e := natCast_two_pow (w - 1)
  constructor <;> omega

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
    bias_eq_nv w _ hw]
  show (nv (2 ^ w) (xs.map (ub w)) &&&
      ((nv (2 ^ w) (xs.map (ub w)) &&& nv (2 ^ w) (List.replicate xs.length (2 ^ (w - 1))))
        >>> (w - 1) * (2 ^ (w - 1) - 1))) % (2 ^ w - 1) = _
  -- the first mask keeps the sign bit of every lane, which is set exactly for `x ≥ 0`
  rw [hcst, land_nv_map w _ _ xs hub (fun _ _ => by omega)]
  have e1 : (xs.map fun x => ub w x &&& 2 ^ (w - 1)) =
      xs.map fun x => 2 ^ (w - 1) * (ub w x / 2 ^ (w - 1)) :=
    List.map_congr_left (fun x hx' => ub_land_top hw (hx x hx'))
  rw [e1, nv_map_mul, Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel_left _ hpos,
    ← nv_map_mul_right, land_nv_map w _ _ xs hub]
  -- shifted down and spread over the low bits, the sign bits keep `x` where `x ≥ 0` and clear
  -- the lane otherwise, and one remainder adds up what is left
  · have e2 : (xs.map fun x => ub w x &&& (ub w x / 2 ^ (w - 1) * (2 ^ (w - 1) - 1))) =
        xs.map Int.toNat :=
      List.map_congr_left (fun x hx' => ub_land_low (hx x hx'))
    rw [e2]
    have := nv_mod (2 ^ w - 1) (xs.map Int.toNat)
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
  have hlen : (xs ++ List.replicate (n - xs.length) 0).length = n := by simp; omega
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
  simp only [absSum, Nat.add_eq, h1, h2]
  exact sum_toNat_add xs

/-- Two masked remainders compute the sum of the entries of a row whose `l1` norm is below
`2 ^ (w - 1)`. -/
theorem sum_eval {w n : Nat} (hw : 1 ≤ w) {xs : List Int} (hn : xs.length ≤ n)
    (hl : l1 xs < 2 ^ (w - 1)) : sum w n (eval (2 ^ w) xs) = xs.sum := by
  obtain ⟨h1, h2⟩ := posSum_pair hw hn hl
  simp only [sum, Int.subNatNat_eq_coe, h1, h2]
  exact sum_toNat_sub xs

/-! ### Reversal and autocorrelation -/

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
        show lanes w n (u &&& 2 ^ (w * n) - 1) = _ ∧ (u &&& 2 ^ (w * n) - 1) < _
        rw [Nat.and_two_pow_sub_one_eq_mod, lanes_mod]
        exact ⟨(reverse_of_length_le_one (by rw [length_lanes]; exact hn)).symm,
          Nat.mod_lt _ (Nat.two_pow_pos _)⟩
      · have hb : Nat.ble n 1 = false :=
          Bool.eq_false_iff.mpr (fun h' => hn (Nat.le_of_ble_eq_true h'))
        simp only [revAux, hb, Bool.cond_false, pow2_eq]
        show lanes w n
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
  rfl

/-! ### Products of guarded rows -/

/-- The product of two guarded rows. If the entries of `u` lie in `[-2 ^ gx, 2 ^ gx)`, those of `v`
in `[-2 ^ gy, 2 ^ gy)`, and `n * 2 ^ gx * (m * 2 ^ gy) < 2 ^ (w - 1)`, then the biased row of the
product of their integers holds the Cauchy product of their entries. -/
theorem entries_mul {w gx gy n m u v : Nat} (hu : guard w gx n u = true)
    (hv : guard w gy m v = true) (hroom : n * 2 ^ gx * (m * 2 ^ gy) < 2 ^ (w - 1)) (hn : 0 < n)
    (hm : 0 < m) :
    entries w (n + m - 1) (ofInt w (n + m - 1) (toInt w n u * toInt w m v)) =
      conv (entries w n u) (entries w m v) := by
  obtain ⟨hgw, hu', hbu⟩ := guard_sound hu
  obtain ⟨-, hv', hbv⟩ := guard_sound hv
  have hw : 1 ≤ w := by omega
  -- the product of the two integers is the value of the Cauchy product, by Kronecker
  rw [← eval_entries hw hu', ← eval_entries hw hv', ← eval_conv]
  -- and the headroom keeps its `l1` norm, so every entry, below the bias
  have hl1 : l1 (conv (entries w n u) (entries w m v)) < 2 ^ (w - 1) := by
    have h1 := l1_le_of_bound hbu
    have h2 := l1_le_of_bound hbv
    rw [length_entries] at h1 h2
    have := l1_conv_le (entries w n u) (entries w m v)
    have := Nat.mul_le_mul h1 h2
    omega
  have hlen : (conv (entries w n u) (entries w m v)).length = n + m - 1 := by
    rw [length_conv (List.length_pos_iff.mp (by rw [length_entries]; exact hm))
      (List.length_pos_iff.mp (by rw [length_entries]; exact hn)), length_entries, length_entries]
  rw [entries_ofInt_eval hw (Nat.le_of_eq hlen) (fits_of_l1_lt hl1), hlen, Nat.sub_self,
    List.replicate_zero, List.append_nil]

/-- The autocorrelation of a guarded row. If the entries of `u` lie in `[-2 ^ g, 2 ^ g)` and
`n * 2 ^ g * (n * 2 ^ g) < 2 ^ (w - 1)`, the `2 * n - 1` entries of `autocorr w n u` are those of
`x ⋆ reverse x` for the entries `x`; the middle one, entry `n - 1`, is `∑ j, x[j] ^ 2`. -/
theorem entries_autocorr {w g n u : Nat} (hu : guard w g n u = true)
    (hroom : n * 2 ^ g * (n * 2 ^ g) < 2 ^ (w - 1)) (hn : 0 < n) :
    entries w (2 * n - 1) (ofInt w (2 * n - 1) (autocorr w n u)) =
      conv (entries w n u) (entries w n u).reverse := by
  obtain ⟨hgw, hu', hbu⟩ := guard_sound hu
  have hw : 1 ≤ w := by omega
  rw [autocorr_eq hw hu']
  have hl1 : l1 (conv (entries w n u) (entries w n u).reverse) < 2 ^ (w - 1) := by
    have h1 := l1_le_of_bound hbu
    rw [length_entries] at h1
    have := l1_conv_le (entries w n u) (entries w n u).reverse
    rw [l1_reverse] at this
    have := Nat.mul_le_mul h1 h1
    omega
  have hne : entries w n u ≠ [] := List.length_pos_iff.mp (by rw [length_entries]; exact hn)
  have hlen : (conv (entries w n u) (entries w n u).reverse).length = 2 * n - 1 := by
    rw [length_conv (by simpa using hne) hne, List.length_reverse, length_entries]; omega
  rw [entries_ofInt_eval hw (Nat.le_of_eq hlen) (fits_of_l1_lt hl1), hlen, Nat.sub_self,
    List.replicate_zero, List.append_nil]

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

/-! ### Unsigned rows -/

private theorem eval_natCast (b : Nat) :
    ∀ ds : List Nat, eval (b : Int) (ds.map Nat.cast) = (nv b ds : Int)
  | [] => rfl
  | d :: ds => by
      simp only [List.map_cons, eval, nv, eval_natCast b ds, Int.natCast_add, Int.natCast_mul]

/-- A row below `2 ^ (w * n)` is the value of its lanes in base `2 ^ w`. -/
theorem eval_lanes {w n u : Nat} (hu : u < 2 ^ (w * n)) :
    eval (2 ^ w) ((lanes w n u).map Nat.cast) = u := by
  rw [← natCast_two_pow, eval_natCast, nv_lanes w n u hu]

private theorem land_replicate (w m : Nat) (hm : m < 2 ^ w) :
    ∀ ds : List Nat, (∀ d ∈ ds, d < 2 ^ w) →
      nv (2 ^ w) ds &&& nv (2 ^ w) (List.replicate ds.length m) = 0 → ∀ d ∈ ds, d &&& m = 0
  | [], _, _ => by simp
  | d :: ds, hd, h => by
      simp only [List.length_cons, List.replicate_succ, nv] at h
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
      rw [nv_lanes w n u hu, length_lanes, nv_replicate, ← ones_eq_nv w n hw]
      exact hm)
    intro d hd
    exact lt_of_land_high hg (hds d hd) (key d hd)

/-- One remainder computes the sum of the lanes of a row, when that sum is below `2 ^ w - 1`. -/
theorem laneSum_eq {w n u : Nat} (hu : u < 2 ^ (w * n)) (hs : (lanes w n u).sum < 2 ^ w - 1) :
    laneSum w u = (lanes w n u).sum := by
  have := nv_mod (2 ^ w - 1) (lanes w n u)
  rw [Nat.sub_add_cancel Nat.one_le_two_pow, nv_lanes w n u hu, Nat.mod_eq_of_lt hs] at this
  unfold laneSum
  rw [pow2_eq]
  exact this

private theorem pack_unsigned (w : Nat) :
    ∀ xs : List Int, pack w xs (signed := false) = nv (2 ^ w) (xs.map Int.toNat)
  | [] => rfl
  | x :: xs => by
      simp only [pack, Bool.cond_false, List.map_cons, nv, Nat.add_eq, pack_unsigned w xs]
      show (x + 0).toNat + (nv _ _ <<< w) = _
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
  have := lanes_nv w (xs.map Int.toNat) (by
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
  have hval : nv (2 ^ w) ((conv X Y).map Int.toNat) = u * v := by
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
  have := lanes_nv w _ hlt
  rw [List.length_map, hlen, hval] at this
  rw [this, hc]

end FloatLib.Numerics.Packed
