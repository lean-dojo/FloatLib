/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Packed.Basic
public import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Digits and masks of packed rows

Fixed-width lanes are base-two-power digits. These lemmas relate lane extraction to Mathlib's
`Nat.ofDigits`, and establish the masks, replicated digits and integer evaluations used by signed
and unsigned row operations.
-/

@[expose] public section

namespace FloatLib.Numerics.Packed

/-- A positive-width power of two is twice the power at the preceding width. -/
theorem two_pow_pred {w : Nat} (hw : 1 ≤ w) : (2 : Int) ^ w = 2 * 2 ^ (w - 1) := by
  rw [← Int.pow_succ']; congr 1; omega

/-- Lane `k + 1` is lane `k` of the row without its lowest lane. -/
theorem lane_succ (w k u : Nat) : lane w (k + 1) u = lane w k (u / 2 ^ w) := by
  simp only [lane_eq, Nat.div_div_eq_div_mul, ← Nat.pow_add]
  congr 3; rw [Nat.mul_succ, Nat.add_comm]

private theorem lanes_succ (w n u : Nat) :
    lanes w (n + 1) u = lane w 0 u :: lanes w n (u / 2 ^ w) := by
  simp only [lanes, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  exact lane_succ w k u

/-- Lane zero is the remainder modulo `2 ^ w`. -/
theorem lane_zero (w u : Nat) : lane w 0 u = u % 2 ^ w := by simp [lane_eq]

/-- Evaluating all lanes recovers a natural row that fits the stated storage width. -/
theorem ofDigits_lanes (w : Nat) :
    ∀ (n u : Nat), u < 2 ^ (w * n) → Nat.ofDigits (2 ^ w : Nat) (lanes w n u) = u
  | 0, u, h => by simp only [mul_zero, pow_zero, Order.lt_one_iff] at h; simp [lanes, h]
  | n + 1, u, h => by
      rw [lanes_succ, Nat.ofDigits_cons, lane_zero, ofDigits_lanes w n (u / 2 ^ w) ?_]
      · exact Nat.mod_add_div u (2 ^ w)
      · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos w), ← Nat.pow_add]
        rwa [Nat.mul_succ] at h

/-- A list of bounded lane digits fits in its total storage width, including width zero. -/
theorem ofDigits_lt (w : Nat) (ds : List Nat)
    (h : ∀ d ∈ ds, d < 2 ^ w) :
    Nat.ofDigits (2 ^ w : Nat) ds < 2 ^ (w * ds.length) := by
  rcases w with _ | w
  · have hz : Nat.ofDigits (1 : Nat) ds = 0 := by
      induction ds with
      | nil => rfl
      | cons d ds ih =>
        have hd : d = 0 := by simpa using h d List.mem_cons_self
        simp only [Nat.ofDigits_cons, hd, Nat.zero_add, Nat.one_mul]
        exact ih (fun e he => h e (List.mem_cons_of_mem _ he))
    simpa using hz
  · rw [Nat.pow_mul]
    exact Nat.ofDigits_lt_base_pow_length (Nat.one_lt_two_pow (by omega)) h

/-- Extracting a list of bounded digits from its Horner value recovers the original list. -/
theorem lanes_ofDigits (w : Nat) : ∀ ds : List Nat, (∀ d ∈ ds, d < 2 ^ w) →
    lanes w ds.length (Nat.ofDigits (2 ^ w : Nat) ds) = ds
  | [], _ => by simp [lanes]
  | d :: ds, h => by
      have hd := h d (by simp)
      rw [List.length_cons, lanes_succ, lane_zero, Nat.ofDigits_cons, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hd,
        Nat.add_mul_div_left _ _ (Nat.two_pow_pos w), Nat.div_eq_of_lt hd, Nat.zero_add,
        lanes_ofDigits w ds (fun e he => h e (by simp [he]))]

/-- The lanes of `b + 2 ^ (w * m) * a` for `b < 2 ^ (w * m)`: those of `b`, then those of `a`. -/
theorem lanes_append (w m k : Nat) {b : Nat} (hb : b < 2 ^ (w * m)) (a : Nat) :
    lanes w (m + k) (b + 2 ^ (w * m) * a) = lanes w m b ++ lanes w k a := by
  induction m generalizing b with
  | zero => simp only [Nat.mul_zero, Nat.pow_zero, Nat.lt_one_iff] at hb; subst hb; simp [lanes]
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

private theorem geom (t : Nat) :
    ∀ n, t * Nat.ofDigits (t + 1 : Nat) (List.replicate n 1) + 1 = (t + 1) ^ n
  | 0 => by simp
  | n + 1 => by
      have ih := geom t n
      simp only [List.replicate_succ, Nat.ofDigits_cons, Nat.pow_succ]
      rw [← ih]; grind

/-- The repeated-one mask is the Horner value of one in every lane. -/
theorem ones_eq_ofDigits (w n : Nat) (hw : 1 ≤ w) :
    ones w n = Nat.ofDigits (2 ^ w : Nat) (List.replicate n 1) := by
  have hpos : 1 ≤ 2 ^ w - 1 := by
    have : 2 ≤ 2 ^ w := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw
    omega
  have hg := geom (2 ^ w - 1) n
  rw [Nat.sub_add_cancel (Nat.one_le_two_pow), ← Nat.pow_mul] at hg
  simp only [ones, pow2_eq, Nat.sub_eq, Nat.mul_eq]
  change (2 ^ (w * n) - 1) / (2 ^ w - 1) = _
  rw [← hg, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ (by omega)]

/-- A constant digit row is the corresponding multiple of the repeated-one row. -/
theorem ofDigits_replicate (b c n : Nat) :
    Nat.ofDigits b (List.replicate n c) = c * Nat.ofDigits b (List.replicate n 1) := by
  rw [Nat.mul_ofDigits, List.map_replicate, Nat.mul_one]

/-- The signed-row bias has the half-range bit set in every lane. -/
theorem bias_eq_ofDigits (w n : Nat) (hw : 1 ≤ w) :
    bias w n = Nat.ofDigits (2 ^ w : Nat) (List.replicate n (2 ^ (w - 1))) := by
  rw [ofDigits_replicate, ← ones_eq_ofDigits w n hw]
  simp [bias, pow2_eq]

/-- Shifting right by whole lanes moves lane `k + a` to lane `k`. -/
theorem lane_shiftRight (w k a u : Nat) : lane w k (u >>> (w * a)) = lane w (k + a) u := by
  rw [lane_eq, lane_eq, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← Nat.pow_add,
    Nat.mul_add, Nat.add_comm (w * a)]

/-- A conjunction acts lane by lane. -/
theorem lane_land (w k u v : Nat) : lane w k (u &&& v) = lane w k u &&& lane w k v := by
  simp only [lane, pow2_eq, Nat.sub_eq, Nat.mul_eq]
  change ((u &&& v) >>> (w * k)) &&& (2 ^ w - 1) =
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
  rw [ones_eq_ofDigits w n hw, ← ofDigits_replicate]
  have h1 := lanes_ofDigits w _ hr
  have h2 := ofDigits_lt w _ hr
  rw [List.length_replicate] at h1 h2
  exact ⟨h1, h2⟩

/-- Lanes split a conjunction when both operands are written lane by lane. -/
theorem land_split {j a b x y : Nat} (ha : a < 2 ^ j) (hb : b < 2 ^ j) :
    (a + 2 ^ j * x) &&& (b + 2 ^ j * y) = (a &&& b) + 2 ^ j * (x &&& y) := by
  have h1 := Nat.mod_add_div ((a + 2 ^ j * x) &&& (b + 2 ^ j * y)) (2 ^ j)
  rw [Nat.and_mod_two_pow, Nat.and_div_two_pow, Nat.add_mul_mod_self_left,
    Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.add_mul_div_left _ _ (Nat.two_pow_pos j),
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos j), Nat.div_eq_of_lt ha, Nat.div_eq_of_lt hb] at h1
  simpa using h1.symm

/-- Bitwise conjunction of bounded digit rows acts separately on each digit. -/
theorem land_ofDigits_map (w : Nat) (f g : Int → Nat) :
    ∀ xs : List Int, (∀ x ∈ xs, f x < 2 ^ w) → (∀ x ∈ xs, g x < 2 ^ w) →
      Nat.ofDigits (2 ^ w : Nat) (xs.map f) &&& Nat.ofDigits (2 ^ w : Nat) (xs.map g) =
        Nat.ofDigits (2 ^ w : Nat) (xs.map fun x => f x &&& g x)
  | [], _, _ => by simp
  | x :: xs, hf, hg => by
      simp only [List.map_cons, Nat.ofDigits_cons]
      rw [land_split (hf x (by simp)) (hg x (by simp)),
        land_ofDigits_map w f g xs (fun y hy => hf y (by simp [hy]))
          (fun y hy => hg y (by simp [hy]))]

/-- A common left factor in every mapped digit factors out of Horner evaluation. -/
theorem ofDigits_map_mul (b c : Nat) (f : Int → Nat) (xs : List Int) :
    Nat.ofDigits b (xs.map fun x => c * f x) = c * Nat.ofDigits b (xs.map f) := by
  simp only [Nat.mul_ofDigits, List.map_map, Function.comp_def]

/-- A common right factor in every mapped digit factors out of Horner evaluation. -/
theorem ofDigits_map_mul_right (b c : Nat) (f : Int → Nat) (xs : List Int) :
    Nat.ofDigits b (xs.map fun x => f x * c) = Nat.ofDigits b (xs.map f) * c := by
  have := ofDigits_map_mul b c f xs
  simp only [Nat.mul_comm _ c]; exact this

/-- `2 ^ w ≡ 1 (mod 2 ^ w - 1)`, so a packed row and the sum of its lanes have the same
remainder. -/
theorem ofDigits_mod (t : Nat) (ds : List Nat) :
    Nat.ofDigits (t + 1 : Nat) ds % t = ds.sum % t := by
  simpa only [Nat.ofDigits_one, Nat.ModEq] using
    Nat.ofDigits_modEq' (t + 1) 1 t (by simp [Nat.ModEq]) ds

/-- The top bit of a bounded word is its quotient by the top-bit weight, at that weight. -/
theorem land_top (m v : Nat) (hv : v < 2 ^ (m + 1)) :
    v &&& 2 ^ m = 2 ^ m * (v / 2 ^ m) := by
  have h := land_split (j := m) (x := v / 2 ^ m) (y := 1) (Nat.mod_lt v (Nat.two_pow_pos m))
    (Nat.two_pow_pos m)
  rw [Nat.mod_add_div, Nat.zero_add, Nat.mul_one, Nat.and_zero, Nat.zero_add] at h
  rw [h]
  have hq : v / 2 ^ m < 2 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos m)]; rw [Nat.pow_succ] at hv; omega
  have hc : v / 2 ^ m = 0 ∨ v / 2 ^ m = 1 := by generalize v / 2 ^ m = q at hq; omega
  rcases hc with e | e <;> rw [e] <;> simp

/-- Integer evaluation of natural digits is the cast of their natural Horner value. -/
theorem eval_natCast (b : Nat) :
    ∀ ds : List Nat, eval (b : Int) (ds.map Nat.cast) = ((Nat.ofDigits b ds : Nat) : Int)
  | [] => rfl
  | d :: ds => by
      simp only [List.map_cons, eval, Nat.ofDigits_cons, eval_natCast b ds,
        Int.natCast_add, Int.natCast_mul]

end FloatLib.Numerics.Packed
