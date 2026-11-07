/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Packed.Proof

/-!
# Windows, rescaling and symmetric rows

These programs reshape a packed row with a few big-number operations, so that the kernel never
walks the lanes one by one, except for `ramp`, which multiplies every entry by its index.

## Main definitions

* `restrict w n a len z` cuts out lanes `[a, a + len)` of a signed row as a row of `len` lanes: one
  shift and one mask.
* `shiftDown w n s z` divides every entry by `2 ^ s`, rounding down, and keeps the lane width;
  `low w n s z` collects the remainders `x % 2 ^ s`, whose sum `laneSum` reads with one more
  remainder. Together they round a row outward to a coarser grid: the row is
  `2 ^ s * shiftDown + low` exactly, every remainder lies in `[0, 2 ^ s)`, and their sum is the `l1`
  distance between the row and its rounding.
* `unfold w n h` writes a half row `a₀, …, aₙ₋₁` out as the two-sided row
  `aₙ₋₁, …, a₁, 2 a₀, a₁, …, aₙ₋₁` (`mirror`), the coefficients of `2 ∑ aₖ cos (k u)` in powers of
  `exp (i u)`, and `unfold w n h (odd := true)` as `-aₙ₋₁, …, -a₁, 0, a₁, …, aₙ₋₁`, those of
  `2 i ∑ aₖ sin (k u)`.
* `signs w n z` multiplies lane `k` of a two-sided row with centre `n - 1` by the sign of
  `k - (n - 1)`, which is the Hilbert multiplier `-i sgn` without its factor `-i`; `signRow` is the
  same on lists.
* `ramp w n u` multiplies entry `k` by `k`, which is what differentiation does to the coefficients
  of a trigonometric polynomial or a power series.

## Main statements

* `restrict_eq`, `shiftDown_eval`, `low_eval`, `laneSum_low`, `unfold_eq`, `signs_eq` and
  `ramp_eq` state each program on the integer lists.
* `eval_shiftDown_add_low`: the rounded row and the remainders put the row back together.
* `entries_ofInt_unfold` and `entries_ramp` read the results back as rows under a range check.
* `signRow_mirror` and `signRow_mirror_odd`: on cosine and sine rows the signs only relabel.

## Implementation notes

`shiftDown` works on the biased row, where entry `x` sits in its lane as `x + 2 ^ (w - 1)`. As long
as `s < w`, the power `2 ^ s` divides the bias, so the low `s` bits of a lane are those of `x`, and
subtracting them leaves an exact multiple of `2 ^ s`. Division by any other number does not act
lane by lane, so a rounding to a decimal grid comes from the caller, and the kernel only measures
its error with `absSum`.

A symmetric row stored as its half is symmetric by construction, so no check ever has to establish
it. I like this one because it removes a whole class of certificate bugs: there is no way to hand
the kernel a cosine row whose two halves disagree.

`ramp` splits the row in halves, like `rev`: the upper half of `n - h` lanes contributes
`2 ^ (w * h) * (ramp + h * value)` of itself. Its cost is a few interpreted steps per lane.

## References

* Yitzhak Katznelson, *An Introduction to Harmonic Analysis*, third edition, Cambridge University
  Press (2004), <https://doi.org/10.1017/CBO9781139165372>, chapter 3 on the conjugate function,
  whose multiplier is `-i sgn n`.

## Tags

packed row, rounding, symmetric row, Hilbert transform
-/

@[expose] public section

namespace FloatLib.Numerics.Packed

/-! ### Kernel programs -/

/-- Lanes `[a, a + len)` of the signed row `z` of `n` lanes, as a signed row of `len` lanes. -/
def restrict (w n a len : Nat) (z : Int) : Int :=
  toInt w len
    (Nat.land (Nat.shiftRight (ofInt w n z) (Nat.mul w a)) (Nat.sub (pow2 (Nat.mul w len)) 1))

/-- The low `s` bits of every lane of the biased row of `z`. For `s < w` they are the remainders
`x % 2 ^ s` of its entries `x`. -/
def low (w n s : Nat) (z : Int) : Nat :=
  Nat.land (ofInt w n z) (Nat.mul (Nat.sub (pow2 s) 1) (ones w n))

/-- Every entry of the signed row `z` of `n` lanes divided by `2 ^ s` and rounded down, in lanes of
the same width. -/
def shiftDown (w n s : Nat) (z : Int) : Int :=
  Int.ediv (Int.sub z (Int.ofNat (low w n s z))) (Int.ofNat (pow2 s))

/-- The two-sided row of the half row `h` of `n` lanes, centred at lane `n - 1`: `mirror` of its
entries, from one reversal and one shift. -/
def unfold (w n h : Nat) (odd : Bool := false) : Int :=
  cond odd (Int.sub (shift w (Nat.sub n 1) (toInt w n h)) (toInt w n (rev w n h)))
    (Int.add (toInt w n (rev w n h)) (shift w (Nat.sub n 1) (toInt w n h)))

/-- The signed row `z` of `2 * n - 1` lanes with lane `k` multiplied by the sign of
`k - (n - 1)`: the upper `n - 1` lanes are kept, the lower ones negated and the centre cleared. -/
def signs (w n : Nat) (z : Int) : Int :=
  Int.sub (shift w n (restrict w (Nat.sub (Nat.mul 2 n) 1) n (Nat.sub n 1) z))
    (restrict w (Nat.sub (Nat.mul 2 n) 1) 0 (Nat.sub n 1) z)

/-- `∑ k < n, k * entry k * 2 ^ (w * k)` for the biased row `u` of `n` lanes, splitting the lanes in
halves; `d` bounds the depth of the recursion. -/
def rampAux (w : Nat) : Nat → Nat → Nat → Int
  | 0, _, _ => 0
  | d + 1, n, u =>
    cond (Nat.ble n 1) 0
      (Int.add (rampAux w d (Nat.div n 2) (Nat.land u (Nat.sub (pow2 (Nat.mul w (Nat.div n 2))) 1)))
        (shift w (Nat.div n 2)
          (Int.add
            (rampAux w d (Nat.sub n (Nat.div n 2)) (Nat.shiftRight u (Nat.mul w (Nat.div n 2))))
            (Int.mul (Int.ofNat (Nat.div n 2))
              (toInt w (Nat.sub n (Nat.div n 2)) (Nat.shiftRight u (Nat.mul w (Nat.div n 2))))))))

/-- The signed row whose entry `k` is `k` times entry `k` of the biased row `u` of `n` lanes. -/
def ramp (w n u : Nat) : Int := rampAux w n n u

/-! ### Integer rows -/

/-- The two-sided row of a half row `a₀, a₁, …, aₙ₋₁`: `aₙ₋₁, …, a₁, 2 a₀, a₁, …, aₙ₋₁`, or with
`(odd := true)` the row `-aₙ₋₁, …, -a₁, 0, a₁, …, aₙ₋₁`. -/
def mirror (a : List Int) (odd : Bool := false) : List Int :=
  match a with
  | [] => []
  | a₀ :: as => (cond odd (as.map (- ·)) as).reverse ++ cond odd 0 (2 * a₀) :: as

/-- Entry `k` multiplied by the sign of `k - c`. -/
def signRow (c : Nat) (xs : List Int) : List Int :=
  xs.mapIdx fun k x => Int.sign ((k : Int) - c) * x

/-! ### Lanes of shifts and masks -/

private theorem shift_eq (w k : Nat) (z : Int) : shift w k z = (2 ^ w) ^ k * z := by
  simp only [shift, pow2_eq, Nat.mul_eq, Int.mul_def, Int.ofNat_eq_natCast, natCast_two_pow,
    Int.pow_mul, Int.mul_comm]

/-- Shifting right by whole lanes moves lane `k + a` to lane `k`. -/
theorem lane_shiftRight (w k a u : Nat) : lane w k (u >>> (w * a)) = lane w (k + a) u := by
  rw [lane_eq, lane_eq, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← Nat.pow_add,
    Nat.mul_add, Nat.add_comm (w * a)]

private theorem entries_drop_take {w n a len : Nat} (h : a + len ≤ n) (u : Nat) :
    ((entries w n u).drop a).take len = (List.range len).map fun k => entry w (k + a) u := by
  apply List.ext_getElem
  · simp [length_entries]; omega
  · intro k h1 h2
    simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
    rw [getElem_entries]
    congr 1; omega

/-! ### Windows -/

/-- `restrict` reads lanes `[a, a + len)` of the biased row of `z`, whatever `z` is. -/
theorem restrict_eq {w n a len : Nat} (hw : 1 ≤ w) (h : a + len ≤ n) (z : Int) :
    restrict w n a len z = eval (2 ^ w) (((entries w n (ofInt w n z)).drop a).take len) := by
  simp only [restrict, pow2_eq, Nat.mul_eq, Nat.sub_eq]
  generalize ofInt w n z = u
  have hv : (u >>> (w * a)) &&& (2 ^ (w * len) - 1) < 2 ^ (w * len) := by
    rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hent : entries w len ((u >>> (w * a)) &&& (2 ^ (w * len) - 1)) =
      ((entries w n u).drop a).take len := by
    rw [entries_drop_take h, entries_eq_lanes, Nat.and_two_pow_sub_one_eq_mod, lanes_mod]
    simp [lanes, lane_shiftRight, entry_eq]
  show toInt w len ((u >>> (w * a)) &&& (2 ^ (w * len) - 1)) = _
  rw [← eval_entries hw hv, hent]

/-! ### Rounding to a coarser grid -/

private theorem emod_biased {w s : Nat} (hs : s < w) (x : Int) :
    (x + 2 ^ (w - 1)) % 2 ^ s = x % 2 ^ s := by
  have : (2 : Int) ^ (w - 1) = 2 ^ s * 2 ^ (w - 1 - s) := by
    rw [← Int.pow_add]; congr 1; omega
  rw [this, Int.add_mul_emod_self_left]

private theorem lanes_ofInt_eval {w n : Nat} (hw : 1 ≤ w) {xs : List Int} (hn : xs.length ≤ n)
    (hx : ∀ x ∈ xs, Fits w x) :
    (lanes w n (ofInt w n (eval (2 ^ w) xs))).map (fun d : Nat => (d : Int)) =
      (xs ++ List.replicate (n - xs.length) 0).map (· + 2 ^ (w - 1)) := by
  have h := entries_ofInt_eval hw hn hx
  rw [entries_eq_lanes] at h
  rw [← h, List.map_map]
  apply List.map_congr_left
  intro d _
  simp

private theorem lanes_land_ones {w n c : Nat} (hw : 1 ≤ w) (hc : c < 2 ^ w) (u : Nat) :
    lanes w n (u &&& c * ones w n) = (lanes w n u).map (· &&& c) := by
  have hm := (lanes_mul_ones (n := n) hw hc).1
  have hk : ∀ k ∈ List.range n, lane w k (c * ones w n) = c := by
    intro k hk
    apply List.eq_of_mem_replicate (n := n)
    rw [← hm]; exact List.mem_map_of_mem hk
  simp only [lanes, List.map_map]
  apply List.map_congr_left
  intro k hk'
  simp [lane_land, hk k hk']

private theorem lanes_low {w n s : Nat} (hs : s < w) {xs : List Int} (hn : xs.length ≤ n)
    (hx : ∀ x ∈ xs, Fits w x) :
    (lanes w n (low w n s (eval (2 ^ w) xs))).map (fun d : Nat => (d : Int)) =
      (xs ++ List.replicate (n - xs.length) 0).map (· % 2 ^ s) := by
  have hw : 1 ≤ w := by omega
  have hc : 2 ^ s - 1 < 2 ^ w := by
    have := Nat.pow_lt_pow_right (a := 2) (by decide) hs
    have := Nat.two_pow_pos s
    omega
  have hl := lanes_ofInt_eval hw hn hx
  simp only [low, pow2_eq, Nat.sub_eq, Nat.mul_eq]
  show (lanes w n (ofInt w n (eval (2 ^ w) xs) &&& (2 ^ s - 1) * ones w n)).map _ = _
  rw [lanes_land_ones hw hc]
  generalize ofInt w n (eval (2 ^ w) xs) = u at hl
  have e := natCast_two_pow s
  calc ((lanes w n u).map (· &&& (2 ^ s - 1))).map (fun d : Nat => (d : Int))
      = ((lanes w n u).map (fun d : Nat => (d : Int))).map (· % 2 ^ s) := by
        simp only [List.map_map]
        apply List.map_congr_left
        intro d _
        simp only [Function.comp_apply, Nat.and_two_pow_sub_one_eq_mod]
        rw [← e]; push_cast; rfl
    _ = _ := by
        rw [hl, List.map_map]
        apply List.map_congr_left
        intro x _
        exact emod_biased hs x

private theorem natCast_sum (ds : List Nat) :
    ((ds.map fun d : Nat => (d : Int)).sum) = (ds.sum : Int) := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [ih]

private theorem l1_of_nonneg : ∀ {zs : List Int}, (∀ z ∈ zs, 0 ≤ z) → (l1 zs : Int) = zs.sum
  | [], _ => rfl
  | z :: zs, h => by
      rw [l1_cons, List.sum_cons, Int.natCast_add, l1_of_nonneg (fun y hy => h y (by simp [hy]))]
      have := h z (by simp)
      omega

private theorem sum_le_of_le {m : Nat} : ∀ {ds : List Nat}, (∀ d ∈ ds, d ≤ m) →
    ds.sum ≤ ds.length * m
  | [], _ => by simp
  | d :: ds, h => by
      have := sum_le_of_le (ds := ds) (fun e he => h e (by simp [he]))
      have := h d (by simp)
      simp only [List.sum_cons, List.length_cons, Nat.succ_mul]
      omega

/-- `low` holds the remainders of the entries modulo `2 ^ s`. -/
theorem low_eval {w n s : Nat} (hs : s < w) {xs : List Int} (hn : xs.length ≤ n)
    (hx : ∀ x ∈ xs, Fits w x) :
    (low w n s (eval (2 ^ w) xs) : Int) = eval (2 ^ w) (xs.map (· % 2 ^ s)) := by
  have hw : 1 ≤ w := by omega
  have hlt : low w n s (eval (2 ^ w) xs) < 2 ^ (w * n) := by
    simp only [low]
    exact Nat.lt_of_le_of_lt Nat.and_le_left (ofInt_eval_lt hw hn hx)
  rw [← eval_lanes hlt, lanes_low hs hn hx]
  simp [eval_append]

/-- `shiftDown` divides every entry by `2 ^ s`, rounding down, when the entries fit. -/
theorem shiftDown_eval {w n s : Nat} (hs : s < w) {xs : List Int} (hn : xs.length ≤ n)
    (hx : ∀ x ∈ xs, Fits w x) :
    shiftDown w n s (eval (2 ^ w) xs) = eval (2 ^ w) (xs.map (· / 2 ^ s)) := by
  have key : eval (2 ^ w) xs - eval (2 ^ w) (xs.map (· % 2 ^ s)) =
      2 ^ s * eval (2 ^ w) (xs.map (· / 2 ^ s)) := by
    rw [← eval_smul, ← eval_sub]
    congr 1
    induction xs with
    | nil => rfl
    | cons x xs ih =>
        simp only [List.map_cons, sub, add, smul, List.map_map] at ih ⊢
        rw [ih (by simp at hn; omega) (fun y hy => hx y (by simp [hy]))]
        congr 1
        have := Int.emod_add_mul_ediv x (2 ^ s); simp; omega
  simp only [shiftDown, Int.ofNat_eq_natCast, low_eval hs hn hx, pow2_eq]
  show (eval (2 ^ w) xs - eval (2 ^ w) (xs.map (· % 2 ^ s))) / ((2 ^ s : Nat) : Int) = _
  rw [key, natCast_two_pow, Int.mul_ediv_cancel_left _ (Int.pow_ne_zero (by decide))]

/-- The remainders and the rounded entries put the row back together: `x = 2 ^ s * (x / 2 ^ s) +
x % 2 ^ s` in every lane. -/
theorem eval_shiftDown_add_low {w n s : Nat} (hs : s < w) {xs : List Int} (hn : xs.length ≤ n)
    (hx : ∀ x ∈ xs, Fits w x) :
    eval (2 ^ w) xs = 2 ^ s * shiftDown w n s (eval (2 ^ w) xs) + low w n s (eval (2 ^ w) xs) := by
  rw [shiftDown_eval hs hn hx, low_eval hs hn hx, ← eval_smul, ← eval_add]
  congr 1
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, add, smul] at ih ⊢
      rw [← ih (by simp at hn; omega) (fun y hy => hx y (by simp [hy]))]
      congr 1
      have := Int.emod_add_mul_ediv x (2 ^ s); omega

/-- One remainder sums the remainders, which is the `l1` distance between the row and its
rounding, when `n * (2 ^ s - 1) < 2 ^ w - 1`. -/
theorem laneSum_low {w n s : Nat} (hs : s < w) {xs : List Int} (hn : xs.length ≤ n)
    (hx : ∀ x ∈ xs, Fits w x) (hroom : n * (2 ^ s - 1) < 2 ^ w - 1) :
    laneSum w (low w n s (eval (2 ^ w) xs)) = l1 (xs.map (· % 2 ^ s)) := by
  have hw : 1 ≤ w := by omega
  have hlt : low w n s (eval (2 ^ w) xs) < 2 ^ (w * n) := by
    simp only [low]
    exact Nat.lt_of_le_of_lt Nat.and_le_left (ofInt_eval_lt hw hn hx)
  have hl := lanes_low hs hn hx
  have hpos : (0 : Int) < 2 ^ s := Int.pow_pos (by decide)
  have e := natCast_two_pow s
  have hnn : ∀ z ∈ xs.map (· % 2 ^ s), 0 ≤ z := by
    intro z hz
    simp only [List.mem_map] at hz
    obtain ⟨x, _, rfl⟩ := hz
    exact Int.emod_nonneg x (Int.ne_of_gt hpos)
  have hsum : ((lanes w n (low w n s (eval (2 ^ w) xs))).sum : Int) = l1 (xs.map (· % 2 ^ s)) := by
    rw [← natCast_sum, hl, l1_of_nonneg hnn, List.map_append, List.sum_append]
    simp
  have hle : (lanes w n (low w n s (eval (2 ^ w) xs))).sum ≤ n * (2 ^ s - 1) := by
    have hb : ∀ d ∈ lanes w n (low w n s (eval (2 ^ w) xs)), d ≤ 2 ^ s - 1 := by
      intro d hd
      have hd' : (d : Int) ∈ (xs ++ List.replicate (n - xs.length) 0).map (· % 2 ^ s) := by
        rw [← hl]; exact List.mem_map_of_mem hd
      simp only [List.mem_map] at hd'
      obtain ⟨x, _, hxd⟩ := hd'
      have := Int.emod_lt_of_pos x hpos
      omega
    have := sum_le_of_le hb
    rwa [length_lanes] at this
  rw [laneSum_eq hlt (by omega)]
  exact_mod_cast hsum

/-! ### Symmetric rows -/

/-- A two-sided row from a half row of `n` entries has `2 * n - 1` entries. -/
theorem length_mirror (a : List Int) (odd : Bool) : (mirror a odd).length = 2 * a.length - 1 := by
  cases a with
  | nil => rfl
  | cons a₀ as => cases odd <;> simp [mirror] <;> omega

/-- The value of a two-sided row: the reversed half row plus the half row moved up to the centre,
with a minus sign on the reversed half for odd rows. -/
theorem eval_mirror (b : Int) (a : List Int) (odd : Bool) :
    eval b (mirror a odd) =
      cond odd (b ^ (a.length - 1) * eval b a - eval b a.reverse)
        (eval b a.reverse + b ^ (a.length - 1) * eval b a) := by
  cases a with
  | nil => cases odd <;> simp [mirror, eval]
  | cons a₀ as =>
      have hrev : ∀ ys : List Int, eval b (ys.map (- ·)).reverse = -eval b ys.reverse := by
        intro ys
        rw [← List.map_reverse, ← neg_eval]
      cases odd <;>
      simp only [mirror, Bool.cond_false, Bool.cond_true, eval_append, List.reverse_cons, eval,
        List.length_reverse, List.length_map, List.length_cons, Nat.add_sub_cancel, hrev] <;>
      grind

/-- `unfold` builds the two-sided row of the half row `h` by one reversal and one shift. -/
theorem unfold_eq {w n h : Nat} (hw : 1 ≤ w) (hh : h < 2 ^ (w * n)) (odd : Bool) :
    unfold w n h odd = eval (2 ^ w) (mirror (entries w n h) odd) := by
  have intSub : ∀ a b : Int, Int.sub a b = a - b := fun _ _ => rfl
  rw [eval_mirror, length_entries, ← entries_rev, eval_entries hw hh,
    eval_entries hw (rev_lt w n h)]
  cases odd <;>
  simp only [unfold, Bool.cond_false, Bool.cond_true, shift, pow2_eq, Nat.mul_eq, Nat.sub_eq,
    Int.add_def, intSub, Int.mul_def, Int.ofNat_eq_natCast, natCast_two_pow, ← Int.pow_mul] <;>
  grind

/-- The two-sided row of a half row with entries in `[-2 ^ g, 2 ^ g)` fits lanes of width `w` when
`g + 2 ≤ w`: the doubled centre needs the extra bit. -/
theorem fits_of_mem_mirror {w g : Nat} (hg : g + 2 ≤ w) {a : List Int}
    (ha : ∀ x ∈ a, -2 ^ g ≤ x ∧ x < 2 ^ g) (odd : Bool) : ∀ y ∈ mirror a odd, Fits w y := by
  have e1 : (2 : Int) ^ (w - 1) = 2 ^ (w - 1 - (g + 1)) * 2 ^ (g + 1) := by
    rw [← Int.pow_add]; congr 1; omega
  have e2 : (2 : Int) ^ (g + 1) = 2 * 2 ^ g := Int.pow_succ' 2 g
  have hp : (1 : Int) ≤ 2 ^ (w - 1 - (g + 1)) := Int.pow_pos (by decide)
  have hq : (0 : Int) < 2 ^ g := Int.pow_pos (by decide)
  have hb : (2 : Int) * 2 ^ g ≤ 2 ^ (w - 1) := by
    have := Int.mul_le_mul_of_nonneg_right hp (by omega : (0 : Int) ≤ 2 * 2 ^ g)
    rw [Int.one_mul] at this
    rw [e1, e2]; exact this
  have fit : ∀ x : Int, -(2 * 2 ^ g) ≤ x → x < 2 * 2 ^ g → Fits w x := fun x h1 h2 => by
    unfold Fits; omega
  intro y hy
  cases a with
  | nil => simp [mirror] at hy
  | cons a₀ as =>
      have h₀ := ha a₀ (by simp)
      have hs : ∀ x ∈ as, -2 ^ g ≤ x ∧ x < 2 ^ g := fun x hx => ha x (by simp [hx])
      cases odd <;> simp only [mirror, Bool.cond_false, Bool.cond_true, List.mem_append,
        List.mem_reverse, List.mem_cons, List.mem_map] at hy
      · rcases hy with hy | rfl | hy
        · have := hs y hy; exact fit y (by omega) (by omega)
        · exact fit _ (by omega) (by omega)
        · have := hs y hy; exact fit y (by omega) (by omega)
      · rcases hy with ⟨x, hx, rfl⟩ | rfl | hy
        · have := hs x hx; exact fit _ (by omega) (by omega)
        · exact fit 0 (by omega) (by omega)
        · have := hs y hy; exact fit y (by omega) (by omega)

/-- The two-sided row that `unfold` builds from a guarded half row reads back as `mirror` of its
entries, when `g + 2 ≤ w`, so that the doubled centre entry still fits. -/
theorem entries_ofInt_unfold {w g n h : Nat} (hh : guard w g n h = true) (hg : g + 2 ≤ w)
    (odd : Bool) :
    entries w (2 * n - 1) (ofInt w (2 * n - 1) (unfold w n h odd)) =
      mirror (entries w n h) odd := by
  obtain ⟨-, hlt, hb⟩ := guard_sound hh
  have hw : 1 ≤ w := by omega
  have hlen : (mirror (entries w n h) odd).length = 2 * n - 1 := by
    rw [length_mirror, length_entries]
  rw [unfold_eq hw hlt, entries_ofInt_eval hw (Nat.le_of_eq hlen) (fits_of_mem_mirror hg hb odd),
    hlen, Nat.sub_self, List.replicate_zero, List.append_nil]

/-- The `l1` norm of a two-sided row is at most twice that of its half row. -/
theorem l1_mirror_le (a : List Int) (odd : Bool) : l1 (mirror a odd) ≤ 2 * l1 a := by
  cases a with
  | nil => simp [mirror, l1]
  | cons a₀ as =>
      have hneg : l1 (as.map (- ·)) = l1 as := by simp [l1, Function.comp_def]
      cases odd <;> simp only [mirror, Bool.cond_false, Bool.cond_true, l1, List.map_append,
        List.sum_append, List.map_reverse, List.sum_reverse, List.map_cons, List.sum_cons] <;>
      simp only [l1] at hneg <;> simp [Int.natAbs_mul] at * <;> omega

/-! ### Signs -/

private theorem signRow_split (c : Nat) (A : List Int) (x : Int) (B : List Int)
    (hA : A.length = c) :
    signRow c (A ++ x :: B) = A.map (- ·) ++ 0 :: B := by
  simp only [signRow, List.mapIdx_append, List.mapIdx_cons]
  congr 1
  · apply List.ext_getElem (by simp)
    intro k h1 h2
    simp only [List.getElem_mapIdx, List.getElem_map]
    have hk : k < c := by simp at h1; omega
    have : Int.sign ((k : Int) - c) = -1 := Int.sign_eq_neg_one_of_neg (by omega)
    rw [this]; omega
  · congr 1
    · simp [hA]
    · apply List.ext_getElem (by simp)
      intro k h1 h2
      simp only [List.getElem_mapIdx]
      have : Int.sign (((k + 1 + A.length : Nat) : Int) - c) = 1 :=
        Int.sign_eq_one_of_pos (by omega)
      rw [this, Int.one_mul]

/-- `signs` multiplies lane `k` of a two-sided row of `2 * n - 1` lanes by the sign of
`k - (n - 1)`, for any `z`. -/
theorem signs_eq {w n : Nat} (hw : 1 ≤ w) (z : Int) :
    signs w n z =
      eval (2 ^ w) (signRow (n - 1) (entries w (2 * n - 1) (ofInt w (2 * n - 1) z))) := by
  have intSub : ∀ a b : Int, Int.sub a b = a - b := fun _ _ => rfl
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [signs, restrict_eq hw, shift, entries, signRow, eval, intSub]
  have h1 : n + (n - 1) ≤ 2 * n - 1 := by omega
  have h0 : 0 + (n - 1) ≤ 2 * n - 1 := by omega
  simp only [signs, Nat.mul_eq, Nat.sub_eq, intSub]
  rw [restrict_eq hw h1, restrict_eq hw h0, shift_eval]
  have hlen := length_entries w (2 * n - 1) (ofInt w (2 * n - 1) z)
  generalize entries w (2 * n - 1) (ofInt w (2 * n - 1) z) = es at hlen ⊢
  have hsplit : es = es.take (n - 1) ++ es[n - 1]'(by omega) :: es.drop n := by
    have := List.drop_eq_getElem_cons (l := es) (i := n - 1) (by omega)
    rw [Nat.sub_add_cancel hn] at this
    rw [← this, List.take_append_drop]
  have htake : (es.drop n).take (n - 1) = es.drop n := List.take_of_length_le (by simp; omega)
  rw [htake, List.drop_zero, eval_append, eval_zeros, List.length_replicate, Int.zero_add]
  conv => rhs; rw [hsplit]
  rw [signRow_split (n - 1) _ _ _ (by simp; omega), eval_append, ← neg_eval]
  rw [List.length_map, List.length_take, show min (n - 1) es.length = n - 1 by omega]
  simp only [eval]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel, Int.pow_succ]
  grind

/-- On a cosine row the signs are a relabelling: they turn `mirror a` into the sine row
`mirror a (odd := true)`. -/
theorem signRow_mirror (a : List Int) : signRow (a.length - 1) (mirror a) = mirror a true := by
  cases a with
  | nil => rfl
  | cons a₀ as =>
      simp only [mirror, Bool.cond_false, Bool.cond_true, List.length_cons, Nat.add_sub_cancel]
      rw [signRow_split _ _ _ _ (by simp), List.map_reverse]

/-- On a sine row the signs give the cosine row of the same entries with the constant term
cleared. -/
theorem signRow_mirror_odd (a : List Int) :
    signRow (a.length - 1) (mirror a true) = mirror (a.set 0 0) := by
  cases a with
  | nil => rfl
  | cons a₀ as =>
      simp only [mirror, Bool.cond_false, Bool.cond_true, List.length_cons, Nat.add_sub_cancel,
        List.set_cons_zero]
      rw [signRow_split _ _ _ _ (by simp), List.map_reverse, List.map_map]
      simp [Function.comp_def]

/-! ### Derivative weights -/

private theorem eval_mapIdx_shift (b : Int) : ∀ (ys : List Int) (m : Nat),
    eval b (ys.mapIdx fun k y => ((k + m : Nat) : Int) * y) =
      eval b (ys.mapIdx fun k y => (k : Int) * y) + m * eval b ys
  | [], _ => by simp [eval]
  | y :: ys, m => by
      simp only [List.mapIdx_cons, eval]
      have h1 := eval_mapIdx_shift b ys (m + 1)
      have h2 := eval_mapIdx_shift b ys 1
      have e1 : (fun k y => ((k + 1 + m : Nat) : Int) * y) =
          (fun k y => ((k + (m + 1) : Nat) : Int) * y) := by
        funext k y; congr 2; omega
      have e2 : (fun k y => ((k + 1 : Nat) : Int) * y) = (fun k y => ((k + 1 : Nat) : Int) * y) :=
        rfl
      rw [e1, h1]
      rw [show (fun (k : Nat) (y : Int) => (((k + 1 : Nat) : Int)) * y) =
          (fun k y => ((k + 1 : Nat) : Int) * y) from rfl] at h2
      simp only [Nat.zero_add] at *
      rw [h2]
      push_cast
      grind

private theorem eval_mapIdx_append (b : Int) (xs ys : List Int) :
    eval b ((xs ++ ys).mapIdx fun k x => (k : Int) * x) =
      eval b (xs.mapIdx fun k x => (k : Int) * x) +
        b ^ xs.length * (eval b (ys.mapIdx fun k x => (k : Int) * x) + xs.length * eval b ys) := by
  rw [List.mapIdx_append, eval_append, List.length_mapIdx, ← eval_mapIdx_shift]

private theorem rampAux_spec (w : Nat) (hw : 1 ≤ w) : ∀ d n u, n ≤ d → u < 2 ^ (w * n) →
    rampAux w d n u = eval (2 ^ w) ((entries w n u).mapIdx fun k x => (k : Int) * x)
  | 0, n, u, h, _ => by
      have : n = 0 := by omega
      subst this; simp [rampAux, entries, eval]
  | d + 1, n, u, hnd, hu => by
      by_cases hn : n ≤ 1
      · have hb : Nat.ble n 1 = true := Nat.ble_eq.mpr hn
        simp only [rampAux, hb, Bool.cond_true]
        rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl <;> simp [entries, eval]
      · have hb : Nat.ble n 1 = false :=
          Bool.eq_false_iff.mpr (fun h' => hn (Nat.le_of_ble_eq_true h'))
        simp only [rampAux, hb, Bool.cond_false, pow2_eq, Nat.mul_eq, Nat.sub_eq, Int.add_def,
          Int.mul_def,
          Int.ofNat_eq_natCast]
        show rampAux w d (n / 2) (u &&& 2 ^ (w * (n / 2)) - 1) +
            shift w (n / 2) (rampAux w d (n - n / 2) (u >>> (w * (n / 2))) +
              ((n / 2 : Nat) : Int) * toInt w (n - n / 2) (u >>> (w * (n / 2)))) = _
        rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
        have hh1 : n / 2 ≤ d := by omega
        have hr1 : n - n / 2 ≤ d := by omega
        have hhn : n / 2 ≤ n := Nat.div_le_self n 2
        generalize n / 2 = h at hh1 hr1 hhn ⊢
        obtain ⟨r, rfl⟩ : ∃ r, n = h + r := ⟨n - h, by omega⟩
        rw [Nat.add_sub_cancel_left] at hr1 ⊢
        have hlo : u % 2 ^ (w * h) < 2 ^ (w * h) := Nat.mod_lt _ (Nat.two_pow_pos _)
        have hhi : u / 2 ^ (w * h) < 2 ^ (w * r) := by
          rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, ← Nat.mul_add,
            Nat.add_comm r h]
          exact hu
        rw [rampAux_spec w hw d h _ hh1 hlo, rampAux_spec w hw d r _ hr1 hhi,
          ← eval_entries hw hhi, shift_eq]
        have hsplit : entries w (h + r) u = entries w h (u % 2 ^ (w * h)) ++
            entries w r (u / 2 ^ (w * h)) := by
          rw [entries_eq_lanes, entries_eq_lanes, entries_eq_lanes, lanes_split, List.map_append]
        rw [hsplit, eval_mapIdx_append, length_entries]

/-- `ramp` multiplies entry `k` by `k`. -/
theorem ramp_eq {w n u : Nat} (hw : 1 ≤ w) (hu : u < 2 ^ (w * n)) :
    ramp w n u = eval (2 ^ w) ((entries w n u).mapIdx fun k x => (k : Int) * x) :=
  rampAux_spec w hw n n u (Nat.le_refl n) hu

/-- The derivative row of a guarded row: entry `k` times `k` reads back as such when
`n * 2 ^ g ≤ 2 ^ (w - 1)`. -/
theorem entries_ramp {w g n u : Nat} (hu : guard w g n u = true) (hroom : n * 2 ^ g ≤ 2 ^ (w - 1)) :
    entries w n (ofInt w n (ramp w n u)) = (entries w n u).mapIdx fun k x => (k : Int) * x := by
  obtain ⟨hgw, hlt, hb⟩ := guard_sound hu
  have hw : 1 ≤ w := by omega
  have hlen : ((entries w n u).mapIdx fun k x => (k : Int) * x).length = n := by
    simp [length_entries]
  have hroom' : (n : Int) * 2 ^ g ≤ 2 ^ (w - 1) := by
    have := natCast_two_pow g
    have := natCast_two_pow (w - 1)
    have h := (Int.ofNat_le.mpr hroom)
    push_cast at h
    omega
  have hfit : ∀ y ∈ (entries w n u).mapIdx (fun k x => (k : Int) * x), Fits w y := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := List.mem_mapIdx.mp hy
    have hk' : k < n := by rw [length_entries] at hk; exact hk
    have hx := hb _ (List.getElem_mem hk)
    generalize (entries w n u)[k] = x at hx
    have hq : (0 : Int) < 2 ^ g := Int.pow_pos (by decide)
    have hk0 : (0 : Int) ≤ k := Int.natCast_nonneg k
    have h1 : (k : Int) * x ≤ k * 2 ^ g := Int.mul_le_mul_of_nonneg_left (Int.le_of_lt hx.2) hk0
    have h2 : (k : Int) * -2 ^ g ≤ k * x := Int.mul_le_mul_of_nonneg_left hx.1 hk0
    have h3 : (k : Int) * 2 ^ g ≤ ((n : Int) - 1) * 2 ^ g :=
      Int.mul_le_mul_of_nonneg_right (by omega) (Int.le_of_lt hq)
    rw [Int.sub_mul, Int.one_mul] at h3
    rw [Int.mul_neg] at h2
    unfold Fits
    omega
  rw [ramp_eq hw hlt, entries_ofInt_eval hw (Nat.le_of_eq hlen) hfit, hlen, Nat.sub_self,
    List.replicate_zero, List.append_nil]

end FloatLib.Numerics.Packed
