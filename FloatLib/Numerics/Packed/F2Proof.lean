/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Packed.F2
public import FloatLib.Numerics.Packed.Lanes

/-!
# Soundness of the packed products over the field of two elements

* `fits_iff`: `fits w M` says that `M` has at most `w` rows, each below `2 ^ w`.
* `lane_mul`: under `fits`, lane `i < n` of `F2.mul w n B M` is the product `rowMul` of lane `i`
  of `B` with `M`, for every `B`.
* `square_iff`: `square n M` says that `M` has exactly `n` rows, each below `2 ^ n`.
* `isInverse_sound`: a passing `isInverse w n B M` gives `rowMul (lane w i B) M = 2 ^ i` for every
  `i < n`: row `i` of `B` times `M` is the `i`-th unit row.
* `isInverse_square`: a passing `isInverse w n B M` has `n ≤ w` and an `n` by `n` matrix `M`.
-/

@[expose] public section

namespace FloatLib.Numerics.Packed.F2

/-- The loop of `fits`, named for the proof. -/
private noncomputable def fitsLoop (w : Nat) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun k => Nat.ble k w)
    (fun m _ step k => Bool.and (Nat.beq (Nat.shiftRight m w) 0) (step (Nat.succ k)))

private theorem fitsLoop_iff (w : Nat) : ∀ (M : List Nat) (k : Nat),
    fitsLoop w M k = true ↔ k + M.length ≤ w ∧ ∀ m ∈ M, m < 2 ^ w
  | [], k => by
    change Nat.ble k w = true ↔ _
    rw [Nat.ble_eq]
    simp
  | m :: M, k => by
    change Bool.and (Nat.beq (m >>> w) 0) (fitsLoop w M (k + 1)) = true ↔ _
    rw [Bool.and_eq_true, fitsLoop_iff w M (k + 1), Nat.beq_eq, Nat.shiftRight_eq_div_pow,
      Nat.div_eq_zero_iff_lt (Nat.two_pow_pos w)]
    simp only [List.length_cons, List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨hm, hlen, hM⟩
      exact ⟨by omega, hm, hM⟩
    · rintro ⟨hlen, hm, hM⟩
      exact ⟨hm, by omega, hM⟩

/-- `fits w M` holds exactly when `M` has at most `w` rows, each below `2 ^ w`. -/
theorem fits_iff (w : Nat) (M : List Nat) :
    fits w M = true ↔ M.length ≤ w ∧ ∀ m ∈ M, m < 2 ^ w := by
  have h := fitsLoop_iff w M 0
  rwa [Nat.zero_add] at h

/-- The loop of `square`, named for the proof. -/
private noncomputable def squareLoop (n : Nat) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun k => Nat.beq k n)
    (fun m _ step k => Bool.and (Nat.beq (Nat.shiftRight m n) 0) (step (Nat.succ k)))

private theorem squareLoop_iff (n : Nat) : ∀ (M : List Nat) (k : Nat),
    squareLoop n M k = true ↔ k + M.length = n ∧ ∀ m ∈ M, m < 2 ^ n
  | [], k => by
    change Nat.beq k n = true ↔ _
    rw [Nat.beq_eq]
    simp
  | m :: M, k => by
    change Bool.and (Nat.beq (m >>> n) 0) (squareLoop n M (k + 1)) = true ↔ _
    rw [Bool.and_eq_true, squareLoop_iff n M (k + 1), Nat.beq_eq, Nat.shiftRight_eq_div_pow,
      Nat.div_eq_zero_iff_lt (Nat.two_pow_pos n)]
    simp only [List.length_cons, List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨hm, hlen, hM⟩
      exact ⟨by omega, hm, hM⟩
    · rintro ⟨hlen, hm, hM⟩
      exact ⟨hm, by omega, hM⟩

/-- `square n M` holds exactly when `M` has `n` rows, each below `2 ^ n`. -/
theorem square_iff (n : Nat) (M : List Nat) :
    square n M = true ↔ M.length = n ∧ ∀ m ∈ M, m < 2 ^ n := by
  have h := squareLoop_iff n M 0
  rwa [Nat.zero_add] at h

/-- The rows of an `n` by `n` matrix fit lanes of `w ≥ n` bits. -/
theorem fits_of_square {w n : Nat} {M : List Nat} (hw : n ≤ w) (h : square n M = true) :
    fits w M = true := by
  obtain ⟨hlen, hM⟩ := (square_iff n M).1 h
  exact (fits_iff w M).2 ⟨by omega, fun m hm =>
    Nat.lt_of_lt_of_le (hM m hm) (Nat.pow_le_pow_right (by decide) hw)⟩

/-- The loop of `mul`, named for the proof. -/
private noncomputable def mulLoop (w n B : Nat) : List Nat → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun m _ step k acc =>
      step (Nat.succ k)
        (Nat.xor acc (Nat.mul (Nat.land (Nat.shiftRight B k) (ones w n)) m)))

/-- The row of bits number `k` of every lane, times `m`, holds `m` in the lanes whose bit is
set. -/
private theorem lane_flags_mul {w n i k m B : Nat} (hk : k < w) (hm : m < 2 ^ w) (hi : i < n) :
    lane w i (((B >>> k) &&& ones w n) * m) = m * ((lane w i B >>> k) &&& 1) := by
  have hw : 1 ≤ w := by omega
  have hflag : ∀ j, lane w j ((B >>> k) &&& ones w n) ≤ 1 := by
    intro j
    rw [lane_land, lane_ones hw]
    split
    · exact Nat.and_le_right
    · simp
  have hroom : ∀ j, lane w j ((B >>> k) &&& ones w n) * m < 2 ^ w := by
    intro j
    have := hflag j
    have h1 : lane w j ((B >>> k) &&& ones w n) * m ≤ 1 * m := Nat.mul_le_mul_right m this
    omega
  rw [lane_mul m hroom i, lane_land, lane_ones hw, ite_eq_left hi, Nat.mul_comm]
  congr 1
  have hshift := lane_shiftRight_mod (Nat.le_of_lt hk) i B
  have hd : 2 ∣ 2 ^ (w - k) := by
    obtain ⟨j, hj⟩ : ∃ j, w - k = j + 1 := ⟨w - k - 1, by omega⟩
    rw [hj, Nat.pow_succ]
    exact Nat.dvd_mul_left 2 _
  rw [← hshift, Nat.and_one_is_mod, Nat.and_one_is_mod]
  exact (Nat.mod_mod_of_dvd _ hd).symm

private theorem mulLoop_lane {w n i B : Nat} (hi : i < n) : ∀ (M : List Nat) (k acc : Nat),
    k + M.length ≤ w → (∀ m ∈ M, m < 2 ^ w) →
      lane w i (mulLoop w n B M k acc) = lane w i acc ^^^ rowMul (lane w i B >>> k) M
  | [], k, acc, _, _ => by
    change lane w i acc = _
    simp [rowMul]
  | m :: M, k, acc, hlen, hM => by
    have hk : k < w := by
      simp only [List.length_cons] at hlen
      omega
    have hm : m < 2 ^ w := hM m (by simp)
    change lane w i (mulLoop w n B M (k + 1) (acc ^^^ ((B >>> k) &&& ones w n) * m)) = _
    rw [mulLoop_lane hi M (k + 1) _ (by simp only [List.length_cons] at hlen; omega)
      (fun x hx => hM x (by simp [hx])), lane_xor, lane_flags_mul hk hm hi]
    change _ = lane w i acc ^^^
      (m * (lane w i B >>> k &&& 1) ^^^ rowMul ((lane w i B >>> k) >>> 1) M)
    rw [← Nat.shiftRight_add, Nat.xor_assoc]

/--
Lane `i` of `F2.mul w n B M` is the product of lane `i` of `B` with `M` over `𝔽₂`, for `i < n`,
when `M` has at most `w` rows, each below `2 ^ w`.
-/
theorem lane_mul {w n i B : Nat} {M : List Nat} (hfit : fits w M = true) (hi : i < n) :
    lane w i (mul w n B M) = rowMul (lane w i B) M := by
  obtain ⟨hlen, hM⟩ := (fits_iff w M).1 hfit
  have h := mulLoop_lane (B := B) hi M 0 0 (by omega) hM
  rw [lane_zero_row, Nat.zero_xor, Nat.shiftRight_zero] at h
  exact h

private theorem unitLanes_iff (w R : Nat) : ∀ n : Nat,
    unitLanes w R n = true ↔ ∀ i < n, lane w i R = 2 ^ i
  | 0 => by
    change true = true ↔ _
    simp
  | n + 1 => by
    change Bool.and (Nat.beq (lane w n R) (1 <<< n)) (unitLanes w R n) = true ↔ _
    rw [Bool.and_eq_true, unitLanes_iff w R n, Nat.beq_eq, Nat.shiftLeft_eq, Nat.one_mul]
    constructor
    · rintro ⟨hn, hlow⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact hlow i h
      · exact hn
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

/--
A passing `isInverse w n B M` proves that `B * M` is the identity over `𝔽₂`: for every `i < n`,
row `i` of `B` (lane `i`) times `M` is the unit row `2 ^ i`.
-/
theorem isInverse_sound {w n B : Nat} {M : List Nat} (h : isInverse w n B M = true) :
    ∀ i < n, rowMul (lane w i B) M = 2 ^ i := by
  unfold isInverse at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.ble_eq] at h
  intro i hi
  rw [← lane_mul (fits_of_square h.1 h.2.1) hi]
  exact (unitLanes_iff w _ n).1 h.2.2 i hi

/-- A passing `isInverse w n B M` has lanes wide enough for a row and an `n` by `n` matrix `M`:
exactly `n` rows, each below `2 ^ n`. -/
theorem isInverse_square {w n B : Nat} {M : List Nat} (h : isInverse w n B M = true) :
    n ≤ w ∧ M.length = n ∧ ∀ m ∈ M, m < 2 ^ n := by
  unfold isInverse at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.ble_eq] at h
  exact ⟨h.1, (square_iff n M).1 h.2.1⟩

end FloatLib.Numerics.Packed.F2
