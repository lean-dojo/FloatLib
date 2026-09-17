/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.LimbArray.Arithmetic.Runtime
public import FloatLib.Kernels.LimbArray.Core.Proof
public import FloatLib.Kernels.FixedWord.Core.Proof.Word

/-!
# Limb arrays: value semantics of the arithmetic kernels

Every loop of `Arithmetic.Runtime` is specified by a `segment` invariant: processing the limbs
from `index` onward changes the segment starting at `index` by the intended amount and leaves the
limbs below `index` untouched. The invariants are proved by induction on the loop's remaining
count, and the `toNat` statements follow by splitting `toNat` into the segment below `index`, the
segment the loop wrote, and the untouched segment above it.

* `toNat_addWordAt` and `toNat_addAt`: adding a word at a limb or bit position, provided the
  result still fits the stored limbs;
* `toNat_add`: `add a b carry` denotes `toNat a + toNat b + carry`, with no side condition because
  the result has one limb more than the wider operand;
* `toNat_sub`: `sub a b borrow` denotes `toNat a - toNat b - borrow` whenever that difference is
  nonnegative and the borrow is at most one;
* `toNat_mul`: `mul a b` denotes `toNat a * toNat b`.

`limb_setIfInBounds` describes array updates; `uint64_low_toNat` and `uint64_high_toNat`
split each intermediate into a result limb and a carry.
-/

@[expose] public section

namespace FloatLib.Numerics.LimbArray

open FloatLib.Numerics.FixedWord

/-! ## Array updates and machine-word digits -/

/-- The limb view of an in-bounds array update. -/
theorem limb_setIfInBounds (arr : Array UInt32) (i : Nat) (x : UInt32) (j : Nat) :
    (⟨arr.setIfInBounds i x⟩ : LimbArray).limb j =
      if i = j ∧ i < arr.size then x else (⟨arr⟩ : LimbArray).limb j := by
  unfold limb
  change (arr.setIfInBounds i x).getD j 0 = _
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i < arr.size
    · simp [hi]
    · rw [ite_eq_left rfl, ite_eq_right hi, ite_eq_right (by simp [hi])]
      change (0 : UInt32) = arr.getD i 0
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
      rfl
  · rw [ite_eq_right hij, ite_eq_right (by simp [hij]), ← Array.getD_eq_getD_getElem?]

/-- Writing one limb in bounds keeps the limb count. -/
@[simp] theorem size_setIfInBounds' (arr : Array UInt32) (i : Nat) (x : UInt32) :
    (⟨arr.setIfInBounds i x⟩ : LimbArray).size = (⟨arr⟩ : LimbArray).size := by
  simp [size]

/-- Segments away from an updated limb are unchanged. -/
theorem segment_setIfInBounds_of_le (arr : Array UInt32) (i : Nat) (x : UInt32) (s n : Nat)
    (h : s + n ≤ i ∨ i < s) :
    segment (⟨arr.setIfInBounds i x⟩ : LimbArray) s n = segment (⟨arr⟩ : LimbArray) s n := by
  apply segment_congr
  intro k hk
  rw [limb_setIfInBounds, ite_eq_right (by omega)]

/-- The low word of a `UInt64` is its value modulo the radix. -/
theorem uint64_low_toNat (x : UInt64) : x.toUInt32.toNat = x.toNat % radix := by
  rw [UInt64.toNat_toUInt32, radix_eq]

/-- The high word of a `UInt64` is its value divided by the radix. -/
theorem uint64_high_toNat (x : UInt64) : (x >>> 32).toUInt32.toNat = x.toNat / radix := by
  rw [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, show (32 : UInt64).toNat % 64 = 32 by decide,
    Nat.shiftRight_eq_div_pow, radix_eq]
  apply Nat.mod_eq_of_lt
  have := UInt64.toNat_lt_size x
  change x.toNat < 2 ^ 64 at this
  omega

/-- Every limb value is below the radix `2^32`. -/
theorem uint32_toNat_lt (x : UInt32) : x.toNat < radix :=
  UInt32.toNat_lt_size x

/-- The three-way split of a value around a written segment. -/
theorem toNat_split (v : LimbArray) (i c : Nat) (h : i + c ≤ v.size) :
    toNat v = segment v 0 i + radix ^ i * segment v i c +
      radix ^ (i + c) * segment v (i + c) (v.size - (i + c)) := by
  unfold toNat
  rw [show v.size = i + c + (v.size - (i + c)) by omega, segment_add, segment_add,
    show i + c + (v.size - (i + c)) - (i + c) = v.size - (i + c) by omega]
  rw [Nat.zero_add, Nat.zero_add, pow_add]

/-! ## Carry propagation -/

/-- The carry loop writes into the output array without resizing it. -/
theorem size_carryLoop (count index : Nat) (carry : UInt32) (out : Array UInt32) :
    (carryLoop count index carry out).size = out.size := by
  induction count generalizing index carry out with
  | zero => rfl
  | succ count ih =>
      unfold carryLoop
      split
      · rfl
      · rw [ih, Array.size_setIfInBounds]

/--
The carry loop adds its carry to the segment it processes and leaves the other limbs unchanged,
provided the sum fits the processed limbs.
-/
theorem carryLoop_spec (count index : Nat) (carry : UInt32) (out : Array UInt32)
    (hsize : index + count ≤ out.size)
    (hfit : segment (⟨out⟩ : LimbArray) index count + carry.toNat < radix ^ count) :
    segment (⟨carryLoop count index carry out⟩ : LimbArray) index count =
        segment (⟨out⟩ : LimbArray) index count + carry.toNat ∧
      ∀ i, i < index ∨ index + count ≤ i →
        (⟨carryLoop count index carry out⟩ : LimbArray).limb i = (⟨out⟩ : LimbArray).limb i := by
  induction count generalizing index carry out with
  | zero =>
      simp only [segment_zero, Nat.zero_add, pow_zero] at hfit ⊢
      have hzero : carry.toNat = 0 := by omega
      simp [carryLoop, hzero]
  | succ count ih =>
      unfold carryLoop
      by_cases hcarry : carry == 0
      · rw [ite_eq_left hcarry]
        have : carry.toNat = 0 := by
          rw [beq_iff_eq] at hcarry
          simp [hcarry]
        simp [this]
      · rw [ite_eq_right hcarry]
        set sum : UInt64 := (out.getD index 0).toUInt64 + carry.toUInt64 with hsum
        set out' := out.setIfInBounds index sum.toUInt32 with hout'
        have hlimb := uint32_toNat_lt (out.getD index 0)
        have hcarryLt := uint32_toNat_lt carry
        have hsumNat : sum.toNat = (out.getD index 0).toNat + carry.toNat := by
          rw [hsum, uint64_add_toNat_of_lt, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
          rw [UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
          unfold radix at hlimb hcarryLt
          omega
        have hindex : index < out.size := by omega
        have hlimbEq : (⟨out⟩ : LimbArray).limb index = out.getD index 0 := rfl
        have hseg := segment_succ (⟨out⟩ : LimbArray) index count
        have hsize' : index + 1 + count ≤ out'.size := by
          rw [hout', Array.size_setIfInBounds]
          omega
        have hsegOut' : segment (⟨out'⟩ : LimbArray) (index + 1) count =
            segment (⟨out⟩ : LimbArray) (index + 1) count :=
          segment_setIfInBounds_of_le out index _ (index + 1) count (Or.inr (by omega))
        have hfit' : segment (⟨out'⟩ : LimbArray) (index + 1) count +
            ((sum >>> 32).toUInt32).toNat < radix ^ count := by
          rw [hsegOut', uint64_high_toNat, hsumNat]
          rw [hseg, hlimbEq, pow_succ] at hfit
          have hdiv := Nat.mod_add_div ((out.getD index 0).toNat + carry.toNat) radix
          unfold radix at hfit hdiv ⊢
          omega
        obtain ⟨ihseg, ihlimb⟩ := ih (index + 1) (sum >>> 32).toUInt32 out' hsize' hfit'
        constructor
        · rw [segment_succ, ihseg, hsegOut', ihlimb index (Or.inl (by omega)), hout',
            limb_setIfInBounds, ite_eq_left ⟨rfl, hindex⟩, uint64_low_toNat, uint64_high_toNat,
            hsumNat, hseg, hlimbEq]
          have hdiv := Nat.mod_add_div ((out.getD index 0).toNat + carry.toNat) radix
          unfold radix at hdiv ⊢
          omega
        · intro i hi
          rw [ihlimb i (by omega), hout', limb_setIfInBounds, ite_eq_right (by omega)]

/-- Adding a word at a limb position, when the sum fits the stored limbs. -/
theorem toNat_addWordAt (v : LimbArray) (index : Nat) (w : UInt32)
    (hindex : index ≤ v.size)
    (hfit : toNat v + w.toNat * radix ^ index < radix ^ v.size) :
    toNat (addWordAt v index w) = toNat v + w.toNat * radix ^ index := by
  have hsplit := toNat_split v index (v.size - index) (by omega)
  rw [show index + (v.size - index) = v.size by omega, Nat.sub_self, segment_zero,
    Nat.mul_zero, Nat.add_zero] at hsplit
  have hsegFit : segment v index (v.size - index) + w.toNat < radix ^ (v.size - index) := by
    have hpow : radix ^ v.size = radix ^ index * radix ^ (v.size - index) := by
      rw [← pow_add, show index + (v.size - index) = v.size by omega]
    rw [hpow] at hfit
    have hpos : 0 < radix ^ index := Nat.pow_pos (by decide)
    have : radix ^ index * (segment v index (v.size - index) + w.toNat) <
        radix ^ index * radix ^ (v.size - index) := by
      rw [Nat.mul_add, Nat.mul_comm (radix ^ index) w.toNat]
      omega
    exact Nat.lt_of_mul_lt_mul_left this
  obtain ⟨hseg, hlimb⟩ :=
    carryLoop_spec (v.size - index) index w v.limbs (by change index + _ ≤ v.size; omega) hsegFit
  have hsizeRes : (addWordAt v index w).size = v.size := by
    change (carryLoop _ _ _ _).size = _
    rw [size_carryLoop]
    rfl
  have hsplitRes := toNat_split (addWordAt v index w) index (v.size - index) (by omega)
  rw [hsizeRes, show index + (v.size - index) = v.size by omega, Nat.sub_self, segment_zero,
    Nat.mul_zero, Nat.add_zero] at hsplitRes
  rw [hsplitRes, hsplit]
  change segment (⟨carryLoop (v.size - index) index w v.limbs⟩ : LimbArray) 0 index +
      radix ^ index * segment (⟨carryLoop (v.size - index) index w v.limbs⟩ : LimbArray) index
        (v.size - index) = _
  rw [hseg]
  have hlow : segment (⟨carryLoop (v.size - index) index w v.limbs⟩ : LimbArray) 0 index =
      segment v 0 index := by
    apply segment_congr
    intro i hi
    rw [Nat.zero_add]
    exact hlimb i (Or.inl hi)
  rw [hlow]
  ring

/-- Adding a word at an index keeps the limb count. -/
theorem size_addWordAt (v : LimbArray) (index : Nat) (w : UInt32) :
    (addWordAt v index w).size = v.size := by
  change (carryLoop _ _ _ _).size = _
  rw [size_carryLoop]
  rfl

/-- The 64-bit shifted word splits into a low and a high limb. -/
theorem shifted_word_toNat (w : UInt32) (r : Nat) (hr : r < 32) :
    (w.toUInt64 <<< UInt64.ofNat r).toNat = w.toNat * 2 ^ r := by
  rw [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat', UInt32.toNat_toUInt64,
    Nat.mod_eq_of_lt (a := r) (by omega : r < 2 ^ 64), Nat.mod_eq_of_lt (by omega : r < 64),
    Nat.shiftLeft_eq]
  apply Nat.mod_eq_of_lt
  have hw := uint32_toNat_lt w
  have hpow : 2 ^ r ≤ 2 ^ 31 := Nat.pow_le_pow_right (by decide) (by omega)
  calc
    w.toNat * 2 ^ r ≤ w.toNat * 2 ^ 31 := Nat.mul_le_mul_left _ hpow
    _ < radix * 2 ^ 31 := Nat.mul_lt_mul_of_pos_right hw (by decide)
    _ = 2 ^ 63 := by decide
    _ < 2 ^ 64 := by decide

/-- Adding `w * 2^k`, when the sum fits the stored limbs and bit `k` lies within the array. -/
theorem toNat_addAt (v : LimbArray) (k : Nat) (w : UInt32)
    (hk : k / 32 + 1 ≤ v.size)
    (hfit : toNat v + w.toNat * 2 ^ k < radix ^ v.size) :
    toNat (addAt v k w) = toNat v + w.toNat * 2 ^ k := by
  unfold addAt
  set shifted : UInt64 := w.toUInt64 <<< UInt64.ofNat (k % 32) with hshifted
  have hshiftedNat : shifted.toNat = w.toNat * 2 ^ (k % 32) :=
    shifted_word_toNat w (k % 32) (Nat.mod_lt _ (by decide))
  have hlow := uint64_low_toNat shifted
  have hhigh := uint64_high_toNat shifted
  have hdecomp : w.toNat * 2 ^ k =
      shifted.toUInt32.toNat * radix ^ (k / 32) +
        (shifted >>> 32).toUInt32.toNat * radix ^ (k / 32 + 1) := by
    rw [hlow, hhigh]
    have h1 : shifted.toNat % radix * radix ^ (k / 32) +
        shifted.toNat / radix * radix ^ (k / 32 + 1) =
          (shifted.toNat % radix + radix * (shifted.toNat / radix)) * radix ^ (k / 32) := by
      ring
    rw [h1, Nat.mod_add_div, hshiftedNat, radix_pow, Nat.mul_assoc, ← pow_add]
    congr 2
    omega
  have hfit1 : toNat v + shifted.toUInt32.toNat * radix ^ (k / 32) < radix ^ v.size := by
    rw [hdecomp] at hfit
    omega
  rw [toNat_addWordAt _ _ _ (by rw [size_addWordAt]; omega)]
  · rw [toNat_addWordAt _ _ _ (by omega) hfit1, hdecomp]
    ring
  · rw [size_addWordAt, toNat_addWordAt _ _ _ (by omega) hfit1, Nat.add_assoc, ← hdecomp]
    exact hfit

/-- Adding a word at a bit offset keeps the limb count. -/
theorem size_addAt (v : LimbArray) (k : Nat) (w : UInt32) : (addAt v k w).size = v.size := by
  unfold addAt
  rw [size_addWordAt, size_addWordAt]

/-! ## Addition -/

/-- The addition loop keeps the size of its accumulator. -/
theorem size_addLoop (a b : LimbArray) (count index : Nat) (carry : UInt32)
    (out : Array UInt32) :
    (addLoop a b count index carry out).size = out.size := by
  induction count generalizing index carry out with
  | zero => simp [addLoop]
  | succ count ih =>
      unfold addLoop
      rw [ih, Array.size_setIfInBounds]

/-- The addition loop writes the sum of the processed segments and the carry. -/
theorem addLoop_spec (a b : LimbArray) (count index : Nat) (carry : UInt32)
    (out : Array UInt32) (hsize : index + count < out.size) :
    segment (⟨addLoop a b count index carry out⟩ : LimbArray) index (count + 1) =
        segment a index count + segment b index count + carry.toNat ∧
      ∀ i, i < index →
        (⟨addLoop a b count index carry out⟩ : LimbArray).limb i = (⟨out⟩ : LimbArray).limb i := by
  induction count generalizing index carry out with
  | zero =>
      simp only [addLoop, segment_zero, Nat.zero_add]
      constructor
      · rw [segment_succ, segment_zero, Nat.mul_zero, Nat.add_zero, limb_setIfInBounds,
          ite_eq_left ⟨rfl, by omega⟩]
      · intro i hi
        rw [limb_setIfInBounds, ite_eq_right (by omega)]
  | succ count ih =>
      unfold addLoop
      set sum : UInt64 := (a.limb index).toUInt64 + (b.limb index).toUInt64 + carry.toUInt64
        with hsum
      set out' := out.setIfInBounds index sum.toUInt32 with hout'
      have ha := uint32_toNat_lt (a.limb index)
      have hb := uint32_toNat_lt (b.limb index)
      have hc := uint32_toNat_lt carry
      have hpair : ((a.limb index).toUInt64 + (b.limb index).toUInt64).toNat =
          (a.limb index).toNat + (b.limb index).toNat := by
        rw [uint64_add_toNat_of_lt, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
        rw [UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
        unfold radix at ha hb
        omega
      have hsumNat : sum.toNat = (a.limb index).toNat + (b.limb index).toNat + carry.toNat := by
        rw [hsum, uint64_add_toNat_of_lt, hpair, UInt32.toNat_toUInt64]
        rw [hpair, UInt32.toNat_toUInt64]
        unfold radix at ha hb hc
        omega
      have hsize' : index + 1 + count < out'.size := by
        rw [hout', Array.size_setIfInBounds]
        omega
      obtain ⟨ihseg, ihlimb⟩ := ih (index + 1) (sum >>> 32).toUInt32 out' hsize'
      constructor
      · rw [segment_succ, ihseg, ihlimb index (by omega), hout', limb_setIfInBounds,
          ite_eq_left ⟨rfl, by omega⟩, uint64_low_toNat, uint64_high_toNat, hsumNat,
          segment_succ a, segment_succ b]
        have hdiv := Nat.mod_add_div
          ((a.limb index).toNat + (b.limb index).toNat + carry.toNat) radix
        unfold radix at hdiv ⊢
        omega
      · intro i hi
        rw [ihlimb i (by omega), hout', limb_setIfInBounds, ite_eq_right (by omega)]

/-- A sum has one limb more than the wider operand, room for the final carry. -/
@[simp] theorem size_add (a b : LimbArray) (carry : UInt32) :
    (add a b carry).size = max a.size b.size + 1 := by
  unfold add size
  rw [size_addLoop, Array.size_replicate]

/-- `add` denotes the sum of its operands and the incoming carry. -/
@[simp, grind =] theorem toNat_add (a b : LimbArray) (carry : UInt32) :
    toNat (add a b carry) = toNat a + toNat b + carry.toNat := by
  unfold toNat
  rw [size_add]
  have hcount : 0 + max a.size b.size <
      (Array.replicate (max a.size b.size + 1) (0 : UInt32)).size := by
    simp
  obtain ⟨hseg, _⟩ := addLoop_spec a b (max a.size b.size) 0 carry _ hcount
  unfold add
  rw [hseg, ← toNat_eq_segment_of_size_le (Nat.le_max_left _ _),
    ← toNat_eq_segment_of_size_le (Nat.le_max_right _ _)]
  rfl

/-! ## Subtraction -/

/-- The subtraction loop keeps the size of its accumulator. -/
theorem size_subLoop (a b : LimbArray) (count index : Nat) (borrow : UInt32)
    (out : Array UInt32) :
    (subLoop a b count index borrow out).size = out.size := by
  induction count generalizing index borrow out with
  | zero => rfl
  | succ count ih =>
      unfold subLoop
      rw [ih, Array.size_setIfInBounds]

/-- The subtraction loop writes the difference of the processed segments when it is nonnegative. -/
theorem subLoop_spec (a b : LimbArray) (count index : Nat) (borrow : UInt32)
    (out : Array UInt32) (hsize : index + count ≤ out.size) (hborrow : borrow.toNat ≤ 1)
    (hle : segment b index count + borrow.toNat ≤ segment a index count) :
    segment (⟨subLoop a b count index borrow out⟩ : LimbArray) index count +
        segment b index count + borrow.toNat = segment a index count ∧
      ∀ i, i < index →
        (⟨subLoop a b count index borrow out⟩ : LimbArray).limb i = (⟨out⟩ : LimbArray).limb i := by
  induction count generalizing index borrow out with
  | zero =>
      simp only [segment_zero, Nat.zero_add] at hle ⊢
      constructor
      · omega
      · intro i _
        rfl
  | succ count ih =>
      unfold subLoop
      dsimp only
      set difference : UInt64 :=
        (a.limb index).toUInt64 + 4294967296 - (b.limb index).toUInt64 - borrow.toUInt64
        with hdifference
      set borrow' : UInt32 := if difference < 4294967296 then 1 else 0 with hborrow'
      set out' := out.setIfInBounds index difference.toUInt32 with hout'
      have ha := uint32_toNat_lt (a.limb index)
      have hb := uint32_toNat_lt (b.limb index)
      have h4 : (4294967296 : UInt64).toNat = radix := by decide
      have hsumNat : ((a.limb index).toUInt64 + 4294967296).toNat =
          (a.limb index).toNat + radix := by
        rw [uint64_add_toNat_of_lt, UInt32.toNat_toUInt64, h4]
        rw [UInt32.toNat_toUInt64, h4]
        unfold radix at ha ⊢
        omega
      have hsub1 : ((a.limb index).toUInt64 + 4294967296 - (b.limb index).toUInt64).toNat =
          (a.limb index).toNat + radix - (b.limb index).toNat := by
        rw [UInt64.toNat_sub_of_le, hsumNat, UInt32.toNat_toUInt64]
        rw [UInt64.le_iff_toNat_le, hsumNat, UInt32.toNat_toUInt64]
        omega
      have hdiffNat : difference.toNat =
          (a.limb index).toNat + radix - (b.limb index).toNat - borrow.toNat := by
        rw [hdifference, UInt64.toNat_sub_of_le, hsub1, UInt32.toNat_toUInt64]
        rw [UInt64.le_iff_toNat_le, hsub1, UInt32.toNat_toUInt64]
        omega
      have hborrow'Nat : borrow'.toNat = if difference.toNat < radix then 1 else 0 := by
        rw [hborrow']
        by_cases h : difference < 4294967296
        · have h' : difference.toNat < radix := by
            rw [UInt64.lt_iff_toNat_lt, h4] at h
            exact h
          rw [ite_eq_left h, ite_eq_left h']
          rfl
        · have h' : ¬ difference.toNat < radix := by
            rw [UInt64.lt_iff_toNat_lt, h4] at h
            exact h
          rw [ite_eq_right h, ite_eq_right h']
          rfl
      have hstep : (a.limb index).toNat + radix * borrow'.toNat =
          difference.toUInt32.toNat + (b.limb index).toNat + borrow.toNat := by
        rw [uint64_low_toNat, hborrow'Nat, hdiffNat]
        unfold radix at ha hb ⊢
        split <;> omega
      have hle' : segment b (index + 1) count + borrow'.toNat ≤ segment a (index + 1) count := by
        rw [segment_succ, segment_succ] at hle
        have hdigit := uint32_toNat_lt difference.toUInt32
        unfold radix at hstep hle hdigit
        omega
      have hsize' : index + 1 + count ≤ out'.size := by
        rw [hout', Array.size_setIfInBounds]
        omega
      have hborrow'Le : borrow'.toNat ≤ 1 := by
        rw [hborrow'Nat]
        split <;> decide
      obtain ⟨ihseg, ihlimb⟩ := ih (index + 1) borrow' out' hsize' hborrow'Le hle'
      constructor
      · have hlimbIndex : (⟨out'⟩ : LimbArray).limb index = difference.toUInt32 := by
          rw [hout', limb_setIfInBounds, ite_eq_left ⟨rfl, by omega⟩]
        rw [segment_succ, ihlimb index (by omega), hlimbIndex, segment_succ b, segment_succ a]
        unfold radix at hstep ⊢
        omega
      · intro i hi
        rw [ihlimb i (by omega), hout', limb_setIfInBounds, ite_eq_right (by omega)]

/-- A difference has as many limbs as the wider operand. -/
@[simp] theorem size_sub (a b : LimbArray) (borrow : UInt32) :
    (sub a b borrow).size = max a.size b.size := by
  unfold sub size
  rw [size_subLoop, Array.size_replicate]

/-- `sub` denotes the difference when it is nonnegative and the borrow is at most one. -/
theorem toNat_sub (a b : LimbArray) (borrow : UInt32) (hborrow : borrow.toNat ≤ 1)
    (hle : toNat b + borrow.toNat ≤ toNat a) :
    toNat (sub a b borrow) = toNat a - toNat b - borrow.toNat := by
  have hcount : 0 + max a.size b.size ≤
      (Array.replicate (max a.size b.size) (0 : UInt32)).size := by
    simp
  have hle' : segment b 0 (max a.size b.size) + borrow.toNat ≤
      segment a 0 (max a.size b.size) := by
    rw [← toNat_eq_segment_of_size_le (Nat.le_max_left _ _),
      ← toNat_eq_segment_of_size_le (Nat.le_max_right _ _)]
    exact hle
  obtain ⟨hseg, _⟩ := subLoop_spec a b (max a.size b.size) 0 borrow _ hcount hborrow hle'
  rw [← toNat_eq_segment_of_size_le (Nat.le_max_left _ _),
    ← toNat_eq_segment_of_size_le (Nat.le_max_right _ _)] at hseg
  have hsize : (sub a b borrow).size = max a.size b.size := size_sub a b borrow
  have hres : toNat (sub a b borrow) =
      segment (⟨subLoop a b (max a.size b.size) 0 borrow
        (Array.replicate (max a.size b.size) 0)⟩ : LimbArray) 0 (max a.size b.size) := by
    unfold toNat
    rw [hsize]
    rfl
  rw [hres]
  omega

/-! ## Multiplication -/

/-- One schoolbook row keeps the size of its accumulator. -/
theorem size_mulRow (b : LimbArray) (m : UInt32) (offset count j : Nat) (carry : UInt32)
    (out : Array UInt32) :
    (mulRow b m offset count j carry out).size = out.size := by
  induction count generalizing j carry out with
  | zero => simp [mulRow]
  | succ count ih =>
      unfold mulRow
      rw [ih, Array.size_setIfInBounds]

/-- A row of the schoolbook product adds `m` times a segment of `b` at its offset. -/
theorem mulRow_spec (b : LimbArray) (m : UInt32) (offset count j : Nat) (carry : UInt32)
    (out : Array UInt32) (hsize : offset + j + count < out.size)
    (hslot : (⟨out⟩ : LimbArray).limb (offset + j + count) = 0) :
    segment (⟨mulRow b m offset count j carry out⟩ : LimbArray) (offset + j) (count + 1) =
        segment (⟨out⟩ : LimbArray) (offset + j) count + m.toNat * segment b j count +
          carry.toNat ∧
      ∀ i, i < offset + j ∨ offset + j + count < i →
        (⟨mulRow b m offset count j carry out⟩ : LimbArray).limb i =
          (⟨out⟩ : LimbArray).limb i := by
  induction count generalizing j carry out with
  | zero =>
      simp only [mulRow, segment_zero, Nat.mul_zero, Nat.zero_add, Nat.add_zero]
      constructor
      · rw [segment_succ, segment_zero, Nat.mul_zero, Nat.add_zero, limb_setIfInBounds,
          ite_eq_left ⟨rfl, by omega⟩]
      · intro i hi
        rw [limb_setIfInBounds, ite_eq_right (by omega)]
  | succ count ih =>
      unfold mulRow
      set term : UInt64 :=
        m.toUInt64 * (b.limb j).toUInt64 + (out.getD (offset + j) 0).toUInt64 + carry.toUInt64
        with hterm
      set out' := out.setIfInBounds (offset + j) term.toUInt32 with hout'
      have hm := uint32_toNat_lt m
      have hb := uint32_toNat_lt (b.limb j)
      have ho := uint32_toNat_lt (out.getD (offset + j) 0)
      have hc := uint32_toNat_lt carry
      have hprod : m.toNat * (b.limb j).toNat ≤ (radix - 1) * (radix - 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      have hmul : (m.toUInt64 * (b.limb j).toUInt64).toNat = m.toNat * (b.limb j).toNat := by
        rw [uint64_mul_toNat_of_lt, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
        rw [UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
        unfold radix at hprod
        omega
      have hadd1 : (m.toUInt64 * (b.limb j).toUInt64 + (out.getD (offset + j) 0).toUInt64).toNat =
          m.toNat * (b.limb j).toNat + (out.getD (offset + j) 0).toNat := by
        rw [uint64_add_toNat_of_lt, hmul, UInt32.toNat_toUInt64]
        rw [hmul, UInt32.toNat_toUInt64]
        unfold radix at hprod ho
        omega
      have htermNat : term.toNat =
          m.toNat * (b.limb j).toNat + (out.getD (offset + j) 0).toNat + carry.toNat := by
        rw [hterm, uint64_add_toNat_of_lt, hadd1, UInt32.toNat_toUInt64]
        rw [hadd1, UInt32.toNat_toUInt64]
        unfold radix at hprod ho hc
        omega
      have hlimbEq : (⟨out⟩ : LimbArray).limb (offset + j) = out.getD (offset + j) 0 := rfl
      have hsize' : offset + (j + 1) + count < out'.size := by
        rw [hout', Array.size_setIfInBounds]
        omega
      have hslot' : (⟨out'⟩ : LimbArray).limb (offset + (j + 1) + count) = 0 := by
        rw [hout', limb_setIfInBounds, ite_eq_right (by omega)]
        rw [show offset + (j + 1) + count = offset + j + (count + 1) by omega]
        exact hslot
      obtain ⟨ihseg, ihlimb⟩ := ih (j + 1) (term >>> 32).toUInt32 out' hsize' hslot'
      have hsegOut' : segment (⟨out'⟩ : LimbArray) (offset + (j + 1)) count =
          segment (⟨out⟩ : LimbArray) (offset + j + 1) count := by
        rw [show offset + (j + 1) = offset + j + 1 by omega]
        exact segment_setIfInBounds_of_le out (offset + j) _ (offset + j + 1) count
          (Or.inr (by omega))
      constructor
      · rw [segment_succ, show offset + j + 1 = offset + (j + 1) by omega, ihseg, hsegOut',
          ihlimb (offset + j) (Or.inl (by omega)), hout', limb_setIfInBounds,
          ite_eq_left ⟨rfl, by omega⟩, uint64_low_toNat, uint64_high_toNat, htermNat,
          segment_succ (⟨out⟩ : LimbArray) (offset + j), segment_succ b j, hlimbEq]
        have hdiv := Nat.mod_add_div
          (m.toNat * (b.limb j).toNat + (out.getD (offset + j) 0).toNat + carry.toNat) radix
        have hdistrib : m.toNat * ((b.limb j).toNat + radix * segment b (j + 1) count) =
            m.toNat * (b.limb j).toNat + radix * (m.toNat * segment b (j + 1) count) := by
          ring
        rw [hdistrib]
        unfold radix at hdiv ⊢
        omega
      · intro i hi
        rw [ihlimb i (by omega), hout', limb_setIfInBounds, ite_eq_right (by omega)]

/-- The schoolbook row loop writes into the output array without resizing it. -/
theorem size_mulRows (a b : LimbArray) (count i : Nat) (out : Array UInt32) :
    (mulRows a b count i out).size = out.size := by
  induction count generalizing i out with
  | zero => rfl
  | succ count ih =>
      unfold mulRows
      rw [ih, size_mulRow]

/-- The row loop maintains the partial product and the zero limbs above it. -/
theorem mulRows_spec (a b : LimbArray) (count i : Nat) (out : Array UInt32)
    (hsize : out.size = a.size + b.size) (hrows : i + count = a.size)
    (hvalue : toNat (⟨out⟩ : LimbArray) = segment a 0 i * toNat b)
    (hzero : ∀ k, i + b.size ≤ k → (⟨out⟩ : LimbArray).limb k = 0) :
    toNat (⟨mulRows a b count i out⟩ : LimbArray) = segment a 0 (i + count) * toNat b := by
  induction count generalizing i out with
  | zero =>
      simpa [mulRows] using hvalue
  | succ count ih =>
      unfold mulRows
      set out' := mulRow b (a.limb i) i b.size 0 0 out with hout'
      have hi : i < a.size := by omega
      have hrowSize : i + 0 + b.size < out.size := by omega
      have hslot : (⟨out⟩ : LimbArray).limb (i + 0 + b.size) = 0 := hzero _ (by omega)
      obtain ⟨hseg, hlimb⟩ := mulRow_spec b (a.limb i) i b.size 0 0 out hrowSize hslot
      simp only [Nat.add_zero, UInt32.toNat_zero] at hseg hlimb
      have hsize' : out'.size = a.size + b.size := by
        rw [hout', size_mulRow, hsize]
      have hzero' : ∀ k, i + 1 + b.size ≤ k → (⟨out'⟩ : LimbArray).limb k = 0 := by
        intro k hk
        rw [hout', hlimb k (Or.inr (by omega))]
        exact hzero k (by omega)
      have hvalue' : toNat (⟨out'⟩ : LimbArray) = segment a 0 (i + 1) * toNat b := by
        have hsplit := toNat_split (⟨out'⟩ : LimbArray) i (b.size + 1) (by
          change i + (b.size + 1) ≤ out'.size
          omega)
        have hsplitOut := toNat_split (⟨out⟩ : LimbArray) i b.size (by
          change i + b.size ≤ out.size
          omega)
        have htop : segment (⟨out'⟩ : LimbArray) (i + (b.size + 1))
            ((⟨out'⟩ : LimbArray).size - (i + (b.size + 1))) = 0 := by
          apply segment_eq_zero_of_limb_eq_zero
          intro k _
          exact hzero' _ (by omega)
        have htopOut : segment (⟨out⟩ : LimbArray) (i + b.size)
            ((⟨out⟩ : LimbArray).size - (i + b.size)) = 0 := by
          apply segment_eq_zero_of_limb_eq_zero
          intro k _
          exact hzero _ (by omega)
        have hlow : segment (⟨out'⟩ : LimbArray) 0 i = segment (⟨out⟩ : LimbArray) 0 i := by
          apply segment_congr
          intro k hk
          rw [Nat.zero_add, hout']
          exact hlimb k (Or.inl hk)
        rw [hsplit, htop, hlow, hout', hseg, Nat.mul_zero, Nat.add_zero]
        rw [hsplitOut, htopOut, Nat.mul_zero, Nat.add_zero] at hvalue
        rw [segment_succ_back, Nat.zero_add, Nat.add_mul, ← hvalue,
          ← toNat_eq_segment_of_size_le (Nat.le_refl _)]
        ring
      exact (show i + 1 + count = i + (count + 1) by omega) ▸
        ih (i + 1) out' hsize' (by omega) hvalue' hzero'

/-- A product has as many limbs as the two operands together. -/
@[simp] theorem size_mul (a b : LimbArray) : (mul a b).size = a.size + b.size := by
  unfold mul size
  rw [size_mulRows, Array.size_replicate]

/-- `mul` denotes the product of its operands. -/
@[simp, grind =] theorem toNat_mul (a b : LimbArray) : toNat (mul a b) = toNat a * toNat b := by
  unfold mul
  rw [mulRows_spec a b a.size 0 _ (by simp) (by simp)]
  · rw [Nat.zero_add]
    rfl
  · change toNat (zero (a.size + b.size)) = _
    simp
  · intro k _
    exact limb_zero _ _

end FloatLib.Numerics.LimbArray
