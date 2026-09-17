/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.LimbArray.Core.Runtime
public import Mathlib.Data.Nat.Digits.Defs
import all Init.Data.Fin.Log2
import all Init.Data.UInt.Log2

/-!
# Limb arrays: value semantics of the accessors

The accessors of `Core.Runtime` have value-level contracts in terms of the natural number `toNat`
of a limb array. The contracts use three groups of lemmas.

* `segment` lemmas: `segment_eq_ofDigits` and `toNat_eq_ofDigits` identify the denotation with
  Mathlib's little-endian base-`2^32` evaluation. Its append, bound, prefix, and injectivity
  theorems apply to limb segments, including zero padding beyond the stored size.
* Digit and bit extraction: `limb_toNat_eq` reads limb `i` as a base-`2^32` digit of `toNat`, and
  `limb_testBit` reads a bit of a limb as a bit of `toNat`. Together with `Nat.eq_of_testBit_eq`
  these turn every bitwise accessor into a statement about `Nat` bits.
* The accessor theorems: `toNat_ofNat`, `ofNat_toNat`, `testBit_eq`, `bitsAt32_toNat`,
  `toNat_lowBits`, `toNat_resize`, `anyBelow_eq_true_iff`, `toNat_orLowBit`, `compare_eq`,
  `isZero_eq_true_iff`, and `log2_eq`.

The compiler certificate `toNat_eq_toNatImpl` replaces the proof-facing `toNat` by its Horner
loop. `limb_toNat_eq` and `limb_testBit` connect limb access to value-level proofs.
-/

@[expose] public section

namespace FloatLib.Numerics.LimbArray

/-! ## Limbs and segments -/

/-- Limbs beyond the stored size read as zero. -/
theorem limb_eq_zero_of_size_le (v : LimbArray) {i : Nat} (h : v.size ≤ i) :
    v.limb i = 0 := by
  unfold limb
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]
  rfl

/-- A stored limb is the corresponding array element. -/
theorem limb_eq_getElem (v : LimbArray) {i : Nat} (h : i < v.limbs.size) :
    v.limb i = v.limbs[i] := by
  unfold limb
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]
  rfl

/-- Every limb is below the radix. -/
theorem limb_toNat_lt (v : LimbArray) (i : Nat) : (v.limb i).toNat < radix :=
  UInt32.toNat_lt_size _

/-- The radix is `2^32`. -/
theorem radix_eq : radix = 2 ^ 32 := by decide

/-- A power of the radix is a power of two. -/
theorem radix_pow (n : Nat) : radix ^ n = 2 ^ (32 * n) := by
  rw [radix_eq, pow_mul]

/-- An empty segment denotes zero. -/
@[simp] theorem segment_zero (v : LimbArray) (s : Nat) : segment v s 0 = 0 := rfl

/-- A segment is its first limb plus the radix times the rest, Horner's rule read from the low
end. -/
theorem segment_succ (v : LimbArray) (s n : Nat) :
    segment v s (n + 1) = (v.limb s).toNat + radix * segment v (s + 1) n := rfl

/-- A segment evaluates its zero-padded limb digits in Mathlib's little-endian convention. -/
theorem segment_eq_ofDigits (v : LimbArray) (s n : Nat) :
    segment v s n = Nat.ofDigits radix ((List.range' s n).map fun i ↦ (v.limb i).toNat) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [segment_succ, List.range'_succ, List.map_cons, Nat.ofDigits_cons, ih]

/-- Splitting a segment. -/
theorem segment_add (v : LimbArray) (s m n : Nat) :
    segment v s (m + n) = segment v s m + radix ^ m * segment v (s + m) n := by
  simp only [segment_eq_ofDigits, ← List.range'_append_1, List.map_append,
    Nat.ofDigits_append, List.length_map, List.length_range']

/-- Adding a limb at the top of a segment. -/
theorem segment_succ_back (v : LimbArray) (s n : Nat) :
    segment v s (n + 1) = segment v s n + (v.limb (s + n)).toNat * radix ^ n := by
  rw [segment_add]
  simp [segment_succ, Nat.mul_comm]

/-- A segment of `n` limbs is below `radix ^ n`. -/
theorem segment_lt (v : LimbArray) (s n : Nat) : segment v s n < radix ^ n := by
  rw [segment_eq_ofDigits]
  have h := Nat.ofDigits_lt_base_pow_length (by decide : 1 < radix)
    (l := (List.range' s n).map fun i ↦ (v.limb i).toNat) (by
      intro d hd
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hd
      exact limb_toNat_lt v i)
  simpa using h

/-- Segments depend only on the limbs they cover. -/
theorem segment_congr {a b : LimbArray} {s n : Nat}
    (h : ∀ i, i < n → a.limb (s + i) = b.limb (s + i)) :
    segment a s n = segment b s n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      have h0 := h 0 (by omega)
      rw [Nat.add_zero] at h0
      rw [segment_succ, segment_succ, h0]
      congr 2
      apply ih
      intro i hi
      have := h (i + 1) (by omega)
      rwa [show s + 1 + i = s + (i + 1) by omega]

/-- A segment of zero limbs is zero. -/
theorem segment_eq_zero_of_limb_eq_zero {v : LimbArray} {s n : Nat}
    (h : ∀ i, i < n → v.limb (s + i) = 0) :
    segment v s n = 0 := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      have h0 := h 0 (by omega)
      rw [Nat.add_zero] at h0
      rw [segment_succ, h0]
      simp only [UInt32.toNat_zero, Nat.zero_add]
      rw [ih]
      · simp
      · intro i hi
        have := h (i + 1) (by omega)
        rwa [show s + 1 + i = s + (i + 1) by omega]

/-- Trailing zero limbs do not change a segment. -/
theorem segment_eq_of_limb_eq_zero {v : LimbArray} {s m n : Nat} (hmn : m ≤ n)
    (h : ∀ i, m ≤ i → i < n → v.limb (s + i) = 0) :
    segment v s n = segment v s m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hk : segment v (s + m) k = 0 := by
    apply segment_eq_zero_of_limb_eq_zero
    intro i hi
    rw [Nat.add_assoc]
    exact h (m + i) (by omega) (by omega)
  rw [segment_add, hk, Nat.mul_zero, Nat.add_zero]

/-- A segment is zero exactly when every covered limb is zero. -/
theorem segment_eq_zero_iff {v : LimbArray} {s n : Nat} :
    segment v s n = 0 ↔ ∀ i, i < n → v.limb (s + i) = 0 := by
  constructor
  · intro h
    induction n generalizing s with
    | zero => intro i hi; omega
    | succ n ih =>
        rw [segment_succ] at h
        have hlimb : (v.limb s).toNat = 0 := by omega
        have hrest : segment v (s + 1) n = 0 := by
          unfold radix at h
          omega
        intro i hi
        cases i with
        | zero => exact UInt32.toNat_inj.mp (by simpa using hlimb)
        | succ i =>
            have := ih hrest i (by omega)
            rwa [show s + (i + 1) = s + 1 + i by omega]
  · exact segment_eq_zero_of_limb_eq_zero

/-! ## The value -/

/-- A limb array's value is the base-`2^32` evaluation of its stored digits. -/
theorem toNat_eq_ofDigits (v : LimbArray) :
    toNat v = Nat.ofDigits radix (v.limbs.toList.map UInt32.toNat) := by
  rw [toNat, segment_eq_ofDigits]
  congr 1
  apply List.ext_getElem
  · simp [size]
  · intro i hi hi'
    simp only [List.length_map, List.length_range'] at hi
    simp only [List.getElem_map, List.getElem_range', Nat.one_mul, Nat.zero_add]
    rw [limb_eq_getElem v hi]
    rfl

/-- `toNat` may be read from any limb count at or above the stored size. -/
theorem toNat_eq_segment_of_size_le {v : LimbArray} {n : Nat} (h : v.size ≤ n) :
    toNat v = segment v 0 n := by
  unfold toNat
  symm
  apply segment_eq_of_limb_eq_zero h
  intro i hi _
  exact limb_eq_zero_of_size_le v (by omega)

/-- The value is below `radix ^ size`. -/
theorem toNat_lt (v : LimbArray) : toNat v < radix ^ v.size :=
  segment_lt v 0 v.size

/-- The value is below `radix ^ n` for every `n` at or above the stored size. -/
theorem toNat_lt_of_size_le {v : LimbArray} {n : Nat} (h : v.size ≤ n) :
    toNat v < radix ^ n := by
  rw [toNat_eq_segment_of_size_le h]
  exact segment_lt v 0 n

/-- The value is below `2^(32 n)` for every `n` at or above the stored size. -/
theorem toNat_lt_two_pow_of_size_le {v : LimbArray} {n : Nat} (h : v.size ≤ n) :
    toNat v < 2 ^ (32 * n) := by
  rw [← radix_pow]
  exact toNat_lt_of_size_le h

/-- A segment starting at limb zero is a prefix of the value. -/
theorem segment_zero_eq_mod (v : LimbArray) (n : Nat) :
    segment v 0 n = toNat v % radix ^ n := by
  rw [toNat_eq_segment_of_size_le (n := max v.size n) (Nat.le_max_left _ _)]
  rw [segment_eq_ofDigits, segment_eq_ofDigits,
    Nat.ofDigits_mod_pow_eq_ofDigits_take n (by decide)]
  · simp only [← List.map_take, ← List.range_eq_range', List.take_range,
      Nat.min_eq_left (Nat.le_max_right v.size n)]
  · intro d hd
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hd
    exact limb_toNat_lt v i

/-- Limb `i` is the base-`2^32` digit `i` of the value. -/
theorem limb_toNat_eq (v : LimbArray) (i : Nat) :
    (v.limb i).toNat = toNat v / radix ^ i % radix := by
  have hle : v.size ≤ max v.size (i + 1) := Nat.le_max_left _ _
  rw [toNat_eq_segment_of_size_le hle]
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.le_max_right v.size (i + 1))
  rw [hk, show i + 1 + k = i + (k + 1) by omega, segment_add, Nat.zero_add, segment_succ]
  have hlow := segment_lt v 0 i
  have hpos : 0 < radix ^ i := Nat.pow_pos (by decide)
  rw [Nat.add_comm, Nat.mul_add_div hpos, Nat.div_eq_of_lt hlow, Nat.add_zero,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (limb_toNat_lt v i)]

/-- Bit `j` of limb `i` is bit `32 i + j` of the value, for `j < 32`. -/
theorem limb_testBit (v : LimbArray) (i j : Nat) (hj : j < 32) :
    (v.limb i).toNat.testBit j = (toNat v).testBit (32 * i + j) := by
  rw [limb_toNat_eq, radix_eq, ← pow_mul, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    Nat.add_comm]
  simp [hj]

/-- A limb has no bits at or above position 32. -/
theorem limb_testBit_eq_false (v : LimbArray) (i j : Nat) (hj : 32 ≤ j) :
    (v.limb i).toNat.testBit j = false := by
  apply Nat.testBit_lt_two_pow
  calc
    (v.limb i).toNat < radix := limb_toNat_lt v i
    _ = 2 ^ 32 := radix_eq
    _ ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) hj

/-- Limb arrays with equal size and value are equal. -/
theorem ext_of_toNat {a b : LimbArray} (hsize : a.size = b.size) (h : toNat a = toNat b) :
    a = b := by
  have hbound (v : LimbArray) : ∀ d ∈ v.limbs.toList.map UInt32.toNat, d < radix := by
    intro d hd
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hd
    exact UInt32.toNat_lt_size w
  rw [toNat_eq_ofDigits, toNat_eq_ofDigits] at h
  have hdigits := Nat.ofDigits_inj_of_len_eq (by decide : 1 < radix)
    (by simpa [size] using hsize) (hbound a) (hbound b) h
  have hlimbs : a.limbs.toList = b.limbs.toList :=
    (List.map_inj_right (fun _ _ h ↦ UInt32.toNat_inj.mp h)).mp hdigits
  cases a
  cases b
  simpa only [LimbArray.mk.injEq, ← Array.toList_inj] using hlimbs

/-- Limbs of two arrays with the same value agree. -/
theorem limb_eq_of_toNat_eq {a b : LimbArray} (h : toNat a = toNat b) (i : Nat) :
    a.limb i = b.limb i := by
  apply UInt32.toNat_inj.mp
  rw [limb_toNat_eq, limb_toNat_eq, h]

/-- A value determined digit by digit. -/
theorem segment_eq_mod_of_digits (v : LimbArray) (n : Nat) :
    ∀ c, (∀ j, j < c → (v.limb j).toNat = n / radix ^ j % radix) →
      segment v 0 c = n % radix ^ c := by
  intro c
  induction c with
  | zero => intro _; simp [Nat.mod_one]
  | succ c ih =>
      intro h
      rw [segment_succ_back, Nat.zero_add, ih (fun j hj => h j (by omega)), h c (by omega),
        Nat.mod_pow_succ, Nat.mul_comm]

/-! ## Horner evaluation -/

/-- The compiled Horner loop computes the segment denotation from an accumulator. -/
theorem hornerFrom_eq (v : LimbArray) (n acc : Nat) :
    hornerFrom v n acc = acc * radix ^ n + segment v 0 n := by
  induction n generalizing acc with
  | zero => simp [hornerFrom]
  | succ n ih =>
      rw [hornerFrom, ih, segment_succ_back, Nat.zero_add]
      ring

/-- The Horner loop computes the value. -/
theorem toNatImpl_eq (v : LimbArray) : toNatImpl v = toNat v := by
  unfold toNatImpl toNat
  rw [hornerFrom_eq]
  simp

/-- Compile the proof-facing front recursion of `toNat` as its tail-recursive Horner loop. -/
-- grind: no rule; this compiler substitution exposes an implementation accumulator.
@[csimp] theorem toNat_eq_toNatImpl : @toNat = @toNatImpl := by
  funext v
  exact (toNatImpl_eq v).symm

/-! ## Construction from a natural number -/

/-- The `ofNat` loop appends exactly `count` limbs to its accumulator. -/
theorem size_ofNatLoop (count n : Nat) (acc : Array UInt32) :
    (ofNatLoop count n acc).size = acc.size + count := by
  induction count generalizing n acc with
  | zero => simp [ofNatLoop]
  | succ count ih =>
      rw [ofNatLoop, ih, Array.size_push]
      omega

/-- The `ofNat` loop keeps the accumulator's prefix and appends the base-`2^32` digits of `n`. -/
theorem getElem_ofNatLoop (count n : Nat) (acc : Array UInt32) (j : Nat)
    (hj : j < (ofNatLoop count n acc).size) :
    (ofNatLoop count n acc)[j] =
      if h : j < acc.size then acc[j] else UInt32.ofNat (n / radix ^ (j - acc.size)) := by
  induction count generalizing n acc with
  | zero =>
      simp only [ofNatLoop] at hj ⊢
      simp [hj]
  | succ count ih =>
      simp only [ofNatLoop] at hj ⊢
      rw [ih]
      by_cases hlt : j < acc.size
      · have hlt' : j < (acc.push (UInt32.ofNat n)).size := by
          rw [Array.size_push]
          omega
        rw [dite_eq_left hlt', dite_eq_left hlt, Array.getElem_push_lt hlt]
      · by_cases heq : j = acc.size
        · subst heq
          simp
        · have hgt : acc.size < j := by omega
          have hge' : ¬ j < (acc.push (UInt32.ofNat n)).size := by
            rw [Array.size_push]
            omega
          rw [dite_eq_right hge', dite_eq_right hlt, Nat.shiftRight_eq_div_pow,
            Array.size_push, ← radix_eq,
            Nat.div_div_eq_div_mul, ← pow_succ', show j - acc.size = j - (acc.size + 1) + 1 by omega]

/-- `ofNat n count` has exactly `count` limbs. -/
@[simp] theorem size_ofNat (n count : Nat) : (ofNat n count).size = count := by
  unfold ofNat size
  rw [size_ofNatLoop]
  simp

/-- Limb `j` of `ofNat n count` is the `j`-th base-`2^32` digit of `n`. -/
theorem limb_ofNat (n count j : Nat) (hj : j < count) :
    (ofNat n count).limb j = UInt32.ofNat (n / radix ^ j) := by
  unfold limb ofNat
  have hsize : j < (ofNatLoop count n (Array.emptyWithCapacity count)).size := by
    rw [size_ofNatLoop]
    simpa using hj
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hsize, Option.getD_some,
    getElem_ofNatLoop]
  simp

/-- The constructed array holds `n` modulo `radix ^ count`. -/
@[simp, grind =] theorem toNat_ofNat (n count : Nat) :
    toNat (ofNat n count) = n % radix ^ count := by
  unfold toNat
  rw [size_ofNat]
  apply segment_eq_mod_of_digits
  intro j hj
  rw [limb_ofNat n count j hj, UInt32.toNat_ofNat']

/-- The constructed array holds `n` when `n` fits `count` limbs. -/
theorem toNat_ofNat_of_lt {n count : Nat} (h : n < radix ^ count) :
    toNat (ofNat n count) = n := by
  rw [toNat_ofNat, Nat.mod_eq_of_lt h]

/-- Rebuilding an array from its value and size is the identity. -/
theorem ofNat_toNat (v : LimbArray) : ofNat (toNat v) v.size = v := by
  apply ext_of_toNat
  · simp
  · rw [toNat_ofNat_of_lt (toNat_lt v)]

/-! ## Zero -/

/-- The zero array has the requested limb count. -/
@[simp] theorem size_zero (count : Nat) : (zero count).size = count := by
  simp [zero, size]

/-- Every limb of the zero array is zero, also beyond its size. -/
theorem limb_zero (count i : Nat) : (zero count).limb i = 0 := by
  unfold limb zero
  rw [Array.getD_eq_getD_getElem?]
  by_cases h : i < count
  · simp [h]
  · rw [Array.getElem?_eq_none (by simpa using h)]
    rfl

/-- The zero array denotes zero. -/
@[simp, grind =] theorem toNat_zero (count : Nat) : toNat (zero count) = 0 := by
  unfold toNat
  apply segment_eq_zero_of_limb_eq_zero
  intro i _
  exact limb_zero count _

/-! ## Leading limb, zero test, and logarithm -/

/-- The top-limb search returns zero exactly when every scanned limb is zero. -/
theorem topLimb_eq_zero_iff (v : LimbArray) (n : Nat) :
    topLimb v n = 0 ↔ ∀ i, i < n → v.limb i = 0 := by
  induction n with
  | zero => simp [topLimb]
  | succ n ih =>
      unfold topLimb
      by_cases h : v.limb n != 0
      · simp only [h, ite_true]
        constructor
        · intro hcontra; omega
        · intro hall
          have := hall n (by omega)
          simp [this] at h
      · simp only [h, Bool.false_eq_true, ite_false]
        rw [ih]
        have hzero : v.limb n = 0 := by simpa using h
        constructor
        · intro hall i hi
          by_cases hin : i < n
          · exact hall i hin
          · have : i = n := by omega
            subst this
            exact hzero
        · intro hall i hi
          exact hall i (by omega)

/-- The top-limb search never returns an index beyond the scanned prefix. -/
theorem topLimb_le (v : LimbArray) (n : Nat) : topLimb v n ≤ n := by
  induction n with
  | zero => simp [topLimb]
  | succ n ih =>
      unfold topLimb
      split
      · exact Nat.le_refl _
      · omega

/-- When the search returns `i + 1`, limb `i` is the highest nonzero limb of the scanned prefix. -/
theorem topLimb_spec (v : LimbArray) (n i : Nat) (h : topLimb v n = i + 1) :
    v.limb i ≠ 0 ∧ i < n ∧ ∀ j, i < j → j < n → v.limb j = 0 := by
  induction n with
  | zero => simp [topLimb] at h
  | succ n ih =>
      unfold topLimb at h
      by_cases hn : v.limb n != 0
      · simp only [hn, ite_true, Nat.add_right_cancel_iff] at h
        subst h
        refine ⟨by simpa using hn, by omega, ?_⟩
        intro j hj hjn
        omega
      · simp only [hn, Bool.false_eq_true, ite_false] at h
        obtain ⟨hne, hlt, hzero⟩ := ih h
        refine ⟨hne, by omega, ?_⟩
        intro j hj hjn
        by_cases hjn' : j < n
        · exact hzero j hj hjn'
        · have : j = n := by omega
          subst this
          simpa using hn

/-- The zero test decides whether the value is zero. -/
theorem isZero_eq_true_iff (v : LimbArray) : isZero v = true ↔ toNat v = 0 := by
  unfold isZero toNat
  rw [beq_iff_eq, topLimb_eq_zero_iff, segment_eq_zero_iff]
  simp

/-- The zero test as a decision. -/
theorem isZero_eq (v : LimbArray) : isZero v = decide (toNat v = 0) := by
  by_cases h : toNat v = 0
  · simp [h, (isZero_eq_true_iff v).mpr h]
  · have : isZero v ≠ true := fun hc => h ((isZero_eq_true_iff v).mp hc)
    simp [h, this]

/-- Native `UInt32.log2` has the natural-number value of `Nat.log2`. -/
@[simp, grind =] theorem uint32_log2_toNat (x : UInt32) : x.log2.toNat = x.toNat.log2 := by
  unfold UInt32.log2 Fin.log2
  rfl

/-- The leading-bit position of a nonzero array is the natural-number logarithm of its value. -/
theorem log2_eq (v : LimbArray) (h : toNat v ≠ 0) : log2 v = (toNat v).log2 := by
  unfold log2
  cases htop : topLimb v v.size with
  | zero =>
      exfalso
      apply h
      unfold toNat
      rw [segment_eq_zero_iff]
      intro i hi
      rw [Nat.zero_add]
      exact (topLimb_eq_zero_iff v v.size).mp htop i (by simpa using hi)
  | succ i =>
      obtain ⟨hne, hlt, hzero⟩ := topLimb_spec v v.size i htop
      dsimp only
      have hvalue : toNat v = segment v 0 i + (v.limb i).toNat * radix ^ i := by
        have hback := segment_succ_back v 0 i
        rw [Nat.zero_add] at hback
        rw [← hback]
        unfold toNat
        apply segment_eq_of_limb_eq_zero (by omega)
        intro j hj hjn
        exact hzero (0 + j) (by omega) (by omega)
      have hlimbNe : (v.limb i).toNat ≠ 0 := by
        intro hc
        exact hne (UInt32.toNat_inj.mp (by simpa using hc))
      have hlow := segment_lt v 0 i
      have hlog := Nat.log2_self_le hlimbNe
      have hlog' := Nat.lt_log2_self (n := (v.limb i).toNat)
      rw [uint32_log2_toNat]
      symm
      rw [Nat.log2_eq_iff h, hvalue, radix_pow]
      constructor
      · calc
          2 ^ (32 * i + (v.limb i).toNat.log2) = 2 ^ (v.limb i).toNat.log2 * 2 ^ (32 * i) := by
            rw [pow_add, Nat.mul_comm]
          _ ≤ (v.limb i).toNat * 2 ^ (32 * i) := Nat.mul_le_mul_right _ hlog
          _ ≤ _ := Nat.le_add_left _ _
      · rw [radix_pow] at hlow
        calc
          segment v 0 i + (v.limb i).toNat * 2 ^ (32 * i) <
              2 ^ (32 * i) + (v.limb i).toNat * 2 ^ (32 * i) := by omega
          _ = ((v.limb i).toNat + 1) * 2 ^ (32 * i) := by ring
          _ ≤ 2 ^ ((v.limb i).toNat.log2 + 1) * 2 ^ (32 * i) :=
            Nat.mul_le_mul_right _ hlog'
          _ = 2 ^ (32 * i + (v.limb i).toNat.log2 + 1) := by
            rw [← pow_add]
            congr 1
            omega

/-! ## Bit access -/

/-- `testBit` reads the bit of the value. -/
theorem testBit_eq (v : LimbArray) (k : Nat) : testBit v k = (toNat v).testBit k := by
  unfold testBit
  have hk : k % 32 < 32 := Nat.mod_lt _ (by decide)
  have hmod : (UInt32.ofNat (k % 32)).toNat % 32 = k % 32 := by
    have hfit : (UInt32.ofNat (k % 32)).toNat = k % 32 := by
      rw [UInt32.toNat_ofNat']
      exact Nat.mod_eq_of_lt (by omega)
    rw [hfit]
    exact Nat.mod_eq_of_lt hk
  conv_rhs => rw [← Nat.div_add_mod k 32]
  rw [← limb_testBit v (k / 32) (k % 32) hk]
  rw [Nat.testBit_eq_decide_div_mod_eq]
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, decide_eq_true_iff, ← UInt32.toNat_inj, UInt32.toNat_and,
    UInt32.toNat_shiftRight, hmod, Nat.shiftRight_eq_div_pow,
    show (1 : UInt32).toNat = 2 ^ 1 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  simp

/-- The mask of the low `r` bits. -/
theorem lowMask32_toNat (r : Nat) (hr : r < 32) : (lowMask32 r).toNat = 2 ^ r - 1 := by
  unfold lowMask32
  have hshift : ((1 : UInt32) <<< UInt32.ofNat r).toNat = 2 ^ r := by
    rw [UInt32.toNat_shiftLeft, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega : r < 2 ^ 32),
      Nat.mod_eq_of_lt hr, Nat.shiftLeft_eq, show (1 : UInt32).toNat = 1 by decide, Nat.one_mul]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hr)
  rw [UInt32.toNat_sub_of_le, hshift]
  · rfl
  · rw [UInt32.le_iff_toNat_le, hshift]
    exact Nat.one_le_two_pow

/-- A masked limb keeps exactly the bits below `r`. -/
theorem testBit_and_lowMask32 (x : UInt32) (r j : Nat) (hr : r < 32) :
    (x &&& lowMask32 r).toNat.testBit j = (x.toNat.testBit j && decide (j < r)) := by
  rw [UInt32.toNat_and, Nat.testBit_and, lowMask32_toNat r hr, Nat.testBit_two_pow_sub_one]

/-- The 32-bit window at `lo` is the value shifted down by `lo`, modulo the radix. -/
@[simp, grind =] theorem bitsAt32_toNat (v : LimbArray) (lo : Nat) :
    (bitsAt32 v lo).toNat = toNat v / 2 ^ lo % radix := by
  rw [radix_eq]
  apply Nat.eq_of_testBit_eq
  intro n
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  have hr : lo % 32 < 32 := Nat.mod_lt _ (by decide)
  have hlo : lo = 32 * (lo / 32) + lo % 32 := (Nat.div_add_mod lo 32).symm
  unfold bitsAt32
  by_cases hr0 : lo % 32 = 0
  · simp only [hr0, beq_self_eq_true, ite_true]
    by_cases hn : n < 32
    · rw [limb_testBit v _ n hn]
      simp only [hn, decide_true, Bool.true_and]
      congr 1
      omega
    · rw [limb_testBit_eq_false v _ n (by omega)]
      simp [hn]
  · have hbeq : (lo % 32 == 0) = false := by simpa using hr0
    simp only [hbeq, Bool.false_eq_true, ite_false]
    have hofNat1 : (UInt32.ofNat (lo % 32)).toNat % 32 = lo % 32 := by
      rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega : lo % 32 < 2 ^ 32)]
      exact Nat.mod_eq_of_lt hr
    have hofNat2 : (UInt32.ofNat (32 - lo % 32)).toNat % 32 = 32 - lo % 32 := by
      rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega : 32 - lo % 32 < 2 ^ 32)]
      exact Nat.mod_eq_of_lt (by omega)
    rw [UInt32.toNat_or, Nat.testBit_or, UInt32.toNat_shiftRight, UInt32.toNat_shiftLeft, hofNat1,
      hofNat2, Nat.testBit_shiftRight, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
    by_cases hn : n < 32
    · by_cases hsplit : n + lo % 32 < 32
      · rw [limb_testBit v _ _ (by omega)]
        have hhigh : ¬ (32 - lo % 32 ≤ n) := by omega
        simp only [hn, decide_true, Bool.true_and, ge_iff_le, hhigh, decide_false,
          Bool.false_and, Bool.or_false]
        congr 1
        omega
      · rw [limb_testBit_eq_false v _ _ (by omega)]
        have hhigh : 32 - lo % 32 ≤ n := by omega
        rw [limb_testBit v _ _ (by omega)]
        simp only [hn, decide_true, Bool.true_and, ge_iff_le, hhigh, Bool.false_or]
        congr 1
        omega
    · rw [limb_testBit_eq_false v _ _ (by omega)]
      simp [hn]

/-! ## Masking and resizing -/

/-- Masking to the low bits keeps the limb count. -/
@[simp] theorem size_lowBits (v : LimbArray) (k : Nat) : (lowBits v k).size = v.size := by
  simp [lowBits, size]

/-- `lowBits` keeps whole limbs below the cut, masks the limb at the cut, and zeroes the rest. -/
theorem limb_lowBits (v : LimbArray) (k i : Nat) :
    (lowBits v k).limb i =
      if i < k / 32 then v.limb i
      else if i = k / 32 then v.limb i &&& lowMask32 (k % 32)
      else 0 := by
  by_cases hi : i < v.size
  · have hi' : i < (lowBits v k).limbs.size := by
      change i < (lowBits v k).size
      rw [size_lowBits]
      exact hi
    rw [limb_eq_getElem _ hi', limb_eq_getElem v hi]
    simp only [lowBits, Array.getElem_mapIdx, beq_iff_eq]
    rfl
  · have h1 : (lowBits v k).limb i = 0 :=
      limb_eq_zero_of_size_le _ (by simpa using hi)
    have h2 : v.limb i = 0 := limb_eq_zero_of_size_le v (by omega)
    rw [h1, h2]
    split
    · rfl
    · split
      · simp
      · rfl

/-- Masking keeps the value modulo `2^k`. -/
@[simp, grind =] theorem toNat_lowBits (v : LimbArray) (k : Nat) : toNat (lowBits v k) = toNat v % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro n
  rw [Nat.testBit_mod_two_pow]
  have hn : n % 32 < 32 := Nat.mod_lt _ (by decide)
  have hdecomp : 32 * (n / 32) + n % 32 = n := Nat.div_add_mod n 32
  rw [← hdecomp, ← limb_testBit _ _ _ hn, ← limb_testBit _ _ _ hn, limb_lowBits]
  by_cases hlt : n / 32 < k / 32
  · have : 32 * (n / 32) + n % 32 < k := by omega
    simp [hlt, this]
  · by_cases heq : n / 32 = k / 32
    · rw [ite_eq_right hlt, ite_eq_left heq, testBit_and_lowMask32 _ _ _ (Nat.mod_lt _ (by decide))]
      have : (32 * (n / 32) + n % 32 < k) ↔ (n % 32 < k % 32) := by omega
      simp [this, Bool.and_comm]
    · have : ¬ (32 * (n / 32) + n % 32 < k) := by omega
      simp [hlt, heq, this]

/-- `resize` has exactly the requested limb count. -/
@[simp] theorem size_resize (v : LimbArray) (count : Nat) : (resize v count).size = count := by
  simp [resize, size]

/-- `resize` keeps the limbs inside the new size and reads zero above it. -/
theorem limb_resize (v : LimbArray) (count i : Nat) :
    (resize v count).limb i = if i < count then v.limb i else 0 := by
  by_cases hi : i < count
  · have hi' : i < (resize v count).limbs.size := by
      change i < (resize v count).size
      rw [size_resize]
      exact hi
    rw [limb_eq_getElem _ hi']
    simp [resize, hi]
  · rw [limb_eq_zero_of_size_le _ (by simpa using hi)]
    simp [hi]

/-- Resizing keeps the value modulo `radix ^ count`. -/
@[simp, grind =] theorem toNat_resize (v : LimbArray) (count : Nat) :
    toNat (resize v count) = toNat v % radix ^ count := by
  rw [radix_pow]
  apply Nat.eq_of_testBit_eq
  intro n
  rw [Nat.testBit_mod_two_pow]
  have hn : n % 32 < 32 := Nat.mod_lt _ (by decide)
  have hdecomp : 32 * (n / 32) + n % 32 = n := Nat.div_add_mod n 32
  rw [← hdecomp, ← limb_testBit _ _ _ hn, ← limb_testBit _ _ _ hn, limb_resize]
  by_cases hi : n / 32 < count
  · have : 32 * (n / 32) + n % 32 < 32 * count := by omega
    simp [hi, this]
  · have : ¬ (32 * (n / 32) + n % 32 < 32 * count) := by omega
    simp [hi, this]

/-- Resizing to at least the stored size keeps the value. -/
theorem toNat_resize_of_size_le (v : LimbArray) {count : Nat} (h : v.size ≤ count) :
    toNat (resize v count) = toNat v := by
  rw [toNat_resize, Nat.mod_eq_of_lt (toNat_lt_of_size_le h)]

/-! ## Sticky bits -/

/-- The sticky scan reports true exactly when some limb below the cut is nonzero. -/
theorem anyLimbBelow_eq_true_iff (v : LimbArray) (q : Nat) :
    anyLimbBelow v q = true ↔ ∃ i, i < q ∧ v.limb i ≠ 0 := by
  induction q with
  | zero => simp [anyLimbBelow]
  | succ q ih =>
      unfold anyLimbBelow
      rw [Bool.or_eq_true, ih, bne_iff_ne]
      constructor
      · rintro (h | ⟨i, hi, hne⟩)
        · exact ⟨q, by omega, h⟩
        · exact ⟨i, by omega, hne⟩
      · rintro ⟨i, hi, hne⟩
        by_cases hiq : i = q
        · subst hiq; exact Or.inl hne
        · exact Or.inr ⟨i, by omega, hne⟩

/-- `anyBelow` detects a nonzero suffix below bit `k`. -/
theorem anyBelow_eq_true_iff (v : LimbArray) (k : Nat) :
    anyBelow v k = true ↔ toNat v % 2 ^ k ≠ 0 := by
  rw [← toNat_lowBits]
  unfold anyBelow
  rw [Bool.or_eq_true, anyLimbBelow_eq_true_iff, bne_iff_ne]
  constructor
  · rintro (⟨i, hi, hne⟩ | hne) hzero
    · rw [toNat, segment_eq_zero_iff] at hzero
      apply hne
      by_cases hsize : i < v.size
      · have := hzero i (by simpa using hsize)
        rw [Nat.zero_add, limb_lowBits, ite_eq_left hi] at this
        exact this
      · exact limb_eq_zero_of_size_le v (by omega)
    · rw [toNat, segment_eq_zero_iff] at hzero
      apply hne
      by_cases hsize : k / 32 < v.size
      · have := hzero (k / 32) (by simpa using hsize)
        rw [Nat.zero_add, limb_lowBits, ite_eq_right (Nat.lt_irrefl _), ite_eq_left rfl] at this
        exact this
      · rw [limb_eq_zero_of_size_le v (by omega)]
        simp
  · intro hne
    by_contra hcontra
    apply hne
    rw [not_or, not_exists] at hcontra
    obtain ⟨hall, hmask⟩ := hcontra
    rw [toNat, segment_eq_zero_iff]
    intro i _
    rw [Nat.zero_add, limb_lowBits]
    split
    · rename_i hi
      by_contra hne'
      exact hall i ⟨hi, hne'⟩
    · split
      · rename_i heq
        subst heq
        simpa using hmask
      · rfl

/-- `anyBelow` as a decision. -/
theorem anyBelow_eq (v : LimbArray) (k : Nat) :
    anyBelow v k = decide (toNat v % 2 ^ k ≠ 0) := by
  by_cases h : toNat v % 2 ^ k ≠ 0
  · simp [h, (anyBelow_eq_true_iff v k).mpr h]
  · have : anyBelow v k ≠ true := fun hc => h ((anyBelow_eq_true_iff v k).mp hc)
    simp only [ne_eq, Decidable.not_not] at h
    simp [h, this]

/-- Setting the sticky bit keeps the limb count. -/
@[simp] theorem size_orLowBit (v : LimbArray) (sticky : Bool) :
    (orLowBit v sticky).size = v.size := by
  cases sticky <;> simp [orLowBit, size]

/-- Setting the sticky bit ors `1` into limb zero and leaves every other limb unchanged. -/
theorem limb_orLowBit_true (v : LimbArray) (hsize : 0 < v.size) (i : Nat) :
    (orLowBit v true).limb i = if i = 0 then v.limb 0 ||| 1 else v.limb i := by
  unfold limb
  change (v.limbs.setIfInBounds 0 (v.limbs.getD 0 0 ||| 1)).getD i 0 = _
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases h0 : i = 0
  · subst h0
    have hsize' : 0 < v.limbs.size := hsize
    simp [hsize']
  · rw [ite_eq_right (Ne.symm h0), ite_eq_right h0, ← Array.getD_eq_getD_getElem?]

/-- Jamming a sticky bit sets bit zero of the value. -/
theorem toNat_orLowBit (v : LimbArray) (hsize : 0 < v.size) (sticky : Bool) :
    toNat (orLowBit v sticky) = if sticky then toNat v ||| 1 else toNat v := by
  cases sticky
  · simp [orLowBit]
  · simp only [ite_true]
    apply Nat.eq_of_testBit_eq
    intro n
    rw [Nat.testBit_or]
    have hn : n % 32 < 32 := Nat.mod_lt _ (by decide)
    have hdecomp : 32 * (n / 32) + n % 32 = n := Nat.div_add_mod n 32
    rw [← hdecomp, ← limb_testBit _ _ _ hn, ← limb_testBit _ _ _ hn, limb_orLowBit_true v hsize]
    by_cases hq : n / 32 = 0
    · rw [ite_eq_left hq, UInt32.toNat_or, Nat.testBit_or,
      show (1 : UInt32).toNat = 1 by decide, hq,
        Nat.mul_zero, Nat.zero_add]
    · rw [ite_eq_right hq]
      have hone : (1 : Nat).testBit (32 * (n / 32) + n % 32) = false := by
        rw [Bool.eq_false_iff, Ne, Nat.testBit_one_eq_true_iff_self_eq_zero]
        omega
      rw [hone, Bool.or_false]

/-! ## Comparison -/

/-- Lexicographic comparison from the top limb down agrees with comparing the denoted segments. -/
theorem compareFrom_eq (a b : LimbArray) (n : Nat) :
    compareFrom a b n = Ord.compare (segment a 0 n) (segment b 0 n) := by
  induction n with
  | zero => simp [compareFrom]
  | succ n ih =>
      unfold compareFrom
      simp only [segment_succ_back, Nat.zero_add]
      have ha := segment_lt a 0 n
      have hb := segment_lt b 0 n
      have hpos : 0 < radix ^ n := Nat.pow_pos (by decide)
      by_cases hlt : a.limb n < b.limb n
      · rw [ite_eq_left hlt]
        rw [UInt32.lt_iff_toNat_lt] at hlt
        symm
        rw [Nat.compare_eq_lt]
        have h1 : ((a.limb n).toNat + 1) * radix ^ n ≤ (b.limb n).toNat * radix ^ n :=
          Nat.mul_le_mul_right _ hlt
        rw [Nat.add_mul, Nat.one_mul] at h1
        omega
      · rw [ite_eq_right hlt]
        by_cases hgt : b.limb n < a.limb n
        · rw [ite_eq_left hgt]
          rw [UInt32.lt_iff_toNat_lt] at hgt
          symm
          rw [Nat.compare_eq_gt]
          have h1 : ((b.limb n).toNat + 1) * radix ^ n ≤ (a.limb n).toNat * radix ^ n :=
            Nat.mul_le_mul_right _ hgt
          rw [Nat.add_mul, Nat.one_mul] at h1
          omega
        · rw [ite_eq_right hgt, ih]
          have heq : a.limb n = b.limb n := by
            rw [UInt32.lt_iff_toNat_lt] at hlt hgt
            exact UInt32.toNat_inj.mp (by omega)
          rw [heq]
          cases hcmp : Ord.compare (segment a 0 n) (segment b 0 n) with
          | lt =>
              symm
              rw [Nat.compare_eq_lt] at hcmp ⊢
              omega
          | eq =>
              symm
              rw [Nat.compare_eq_eq] at hcmp ⊢
              omega
          | gt =>
              symm
              rw [Nat.compare_eq_gt] at hcmp ⊢
              omega

/-- Limb comparison compares the values. -/
theorem compare_eq (a b : LimbArray) : compare a b = Ord.compare (toNat a) (toNat b) := by
  unfold compare
  rw [compareFrom_eq, ← toNat_eq_segment_of_size_le (Nat.le_max_left _ _),
    ← toNat_eq_segment_of_size_le (Nat.le_max_right _ _)]

end FloatLib.Numerics.LimbArray
