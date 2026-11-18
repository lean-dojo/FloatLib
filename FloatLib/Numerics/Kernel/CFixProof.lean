/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.CBall.Exponential
public import FloatLib.Numerics.Kernel.CFix

import Mathlib.Tactic.Positivity

/-!
# `CFix` operations enclose complex arithmetic

`CFix.Contains s z a b` says that, when the flag of `z` is true, `a` and `b` are within the
radius of the two parts of `z` at the scale `s`. Numbers are of any ordered field, and
`CFix.Mem s z w` is the same for the parts of a complex number `w`. For all values:

* `contains_one`, `contains_zero`, `contains_bad`;
* `contains_mul`: the product of members `(a + i b) (c + i d)` is a member of `mul s x y`;
* `contains_conj`: the conjugate of a member is a member of `conj s x`;
* `contains_ofCBall`: a member of a complex ball is a member of `ofCBall s z`;
* `mem_one`, `mem_zero`, `mem_mul`, `mem_conj`, `mem_ofCBall`, `mem_pow2`: the same for complex
  numbers and all powers `2 ^ k`;
* `CSum.contains_zero`, `CSum.contains_push`, `CSum.contains_add`: a `CSum` contains the sum of
  members of the values pushed into it;
* `CSum.contains_scale`: a sum times a complex number contains the product of members.

When the flag is false, `Contains` gives no enclosure information. A computation is certified by
these theorems together with the test that the final flag is true.
-/

@[expose] public section

namespace FloatLib.Numerics.Kernel

namespace CFix

variable {K : Type*} [Field K] [LinearOrder K]

/-- The number that the part `n` stands for at the scale `s`: `(n - 2 * 2 ^ s) / 2 ^ s`. -/
def val (s n : Nat) : K := ((n : K) - 2 * 2 ^ s) / 2 ^ s

/--
When the flag of `z` is true, `a` is within the radius of its real part and `b` of its imaginary
part, at the scale `s`.
-/
def Contains (s : Nat) (z : CFix) (a b : K) : Prop :=
  z.ok = true → |a - val s z.re| ≤ (z.rad : K) / 2 ^ s ∧ |b - val s z.im| ≤ (z.rad : K) / 2 ^ s

/-- The offset is `2 * 2 ^ s`. -/
theorem offset_eq (s : Nat) : offset s = 2 * 2 ^ s := Nat.shiftLeft_eq 2 s

/-- A value that stands for nothing contains everything. -/
theorem contains_bad (s : Nat) (a b : K) : CFix.Contains s CFix.bad a b :=
  fun h => (Bool.false_ne_true h).elim

/-- The conjugate of a member is a member of the conjugate. -/
theorem contains_conj {s : Nat} {x : CFix} {a b : K} (hx : x.Contains s a b) :
    (conj s x).Contains s a (-b) := by
  intro hok
  have hok' : x.ok = true ∧ x.im ≤ 4 * 2 ^ s := by
    have h : Bool.and x.ok (Nat.ble x.im (Nat.shiftLeft 4 s)) = true := hok
    rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq] at h
    simpa using h
  obtain ⟨hre, him⟩ := hx hok'.1
  refine ⟨hre, ?_⟩
  have hval : val (K := K) s (conj s x).im = -val s x.im := by
    change (((Nat.sub (Nat.shiftLeft 4 s) x.im : ℕ) : K) - 2 * 2 ^ s) / 2 ^ s = _
    rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq]
    change (((4 * 2 ^ s - x.im : ℕ) : K) - 2 * 2 ^ s) / 2 ^ s = _
    rw [Nat.cast_sub hok'.2]
    unfold val
    push_cast
    rw [sub_sub, show (4 : K) * 2 ^ s - (x.im + 2 * 2 ^ s) =
      -((x.im : K) - 2 * 2 ^ s) by ring, neg_div]
  rw [hval, neg_sub_neg, abs_sub_comm]
  exact him

variable [IsStrictOrderedRing K]

/-- An integral coordinate shifted to scale `s` decodes to the integer minus the offset two. -/
theorem val_shiftLeft (s n : Nat) : val (K := K) s (n <<< s) = (n : K) - 2 := by
  unfold val
  rw [Nat.shiftLeft_eq]
  push_cast
  rw [← sub_mul, mul_div_cancel_right₀ _ (pow_ne_zero _ (by positivity))]

/-- The cast of a truncated difference in both directions is the absolute difference. -/
theorem cast_absDiff (a b : Nat) :
    (((a - b) + (b - a) : ℕ) : K) = |(a : K) - b| := by
  rcases Nat.le_total a b with h | h
  · have hK : (a : K) ≤ b := by exact_mod_cast h
    rw [Nat.sub_eq_zero_of_le h, Nat.zero_add, Nat.cast_sub h, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.2 hK)]
  · have hK : (b : K) ≤ a := by exact_mod_cast h
    rw [Nat.sub_eq_zero_of_le h, Nat.add_zero, Nat.cast_sub h, abs_of_nonneg (sub_nonneg.2 hK)]

/-- The quotient by `2 ^ s` rounded down, between its two bounds in the field. -/
theorem div_floor_bounds (n s : Nat) :
    ((n / 2 ^ s : ℕ) : K) ≤ (n : K) / 2 ^ s ∧ (n : K) / 2 ^ s < ((n / 2 ^ s : ℕ) : K) + 1 := by
  have hq : (0 : K) < 2 ^ s := by positivity
  have h2 : n < 2 ^ s * (n / 2 ^ s + 1) :=
    Nat.lt_mul_div_succ n (Nat.pos_of_ne_zero (by positivity))
  have h2' : (n : K) < 2 ^ s * (((n / 2 ^ s : ℕ) : K) + 1) := by exact_mod_cast h2
  constructor
  · simpa only [Nat.cast_pow, Nat.cast_ofNat] using (Nat.cast_div_le (α := K) (m := n) (n := 2 ^ s))
  · rw [div_lt_iff₀ hq, mul_comm]; exact h2'

/--
The rounding of one part of a product: when `u` is within `T / q²` of the exact value
`E = M / q² - o`, and `R` is `M / q` rounded down and `F` is `T / q` rounded down, then `u` is
within `(F + 2) / q` of `(R - o q) / q`.
-/
theorem part_bound {q u E M R T F o : K} (hq : 0 < q) (hE : |u - E| ≤ T / q ^ 2)
    (hEeq : E = M / q ^ 2 - o) (h1 : R ≤ M / q) (h2 : M / q < R + 1) (hT : T / q < F + 1) :
    |u - (R - o * q) / q| ≤ (F + 2) / q := by
  have hval : (R - o * q) / q = R / q - o := by
    rw [sub_div, mul_div_cancel_right₀ _ hq.ne']
  have hgap : |E - (R / q - o)| ≤ 1 / q := by
    have hrw : E - (R / q - o) = (M / q - R) / q := by
      rw [hEeq, sub_sub_sub_cancel_right, pow_two, div_mul_eq_div_div, ← sub_div]
    rw [hrw, abs_of_nonneg (div_nonneg (by linarith) hq.le)]
    exact div_le_div_of_nonneg_right (by linarith) hq.le
  have hT' : T / q ^ 2 ≤ (F + 1) / q := by
    rw [pow_two, div_mul_eq_div_div]
    exact div_le_div_of_nonneg_right hT.le hq.le
  rw [hval]
  calc |u - (R / q - o)| ≤ 1 / q + (F + 1) / q := compose_error (hE.trans hT') hgap
    _ = (F + 2) / q := by rw [add_comm, ← add_div, add_assoc]; norm_num

/-- `one s` contains one. -/
theorem contains_one (s : Nat) : (one s).Contains s (1 : K) 0 := by
  intro _
  norm_num [one, val_shiftLeft]

/-- `zero s` contains zero. -/
theorem contains_zero (s : Nat) : (zero s).Contains s (0 : K) 0 := by
  intro _
  simp [zero, val_shiftLeft]

/-- The magnitude is the sum of the magnitudes of the two parts, in units. -/
theorem mag_cast (s : Nat) (x : CFix) :
    (mag s x : K) = (|val (K := K) s x.re| + |val (K := K) s x.im|) * 2 ^ s := by
  have hq : (0 : K) < 2 ^ s := by positivity
  have hmag : mag s x = (x.re - 2 * 2 ^ s + (2 * 2 ^ s - x.re)) +
      (x.im - 2 * 2 ^ s + (2 * 2 ^ s - x.im)) := by
    change Nat.add (Nat.add (Nat.sub x.re (offset s)) (Nat.sub (offset s) x.re))
      (Nat.add (Nat.sub x.im (offset s)) (Nat.sub (offset s) x.im)) = _
    rw [offset_eq]
    rfl
  rw [hmag, Nat.cast_add, cast_absDiff, cast_absDiff]
  unfold val
  rw [abs_div, abs_div, abs_of_pos hq]
  push_cast
  rw [← add_div, div_mul_cancel₀ _ hq.ne']

/-- The scale of a rounded ball is at most the precision. -/
theorem scale_round_le (x : Ball) (p : Nat) : (x.round p).scale ≤ p := by
  change Nat.sub x.scale (Nat.sub x.scale p) ≤ p
  simp only [Nat.sub_eq]
  omega

/-- One part of `ofCBall`: a member of a ball whose scale is at most `s` is within the lifted
radius of the lifted numerator, when the midpoint is at least `-2`. -/
theorem part_spec {s : Nat} {a : Ball} (hsc : a.scale ≤ s) (hok : partOk s a = true) {v : K}
    (hv : a.Contains v) : |v - val s (partOf s a)| ≤ (radOf s a : K) / 2 ^ s := by
  obtain ⟨P, M, R, sc⟩ := a
  rw [Ball.contains_mk] at hv
  have hsc' : sc ≤ s := hsc
  have hle : M * 2 ^ (s - sc) ≤ P * 2 ^ (s - sc) + 2 * 2 ^ s := by
    have h : Nat.ble (Nat.shiftLeft M (Nat.sub s sc))
        (Nat.add (Nat.shiftLeft P (Nat.sub s sc)) (offset s)) = true := hok
    have h' := Nat.le_of_ble_eq_true h
    rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq, offset_eq] at h'
    rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq] at h'
    exact h'
  have hpart : partOf s ⟨P, M, R, sc⟩ = P * 2 ^ (s - sc) + 2 * 2 ^ s - M * 2 ^ (s - sc) := by
    change Nat.sub (Nat.add (Nat.shiftLeft P (Nat.sub s sc)) (offset s))
      (Nat.shiftLeft M (Nat.sub s sc)) = _
    simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, offset_eq]
    rfl
  have hrad : radOf s ⟨P, M, R, sc⟩ = R * 2 ^ (s - sc) := Nat.shiftLeft_eq _ _
  have hpow : (2 : K) ^ s = 2 ^ sc * 2 ^ (s - sc) := by
    rw [← pow_add, Nat.add_sub_of_le hsc']
  have h3 : (0 : K) < 2 ^ (s - sc) := by positivity
  rw [hpart, hrad]
  unfold val
  rw [Nat.cast_sub hle]
  push_cast
  rw [hpow]
  have e1 : ((P : K) * 2 ^ (s - sc) + 2 * (2 ^ sc * 2 ^ (s - sc)) - M * 2 ^ (s - sc) -
      2 * (2 ^ sc * 2 ^ (s - sc))) / (2 ^ sc * 2 ^ (s - sc)) = ((P : K) - M) / 2 ^ sc := by
    rw [add_sub_right_comm, add_sub_cancel_right, ← sub_mul,
      mul_div_mul_right _ _ h3.ne']
  have e2 : (R : K) * 2 ^ (s - sc) / (2 ^ sc * 2 ^ (s - sc)) = (R : K) / 2 ^ sc := by
    exact mul_div_mul_right _ _ h3.ne'
  rw [e1, e2]
  exact hv

/-- A member of a complex ball is a member of the ball on the grid. -/
theorem contains_ofCBall {s : Nat} {z : CBall} {a b : K} (hz : z.Contains a b) :
    (ofCBall s z).Contains s a b := by
  intro hok
  have hok' : partOk s (z.re.round s) = true ∧ partOk s (z.im.round s) = true := by
    have h : Bool.and (partOk s (z.re.round s)) (partOk s (z.im.round s)) = true := hok
    simpa using h
  have hre := part_spec (scale_round_le z.re s) hok'.1 (Ball.contains_round hz.1 s)
  have him := part_spec (scale_round_le z.im s) hok'.2 (Ball.contains_round hz.2 s)
  have hq : (0 : K) < 2 ^ s := by positivity
  have hrad : (ofCBall s z).rad =
      maxNat (radOf s (z.re.round s)) (radOf s (z.im.round s)) := rfl
  rw [hrad, maxNat_eq]
  refine ⟨hre.trans ?_, him.trans ?_⟩
  · exact div_le_div_of_nonneg_right (by exact_mod_cast le_max_left _ _) hq.le
  · exact div_le_div_of_nonneg_right (by exact_mod_cast le_max_right _ _) hq.le

end CFix

namespace CSum

variable {K : Type*} [Field K] [LinearOrder K]

/--
When the flag of `S` is true, `a` is within the summed radius of the real part of the sum and `b`
of its imaginary part, at the scale `s`: the offsets of the `count` values are removed.
-/
def Contains (s : Nat) (S : CSum) (a b : K) : Prop :=
  S.ok = true →
    |a - ((S.re : K) - S.count * (2 * 2 ^ s)) / 2 ^ s| ≤ (S.rad : K) / 2 ^ s ∧
    |b - ((S.im : K) - S.count * (2 * 2 ^ s)) / 2 ^ s| ≤ (S.rad : K) / 2 ^ s

/-- A member of a fixed-point value is a member of its one-element sum. -/
theorem contains_single {s : Nat} {z : CFix} {a b : K} (hz : z.Contains s a b) :
    (single z).Contains s a b := by
  simpa only [Contains, single, Nat.cast_one, one_mul, CFix.Contains, CFix.val] using hz

/-- A sum that stands for nothing contains everything. -/
theorem contains_bad (s : Nat) (a b : K) : CSum.Contains s CSum.bad a b :=
  fun h => (Bool.false_ne_true h).elim

variable [IsStrictOrderedRing K]

/-- The empty sum contains zero. -/
theorem contains_zero (s : Nat) : zero.Contains s (0 : K) 0 := by
  intro _
  simp [zero]

/-- The sum of two sums contains the sum of their members. -/
theorem contains_add {s : Nat} {S T : CSum} {a b a' b' : K} (hS : S.Contains s a b)
    (hT : T.Contains s a' b') : (add S T).Contains s (a + a') (b + b') := by
  intro hok
  have hok' : S.ok = true ∧ T.ok = true := by
    have h : Bool.and S.ok T.ok = true := hok
    simpa using h
  obtain ⟨hSa, hSb⟩ := hS hok'.1
  obtain ⟨hTa, hTb⟩ := hT hok'.2
  have hre : (((add S T).re : K) - (add S T).count * (2 * 2 ^ s)) / 2 ^ s =
      ((S.re : K) - S.count * (2 * 2 ^ s)) / 2 ^ s +
        ((T.re : K) - T.count * (2 * 2 ^ s)) / 2 ^ s := by
    change (((Nat.add S.re T.re : ℕ) : K) - ((Nat.add S.count T.count : ℕ) : K) * (2 * 2 ^ s)) /
      2 ^ s = _
    simp only [Nat.add_eq, Nat.cast_add, add_mul, add_sub_add_comm, add_div]
  have him : (((add S T).im : K) - (add S T).count * (2 * 2 ^ s)) / 2 ^ s =
      ((S.im : K) - S.count * (2 * 2 ^ s)) / 2 ^ s +
        ((T.im : K) - T.count * (2 * 2 ^ s)) / 2 ^ s := by
    change (((Nat.add S.im T.im : ℕ) : K) - ((Nat.add S.count T.count : ℕ) : K) * (2 * 2 ^ s)) /
      2 ^ s = _
    simp only [Nat.add_eq, Nat.cast_add, add_mul, add_sub_add_comm, add_div]
  have hrad : ((add S T).rad : K) / 2 ^ s = (S.rad : K) / 2 ^ s + (T.rad : K) / 2 ^ s := by
    change ((Nat.add S.rad T.rad : ℕ) : K) / 2 ^ s = _
    simp only [Nat.add_eq, Nat.cast_add, add_div]
  rw [hre, him, hrad]
  exact ⟨Backward.add hSa hTa, Backward.add hSb hTb⟩

/-- Pushing a value adds its member to the member of the sum. -/
theorem contains_push {s : Nat} {z : CFix} {S : CSum} {a b a' b' : K} (hz : z.Contains s a b)
    (hS : S.Contains s a' b') : (push z S).Contains s (a + a') (b + b') :=
  contains_add (contains_single hz) hS

/-- The real part of a scaled sum, in ordinary notation. -/
theorem scale_re (s : Nat) (z : CFix) (S : CSum) :
    (scale s z S).re = (z.re * S.re + S.count * (2 * 2 ^ s) * z.im + S.im * 2 ^ (s + 1) +
      S.count * (2 * 2 ^ s) * 2 ^ s -
      (z.im * S.im + S.count * (2 * 2 ^ s) * z.re + S.re * 2 ^ (s + 1))) / 2 ^ s := by
  change Nat.shiftRight (Nat.sub (Nat.add (Nat.add (Nat.add (Nat.mul z.re S.re)
      (Nat.mul (Nat.mul S.count (CFix.offset s)) z.im)) (Nat.shiftLeft S.im (Nat.succ s)))
      (Nat.shiftLeft (Nat.mul S.count (CFix.offset s)) s))
    (Nat.add (Nat.add (Nat.mul z.im S.im) (Nat.mul (Nat.mul S.count (CFix.offset s)) z.re))
      (Nat.shiftLeft S.re (Nat.succ s)))) s = _
  simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow,
    CFix.offset_eq]
  rfl

/-- The imaginary part of a scaled sum, in ordinary notation. -/
theorem scale_im (s : Nat) (z : CFix) (S : CSum) :
    (scale s z S).im = (z.re * S.im + z.im * S.re + 5 * (S.count * (2 * 2 ^ s) * 2 ^ s) -
      (S.count * (2 * 2 ^ s) * (z.re + z.im) + (S.re + S.im) * 2 ^ (s + 1))) / 2 ^ s := by
  change Nat.shiftRight (Nat.sub (Nat.add (Nat.add (Nat.mul z.re S.im) (Nat.mul z.im S.re))
      (Nat.mul 5 (Nat.shiftLeft (Nat.mul S.count (CFix.offset s)) s)))
    (Nat.add (Nat.mul (Nat.mul S.count (CFix.offset s)) (Nat.add z.re z.im))
      (Nat.shiftLeft (Nat.add S.re S.im) (Nat.succ s)))) s = _
  simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow,
    CFix.offset_eq]
  rfl

/-- The radius of a scaled sum, in ordinary notation. -/
theorem scale_rad (s : Nat) (z : CFix) (S : CSum) :
    (scale s z S).rad =
      (CFix.mag s z * S.rad + mag s S * z.rad + 2 * z.rad * S.rad) / 2 ^ s + 2 := by
  change Nat.add (Nat.shiftRight (Nat.add (Nat.add (Nat.mul (CFix.mag s z) S.rad)
    (Nat.mul (mag s S) z.rad)) (Nat.mul (Nat.mul 2 z.rad) S.rad)) s) 2 = _
  simp only [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
  rfl

/-- The flag of a scaled sum: both flags, and neither subtraction below zero. -/
theorem scale_ok (s : Nat) (z : CFix) (S : CSum) :
    (scale s z S).ok = true ↔ (z.ok = true ∧ S.ok = true) ∧
      z.im * S.im + S.count * (2 * 2 ^ s) * z.re + S.re * 2 ^ (s + 1) ≤
        z.re * S.re + S.count * (2 * 2 ^ s) * z.im + S.im * 2 ^ (s + 1) +
          S.count * (2 * 2 ^ s) * 2 ^ s ∧
      S.count * (2 * 2 ^ s) * (z.re + z.im) + (S.re + S.im) * 2 ^ (s + 1) ≤
        z.re * S.im + z.im * S.re + 5 * (S.count * (2 * 2 ^ s) * 2 ^ s) := by
  change Bool.and (Bool.and z.ok S.ok) (Bool.and
    (Nat.ble (Nat.add (Nat.add (Nat.mul z.im S.im) (Nat.mul (Nat.mul S.count (CFix.offset s)) z.re))
        (Nat.shiftLeft S.re (Nat.succ s)))
      (Nat.add (Nat.add (Nat.add (Nat.mul z.re S.re)
        (Nat.mul (Nat.mul S.count (CFix.offset s)) z.im)) (Nat.shiftLeft S.im (Nat.succ s)))
        (Nat.shiftLeft (Nat.mul S.count (CFix.offset s)) s)))
    (Nat.ble (Nat.add (Nat.mul (Nat.mul S.count (CFix.offset s)) (Nat.add z.re z.im))
        (Nat.shiftLeft (Nat.add S.re S.im) (Nat.succ s)))
      (Nat.add (Nat.add (Nat.mul z.re S.im) (Nat.mul z.im S.re))
        (Nat.mul 5 (Nat.shiftLeft (Nat.mul S.count (CFix.offset s)) s))))) = true ↔ _
  simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, CFix.offset_eq, Bool.and_eq_true, Nat.ble_eq]
  rfl

/-- The midpoint of the real part of a sum. -/
def mid (s : Nat) (S : CSum) (part : Nat) : K := ((part : K) - S.count * (2 * 2 ^ s)) / 2 ^ s

/-- The magnitude of a sum is the sum of the magnitudes of the two parts of its midpoint, in
units. -/
theorem mag_cast (s : Nat) (S : CSum) :
    (mag s S : K) = (|mid (K := K) s S S.re| + |mid (K := K) s S S.im|) * 2 ^ s := by
  have hq : (0 : K) < 2 ^ s := by positivity
  have hmag : mag s S = (S.re - S.count * (2 * 2 ^ s) + (S.count * (2 * 2 ^ s) - S.re)) +
      (S.im - S.count * (2 * 2 ^ s) + (S.count * (2 * 2 ^ s) - S.im)) := by
    change Nat.add (Nat.add (Nat.sub S.re (Nat.mul S.count (CFix.offset s)))
        (Nat.sub (Nat.mul S.count (CFix.offset s)) S.re))
      (Nat.add (Nat.sub S.im (Nat.mul S.count (CFix.offset s)))
        (Nat.sub (Nat.mul S.count (CFix.offset s)) S.im)) = _
    rw [CFix.offset_eq]
    rfl
  rw [hmag, Nat.cast_add, CFix.cast_absDiff, CFix.cast_absDiff]
  unfold mid
  rw [abs_div, abs_div, abs_of_pos hq]
  push_cast
  rw [← add_div, div_mul_cancel₀ _ hq.ne']

/-- A member of a sum times a member of a complex number is a member of the scaled sum. -/
theorem contains_scale {s : Nat} {z : CFix} {S : CSum} {a b A B : K} (hz : z.Contains s a b)
    (hS : S.Contains s A B) : (scale s z S).Contains s (a * A - b * B) (a * B + b * A) := by
  intro hok
  obtain ⟨⟨hzok, hSok⟩, hNP, hNP'⟩ := (scale_ok s z S).1 hok
  obtain ⟨hza, hzb⟩ := hz hzok
  obtain ⟨hSA, hSB⟩ := hS hSok
  have hq : (0 : K) < 2 ^ s := by positivity
  have h1s : (2 : K) ^ (s + 1) = 2 * 2 ^ s := pow_succ' _ _
  have hmz := CFix.mag_cast (K := K) s z
  have hmS := mag_cast (K := K) s S
  change |A - mid s S S.re| ≤ _ at hSA
  change |B - mid s S S.im| ≤ _ at hSB
  have hT := (CFix.div_floor_bounds (K := K)
    (CFix.mag s z * S.rad + mag s S * z.rad + 2 * z.rad * S.rad) s).2
  have hTid : ((CFix.mag s z * S.rad + mag s S * z.rad + 2 * z.rad * S.rad : ℕ) : K) /
        (2 ^ s) ^ 2 =
      (z.rad : K) / 2 ^ s * (|mid (K := K) s S S.re| + (S.rad : K) / 2 ^ s) +
        |CFix.val (K := K) s z.re| * ((S.rad : K) / 2 ^ s) +
      ((z.rad : K) / 2 ^ s * (|mid (K := K) s S S.im| + (S.rad : K) / 2 ^ s) +
        |CFix.val (K := K) s z.im| * ((S.rad : K) / 2 ^ s)) := by
    push_cast
    rw [hmz, hmS]
    field_simp
    ring
  have hcount : (scale s z S).count = S.count := rfl
  constructor
  · have hfl := CFix.div_floor_bounds (K := K) (z.re * S.re + S.count * (2 * 2 ^ s) * z.im +
      S.im * 2 ^ (s + 1) + S.count * (2 * 2 ^ s) * 2 ^ s -
      (z.im * S.im + S.count * (2 * 2 ^ s) * z.re + S.re * 2 ^ (s + 1))) s
    have hE : |a * A - b * B - (CFix.val s z.re * mid s S S.re - CFix.val s z.im * mid s S S.im)| ≤
        ((CFix.mag s z * S.rad + mag s S * z.rad + 2 * z.rad * S.rad : ℕ) : K) / (2 ^ s) ^ 2 := by
      rw [hTid]
      exact Backward.sub (Backward.deviation_mul hza hSA) (Backward.deviation_mul hzb hSB)
    have hEeq : CFix.val (K := K) s z.re * mid s S S.re - CFix.val s z.im * mid s S S.im =
        ((z.re * S.re + S.count * (2 * 2 ^ s) * z.im + S.im * 2 ^ (s + 1) +
          S.count * (2 * 2 ^ s) * 2 ^ s -
          (z.im * S.im + S.count * (2 * 2 ^ s) * z.re + S.re * 2 ^ (s + 1)) : ℕ) : K) /
          (2 ^ s) ^ 2 - 2 * (S.count : K) := by
      rw [Nat.cast_sub hNP]
      push_cast
      rw [h1s]
      unfold CFix.val mid
      field_simp
      ring
    have := CFix.part_bound hq hE hEeq hfl.1 hfl.2 hT
    rw [scale_re, scale_rad, hcount]
    push_cast at this ⊢
    rw [← mul_assoc (S.count : K), mul_comm (S.count : K) 2]
    exact this
  · have hfl := CFix.div_floor_bounds (K := K) (z.re * S.im + z.im * S.re +
      5 * (S.count * (2 * 2 ^ s) * 2 ^ s) -
      (S.count * (2 * 2 ^ s) * (z.re + z.im) + (S.re + S.im) * 2 ^ (s + 1))) s
    have hE : |a * B + b * A - (CFix.val s z.re * mid s S S.im + CFix.val s z.im * mid s S S.re)| ≤
        ((CFix.mag s z * S.rad + mag s S * z.rad + 2 * z.rad * S.rad : ℕ) : K) / (2 ^ s) ^ 2 := by
      have h := Backward.add (Backward.deviation_mul hza hSB) (Backward.deviation_mul hzb hSA)
      rw [hTid]
      simpa only [mul_add, add_assoc, add_comm, add_left_comm] using h
    have hEeq : CFix.val (K := K) s z.re * mid s S S.im + CFix.val s z.im * mid s S S.re =
        ((z.re * S.im + z.im * S.re + 5 * (S.count * (2 * 2 ^ s) * 2 ^ s) -
          (S.count * (2 * 2 ^ s) * (z.re + z.im) + (S.re + S.im) * 2 ^ (s + 1)) : ℕ) : K) /
          (2 ^ s) ^ 2 - 2 * (S.count : K) := by
      rw [Nat.cast_sub hNP']
      push_cast
      rw [h1s]
      unfold CFix.val mid
      field_simp
      ring
    have := CFix.part_bound hq hE hEeq hfl.1 hfl.2 hT
    rw [scale_im, scale_rad, hcount]
    push_cast at this ⊢
    rw [show (S.count : K) * (2 * 2 ^ s) = 2 * (S.count : K) * 2 ^ s by ac_rfl]
    exact this

end CSum

namespace CFix

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The product of members is a member of the product: scaling specialized to count one. -/
theorem contains_mul {s : Nat} {x y : CFix} {a b c d : K} (hx : x.Contains s a b)
    (hy : y.Contains s c d) : (mul s x y).Contains s (a * c - b * d) (a * d + b * c) := by
  have h := CSum.contains_scale hx (CSum.contains_single hy)
  simpa only [Contains, val, mul, CSum.Contains, CSum.scale, CSum.single,
    Nat.cast_one, one_mul] using h

/-! ### Complex numbers -/

/-- The complex number `w` is a member of `z` at the scale `s`. -/
def Mem (s : Nat) (z : CFix) (w : ℂ) : Prop := z.Contains s w.re w.im

/-- `one s` contains one. -/
theorem mem_one (s : Nat) : (one s).Mem s 1 := contains_one s

/-- `zero s` contains zero. -/
theorem mem_zero (s : Nat) : (zero s).Mem s 0 := contains_zero s

/-- A product of members is a member of the product. -/
theorem mem_mul {s : Nat} {x y : CFix} {z w : ℂ} (hx : x.Mem s z) (hy : y.Mem s w) :
    (mul s x y).Mem s (z * w) := by
  simpa only [Mem, Complex.mul_re, Complex.mul_im] using contains_mul hx hy

/-- The conjugate of a member is a member of the conjugate. -/
theorem mem_conj {s : Nat} {x : CFix} {z : ℂ} (hx : x.Mem s z) :
    (conj s x).Mem s (starRingEnd ℂ z) := contains_conj hx

/-- A member of a complex ball is a member of the ball on the grid. -/
theorem mem_ofCBall {s : Nat} {z : CBall} {w : ℂ} (hz : z.Mem w) : (ofCBall s z).Mem s w :=
  contains_ofCBall hz

/-- Repeated squaring encloses the corresponding power for every number of steps. -/
theorem mem_pow2 {s : Nat} {x : CFix} {z : ℂ} (k : Nat) (hx : x.Mem s z) :
    (pow2 s k x).Mem s (z ^ (2 ^ k)) := by
  induction k with
  | zero => simpa [pow2] using hx
  | succ k ih =>
    change (mul s (pow2 s k x) (pow2 s k x)).Mem s (z ^ (2 ^ (k + 1)))
    rw [Nat.pow_succ, Nat.mul_two, pow_add]
    exact mem_mul ih ih

end CFix

end FloatLib.Numerics.Kernel
