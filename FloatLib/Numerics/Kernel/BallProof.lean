/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.ErrorBound.Algebra
public import FloatLib.Numerics.Kernel.Ball
public import FloatLib.Numerics.Kernel.DyadProof

import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# `Ball` operations enclose the operations of an ordered field

`Ball.Contains b v` says that `v`, a number of any ordered field `K`, is within the radius of the
midpoint of `b`. Every operation of `FloatLib.Numerics.Kernel.Ball` returns a ball that contains
the result of the same operation on any members, for all balls:

* `contains_iff`: membership is `lower ≤ v ≤ upper`; `contains_mk` writes it out for given
  fields;
* `contains_ofDyad`, `contains_ofNat`, `contains_ofFrac`, `contains_ofBounds`;
* `contains_add`, `contains_neg`, `contains_sub`, `contains_mul`;
* `contains_inv`, `contains_div`, for a divisor that `apart` accepts, and `apart_iff`: `apart`
  holds exactly when zero is not a member;
* `contains_drop`, `contains_round`, `contains_trim`: rounding keeps every member;
* `le_sound`, `lt_sound`: a passed comparison holds for all members.

Nothing is proved about how small the radius of a rounded ball is, apart from what its definition
says.
-/

@[expose] public section

namespace FloatLib.Numerics.Kernel.Ball

variable {K : Type*} [Field K] [LinearOrder K]

/-- `v` is a member of the ball `b`: its distance to the midpoint is at most the radius. -/
def Contains (b : Ball) (v : K) : Prop := |v - (b.mid.toRat : K)| ≤ (b.radius.toRat : K)

/-- The negation of a member is a member of the negation. -/
theorem contains_neg {x : Ball} {v : K} (hv : x.Contains v) : x.neg.Contains (-v) := by
  unfold Contains at hv ⊢
  have hmid : x.neg.mid.toRat = -x.mid.toRat := Dyad.toRat_neg x.mid
  have hradius : x.neg.radius.toRat = x.radius.toRat := rfl
  rw [hmid, hradius]
  push_cast
  rw [neg_sub_neg, abs_sub_comm]
  exact hv

variable [IsStrictOrderedRing K]

/--
Membership in the ball with the given fields, written out: the form in which a hypothesis about
a real number is usually at hand.
-/
theorem contains_mk (plus minus rad scale : Nat) (v : K) :
    (Ball.mk plus minus rad scale).Contains v ↔
      |v - ((plus : K) - minus) / 2 ^ scale| ≤ (rad : K) / 2 ^ scale := by
  unfold Contains
  simp only [mid, radius, Dyad.toRat_mk]
  push_cast
  rw [sub_zero]

/-- The radius is `rad / 2 ^ scale`. -/
theorem toRat_radius (b : Ball) : b.radius.toRat = (b.rad : ℚ) / 2 ^ b.scale := by
  simp [radius]

/-- The radius is not negative. -/
theorem radius_nonneg (b : Ball) : 0 ≤ b.radius.toRat := by
  rw [toRat_radius]
  positivity

/-- The lower end is the midpoint minus the radius. -/
theorem toRat_lower (b : Ball) : b.lower.toRat = b.mid.toRat - b.radius.toRat := by
  simp only [lower, mid, radius, Dyad.toRat_mk, Nat.add_eq]
  push_cast
  ring

/-- The upper end is the midpoint plus the radius. -/
theorem toRat_upper (b : Ball) : b.upper.toRat = b.mid.toRat + b.radius.toRat := by
  simp only [upper, mid, radius, Dyad.toRat_mk, Nat.add_eq]
  push_cast
  ring

/-- The members of a ball are the numbers between its two ends. -/
theorem contains_iff (b : Ball) (v : K) :
    b.Contains v ↔ (b.lower.toRat : K) ≤ v ∧ v ≤ (b.upper.toRat : K) := by
  unfold Contains
  rw [toRat_lower, toRat_upper]
  push_cast
  simp only [abs_le, le_sub_iff_add_le, sub_le_iff_le_add, neg_add_eq_sub,
    add_comm (b.radius.toRat : K)]

/-- A rational within the radius of the midpoint is a member, in every ordered field. -/
theorem contains_of_rat {b : Ball} {q : ℚ} (h : |q - b.mid.toRat| ≤ b.radius.toRat) :
    b.Contains (q : K) := by
  have hcast := Rat.cast_le (K := K) |>.2 h
  rw [Rat.cast_abs, Rat.cast_sub] at hcast
  exact hcast

/-- The ball around a dyadic number contains it. -/
theorem contains_ofDyad (d : Dyad) : (ofDyad d).Contains (d.toRat : K) := by
  refine contains_of_rat ?_
  change |d.toRat - d.toRat| ≤ (Dyad.mk 0 0 d.scale).toRat
  simp

/-- The ball around a natural number contains it. -/
theorem contains_ofNat (n : Nat) : (ofNat n).Contains (n : K) := by
  have h := contains_ofDyad (K := K) (Dyad.ofNat n)
  rw [Dyad.toRat_ofNat, Rat.cast_natCast] at h
  exact h

/-- `ofFrac q p` contains the fraction `q`. -/
theorem contains_ofFrac (q : Frac) (p : Nat) : (ofFrac q p).Contains (q.toRat : K) := by
  refine contains_of_rat ?_
  have hden : (0 : ℚ) < q.den := q.den_cast_pos
  have hdenInt : (0 : Int) < (q.den : Int) := Int.natCast_pos.2 q.den_pos
  have hmid : (ofFrac q p).mid.toRat =
      ((q.num.toInt * 2 ^ p / (q.den : Int) : Int) : ℚ) / 2 ^ p := by
    rw [Dyad.toRat_eq_num]
    change ((((q.num.shiftLeft p).floorDiv q.den).toInt : Int) : ℚ) / 2 ^ p = _
    rw [Signed.toInt_floorDiv, Signed.toInt_shiftLeft]
  have hq : q.toRat = (q.num.toInt : ℚ) / q.den := by
    rw [Frac.toRat_eq, Signed.toInt_eq]
    simp [Frac.num]
  have hradius : (ofFrac q p).radius.toRat = 1 / 2 ^ p := by
    rw [toRat_radius]
    change ((1 : Nat) : ℚ) / 2 ^ p = _
    rw [Nat.cast_one]
  have hlow := Int.ediv_mul_le (q.num.toInt * 2 ^ p) (b := (q.den : Int)) hdenInt.ne'
  have hhigh := Int.lt_ediv_add_one_mul_self (q.num.toInt * 2 ^ p) hdenInt
  have hlowQ := Int.cast_le (R := ℚ) |>.2 hlow
  have hhighQ := Int.cast_lt (R := ℚ) |>.2 hhigh
  push_cast at hlowQ hhighQ
  rw [hmid, hq, hradius, abs_le]
  constructor
  · have h : ((q.num.toInt * 2 ^ p / (q.den : Int) : Int) : ℚ) / 2 ^ p ≤
        (q.num.toInt : ℚ) / q.den := by
      rw [div_le_div_iff₀ (by positivity) hden]
      exact hlowQ
    have hpos : (0 : ℚ) < 1 / 2 ^ p := by positivity
    linarith
  · have h : (q.num.toInt : ℚ) / q.den ≤
        (((q.num.toInt * 2 ^ p / (q.den : Int) : Int) : ℚ) + 1) / 2 ^ p := by
      rw [div_le_div_iff₀ hden (by positivity)]
      exact hhighQ.le
    rw [add_div] at h
    linarith

/-- `ofBounds lo hi` contains every number from `lo` to `hi`. -/
theorem contains_ofBounds {lo hi : Dyad} {v : K} (hlo : (lo.toRat : K) ≤ v)
    (hhi : v ≤ (hi.toRat : K)) : (ofBounds lo hi).Contains v := by
  have hmid : (ofBounds lo hi).mid.toRat = (lo.toRat + hi.toRat) / 2 := by
    change ((lo.add hi).divPow2 1).toRat = _
    rw [Dyad.toRat_divPow2, Dyad.toRat_add, pow_one]
  have hradius : (hi.toRat - lo.toRat) / 2 ≤ (ofBounds lo hi).radius.toRat := by
    rw [toRat_radius, Dyad.toRat_lift hi (lo.scale - hi.scale),
      Dyad.toRat_lift lo (hi.scale - lo.scale), ← Dyad.scale_align lo.scale hi.scale, ← sub_div,
      div_div]
    change _ ≤ (((hi.plus <<< (lo.scale - hi.scale) + lo.minus <<< (hi.scale - lo.scale) -
      (hi.minus <<< (lo.scale - hi.scale) + lo.plus <<< (hi.scale - lo.scale)) : Nat) : Nat) : ℚ) /
        2 ^ (lo.scale + (hi.scale - lo.scale) + 1)
    rw [pow_succ, div_le_div_iff_of_pos_right (by positivity)]
    have h := Nat.cast_le (α := ℚ) |>.2
      (le_tsub_add (a := hi.minus <<< (lo.scale - hi.scale) + lo.plus <<< (hi.scale - lo.scale))
        (b := hi.plus <<< (lo.scale - hi.scale) + lo.minus <<< (hi.scale - lo.scale)))
    simp only [Nat.shiftLeft_eq] at h ⊢
    push_cast at h ⊢
    linarith
  have hradiusK := Rat.cast_le (K := K) |>.2 hradius
  unfold Contains
  rw [hmid, abs_le]
  push_cast at hradiusK ⊢
  constructor <;> linarith

/-- The midpoint of a sum is the sum of the midpoints. -/
theorem mid_add (x y : Ball) : (x.add y).mid.toRat = x.mid.toRat + y.mid.toRat :=
  Dyad.toRat_add x.mid y.mid

/-- The radius of a sum is the sum of the radii. -/
theorem radius_add (x y : Ball) : (x.add y).radius.toRat = x.radius.toRat + y.radius.toRat := by
  rw [toRat_radius, toRat_radius, toRat_radius]
  have h := Dyad.toRat_lift (Dyad.mk x.rad 0 x.scale) (y.scale - x.scale)
  have h' := Dyad.toRat_lift (Dyad.mk y.rad 0 y.scale) (x.scale - y.scale)
  rw [Dyad.toRat_mk] at h h'
  simp only [Nat.cast_zero, sub_zero] at h h'
  rw [h, h', ← Dyad.scale_align x.scale y.scale, ← add_div]
  change (((x.rad <<< (y.scale - x.scale) + y.rad <<< (x.scale - y.scale) : Nat) : ℚ)) /
    2 ^ (x.scale + (y.scale - x.scale)) = _
  simp only [Nat.shiftLeft_eq]
  push_cast
  rfl

/-- A sum of members is a member of the sum. -/
theorem contains_add {x y : Ball} {v w : K} (hv : x.Contains v) (hw : y.Contains w) :
    (x.add y).Contains (v + w) := by
  unfold Contains at hv hw ⊢
  rw [mid_add, radius_add]
  push_cast
  exact Backward.add hv hw

/-- A difference of members is a member of the difference. -/
theorem contains_sub {x y : Ball} {v w : K} (hv : x.Contains v) (hw : y.Contains w) :
    (x.sub y).Contains (v - w) := by
  rw [sub_eq_add_neg]
  exact contains_add hv (contains_neg hw)

/-- The midpoint of a product is the product of the midpoints. -/
theorem mid_mul (x y : Ball) : (x.mul y).mid.toRat = x.mid.toRat * y.mid.toRat := by
  change (x.mid.mul y.mid).norm.toRat = _
  rw [Dyad.toRat_norm, Dyad.toRat_mul]

/-- The bound `(plus + minus) / 2 ^ scale` on the absolute value of the midpoint. -/
theorem abs_mid_le (x : Ball) : |x.mid.toRat| ≤ ((x.plus : ℚ) + x.minus) / 2 ^ x.scale := by
  have hplus : (0 : ℚ) ≤ x.plus := Nat.cast_nonneg _
  have hminus : (0 : ℚ) ≤ x.minus := Nat.cast_nonneg _
  change |(Dyad.mk x.plus x.minus x.scale).toRat| ≤ _
  rw [Dyad.toRat_mk, abs_div, abs_of_pos (by positivity : (0 : ℚ) < 2 ^ x.scale),
    div_le_div_iff_of_pos_right (by positivity)]
  simpa only [abs_of_nonneg hplus, abs_of_nonneg hminus] using
    abs_sub (x.plus : ℚ) x.minus

/-- The radius of a product, in terms of the radii and the bounds on the midpoints. -/
theorem radius_mul (x y : Ball) :
    (x.mul y).radius.toRat =
      ((x.plus : ℚ) + x.minus) / 2 ^ x.scale * y.radius.toRat +
        (((y.plus : ℚ) + y.minus) / 2 ^ y.scale + y.radius.toRat) * x.radius.toRat := by
  rw [toRat_radius, toRat_radius, toRat_radius]
  change (((x.plus + x.minus) * y.rad + (y.plus + y.minus + y.rad) * x.rad : Nat) : ℚ) /
    2 ^ (x.scale + y.scale) = _
  push_cast
  rw [pow_add]
  field_simp

/-- The distance of a product to the product of two centres. -/
private theorem abs_mul_sub_le {v w m n r s A B : K} (hv : |v - m| ≤ r) (hw : |w - n| ≤ s)
    (hA : |m| ≤ A) (hB : |n| ≤ B) : |v * w - m * n| ≤ A * s + (B + s) * r := by
  calc
    |v * w - m * n| ≤ r * (|n| + s) + |m| * s := Backward.deviation_mul hv hw
    _ ≤ r * (B + s) + A * s :=
      add_le_add (mul_le_mul_of_nonneg_left (add_le_add hB le_rfl) ((abs_nonneg _).trans hv))
        (mul_le_mul_of_nonneg_right hA ((abs_nonneg _).trans hw))
    _ = A * s + (B + s) * r := by ac_rfl

/-- A product of members is a member of the product. -/
theorem contains_mul {x y : Ball} {v w : K} (hv : x.Contains v) (hw : y.Contains w) :
    (x.mul y).Contains (v * w) := by
  unfold Contains at hv hw ⊢
  have hx := Rat.cast_le (K := K) |>.2 (abs_mid_le x)
  have hy := Rat.cast_le (K := K) |>.2 (abs_mid_le y)
  rw [Rat.cast_abs] at hx hy
  rw [mid_mul, radius_mul]
  push_cast at hx hy ⊢
  exact abs_mul_sub_le hv hw hx hy

/-- The midpoint of `drop k` is the midpoint with its lowest `k` bits removed downward. -/
theorem mid_drop (x : Ball) (k : Nat) : (x.drop k).mid = x.mid.dropDown k := rfl

/-- The new radius of `drop k` covers the old one and what the midpoint moved by. -/
theorem radius_drop_ge (x : Ball) (k : Nat) :
    x.radius.toRat + (2 ^ k - 1) / 2 ^ x.scale ≤ (x.drop k).radius.toRat := by
  have hscale : k - x.scale + x.scale = k + (x.scale - k) := by omega
  have hpow : (2 : ℚ) ^ (k - x.scale) * 2 ^ x.scale = 2 ^ k * 2 ^ (x.scale - k) := by
    rw [← pow_add, ← pow_add, hscale]
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hnat : x.rad + (2 ^ k - 1) ≤ (x.rad + 2 * (2 ^ k - 1)) / 2 ^ k * 2 ^ k := by
    have h := Nat.lt_div_mul_add (a := x.rad + 2 * (2 ^ k - 1)) hpos
    omega
  have hcast := Nat.cast_le (α := ℚ) |>.2 hnat
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hpos] at hcast
  push_cast at hcast
  rw [toRat_radius, toRat_radius, ← add_div]
  change _ ≤ (((x.rad + 2 * (1 <<< k - 1)) >>> k <<< (k - x.scale) : Nat) : ℚ) / 2 ^ (x.scale - k)
  rw [Nat.one_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    div_le_div_iff₀ (by positivity) (by positivity)]
  push_cast
  have hfactor : (0 : ℚ) ≤ 2 ^ (x.scale - k) := by positivity
  calc ((x.rad : ℚ) + (2 ^ k - 1)) * 2 ^ (x.scale - k)
      ≤ (((x.rad + 2 * (2 ^ k - 1)) / 2 ^ k : Nat) : ℚ) * 2 ^ k * 2 ^ (x.scale - k) :=
        mul_le_mul_of_nonneg_right hcast hfactor
    _ = (((x.rad + 2 * (2 ^ k - 1)) / 2 ^ k : Nat) : ℚ) * 2 ^ (k - x.scale) * 2 ^ x.scale := by
        linear_combination
          (-(((x.rad + 2 * (2 ^ k - 1)) / 2 ^ k : Nat) : ℚ)) * hpow

/-- `drop k` keeps every member. -/
theorem contains_drop {x : Ball} {v : K} (hv : x.Contains v) (k : Nat) :
    (x.drop k).Contains v := by
  unfold Contains at hv ⊢
  have hdown := Rat.cast_le (K := K) |>.2 (Dyad.dropDown_le x.mid k)
  have hmoved := Rat.cast_le (K := K) |>.2 (Dyad.sub_dropDown_le x.mid k)
  have hradius := Rat.cast_le (K := K) |>.2 (radius_drop_ge x k)
  rw [mid_drop]
  rw [abs_le] at hv ⊢
  have hscale : x.mid.scale = x.scale := rfl
  rw [hscale] at hmoved
  push_cast at hmoved hradius
  constructor <;> linarith [hv.1, hv.2]

/-- `round p` keeps every member. -/
theorem contains_round {x : Ball} {v : K} (hv : x.Contains v) (p : Nat) :
    (x.round p).Contains v :=
  contains_drop hv _

/-- `trim count` keeps every member. -/
theorem contains_trim {x : Ball} {v : K} (hv : x.Contains v) (count : Nat) :
    (x.trim count).Contains v :=
  contains_drop hv _

/--
The reciprocal on magnitudes: for `w` within `R / 2 ^ s` of `c / 2 ^ s` with `R < c`, the ball
between `2 ^ (s + p) / (c + R)` rounded down and `2 ^ (s + p) / (c - R)` rounded up, in units of
`2 ^ (-p)`, contains `1 / w`.
-/
private theorem inv_core {c R s : Nat} (p : Nat) (hR : R < c) {w : K}
    (hw : |w - (c : K) / 2 ^ s| ≤ (R : K) / 2 ^ s) :
    (Ball.mk
      (Nat.add (Nat.div (Nat.shiftLeft 1 (Nat.add s p)) (Nat.add c R))
        (Kernel.ceilDiv (Nat.shiftLeft 1 (Nat.add s p)) (Nat.sub c R)))
      0
      (Nat.sub (Kernel.ceilDiv (Nat.shiftLeft 1 (Nat.add s p)) (Nat.sub c R))
        (Nat.div (Nat.shiftLeft 1 (Nat.add s p)) (Nat.add c R)))
      (Nat.succ p)).Contains w⁻¹ := by
  have hshift : Nat.shiftLeft 1 (Nat.add s p) = 2 ^ (s + p) := Nat.one_shiftLeft _
  rw [hshift, contains_mk]
  generalize hL : Nat.div (2 ^ (s + p)) (Nat.add c R) = L
  generalize hU : Kernel.ceilDiv (2 ^ (s + p)) (Nat.sub c R) = U
  have hs : (0 : K) < 2 ^ s := by positivity
  have hp : (0 : K) < 2 ^ p := by positivity
  obtain ⟨hlo, hhi⟩ := abs_le.1 hw
  have hposN : 0 < c - R := Nat.sub_pos_of_lt hR
  have hcR : ((c - R : Nat) : K) = (c : K) - R := Nat.cast_sub hR.le
  have hposK : (0 : K) < (c : K) - R := by rw [← hcR]; exact_mod_cast hposN
  have hwlo : ((c : K) - R) / 2 ^ s ≤ w := by rw [sub_div]; simp_all
  have hwhi : w ≤ ((c : K) + R) / 2 ^ s := by rw [add_div]; linarith
  have hwpos : 0 < w := lt_of_lt_of_le (div_pos hposK hs) hwlo
  have hLn : L * (c + R) ≤ 2 ^ (s + p) := by rw [← hL]; exact Nat.div_mul_le_self _ _
  have hUn : 2 ^ (s + p) ≤ (c - R) * U := by rw [← hU]; exact le_mul_ceilDiv hposN
  have hLU : L ≤ U := by
    have h1 : L * (c + R) ≤ U * (c + R) :=
      le_trans hLn (le_trans hUn (by
        rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)))
    exact Nat.le_of_mul_le_mul_right h1 (by omega)
  have hpow : (2 : K) ^ (s + p) = 2 ^ p * 2 ^ s := by rw [pow_add, mul_comm]
  have hLK : (L : K) * ((c : K) + R) ≤ 2 ^ p * 2 ^ s := by
    have h := Nat.cast_le (α := K) |>.2 hLn
    push_cast at h
    rw [hpow] at h
    exact h
  have hUK : (2 : K) ^ p * 2 ^ s ≤ ((c : K) - R) * U := by
    have h := Nat.cast_le (α := K) |>.2 hUn
    rw [Nat.cast_mul, hcR] at h
    push_cast at h
    rw [hpow] at h
    exact h
  have hlower : (L : K) / 2 ^ p ≤ w⁻¹ := by
    rw [div_le_iff₀ hp, inv_mul_eq_div, le_div_iff₀ hwpos]
    have h1 : (L : K) * w ≤ L * (((c : K) + R) / 2 ^ s) :=
      mul_le_mul_of_nonneg_left hwhi (Nat.cast_nonneg L)
    have h2 : (L : K) * (((c : K) + R) / 2 ^ s) ≤ 2 ^ p := by
      rw [← mul_div_assoc, div_le_iff₀ hs]
      exact hLK
    exact le_trans h1 h2
  have hupper : w⁻¹ ≤ (U : K) / 2 ^ p := by
    rw [le_div_iff₀ hp, inv_mul_eq_div, div_le_iff₀ hwpos]
    have h1 : (U : K) * (((c : K) - R) / 2 ^ s) ≤ U * w :=
      mul_le_mul_of_nonneg_left hwlo (Nat.cast_nonneg U)
    have h2 : (2 : K) ^ p ≤ (U : K) * (((c : K) - R) / 2 ^ s) := by
      rw [← mul_div_assoc, le_div_iff₀ hs, mul_comm (U : K)]
      exact hUK
    exact le_trans h2 h1
  have hcast : ((Nat.sub U L : Nat) : K) = (U : K) - L := Nat.cast_sub hLU
  have hsum : ((Nat.add L U : Nat) : K) = (L : K) + U := Nat.cast_add L U
  have hsucc : (2 : K) ^ Nat.succ p = 2 ^ p * 2 := pow_succ 2 p
  rw [hcast, hsum, hsucc, Nat.cast_zero, sub_zero, abs_le]
  have hmid : ((L : K) + U) / (2 ^ p * 2) = (L / 2 ^ p + U / 2 ^ p) / 2 := by
    field_simp
  have hrad : ((U : K) - L) / (2 ^ p * 2) = (U / 2 ^ p - L / 2 ^ p) / 2 := by
    field_simp
  rw [hmid, hrad]
  constructor <;> linarith

/-- `apart` holds exactly when zero is not a member. -/
theorem apart_iff (x : Ball) : x.apart = true ↔ ¬ x.Contains (0 : K) := by
  obtain ⟨P, M, R, s⟩ := x
  have hs : (0 : K) < 2 ^ s := by positivity
  rw [contains_mk, zero_sub, abs_neg, abs_div, abs_of_pos hs, div_le_div_iff_of_pos_right hs]
  have happ : (Ball.mk P M R s).apart = true ↔ R < (P - M) + (M - P) := by
    change Nat.ble (R + 1) ((P - M) + (M - P)) = true ↔ _
    rw [Nat.ble_eq]
    exact Nat.succ_le_iff
  rw [happ, not_le]
  rcases Nat.le_total M P with h | h
  · have hc : |(P : K) - M| = ((P - M + (M - P) : Nat) : K) := by
      rw [show P - M + (M - P) = P - M by omega, Nat.cast_sub h]
      exact abs_of_nonneg (sub_nonneg.2 (Nat.cast_le.2 h))
    rw [hc, Nat.cast_lt]
  · have hc : |(P : K) - M| = ((P - M + (M - P) : Nat) : K) := by
      rw [show P - M + (M - P) = M - P by omega, Nat.cast_sub h, abs_sub_comm]
      exact abs_of_nonneg (sub_nonneg.2 (Nat.cast_le.2 h))
    rw [hc, Nat.cast_lt]

/-- The reciprocal of a member of a ball that is apart from zero is a member of `inv x p`. -/
theorem contains_inv {x : Ball} (hx : x.apart = true) (p : Nat) {v : K} (hv : x.Contains v) :
    (x.inv p).Contains v⁻¹ := by
  obtain ⟨P, M, R, s⟩ := x
  rw [contains_mk] at hv
  have hR : R < Nat.add (Nat.sub P M) (Nat.sub M P) :=
    Nat.lt_of_succ_le (Nat.le_of_ble_eq_true hx)
  unfold inv
  dsimp only
  generalize hc : Nat.add (Nat.sub P M) (Nat.sub M P) = c at hR ⊢
  cases hble : Nat.ble M P
  · have hPM : P ≤ M := Nat.le_of_lt (Nat.lt_of_not_le (fun h => by
      rw [Nat.ble_eq_true_of_le h] at hble; exact Bool.noConfusion hble))
    have hcK : (c : K) = (M : K) - P := by
      rw [← hc]
      change ((P - M + (M - P) : Nat) : K) = _
      rw [show P - M + (M - P) = M - P by omega, Nat.cast_sub hPM]
    have hw : |(-v) - (c : K) / 2 ^ s| ≤ (R : K) / 2 ^ s := by
      rw [hcK, ← abs_neg]
      have : -(-v - ((M : K) - P) / 2 ^ s) = v - ((P : K) - M) / 2 ^ s := by ring
      rw [this]
      exact hv
    have h := contains_neg (inv_core p hR hw)
    rw [inv_neg, neg_neg] at h
    exact h
  · have hMP : M ≤ P := Nat.le_of_ble_eq_true hble
    have hcK : (c : K) = (P : K) - M := by
      rw [← hc]
      change ((P - M + (M - P) : Nat) : K) = _
      rw [show P - M + (M - P) = P - M by omega, Nat.cast_sub hMP]
    rw [← hcK] at hv
    exact inv_core p hR hv

/--
The quotient of a member of `x` by a member of a ball `y` that is apart from zero is a member of
`div x y p`.
-/
theorem contains_div {x y : Ball} (hy : y.apart = true) (p : Nat) {u v : K}
    (hu : x.Contains u) (hv : y.Contains v) : (x.div y p).Contains (u / v) := by
  rw [div_eq_mul_inv]
  exact contains_mul hu (contains_inv hy p hv)

/-- A passed `le` holds for all members: each member of `x` is at most each member of `y`. -/
theorem le_sound {x y : Ball} (h : x.le y = true) {v w : K} (hv : x.Contains v)
    (hw : y.Contains w) : v ≤ w :=
  le_trans ((contains_iff x v).1 hv).2
    (le_trans (Dyad.le_cast h) ((contains_iff y w).1 hw).1)

/-- A passed `lt` holds for all members: each member of `x` is less than each member of `y`. -/
theorem lt_sound {x y : Ball} (h : x.lt y = true) {v w : K} (hv : x.Contains v)
    (hw : y.Contains w) : v < w :=
  lt_of_le_of_lt ((contains_iff x v).1 hv).2
    (lt_of_lt_of_le (Dyad.lt_cast h) ((contains_iff y w).1 hw).1)

end FloatLib.Numerics.Kernel.Ball
