/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.Signed
public import FloatLib.Numerics.Kernel.ZProof

/-!
# `Signed` computes in the integers

Every operation of `FloatLib.Numerics.Kernel.Signed` is the integer operation on the values
`toInt`, for all pairs, normal or not.

* `toInt_eq`: `x.toInt = x.plus - x.minus`; `toInt_ofInt`, `ofInt_toInt`: `ofInt` is the normal pair
  of an integer.
* `toInt_add`, `toInt_sub`, `toInt_neg`, `toInt_mul`, `toInt_pow`, `toInt_shiftLeft`,
  `natAbs_eq`, `toInt_norm`, `toInt_min`, `toInt_max`.
* `le_iff`, `lt_iff`, `beq_iff`, `isNeg_iff`: the Boolean comparisons decide the order of the
  integers.
* `toInt_floorDiv`, `toInt_ceilDiv`, `toInt_floorShift`, `toInt_ceilShift`, `mod_eq`: rounded
  division is `Int` division, which rounds down, and its mirror image.
* `normal_ofInt`, `normal_norm`, `normal_add`, `normal_sub`, `normal_mul` and their siblings:
  which results are normal.

`FloatLib.Numerics.Kernel.Rules` states the same facts as rewrite rules from `Int` expressions
to `Signed` ones.
-/

@[expose] public section

namespace FloatLib.Numerics.Kernel.Signed

/-- Two pairs with the same parts are equal. -/
@[ext] theorem ext {x y : Signed} (hplus : x.plus = y.plus) (hminus : x.minus = y.minus) : x =
    y := by
  cases x
  cases y
  simp_all

/-- Two pairs are equal exactly when they have the same parts. -/
add_decl_doc FloatLib.Numerics.Kernel.Signed.ext_iff

/-- The integer of a pair is the difference of its parts. -/
theorem toInt_eq (x : Signed) : x.toInt = (x.plus : Int) - x.minus :=
  Z.subNat_eq x.plus x.minus

/-- `ofInt z` stands for `z`. -/
@[simp] theorem toInt_ofInt (z : Int) : (ofInt z).toInt = z := by
  rw [toInt_eq]
  cases z with
  | ofNat n => simp [ofInt]
  | negSucc n =>
    change ((0 : Nat) : Int) - ((n + 1 : Nat) : Int) = Int.negSucc n
    rw [Int.negSucc_eq]
    omega

/-- `ofNat n` stands for `n`. -/
@[simp] theorem toInt_ofNat (n : Nat) : (ofNat n).toInt = n := by
  simp [toInt_eq, ofNat]

/-- Normalizing keeps the integer. -/
@[simp] theorem toInt_norm (x : Signed) : x.norm.toInt = x.toInt := by
  simp only [toInt_eq, norm]
  change ((x.plus - x.minus : Nat) : Int) - ((x.minus - x.plus : Nat) : Int) = _
  omega

/-- The pair of the integer of a pair is its normal pair. -/
theorem ofInt_toInt (x : Signed) : ofInt x.toInt = x.norm := by
  obtain ⟨p, n⟩ := x
  rw [toInt_eq]
  rcases le_total n p with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    have : ((n + k : Nat) : Int) - (n : Int) = Int.ofNat k := by
      simp only [Int.ofNat_eq_natCast]
      omega
    simp only [this]
    apply ext <;> simp [ofInt, norm]
  · rcases Nat.lt_or_ge p n with hlt | hge
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
      have : ((p : Nat) : Int) - ((p + k + 1 : Nat) : Int) = Int.negSucc k := by
        rw [Int.negSucc_eq]
        omega
      simp only [this]
      apply ext <;> simp only [ofInt, Nat.succ_eq_add_one, norm, Nat.sub_eq] <;> omega
    · have hpn : p = n := le_antisymm h hge
      subst hpn
      have : ((p : Nat) : Int) - (p : Int) = Int.ofNat 0 := by simp
      simp only [this]
      apply ext <;> simp [ofInt, norm]

/-- `add` is addition of integers. -/
@[simp] theorem toInt_add (x y : Signed) : (x.add y).toInt = x.toInt + y.toInt := by
  simp only [toInt_eq, add]
  change ((x.plus + y.plus - (x.minus + y.minus) : Nat) : Int) - ((x.minus + y.minus - (x.plus +
    y.plus) : Nat) : Int) = _
  omega

/-- `sub` is subtraction of integers. -/
@[simp] theorem toInt_sub (x y : Signed) : (x.sub y).toInt = x.toInt - y.toInt := by
  simp only [toInt_eq, sub]
  change ((x.plus + y.minus - (x.minus + y.plus) : Nat) : Int) - ((x.minus + y.plus - (x.plus +
    y.minus) : Nat) : Int) = _
  omega

/-- `neg` is negation of integers. -/
@[simp] theorem toInt_neg (x : Signed) : x.neg.toInt = -x.toInt := by
  simp only [toInt_eq, neg]
  omega

/-- `mul` is multiplication of integers. -/
@[simp] theorem toInt_mul (x y : Signed) : (x.mul y).toInt = x.toInt * y.toInt := by
  simp only [toInt_eq, mul]
  change ((x.plus * y.plus + x.minus * y.minus : Nat) : Int) - ((x.plus * y.minus + x.minus *
    y.plus : Nat) : Int) = _
  push_cast
  ring

/-- `natAbs` is the absolute value of the integer. -/
theorem natAbs_eq (x : Signed) : x.natAbs = x.toInt.natAbs := by
  rw [toInt_eq]
  change x.plus - x.minus + (x.minus - x.plus) = _
  omega

/-- `shiftLeft` multiplies the integer by `2 ^ k`. -/
@[simp] theorem toInt_shiftLeft (x : Signed) (k : Nat) :
    (x.shiftLeft k).toInt = x.toInt * 2 ^ k := by
  simp only [toInt_eq, shiftLeft]
  change ((x.plus <<< k : Nat) : Int) - ((x.minus <<< k : Nat) : Int) = _
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  push_cast
  ring

/-- `le` decides `≤` on the integers. -/
theorem le_iff (x y : Signed) : x.le y = true ↔ x.toInt ≤ y.toInt := by
  simp only [toInt_eq, le]
  change Nat.ble (x.plus + y.minus) (y.plus + x.minus) = true ↔ _
  rw [Nat.ble_eq]
  omega

/-- `lt` decides `<` on the integers. -/
theorem lt_iff (x y : Signed) : x.lt y = true ↔ x.toInt < y.toInt := by
  simp only [toInt_eq, lt]
  change Nat.ble (x.plus + y.minus + 1) (y.plus + x.minus) = true ↔ _
  rw [Nat.ble_eq]
  omega

/-- `beq` decides equality of the integers. -/
theorem beq_iff (x y : Signed) : x.beq y = true ↔ x.toInt = y.toInt := by
  simp only [toInt_eq, beq]
  change Nat.beq (x.plus + y.minus) (y.plus + x.minus) = true ↔ _
  rw [Nat.beq_eq]
  omega

/-- `isNeg` decides whether the integer is negative. -/
theorem isNeg_iff (x : Signed) : x.isNeg = true ↔ x.toInt < 0 := by
  simp only [toInt_eq, isNeg]
  change Nat.ble (x.plus + 1) x.minus = true ↔ _
  rw [Nat.ble_eq]
  omega

/-- `pow` is the power of the integer. -/
@[simp] theorem toInt_pow (x : Signed) (n : Nat) : (x.pow n).toInt = x.toInt ^ n := by
  obtain ⟨p, q⟩ := x
  simp only [toInt_eq, pow, natAbs]
  change ((1 - n % 2 * (1 - (1 - (q - p))))* (p - q + (q - p)) ^ n : Nat) -
      ((n % 2 * (1 - (1 - (q - p))) * (p - q + (q - p)) ^ n : Nat) : Int) = ((p : Int) - q) ^ n
  rcases Nat.lt_or_ge p q with hlt | hge
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have h1 : 1 - (1 - (p + d + 1 - p)) = 1 := by omega
    have h2 : p - (p + d + 1) + (p + d + 1 - p) = d + 1 := by omega
    have h3 : ((p : Int) - ((p + d + 1 : Nat) : Int)) = -((d + 1 : Nat) : Int) := by
      push_cast
      omega
    rw [h1, h2, h3, Nat.mul_one]
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · rw [hn, Even.neg_pow (Nat.even_iff.2 hn)]
      simp
    · rw [hn, Odd.neg_pow (Nat.odd_iff.2 hn)]
      simp
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hge
    have h1 : 1 - (1 - (q - (q + d))) = 0 := by omega
    have h2 : q + d - q + (q - (q + d)) = d := by omega
    have h3 : (((q + d : Nat) : Int) - (q : Int)) = (d : Int) := by
      push_cast
      omega
    rw [h1, h2, h3]
    simp

/-- `floorDiv` is `Int` division by a natural number, which rounds down. -/
@[simp] theorem toInt_floorDiv (x : Signed) (d : Nat) :
    (x.floorDiv d).toInt = x.toInt / (d : Int) := by
  obtain ⟨p, q⟩ := x
  simp only [toInt_eq, floorDiv]
  change (((p - q) / d : Nat) : Int) - ((Kernel.ceilDiv (q - p) d : Nat) : Int) = _
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · change (((p - q) / 0 : Nat) : Int) - (((q - p + (0 - 1)) / 0 : Nat) : Int) = _
    simp
  rcases Nat.lt_or_ge p q with hlt | hge
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have h1 : p - (p + e + 1) = 0 := by omega
    have h2 : p + e + 1 - p = e + 1 := by omega
    have h3 : ((p : Int) - ((p + e + 1 : Nat) : Int)) = -((e + 1 : Nat) : Int) := by
      push_cast
      omega
    rw [h1, h2, h3, neg_ediv_natCast hd]
    simp
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hge
    have h1 : q + e - q = e := by omega
    have h2 : q - (q + e) = 0 := by omega
    have h3 : (((q + e : Nat) : Int) - (q : Int)) = (e : Int) := by
      push_cast
      omega
    have h4 : Kernel.ceilDiv 0 d = 0 := by
      rw [ceilDiv_eq_ite hd]
      simp
    rw [h1, h2, h3, h4]
    simp

/-- Rounding a quotient up is rounding the quotient of the negation down. -/
theorem ceilDiv_eq (x : Signed) (d : Nat) : x.ceilDiv d = (x.neg.floorDiv d).neg := rfl

/-- `ceilDiv` is the quotient rounded up: the negated `Int` quotient of the negation. -/
@[simp] theorem toInt_ceilDiv (x : Signed) (d : Nat) :
    (x.ceilDiv d).toInt = -((-x.toInt) / (d : Int)) := by
  rw [ceilDiv_eq, toInt_neg, toInt_floorDiv, toInt_neg]

/-- A shift to the right, rounded down, is division by `2 ^ k` rounded down. -/
theorem floorShift_eq (x : Signed) (k : Nat) : x.floorShift k = x.floorDiv (2 ^ k) := by
  apply ext
  · change (x.plus - x.minus) >>> k = (x.plus - x.minus) / 2 ^ k
    exact Nat.shiftRight_eq_div_pow _ _
  · exact Kernel.ceilShift_eq _ _

/-- A shift to the right, rounded up, is division by `2 ^ k` rounded up. -/
theorem ceilShift_eq (x : Signed) (k : Nat) : x.ceilShift k = x.ceilDiv (2 ^ k) := by
  apply ext
  · exact Kernel.ceilShift_eq _ _
  · change (x.minus - x.plus) >>> k = (x.minus - x.plus) / 2 ^ k
    exact Nat.shiftRight_eq_div_pow _ _

/-- `floorShift` is the shift of integers to the right, which rounds down. -/
@[simp] theorem toInt_floorShift (x : Signed) (k : Nat) :
    (x.floorShift k).toInt = x.toInt >>> k := by
  rw [floorShift_eq, toInt_floorDiv, Int.shiftRight_eq_div_pow]

/-- `ceilShift` is the quotient by `2 ^ k` rounded up. -/
@[simp] theorem toInt_ceilShift (x : Signed) (k : Nat) :
    (x.ceilShift k).toInt = -((-x.toInt) >>> k) := by
  rw [ceilShift_eq, toInt_ceilDiv, Int.shiftRight_eq_div_pow]

/-- `mod` is the remainder of the integer modulo a positive natural number. -/
theorem mod_eq (x : Signed) {d : Nat} (hd : 0 < d) : ((x.mod d : Nat) : Int) = x.toInt % (d :
    Int) := by
  obtain ⟨p, q⟩ := x
  rw [toInt_eq]
  change (((p % d + (d - q % d)) % d : Nat) : Int) = ((p : Int) - q) % d
  have hq : q % d < d := Nat.mod_lt q hd
  rw [Int.natCast_mod, Nat.cast_add, Nat.cast_sub hq.le, Int.natCast_mod, Int.natCast_mod]
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
  have hp := Int.mul_ediv_add_emod (p : Int) d
  have hq' := Int.mul_ediv_add_emod (q : Int) d
  have : (p : Int) % d + (d - (q : Int) % d) - (p - q) = d * (1 - p / d + q / d) := by
    linarith
  rw [this]
  exact Int.mul_emod_right _ _

/-- `min` is the smaller of the two integers. -/
@[simp] theorem toInt_min (x y : Signed) : (x.min y).toInt = Min.min x.toInt y.toInt := by
  simp only [toInt_eq, min, minNat_eq, maxNat_eq]
  change ((Min.min (x.plus - x.minus) (y.plus - y.minus) : Nat) : Int) -
    ((Max.max (x.minus - x.plus) (y.minus - y.plus) : Nat) : Int) = _
  omega

/-- `max` is the larger of the two integers. -/
@[simp] theorem toInt_max (x y : Signed) : (x.max y).toInt = Max.max x.toInt y.toInt := by
  simp only [toInt_eq, max, minNat_eq, maxNat_eq]
  change ((Max.max (x.plus - x.minus) (y.plus - y.minus) : Nat) : Int) -
    ((Min.min (x.minus - x.plus) (y.minus - y.plus) : Nat) : Int) = _
  omega

/-! ### Normal pairs -/

/-- The pair of an integer is normal. -/
theorem normal_ofInt (z : Int) : (ofInt z).Normal := by
  cases z with
  | ofNat n => exact Or.inr rfl
  | negSucc n => exact Or.inl rfl

/-- The pair of a natural number is normal. -/
theorem normal_ofNat (n : Nat) : (ofNat n).Normal := Or.inr rfl

/-- A pair of two truncated differences `a - b` and `b - a` is normal. -/
theorem normal_mk_sub (a b : Nat) : Normal ⟨a - b, b - a⟩ := by
  change a - b = 0 ∨ b - a = 0
  omega

/-- `norm` returns a normal pair. -/
theorem normal_norm (x : Signed) : x.norm.Normal := normal_mk_sub _ _

/-- `add` returns a normal pair. -/
theorem normal_add (x y : Signed) : (x.add y).Normal := normal_mk_sub _ _

/-- `sub` returns a normal pair. -/
theorem normal_sub (x y : Signed) : (x.sub y).Normal := normal_mk_sub _ _

/-- The negation of a normal pair is normal. -/
theorem normal_neg {x : Signed} (hx : x.Normal) : x.neg.Normal := hx.symm

/-- The product of two normal pairs is normal. -/
theorem normal_mul {x y : Signed} (hx : x.Normal) (hy : y.Normal) : (x.mul y).Normal := by
  obtain ⟨p, q⟩ := x
  obtain ⟨r, s⟩ := y
  change p * r + q * s = 0 ∨ p * s + q * r = 0
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> simp_all

/-- A normal pair is its own normal pair. -/
theorem norm_of_normal {x : Signed} (hx : x.Normal) : x.norm = x := by
  obtain ⟨p, q⟩ := x
  rcases hx with hx | hx <;> simp_all [norm]

/-- Two normal pairs of the same integer are equal. -/
theorem eq_of_toInt_eq {x y : Signed} (hx : x.Normal) (hy : y.Normal)
    (h : x.toInt = y.toInt) : x = y := by
  rw [← norm_of_normal hx, ← norm_of_normal hy, ← ofInt_toInt, ← ofInt_toInt, h]

end FloatLib.Numerics.Kernel.Signed
