/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Exact
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Literal
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Value

/-!
# `pown` on encodings

IEEE 754-2019 §9.2 `pown` raises a value to an integer power with one rounding to nearest
even. The reference `Model.pown` forms the power of the exact rational value and rounds its
reduced numerator and denominator.

`pown fmt n a` computes the encoding of the result from the word `a`: a finite nonzero word is
decoded by `KernelPath.decode`, the power of its significand is a natural number, the power of
two of its exponent goes to the numerator or to the denominator, and `ofRatio` rounds the
quotient, or its reciprocal for a negative exponent, with the sign of an odd power of a
negative value (`powRatio`). A zero, an infinity, a NaN and the exponent zero go to the
reference. `pown_eq_spec` proves `pown` equal to the encoding of `Model.pown`, for every format
descriptor, every value and every integer exponent.

`Value.pown` is the operation on stored values, with `Value.pown_eq_lift` and the rule
`Value.toNat_pown`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

/--
Encoding of the `k`-th power of the dyadic `d`, or of its reciprocal, rounded to nearest even
(`powRatio_eq`): the quotient of `significand ^ k` and a power of two, with the sign of an odd
power of a negative value.
-/
def powRatio (fmt : FloatFormat) (d : Numerics.Dyadic) (k : Nat) (reciprocal : Bool) : Nat :=
  (fun exponent sign =>
    (fun num den =>
      Bool.casesOn (motive := fun _ => Nat) reciprocal
        (ofRatio fmt .nearest sign num den) (ofRatio fmt .nearest sign den num))
      (Nat.shiftLeft (Nat.pow d.significand k) (Kernel.Z.toNat exponent))
      (Nat.shiftLeft 1 (Kernel.Z.toNat (Kernel.Z.neg exponent))))
    (Kernel.Z.mul d.exponent (Int.ofNat k))
    (signNat (Bool.and d.negative (Nat.beq (Nat.mod k 2) 1)))

/--
Encoding of the value that `a` encodes raised to the power `n`, rounded to nearest even
(`pown_eq_spec`).
-/
def pown (fmt : FloatFormat) (n : Int) (a : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat)
    (Bool.and (Nat.beq (finiteCode fmt a) 1) (Bool.not (Nat.beq (zeroCode fmt a) 1)))
    ((Model.pown (Model.ofNatBits a : Model fmt) n).toNatBits)
    (Int.casesOn (motive := fun _ => Nat) n
      (fun k =>
        Bool.casesOn (motive := fun _ => Nat) (Nat.beq k 0)
          (powRatio fmt (decode fmt a) k false)
          ((Model.pown (Model.ofNatBits a : Model fmt) n).toNatBits))
      (fun k => powRatio fmt (decode fmt a) (Nat.succ k) true))

/--
`ofRatio` to nearest even with a sign computes the reference rounding of the reduced fraction
of the quotient, for every format descriptor and every nonzero denominator.
-/
theorem ofRatio_eq_roundRat (fmt : FloatFormat) (negative : Bool) (r : ℚ) (num den : Nat)
    (hden : den ≠ 0) (hr : r = (num : ℚ) / (den : ℚ)) :
    ofRatio fmt .nearest (signNat negative) num den =
      (Model.roundRat fmt negative r.num.natAbs r.den).toNatBits := by
  obtain ⟨g, hg, hnum, hdenEq, -⟩ := exists_common_factor r num den hden hr
  rw [ofRatio_eq]
  conv_lhs => rw [hnum, hdenEq]
  rw [roundRat_mul_right fmt negative _ _ g hg]

/-- The reference rounding of a rational reads its sign and the fraction of its magnitude. -/
theorem roundAlgebraicRat_eq_abs (fmt : FloatFormat) (v : ℚ) :
    Model.roundAlgebraicRat fmt v =
      Model.roundRat fmt (decide (v < 0)) |v|.num.natAbs |v|.den := by
  unfold Model.roundAlgebraicRat
  rcases le_or_gt 0 v with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, Rat.neg_num, Rat.neg_den, Int.natAbs_neg]

/-- The magnitude of the rational value of a dyadic. -/
theorem abs_toRat (d : Numerics.Dyadic) :
    |d.toRat| = (d.significand : ℚ) * (2 : ℚ) ^ d.exponent := by
  unfold Numerics.Dyadic.toRat Numerics.Dyadic.signedSignificand
  rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℚ) < 2) _)]
  congr 1
  cases d.negative <;> simp

/-- A power of a nonzero dyadic is negative exactly for an odd power of a negative dyadic. -/
theorem toRat_zpow_neg (d : Numerics.Dyadic) (hd : d.significand ≠ 0) (n : Int) :
    decide (d.toRat ^ n < 0) = (d.negative && Nat.beq (n.natAbs % 2) 1) := by
  have hm : (0 : ℚ) < (d.significand : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hd
  have htwo : (0 : ℚ) < (2 : ℚ) ^ d.exponent := zpow_pos (by norm_num) _
  rw [Bool.eq_iff_iff, decide_eq_true_eq, Bool.and_eq_true, Nat.beq_eq]
  unfold Numerics.Dyadic.toRat Numerics.Dyadic.signedSignificand
  cases hnegative : d.negative
  · have hpos : (0 : ℚ) < Rat.ofInt (Int.ofNat d.significand) * (2 : ℚ) ^ d.exponent := by
      have hcast : (Rat.ofInt (Int.ofNat d.significand) : ℚ) = (d.significand : ℚ) := by simp
      rw [hcast]
      exact mul_pos hm htwo
    have hpower := zpow_pos hpos n
    simp only [Bool.false_eq_true, ite_false, false_and, iff_false, not_lt]
    exact hpower.le
  · have hneg : Rat.ofInt (-Int.ofNat d.significand) * (2 : ℚ) ^ d.exponent < 0 := by
      have hcast : (Rat.ofInt (-Int.ofNat d.significand) : ℚ) = -(d.significand : ℚ) := by simp
      rw [hcast]
      exact mul_neg_of_neg_of_pos (neg_neg_of_pos hm) htwo
    simp only [ite_true, true_and]
    rcases Int.even_or_odd n with heven | hodd
    · have hmod : n.natAbs % 2 = 0 := by
        have := Int.even_iff.1 heven
        omega
      have hpower := heven.zpow_nonneg (Rat.ofInt (-Int.ofNat d.significand) * (2 : ℚ) ^ d.exponent)
      rw [hmod]
      constructor
      · intro h
        exact absurd h (not_lt.mpr hpower)
      · intro h
        exact absurd h (by decide)
    · have hmod : n.natAbs % 2 = 1 := by
        have := Int.odd_iff.1 hodd
        omega
      rw [hmod]
      exact ⟨fun _ => rfl, fun _ => hodd.zpow_neg_iff.2 hneg⟩

/--
`powRatio` computes the encoding of the reference rounding of a power of a nonzero dyadic, or
of its reciprocal, for every format descriptor and every exponent.
-/
theorem powRatio_eq (fmt : FloatFormat) (d : Numerics.Dyadic) (hd : d.significand ≠ 0) (k : Nat)
    (reciprocal : Bool) :
    powRatio fmt d k reciprocal =
      (Model.roundAlgebraicRat fmt
        (d.toRat ^ (if reciprocal then -(k : Int) else (k : Int)))).toNatBits := by
  have hpow : |d.toRat| ^ k =
      ((d.significand ^ k <<< (d.exponent * (k : Int)).toNat : Nat) : ℚ) /
        ((1 <<< (-(d.exponent * (k : Int))).toNat : Nat) : ℚ) := by
    rw [abs_toRat, mul_pow, ← zpow_natCast ((2 : ℚ) ^ d.exponent) k, ← zpow_mul]
    simp only [Nat.shiftLeft_eq, Nat.one_mul]
    push_cast
    rw [mul_div_assoc]
    congr 1
    rw [← zpow_natCast (2 : ℚ) (d.exponent * (k : Int)).toNat,
      ← zpow_natCast (2 : ℚ) (-(d.exponent * (k : Int))).toNat, ← zpow_sub₀ (by norm_num)]
    congr 1
    omega
  have hN : d.significand ^ k <<< (d.exponent * (k : Int)).toNat ≠ 0 := by
    simp [Nat.shiftLeft_eq, hd]
  have hD : 1 <<< (-(d.exponent * (k : Int))).toNat ≠ 0 := by
    simp [Nat.shiftLeft_eq]
  have hsign : ∀ n : Int, n.natAbs = k →
      decide (d.toRat ^ n < 0) = (d.negative && Nat.beq (k % 2) 1) := by
    intro n hn
    rw [toRat_zpow_neg d hd n, hn]
  unfold powRatio
  simp only [Kernel.Z.mul_eq, Kernel.Z.toNat_eq, Kernel.Z.neg_eq]
  cases reciprocal
  · change ofRatio fmt .nearest (signNat (d.negative && Nat.beq (k % 2) 1))
        (d.significand ^ k <<< (d.exponent * (k : Int)).toNat)
        (1 <<< (-(d.exponent * (k : Int))).toNat) = _
    rw [roundAlgebraicRat_eq_abs,
      ofRatio_eq_roundRat fmt _ (|d.toRat ^ (k : Int)|) _ _ hD
        (by rw [abs_zpow, zpow_natCast, hpow]),
      ← hsign (k : Int) (Int.natAbs_natCast k)]
    rfl
  · change ofRatio fmt .nearest (signNat (d.negative && Nat.beq (k % 2) 1))
        (1 <<< (-(d.exponent * (k : Int))).toNat)
        (d.significand ^ k <<< (d.exponent * (k : Int)).toNat) = _
    rw [roundAlgebraicRat_eq_abs,
      ofRatio_eq_roundRat fmt _ (|d.toRat ^ (-(k : Int))|) _ _ hN
        (by rw [abs_zpow, zpow_neg, zpow_natCast, hpow, inv_div]),
      ← hsign (-(k : Int)) (by simp)]
    rfl

/--
`pown` computes the encoding of `Model.pown x n`, for every format descriptor, every value and
every integer exponent.
-/
theorem pown_eq_spec {fmt : FloatFormat} (n : Int) (x : Model fmt) :
    pown fmt n x.toNatBits = (Model.pown x n).toNatBits := by
  unfold pown
  rw [Model.ofNatBits_toNatBits, finiteCode_eq, zeroCode_eq]
  cases hfinite : Model.isFinite x
  · rfl
  cases hzero : Model.isZero x
  swap
  · rfl
  have hdecode := toDyadic?_eq_decode x hfinite
  have hsignificand := Model.significand_ne_zero_of_toDyadic?_some_of_isZero_eq_false hdecode hzero
  have hnan := Model.isNaN_eq_false_of_isFinite_eq_true x hfinite
  have hspec : ∀ m : Int, m ≠ 0 →
      Model.pown x m = Model.roundAlgebraicRat fmt ((decode fmt x.toNatBits).toRat ^ m) := by
    intro m hm
    unfold Model.pown
    rw [Model.isSignaling_eq_false_of_isNaN_eq_false x hnan,
      (Model.chooseNaN1_eq_none_iff x).mpr hnan,
      hzero, Model.isInfinite_eq_false_of_isFinite_eq_true x hfinite]
    simp only [Bool.false_eq_true, ↓reduceIte, hm, Model.toRat?, hdecode, Option.map_some]
  rcases n with k | k
  · rcases k with _ | k
    · rfl
    · change powRatio fmt (decode fmt x.toNatBits) (k + 1) false = _
      rw [powRatio_eq fmt _ hsignificand, hspec _ (by simp only [Int.ofNat_eq_natCast]; omega)]
      rfl
  · change powRatio fmt (decode fmt x.toNatBits) (k + 1) true = _
    rw [powRatio_eq fmt _ hsignificand, hspec _ (by simp only [Int.negSucc_eq]; omega)]
    rfl

namespace Value

universe u

variable {F : Type u} [EncodedFormat F] {format : FloatFormat} [view : NatView F format]

/-- Kernel `pown` of a stored value: the value raised to the power `n`, rounded to nearest. -/
def pown (n : Int) (x : FloatLib.Floats.ExecFloat F) : FloatLib.Floats.ExecFloat F :=
  unary (KernelPath.pown format n) (fun x => Model.pown x n) (pown_eq_spec n) x

/-- The kernel `pown` is the model operation carried through the conversions. -/
theorem pown_eq_lift (n : Int) (x : FloatLib.Floats.ExecFloat F) :
    pown n x = NatView.liftUnary (fun x => Model.pown x n) x :=
  unary_eq _ _ _ x

/-- The encoding of a power is the flat operation on the encoding. -/
@[kernel_optimize] theorem toNat_pown (n : Int) (x : FloatLib.Floats.ExecFloat F) :
    toNat (pown n x) = KernelPath.pown format n (toNat x) :=
  toNat_unary _ _ _ x

end Value

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
