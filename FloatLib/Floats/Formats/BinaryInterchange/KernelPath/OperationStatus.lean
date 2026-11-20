/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Add
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Fma
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Mul
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Status
public import FloatLib.Floats.Formats.BinaryInterchange.Status.Proof

import Mathlib.Tactic.Positivity

/-!
# Kernel path: the IEEE status of addition, subtraction, multiplication and fused multiply-add

`addStatus`, `subStatus`, `mulStatus` and `fmaStatus` are the status numbers of the four
operations whose exact result is a dyadic: the five exception flags and the ternary value of
`Model.add x y (mode := mode) (status := true)` and its siblings, computed on the encodings of the
operands. For finite operands the exact result is formed without rounding and passed to
`roundStatus` with the delivered word. For an operand that is not finite the only flag is invalid
operation, raised by a signaling NaN or by an invalid combination of infinities and zeros.

`addStatus_eq`, `subStatus_eq`, `mulStatus_eq` and `fmaStatus_eq` prove that the decoded flags and
ternary value are the reference ones, for every format descriptor, every rounding direction and
all operands.

Each status number is a function of the delivered word (`addStatusWith`, `subStatusWith`,
`mulStatusWith`, `fmaStatusWith`), taken at the operation on the encodings. A statement about
the value and the flags of one operation gives that function the word it has already computed.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

/-- The status number of an exactly delivered result: invalid when `invalid` is not zero. -/
def invalidStatus (invalid : Nat) : Nat :=
  Nat.add (Nat.sub 1 (Nat.sub 1 invalid)) 32

/--
The ternary code of the delivered word `w` against the exact infinity of the sign `sign`: `1`
(equal) when `w` is that infinity, and otherwise `2` (greater) for a negative and `0` (less)
for a positive sign, as `Model.exactInfinityTernary`.
-/
def infinityTernary (fmt : FloatFormat) (sign w : Nat) : Nat :=
  (fun sw uw =>
    (fun exact => Nat.add exact (Nat.mul (Nat.sub 1 exact) (Nat.mul 2 sign)))
      (Nat.mul (infFlag fmt uw) (Nat.sub 1 (Nat.xor sw sign))))
    (Nat.shiftRight w (signPos fmt)) (Nat.land w (magnitudeMask fmt))

/-- One when the sum of the signed magnitudes `±X` and `±Y` is negative. -/
def sumSign (sa X sb Y : Nat) : Nat :=
  gtFlag (Nat.add (Nat.mul sa X) (Nat.mul sb Y))
    (Nat.add (Nat.mul (Nat.sub 1 sa) X) (Nat.mul (Nat.sub 1 sb) Y))

/-- The magnitude of the sum of the signed magnitudes `±X` and `±Y`. -/
def sumMagnitude (sa X sb Y : Nat) : Nat :=
  (fun positive negative => Nat.add (Nat.sub positive negative) (Nat.sub negative positive))
    (Nat.add (Nat.mul (Nat.sub 1 sa) X) (Nat.mul (Nat.sub 1 sb) Y))
    (Nat.add (Nat.mul sa X) (Nat.mul sb Y))

/--
The status number of the sum of the values encoded by `a` and `b`, rounded in the direction
`mode`, when `w` is the word of the rounded sum. `addStatus` is this number at
`add fmt mode a b`. With the word as an argument, a statement about the value and the flags of
one sum computes the sum once.
-/
def addStatusWith (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b w : Nat) : Nat :=
  (fun sa sb ua ub =>
    Bool.casesOn (motive := fun _ => Nat)
      (Nat.beq (Nat.add (nonFinite fmt sa ua) (nonFinite fmt sb ub)) 0)
      ((fun infA infB nanA nanB =>
          invalidStatus
            (Nat.add
              (Nat.add (Nat.mul nanA (signalingFlag fmt a)) (Nat.mul nanB (signalingFlag fmt b)))
              (Nat.mul (Nat.sub 1 (Nat.add nanA nanB))
                (Nat.mul (Nat.mul infA infB) (Nat.xor sa sb)))))
        (infFlag fmt ua) (infFlag fmt ub) (nanFlag fmt sa ua) (nanFlag fmt sb ub))
      ((fun ha hb =>
          (fun X Y =>
            roundStatus fmt mode (sumSign sa X sb Y) (sumMagnitude sa X sb Y) 0 w)
            (Nat.shiftLeft (Nat.sub ua (Nat.shiftLeft ha fmt.fracWidth)) (Nat.add ha 2))
            (Nat.shiftLeft (Nat.sub ub (Nat.shiftLeft hb fmt.fracWidth)) (Nat.add hb 2)))
        (Nat.sub (Nat.shiftRight ua fmt.fracWidth) 1)
        (Nat.sub (Nat.shiftRight ub fmt.fracWidth) 1)))
    (Nat.shiftRight a (signPos fmt)) (Nat.shiftRight b (signPos fmt))
    (Nat.land a (magnitudeMask fmt)) (Nat.land b (magnitudeMask fmt))

/--
The status number of the sum of the values encoded by `a` and `b`, rounded in the direction
`mode` (`addStatus_eq`).
-/
def addStatus (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b : Nat) : Nat :=
  addStatusWith fmt mode a b (add fmt mode a b)

/--
The status number of the difference of the values encoded by `a` and `b`, rounded in the
direction `mode`, when `w` is the word of the rounded difference. `subStatus` is this number at
`sub fmt mode a b`.
-/
def subStatusWith (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b w : Nat) : Nat :=
  addStatusWith fmt mode a (neg fmt b) w

/--
The status number of the difference of the values encoded by `a` and `b`, rounded in the
direction `mode` (`subStatus_eq`).
-/
def subStatus (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b : Nat) : Nat :=
  addStatus fmt mode a (neg fmt b)

/--
The status number of the product of the values encoded by `a` and `b`, rounded in the direction
`mode`, when `w` is the word of the rounded product. `mulStatus` is this number at
`mul fmt mode a b`.
-/
def mulStatusWith (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b w : Nat) : Nat :=
  (fun sa sb ua ub =>
    Bool.casesOn (motive := fun _ => Nat)
      (Nat.beq (Nat.add (nonFinite fmt sa ua) (nonFinite fmt sb ub)) 0)
      ((fun infA infB nanA nanB =>
          invalidStatus
            (Nat.add
              (Nat.add (Nat.mul nanA (signalingFlag fmt a)) (Nat.mul nanB (signalingFlag fmt b)))
              (Nat.mul (Nat.sub 1 (Nat.add nanA nanB))
                (Nat.add (Nat.mul infA (zeroFlag fmt sb ub)) (Nat.mul infB (zeroFlag fmt sa ua))))))
        (infFlag fmt ua) (infFlag fmt ub) (nanFlag fmt sa ua) (nanFlag fmt sb ub))
      ((fun ha hb =>
          roundStatus fmt mode (Nat.xor sa sb)
            (Nat.shiftLeft
              (Nat.mul (Nat.sub ua (Nat.shiftLeft ha fmt.fracWidth))
                (Nat.sub ub (Nat.shiftLeft hb fmt.fracWidth)))
              (Nat.add (Nat.add ha hb) 2))
            fmt.subnormalAlignExp w)
        (Nat.sub (Nat.shiftRight ua fmt.fracWidth) 1)
        (Nat.sub (Nat.shiftRight ub fmt.fracWidth) 1)))
    (Nat.shiftRight a (signPos fmt)) (Nat.shiftRight b (signPos fmt))
    (Nat.land a (magnitudeMask fmt)) (Nat.land b (magnitudeMask fmt))

/--
The status number of the product of the values encoded by `a` and `b`, rounded in the direction
`mode` (`mulStatus_eq`).
-/
def mulStatus (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b : Nat) : Nat :=
  mulStatusWith fmt mode a b (mul fmt mode a b)

/--
The status number of `x * y + z` rounded once in the direction `mode`, for the values encoded by
`a`, `b` and `c`, when `w` is the word of the rounded result. `fmaStatus` is this number at
`fma fmt mode a b c`.
-/
def fmaStatusWith (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b c w : Nat) : Nat :=
  (fun sa sb sc ua ub uc =>
    Bool.casesOn (motive := fun _ => Nat)
      (Nat.beq
        (Nat.add (Nat.add (nonFinite fmt sa ua) (nonFinite fmt sb ub)) (nonFinite fmt sc uc)) 0)
      ((fun infA infB infC nanA nanB nanC =>
          (fun anyInf anyZero =>
            invalidStatus
              (Nat.add
                (Nat.add
                  (Nat.add
                    (Nat.add (Nat.mul nanA (signalingFlag fmt a))
                      (Nat.mul nanB (signalingFlag fmt b)))
                    (Nat.mul nanC (signalingFlag fmt c)))
                  (Nat.mul anyInf anyZero))
                (Nat.mul (Nat.sub 1 (Nat.add (Nat.add nanA nanB) nanC))
                  (Nat.mul (Nat.mul (Nat.mul anyInf (Nat.sub 1 anyZero)) infC)
                    (Nat.xor sc (Nat.xor sa sb))))))
            (Nat.sub 1 (Nat.sub 1 (Nat.add infA infB)))
            (Nat.sub 1 (Nat.sub 1 (Nat.add (zeroFlag fmt sa ua) (zeroFlag fmt sb ub)))))
        (infFlag fmt ua) (infFlag fmt ub) (infFlag fmt uc)
        (nanFlag fmt sa ua) (nanFlag fmt sb ub) (nanFlag fmt sc uc))
      ((fun ha hb hc =>
          (fun X Z =>
            roundStatus fmt mode (sumSign (Nat.xor sa sb) X sc Z)
              (sumMagnitude (Nat.xor sa sb) X sc Z) fmt.subnormalAlignExp w)
            (Nat.shiftLeft
              (Nat.mul (Nat.sub ua (Nat.shiftLeft ha fmt.fracWidth))
                (Nat.sub ub (Nat.shiftLeft hb fmt.fracWidth)))
              (Nat.add (Nat.add ha hb) 2))
            (Nat.shiftLeft (Nat.sub uc (Nat.shiftLeft hc fmt.fracWidth))
              (Nat.add (Nat.add hc fmt.subnormalAlignExp) 2)))
        (Nat.sub (Nat.shiftRight ua fmt.fracWidth) 1) (Nat.sub (Nat.shiftRight ub fmt.fracWidth) 1)
        (Nat.sub (Nat.shiftRight uc fmt.fracWidth) 1)))
    (Nat.shiftRight a (signPos fmt)) (Nat.shiftRight b (signPos fmt))
    (Nat.shiftRight c (signPos fmt))
    (Nat.land a (magnitudeMask fmt)) (Nat.land b (magnitudeMask fmt))
    (Nat.land c (magnitudeMask fmt))

/--
The status number of `x * y + z` rounded once in the direction `mode`, for the values encoded by
`a`, `b` and `c` (`fmaStatus_eq`).
-/
def fmaStatus (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b c : Nat) : Nat :=
  fmaStatusWith fmt mode a b c (fma fmt mode a b c)

/-! ## Exact results and exactly delivered results -/

/-- `invalidStatus` is the status of a result delivered with at most the invalid flag. -/
theorem invalidStatus_eq {fmt : FloatFormat} (value : Model fmt) (invalid : Bool) (n : Nat)
    (hn : n ≠ 0 ↔ invalid = true) :
    decodeStatus (invalidStatus n) = (Model.outcomeWithInvalid value invalid).status ∧
      decodeTernary (invalidStatus n) = (Model.outcomeWithInvalid value invalid).ternary := by
  unfold invalidStatus Model.outcomeWithInvalid
  simp only [Nat.add_eq, Nat.sub_eq]
  cases invalid
  · have h0 : n = 0 := by
      by_contra h
      exact absurd (hn.1 h) (by decide)
    subst h0
    exact ⟨by decide +kernel, by decide +kernel⟩
  · have h1 : 1 - (1 - n) = 1 := by
      have := hn.2 rfl
      omega
    rw [h1]
    exact ⟨by decide +kernel, by decide +kernel⟩

/-- The sign and magnitude of a sum of two signed magnitudes, as a rational. -/
theorem signed_sum (sa sb X Y : Nat) (hsa : sa ≤ 1) (hsb : sb ≤ 1) :
    (if sumSign sa X sb Y = 1 then (-1 : ℚ) else 1) * (sumMagnitude sa X sb Y : ℚ) =
      (if sa = 1 then (-1 : ℚ) else 1) * (X : ℚ) + (if sb = 1 then (-1 : ℚ) else 1) * (Y : ℚ) := by
  have hdifference : ∀ P S : Nat,
      (if gtFlag S P = 1 then (-1 : ℚ) else 1) * (((P - S) + (S - P) : ℕ) : ℚ) =
        (P : ℚ) - (S : ℚ) := by
    intro P S
    rw [gtFlag_eq]
    rcases Nat.lt_trichotomy P S with h | h | h
    · have hE : P - S + (S - P) = S - P := by omega
      rw [hE, Nat.cast_sub (Nat.le_of_lt h)]
      simp [h]
    · subst h
      simp
    · have hE : P - S + (S - P) = P - S := by omega
      have hn : ¬ P < S := by omega
      rw [hE, Nat.cast_sub (Nat.le_of_lt h)]
      simp [hn]
  unfold sumSign sumMagnitude
  simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq]
  rw [hdifference]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hsa with h | h <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hsb with h' | h' <;> subst h <;> subst h' <;>
    simp only [tsub_zero, one_mul, Nat.cast_add, zero_mul, add_zero, CharP.cast_eq_zero,
      zero_ne_one, ↓reduceIte, tsub_self, zero_add, neg_mul, zero_sub, neg_add_rev] <;> ring

/-- The sign of a sum of two signed magnitudes is zero or one. -/
theorem sumSign_le_one (sa X sb Y : Nat) : sumSign sa X sb Y ≤ 1 := by
  unfold sumSign
  rw [gtFlag_eq]
  split <;> omega

/-- A dyadic with rational value zero has a zero significand. -/
theorem significand_eq_zero_of_toRat (d : Numerics.Dyadic) (h : d.toRat = 0) :
    d.significand = 0 := by
  obtain ⟨negative, significand, exponent⟩ := d
  rw [toRat_mk] at h
  have hpow : (2 : ℚ) ^ exponent ≠ 0 := zpow_ne_zero _ (by norm_num)
  have hsign : (if negative then (-1 : ℚ) else 1) ≠ 0 := by cases negative <;> norm_num
  have := mul_eq_zero.1 h
  rcases this with h1 | h1
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd h2 hsign
    · exact_mod_cast h2
  · exact absurd h1 hpow

/-- A zero on the scale of a status computation is the rational zero. -/
theorem toRat_eq_zero_of_magnitude {d : Numerics.Dyadic} {sign E : Nat} {c : Int}
    (hvalue : d.toRat = (if sign = 1 then -1 else 1) * (E : ℚ) * (2 : ℚ) ^ c) (hE : E = 0) :
    d.toRat = 0 := by
  rw [hvalue, hE]
  simp

/-- A value with an exact dyadic value is finite. -/
theorem isFinite_of_toDyadic? {fmt : FloatFormat} {x : Model fmt} {d : Numerics.Dyadic}
    (hd : Model.toDyadic? x = some d) : Model.isFinite x = true := by
  rw [← Model.toDyadic?_isSome_eq_isFinite, hd]
  rfl

/-- A value without an exact dyadic value is not finite. -/
theorem isFinite_eq_false_of_toDyadic? {fmt : FloatFormat} {x : Model fmt}
    (hd : Model.toDyadic? x = none) : Model.isFinite x = false := by
  rw [← Model.toDyadic?_isSome_eq_isFinite, hd]
  rfl

/-- A natural number that is not zero fails the test for zero. -/
theorem beq_zero_of_ne {n : Nat} (hn : n ≠ 0) : Nat.beq n 0 = false := by
  cases n
  · exact absurd rfl hn
  · rfl

/--
The rational value of the exact product of two decoded finite values, on the scale of a status
computation with the offset `fmt.subnormalAlignExp`.
-/
theorem product_toRat {fmt : FloatFormat} (x y : Model fmt) (dx dy : Numerics.Dyadic)
    (hdx : Model.toDyadic? x = some dx) (hdy : Model.toDyadic? y = some dy) :
    (⟨Bool.xor dx.negative dy.negative, dx.significand * dy.significand,
        dx.exponent + dy.exponent⟩ : Numerics.Dyadic).toRat =
      (if (if Bool.xor (Model.signBit x) (Model.signBit y) then 1 else 0 : Nat) = 1
        then -1 else 1) *
        ((((if Model.expField x = 0 then Model.fracField x
            else 2 ^ fmt.fracWidth + Model.fracField x) *
          (if Model.expField y = 0 then Model.fracField y
            else 2 ^ fmt.fracWidth + Model.fracField y)) <<<
          (Model.expField x - 1 + (Model.expField y - 1) + 2) : ℕ) : ℚ) *
        (2 : ℚ) ^ (fmt.minSubnormalExponent - (fmt.subnormalAlignExp : Int) - 2) := by
  have hbias : 1 ≤ fmt.exponentBias + fmt.fracWidth := by
    have := fmt.fracWidth_pos
    omega
  have hK : fmt.subnormalAlignExp = fmt.exponentBias + fmt.fracWidth - 1 := rfl
  obtain ⟨dx', hdx', hnx, hsx, hex⟩ := toDyadic?_of_isFinite x (isFinite_of_toDyadic? hdx)
  obtain rfl : dx' = dx := Option.some.inj (hdx'.symm.trans hdx)
  obtain ⟨dy', hdy', hny, hsy, hey⟩ := toDyadic?_of_isFinite y (isFinite_of_toDyadic? hdy)
  obtain rfl : dy' = dy := Option.some.inj (hdy'.symm.trans hdy)
  rw [toRat_of_fields _ (dx'.significand * dy'.significand)
    (Model.expField x - 1 + (Model.expField y - 1) + 2)
    (fmt.minSubnormalExponent - (fmt.subnormalAlignExp : Int) - 2)
    rfl (fun h => by
      have hx0 : dx'.significand ≠ 0 := fun h0 => h (by rw [h0, Nat.zero_mul])
      have hy0 : dy'.significand ≠ 0 := fun h0 => h (by rw [h0, Nat.mul_zero])
      change dx'.exponent + dy'.exponent = _
      rw [hex hx0, hey hy0, hK]
      simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
        Int.ofNat_eq_natCast]
      push_cast
      omega), hnx, hny, hsx, hsy, Nat.shiftLeft_eq]
  cases Bool.xor (Model.signBit x) (Model.signBit y) <;> simp

/-! ## Addition and subtraction -/

/--
`addStatus` computes the flags and the ternary value of the reference addition
`Model.add x y (mode := mode) (status := true)`, for every format descriptor, every rounding
direction and all operands.
-/
theorem addStatus_eq {fmt : FloatFormat} (mode : Model.IEEERoundingMode) (x y : Model fmt) :
    decodeStatus (addStatus fmt mode x.toNatBits y.toNatBits) =
        (Model.add x y (mode := mode) (status := true)).status ∧
      decodeTernary (addStatus fmt mode x.toNatBits y.toNatBits) =
        (Model.add x y (mode := mode) (status := true)).ternary := by
  have hfx := Model.fracField_lt_pow2 x
  have hfy := Model.fracField_lt_pow2 y
  rw [← Model.Internal.Status.add_eq]
  unfold addStatus addStatusWith Model.Internal.Status.add
  simp only [Nat.shiftRight_eq', Nat.land_eq, Nat.shiftLeft_eq', Nat.sub_eq, Nat.add_eq,
    Nat.mul_eq, Nat.xor_eq, sign_toNatBits, magnitude_toNatBits, fields_shiftRight _ _ _ hfx,
    fields_shiftRight _ _ _ hfy, fields_sub_shiftLeft, xor_sign, infFlag_eq, nanFlag_eq,
    nanFlag_mul_signalingFlag]
  cases hdx : Model.toDyadic? x with
  | some dx =>
    cases hdy : Model.toDyadic? y with
    | some dy =>
      have hfinx := isFinite_of_toDyadic? hdx
      have hfiny := isFinite_of_toDyadic? hdy
      rw [nonFinite_eq_zero_of_isFinite x hfinx, nonFinite_eq_zero_of_isFinite y hfiny,
        show Nat.beq (0 + 0) 0 = true from rfl]
      have hratx := decoded_toRat x dx hdx 0
      have hraty := decoded_toRat y dy hdy 0
      simp only [Nat.add_zero] at hratx hraty
      have hvalue : (Model.addDyadic dx dy).toRat = _ :=
        (Numerics.Dyadic.add_toRat dx dy).trans (by
          rw [hratx, hraty, ← add_mul, ← signed_sum _ _ _ _ (by split <;> omega)
            (by split <;> omega)])
      have hresult : add fmt mode x.toNatBits y.toNatBits =
          (Model.Internal.Directed.add mode x y).toNatBits := by
        rw [add_eq_spec, Model.Internal.Directed.add_eq]
      rw [hresult]
      refine roundStatus_eq fmt mode _ _ _ 0 (sumSign_le_one _ _ _ _)
        (by simpa only [Nat.cast_zero, sub_zero] using hvalue) _ ?_
      intro hE
      have hzero := significand_eq_zero_of_toRat _ (toRat_eq_zero_of_magnitude hvalue hE)
      rw [Model.Internal.Directed.add_eq, add_of_finite mode x y dx dy hdx hdy]
      unfold roundedSum
      rw [show ((Model.addDyadic dx dy).significand == 0) = true by simp [hzero], ite_eq_left rfl]
      exact Model.isFinite_eq_true_of_isZero_eq_true _ (Model.isZero_zero fmt _)
    | none =>
      have hfiny := isFinite_eq_false_of_toDyadic? hdy
      have hguard : nonFinite fmt (if Model.signBit x then 1 else 0)
            (Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x) +
          nonFinite fmt (if Model.signBit y then 1 else 0)
            (Model.expField y * 2 ^ fmt.fracWidth + Model.fracField y) ≠ 0 := by
        intro h
        rw [isFinite_of_nonFinite_eq_zero y (Nat.eq_zero_of_add_eq_zero h).2] at hfiny
        exact absurd hfiny (by decide)
      rw [beq_zero_of_ne hguard]
      refine invalidStatus_eq _ _ _ ?_
      cases Model.isSignaling x <;> cases Model.isSignaling y <;> cases Model.isNaN x <;>
        cases Model.isNaN y <;> cases Model.isInfinite x <;> cases Model.isInfinite y <;>
        cases Model.signBit x <;> cases Model.signBit y <;> decide
  | none =>
    have hfinx := isFinite_eq_false_of_toDyadic? hdx
    have hguard : nonFinite fmt (if Model.signBit x then 1 else 0)
          (Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x) +
        nonFinite fmt (if Model.signBit y then 1 else 0)
          (Model.expField y * 2 ^ fmt.fracWidth + Model.fracField y) ≠ 0 := by
      intro h
      rw [isFinite_of_nonFinite_eq_zero x (Nat.eq_zero_of_add_eq_zero h).1] at hfinx
      exact absurd hfinx (by decide)
    rw [beq_zero_of_ne hguard]
    refine invalidStatus_eq _ _ _ ?_
    cases Model.isSignaling x <;> cases Model.isSignaling y <;> cases Model.isNaN x <;>
      cases Model.isNaN y <;> cases Model.isInfinite x <;> cases Model.isInfinite y <;>
      cases Model.signBit x <;> cases Model.signBit y <;> decide

/--
`subStatus` computes the flags and the ternary value of the reference subtraction
`Model.sub x y (mode := mode) (status := true)`, for every format descriptor, every rounding
direction and all operands.
-/
theorem subStatus_eq {fmt : FloatFormat} (mode : Model.IEEERoundingMode) (x y : Model fmt) :
    decodeStatus (subStatus fmt mode x.toNatBits y.toNatBits) =
        (Model.sub x y (mode := mode) (status := true)).status ∧
      decodeTernary (subStatus fmt mode x.toNatBits y.toNatBits) =
        (Model.sub x y (mode := mode) (status := true)).ternary := by
  unfold subStatus
  rw [neg_eq_spec]
  exact addStatus_eq mode x (Model.neg y)

/-! ## Multiplication -/

/--
`mulStatus` computes the flags and the ternary value of the reference multiplication
`Model.mul x y (mode := mode) (status := true)`, for every format descriptor, every rounding
direction and all operands.
-/
theorem mulStatus_eq {fmt : FloatFormat} (mode : Model.IEEERoundingMode) (x y : Model fmt) :
    decodeStatus (mulStatus fmt mode x.toNatBits y.toNatBits) =
        (Model.mul x y (mode := mode) (status := true)).status ∧
      decodeTernary (mulStatus fmt mode x.toNatBits y.toNatBits) =
        (Model.mul x y (mode := mode) (status := true)).ternary := by
  have hfx := Model.fracField_lt_pow2 x
  have hfy := Model.fracField_lt_pow2 y
  rw [← Model.Internal.Status.mul_eq]
  unfold mulStatus mulStatusWith Model.Internal.Status.mul
  simp only [Nat.shiftRight_eq', Nat.land_eq, Nat.shiftLeft_eq', Nat.sub_eq, Nat.add_eq,
    Nat.mul_eq, Nat.xor_eq, sign_toNatBits, magnitude_toNatBits, fields_shiftRight _ _ _ hfx,
    fields_shiftRight _ _ _ hfy, fields_sub_shiftLeft, xor_sign, infFlag_eq, nanFlag_eq,
    zeroFlag_eq, nanFlag_mul_signalingFlag]
  cases hdx : Model.toDyadic? x with
  | some dx =>
    cases hdy : Model.toDyadic? y with
    | some dy =>
      have hfinx := isFinite_of_toDyadic? hdx
      have hfiny := isFinite_of_toDyadic? hdy
      rw [nonFinite_eq_zero_of_isFinite x hfinx, nonFinite_eq_zero_of_isFinite y hfiny,
        show Nat.beq (0 + 0) 0 = true from rfl]
      have hvalue := product_toRat x y dx dy hdx hdy
      have hresult : mul fmt mode x.toNatBits y.toNatBits =
          (Model.Internal.Directed.mul mode x y).toNatBits := by
        rw [mul_eq_spec, Model.Internal.Directed.mul_eq]
      rw [hresult]
      refine roundStatus_eq fmt mode _ _ _ _ (by split <;> omega) hvalue _ ?_
      intro hE
      have hzero := significand_eq_zero_of_toRat _ (toRat_eq_zero_of_magnitude hvalue hE)
      rw [Model.Internal.Directed.mul_eq, mul_of_finite mode x y dx dy hdx hdy]
      rw [show dx.significand * dy.significand = 0 from hzero, roundDyadic_zero]
      exact Model.isFinite_eq_true_of_isZero_eq_true _ (Model.isZero_zero fmt _)
    | none =>
      have hfiny := isFinite_eq_false_of_toDyadic? hdy
      have hguard : nonFinite fmt (if Model.signBit x then 1 else 0)
            (Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x) +
          nonFinite fmt (if Model.signBit y then 1 else 0)
            (Model.expField y * 2 ^ fmt.fracWidth + Model.fracField y) ≠ 0 := by
        intro h
        rw [isFinite_of_nonFinite_eq_zero y (Nat.eq_zero_of_add_eq_zero h).2] at hfiny
        exact absurd hfiny (by decide)
      rw [beq_zero_of_ne hguard]
      refine invalidStatus_eq _ _ _ ?_
      cases Model.isSignaling x <;> cases Model.isSignaling y <;> cases Model.isNaN x <;>
        cases Model.isNaN y <;> cases Model.isInfinite x <;> cases Model.isInfinite y <;>
        cases Model.isZero x <;> cases Model.isZero y <;> decide
  | none =>
    have hfinx := isFinite_eq_false_of_toDyadic? hdx
    have hguard : nonFinite fmt (if Model.signBit x then 1 else 0)
          (Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x) +
        nonFinite fmt (if Model.signBit y then 1 else 0)
          (Model.expField y * 2 ^ fmt.fracWidth + Model.fracField y) ≠ 0 := by
      intro h
      rw [isFinite_of_nonFinite_eq_zero x (Nat.eq_zero_of_add_eq_zero h).1] at hfinx
      exact absurd hfinx (by decide)
    rw [beq_zero_of_ne hguard]
    refine invalidStatus_eq _ _ _ ?_
    cases Model.isSignaling x <;> cases Model.isSignaling y <;> cases Model.isNaN x <;>
      cases Model.isNaN y <;> cases Model.isInfinite x <;> cases Model.isInfinite y <;>
      cases Model.isZero x <;> cases Model.isZero y <;> decide

/-! ## Fused multiply-add -/

/-- The invalid-operation test of a fused multiply-add, on flags that are zero or one. -/
private theorem fma_invalid_iff (sx sy sz nx ny nz ix iy iz zx zy c p : Bool) :
    (((if sx then 1 else 0 : Nat) + (if sy then 1 else 0)) + (if sz then 1 else 0)) +
          (1 - (1 - ((if ix then 1 else 0 : Nat) + (if iy then 1 else 0)))) *
            (1 - (1 - ((if zx then 1 else 0 : Nat) + (if zy then 1 else 0)))) +
        (1 - (((if nx then 1 else 0 : Nat) + (if ny then 1 else 0)) + (if nz then 1 else 0))) *
          ((1 - (1 - ((if ix then 1 else 0 : Nat) + (if iy then 1 else 0)))) *
              (1 - (1 - (1 - ((if zx then 1 else 0 : Nat) + (if zy then 1 else 0))))) *
              (if iz then 1 else 0) *
            (if Bool.xor c p then 1 else 0)) ≠ 0 ↔
      (sx || sy || sz || ((ix || iy) && (zx || zy)) ||
        (!(nx || ny || nz) && ((ix || iy) && !(zx || zy) && iz && (c != p)))) = true := by
  revert sx sy sz nx ny nz ix iy iz zx zy c p
  decide +kernel

/--
`fmaStatus` computes the flags and the ternary value of the reference fused multiply-add
`Model.fma x y z (mode := mode) (status := true)`, for every format descriptor, every rounding
direction and all operands.
-/
theorem fmaStatus_eq {fmt : FloatFormat} (mode : Model.IEEERoundingMode) (x y z : Model fmt) :
    decodeStatus (fmaStatus fmt mode x.toNatBits y.toNatBits z.toNatBits) =
        (Model.fma x y z (mode := mode) (status := true)).status ∧
      decodeTernary (fmaStatus fmt mode x.toNatBits y.toNatBits z.toNatBits) =
        (Model.fma x y z (mode := mode) (status := true)).ternary := by
  have hfx := Model.fracField_lt_pow2 x
  have hfy := Model.fracField_lt_pow2 y
  have hfz := Model.fracField_lt_pow2 z
  rw [← Model.Internal.Status.fma_eq]
  unfold fmaStatus fmaStatusWith Model.Internal.Status.fma
  simp only [Nat.shiftRight_eq', Nat.land_eq, Nat.shiftLeft_eq', Nat.sub_eq, Nat.add_eq,
    Nat.mul_eq, Nat.xor_eq, sign_toNatBits, magnitude_toNatBits, fields_shiftRight _ _ _ hfx,
    fields_shiftRight _ _ _ hfy, fields_shiftRight _ _ _ hfz, fields_sub_shiftLeft, xor_sign,
    infFlag_eq, nanFlag_eq, zeroFlag_eq, nanFlag_mul_signalingFlag]
  have hguard : (Model.isFinite x = false ∨ Model.isFinite y = false ∨
        Model.isFinite z = false) →
      nonFinite fmt (if Model.signBit x then 1 else 0)
            (Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x) +
          nonFinite fmt (if Model.signBit y then 1 else 0)
            (Model.expField y * 2 ^ fmt.fracWidth + Model.fracField y) +
        nonFinite fmt (if Model.signBit z then 1 else 0)
          (Model.expField z * 2 ^ fmt.fracWidth + Model.fracField z) ≠ 0 := by
    intro hsome h
    obtain ⟨hxy, hz⟩ := Nat.eq_zero_of_add_eq_zero h
    obtain ⟨hx, hy⟩ := Nat.eq_zero_of_add_eq_zero hxy
    rw [isFinite_of_nonFinite_eq_zero x hx, isFinite_of_nonFinite_eq_zero y hy,
      isFinite_of_nonFinite_eq_zero z hz] at hsome
    simp at hsome
  cases hdx : Model.toDyadic? x with
  | none =>
    rw [beq_zero_of_ne (hguard (Or.inl (isFinite_eq_false_of_toDyadic? hdx)))]
    exact invalidStatus_eq _ _ _ (fma_invalid_iff _ _ _ _ _ _ _ _ _ _ _ _ _)
  | some dx =>
    cases hdy : Model.toDyadic? y with
    | none =>
      rw [beq_zero_of_ne (hguard (Or.inr (Or.inl (isFinite_eq_false_of_toDyadic? hdy))))]
      exact invalidStatus_eq _ _ _ (fma_invalid_iff _ _ _ _ _ _ _ _ _ _ _ _ _)
    | some dy =>
      cases hdz : Model.toDyadic? z with
      | none =>
        rw [beq_zero_of_ne (hguard (Or.inr (Or.inr (isFinite_eq_false_of_toDyadic? hdz))))]
        exact invalidStatus_eq _ _ _ (fma_invalid_iff _ _ _ _ _ _ _ _ _ _ _ _ _)
      | some dz =>
        rw [nonFinite_eq_zero_of_isFinite x (isFinite_of_toDyadic? hdx),
          nonFinite_eq_zero_of_isFinite y (isFinite_of_toDyadic? hdy),
          nonFinite_eq_zero_of_isFinite z (isFinite_of_toDyadic? hdz),
          show Nat.beq (0 + 0 + 0) 0 = true from rfl]
        have hproduct := product_toRat x y dx dy hdx hdy
        have hratz := decoded_toRat z dz hdz fmt.subnormalAlignExp
        have hvalue : (Model.addDyadic
              ⟨Bool.xor dx.negative dy.negative, dx.significand * dy.significand,
                dx.exponent + dy.exponent⟩ dz).toRat = _ :=
          (Numerics.Dyadic.add_toRat _ dz).trans (by
            rw [hproduct, hratz, ← add_mul, ← signed_sum _ _ _ _ (by split <;> omega)
              (by split <;> omega)])
        have hresult : fma fmt mode x.toNatBits y.toNatBits z.toNatBits =
            (Model.Internal.Directed.fma mode x y z).toNatBits := by
          rw [fma_eq_spec, Model.Internal.Directed.fma_eq]
        rw [hresult]
        refine roundStatus_eq fmt mode _ _ _ _ (sumSign_le_one _ _ _ _) hvalue _ ?_
        intro hE
        have hzero := significand_eq_zero_of_toRat _ (toRat_eq_zero_of_magnitude hvalue hE)
        rw [Model.Internal.Directed.fma_eq, fma_of_finite mode x y z dx dy dz hdx hdy hdz]
        unfold roundedSum
        rw [show ((Model.addDyadic
            ⟨Bool.xor dx.negative dy.negative, dx.significand * dy.significand,
              dx.exponent + dy.exponent⟩ dz).significand == 0) = true by simp [hzero],
          ite_eq_left rfl]
        exact Model.isFinite_eq_true_of_isZero_eq_true _ (Model.isZero_zero fmt _)

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
