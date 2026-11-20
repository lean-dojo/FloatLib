/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Special
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.EReal

import FloatLib.Numerics.Exact.Dyadic.Order
import Mathlib.Tactic.Positivity

/-!
# Comparison and classification on natural-number encodings

`compareCode fmt a b` is the IEEE comparison of the values encoded by `a` and `b`, as a number:
`0` for less, `1` for equal, `2` for greater and `3` for unordered. A word that is not a NaN
gets the key `2 ^ signPos + fields` when its sign is clear and `2 ^ signPos - fields` when it is
set. The key is monotone in the value (the two zeros share one key, an infinity lies beyond
every finite value), so two naturals are compared instead of two decoded values.

`compareCode_eq` proves that the code is `Model.compare`, for every format descriptor and every
pair of operands. `nanCode`, `infCode`, `zeroCode`, `finiteCode` and `signCode` classify a word,
and `nanCode_eq` and its siblings prove that they are `Model.isNaN`, `isInfinite`, `isZero`,
`isFinite` and `signBit`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

/--
The comparison key of a word that is not a NaN, from its sign and its exponent and fraction
fields: `2 ^ signPos fmt + magnitude` for a clear sign and `2 ^ signPos fmt - magnitude` for a
set one.
-/
def compareKey (fmt : FloatFormat) (sign magnitude : Nat) : Nat :=
  Nat.sub (Nat.add (Nat.pow 2 (signPos fmt)) magnitude) (Nat.mul (Nat.mul 2 sign) magnitude)

/--
The comparison of the values encoded by `a` and `b`: `0` less, `1` equal, `2` greater, `3`
unordered (`compareCode_eq`).
-/
def compareCode (fmt : FloatFormat) (a b : Nat) : Nat :=
  (fun sa sb ua ub =>
    Bool.casesOn (motive := fun _ => Nat)
      (Nat.beq (Nat.add (nanFlag fmt sa ua) (nanFlag fmt sb ub)) 0)
      3
      ((fun ka kb =>
        Nat.sub (Nat.add 1 (Nat.sub 1 (Nat.sub 1 (Nat.sub ka kb))))
          (Nat.sub 1 (Nat.sub 1 (Nat.sub kb ka))))
        (compareKey fmt sa ua) (compareKey fmt sb ub)))
    (Nat.shiftRight a (signPos fmt)) (Nat.shiftRight b (signPos fmt))
    (Nat.land a (magnitudeMask fmt)) (Nat.land b (magnitudeMask fmt))

/-- The comparison result that a code stands for. -/
def decodeOrdering (code : Nat) : Option Ordering :=
  Bool.casesOn (motive := fun _ => Option Ordering) (Nat.beq code 0)
    (Bool.casesOn (motive := fun _ => Option Ordering) (Nat.beq code 1)
      (Bool.casesOn (motive := fun _ => Option Ordering) (Nat.beq code 2) none (some .gt))
      (some .eq))
    (some .lt)

/-- One when the word `a` is a NaN (`nanCode_eq`). -/
def nanCode (fmt : FloatFormat) (a : Nat) : Nat :=
  nanFlag fmt (Nat.shiftRight a (signPos fmt)) (Nat.land a (magnitudeMask fmt))

/-- One when the word `a` is an infinity (`infCode_eq`). -/
def infCode (fmt : FloatFormat) (a : Nat) : Nat :=
  infFlag fmt (Nat.land a (magnitudeMask fmt))

/-- One when the word `a` is a zero (`zeroCode_eq`). -/
def zeroCode (fmt : FloatFormat) (a : Nat) : Nat :=
  zeroFlag fmt (Nat.shiftRight a (signPos fmt)) (Nat.land a (magnitudeMask fmt))

/-- One when the word `a` is finite (`finiteCode_eq`). -/
def finiteCode (fmt : FloatFormat) (a : Nat) : Nat :=
  Nat.sub 1 (nonFinite fmt (Nat.shiftRight a (signPos fmt)) (Nat.land a (magnitudeMask fmt)))

/-- The sign bit of the word `a` (`signCode_eq`). -/
def signCode (fmt : FloatFormat) (a : Nat) : Nat :=
  Nat.shiftRight a (signPos fmt)

/--
`some value` when `code` is one and `none` otherwise: the result of an operation that has a
value on finite words only. A rewrite rule states such a result with this function and not with
a `Bool` recursor: the kernel tries to evaluate the condition of a recursor whenever it compares
two forms of it, which does not end on a loop whose length is still a variable.
-/
def someWhen {α : Type} (code : Nat) (value : α) : Option α :=
  Bool.casesOn (motive := fun _ => Option α) (Nat.beq code 1) none (some value)

/-! ## Keys are monotone -/

/-- The comparison code of two keys is the comparison of the keys. -/
theorem decodeOrdering_keys (ka kb : Nat) :
    decodeOrdering (1 + (1 - (1 - (ka - kb))) - (1 - (1 - (kb - ka)))) =
      some (compare ka kb) := by
  rcases Nat.lt_trichotomy ka kb with h | h | h
  · have hcode : 1 + (1 - (1 - (ka - kb))) - (1 - (1 - (kb - ka))) = 0 := by omega
    rw [hcode, (compare_lt_iff_lt).2 h]
    rfl
  · subst h
    have hcode : 1 + (1 - (1 - (ka - ka))) - (1 - (1 - (ka - ka))) = 1 := by omega
    rw [hcode, (compare_eq_iff_eq).2 rfl]
    rfl
  · have hcode : 1 + (1 - (1 - (ka - kb))) - (1 - (1 - (kb - ka))) = 2 := by omega
    rw [hcode, (compare_gt_iff_gt).2 h]
    rfl

/-- Two comparisons with the same strict and equal cases have the same result. -/
theorem compare_congr {α β : Type*} [LinearOrder α] [LinearOrder β] {a b : α} {c d : β}
    (hlt : a < b ↔ c < d) (heq : a = b ↔ c = d) : compare a b = compare c d := by
  rcases lt_trichotomy a b with h | h | h
  · rw [(compare_lt_iff_lt).2 h, (compare_lt_iff_lt).2 (hlt.1 h)]
  · rw [(compare_eq_iff_eq).2 h, (compare_eq_iff_eq).2 (heq.1 h)]
  · have hcd : d < c := by
      rcases lt_trichotomy c d with h' | h' | h'
      · exact absurd (hlt.2 h') (lt_asymm h)
      · exact absurd (heq.2 h') (ne_of_gt h)
      · exact h'
    rw [(compare_gt_iff_gt).2 h, (compare_gt_iff_gt).2 hcd]

/--
The exact magnitudes `m * 2 ^ h` of two decoded words are ordered as their exponent and fraction
fields `h * F + m`, for significands below `2 * F` that are at least `F` when `h` is not zero.
-/
theorem magnitude_lt_iff {F ma ha mb hb : Nat} (hma : ma < 2 * F) (hmb : mb < 2 * F)
    (hna : 1 ≤ ha → F ≤ ma) (hnb : 1 ≤ hb → F ≤ mb) :
    ma * 2 ^ ha < mb * 2 ^ hb ↔ ha * F + ma < hb * F + mb := by
  have key : ∀ {m h m' h' : Nat}, m < 2 * F → (1 ≤ h' → F ≤ m') → h < h' →
      m * 2 ^ h < m' * 2 ^ h' ∧ h * F + m < h' * F + m' := by
    intro m h m' h' hm hn hlt
    have hF := hn (by omega)
    constructor
    · calc m * 2 ^ h < 2 * F * 2 ^ h := Nat.mul_lt_mul_of_pos_right hm (Nat.two_pow_pos _)
        _ = F * 2 ^ (h + 1) := by rw [Nat.pow_succ]; ac_rfl
        _ ≤ F * 2 ^ h' := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hlt)
        _ ≤ m' * 2 ^ h' := Nat.mul_le_mul_right _ hF
    · have h1 : (h + 1) * F ≤ h' * F := Nat.mul_le_mul_right F hlt
      have h2 : (h + 1) * F = h * F + F := by rw [add_mul]; ac_rfl
      omega
  rcases Nat.lt_trichotomy ha hb with h | h | h
  · have := key hma hnb h
    exact iff_of_true this.1 this.2
  · subst h
    rw [Nat.mul_lt_mul_right (Nat.two_pow_pos _)]
    omega
  · have := key hmb hna h
    exact iff_of_false (by omega) (by omega)

/-! ## The code is the reference comparison -/

/-- The rational value of a decoded finite word: sign, magnitude `m * 2 ^ h` and a scale. -/
theorem toRat_of_fields (d : Numerics.Dyadic) (m h : Nat) (c : Int) (hsig : d.significand = m)
    (hexp : m ≠ 0 → d.exponent = (h : Int) + c) :
    d.toRat = (if d.negative then -1 else 1) * ((m * 2 ^ h : ℕ) : ℚ) * (2 : ℚ) ^ c := by
  obtain ⟨negative, significand, exponent⟩ := d
  dsimp only at hsig hexp ⊢
  subst hsig
  unfold Numerics.Dyadic.toRat Numerics.Dyadic.signedSignificand
  by_cases h0 : significand = 0
  · subst h0
    simp
  · rw [hexp h0, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast]
    cases negative <;> simp [mul_assoc]

/--
Two signed magnitudes scaled by one positive factor compare as their keys: `P + u` for a clear
sign and `P - u` for a set one, where the fields `u` are ordered as the magnitudes.
-/
theorem compare_signed_eq_compare_keys (na nb : Bool) (X Y P ux uy : ℕ) (C : ℚ) (hC : 0 < C)
    (hux : ux ≤ P) (huy : uy ≤ P) (hlt : X < Y ↔ ux < uy) (hgt : Y < X ↔ uy < ux)
    (hzx : X = 0 ↔ ux = 0) (hzy : Y = 0 ↔ uy = 0) :
    compare ((if na then -1 else 1) * (X : ℚ) * C) ((if nb then -1 else 1) * (Y : ℚ) * C) =
      compare (if na then P - ux else P + ux) (if nb then P - uy else P + uy) := by
  have heq : X = Y ↔ ux = uy := by
    constructor <;> intro h <;> omega
  have hXC : 0 ≤ (X : ℚ) * C := by positivity
  have hYC : 0 ≤ (Y : ℚ) * C := by positivity
  have hzeroX : (X : ℚ) * C = 0 ↔ ux = 0 := by
    rw [mul_eq_zero, Nat.cast_eq_zero, hzx]
    constructor
    · rintro (h | h)
      · exact h
      · exact absurd h hC.ne'
    · intro h; exact Or.inl h
  have hzeroY : (Y : ℚ) * C = 0 ↔ uy = 0 := by
    rw [mul_eq_zero, Nat.cast_eq_zero, hzy]
    constructor
    · rintro (h | h)
      · exact h
      · exact absurd h hC.ne'
    · intro h; exact Or.inl h
  apply compare_congr
  · cases na <;> cases nb <;> simp only [Bool.false_eq_true, ite_true, ite_false, one_mul,
      neg_mul]
    · rw [mul_lt_mul_iff_of_pos_right hC, Nat.cast_lt, hlt]
      omega
    · constructor
      · intro h; linarith
      · intro h; omega
    · constructor
      · intro h
        have hne : ¬ (ux = 0 ∧ uy = 0) := by
          rintro ⟨h1, h2⟩
          rw [hzeroX.2 h1, hzeroY.2 h2] at h
          simp at h
        omega
      · intro h
        have hne : ¬ ((X : ℚ) * C = 0 ∧ (Y : ℚ) * C = 0) := by
          rintro ⟨h1, h2⟩
          have := hzeroX.1 h1
          have := hzeroY.1 h2
          omega
        by_contra hnot
        exact hne ⟨by linarith, by linarith⟩
    · rw [neg_lt_neg_iff, mul_lt_mul_iff_of_pos_right hC, Nat.cast_lt, hgt]
      omega
  · cases na <;> cases nb <;> simp only [Bool.false_eq_true, ite_true, ite_false, one_mul,
      neg_mul]
    · rw [mul_left_inj' hC.ne', Nat.cast_inj, heq]
      omega
    · constructor
      · intro h
        have h1 := hzeroX.1 (by linarith)
        have h2 := hzeroY.1 (by simp_all)
        omega
      · intro h
        have h1 : ux = 0 := by omega
        have h2 : uy = 0 := by omega
        rw [hzeroX.2 h1, hzeroY.2 h2]
        simp
    · constructor
      · intro h
        have h1 := hzeroX.1 (by linarith)
        have h2 := hzeroY.1 (by simp_all)
        omega
      · intro h
        have h1 : ux = 0 := by omega
        have h2 : uy = 0 := by omega
        rw [hzeroX.2 h1, hzeroY.2 h2]
        simp
    · rw [neg_inj, mul_left_inj' hC.ne', Nat.cast_inj, heq]
      omega

/-- The key of a word, by its sign. -/
theorem compareKey_eq (fmt : FloatFormat) (negative : Bool) (u : Nat)
    (hu : u ≤ 2 ^ signPos fmt) :
    compareKey fmt (if negative then 1 else 0) u =
      if negative then 2 ^ signPos fmt - u else 2 ^ signPos fmt + u := by
  unfold compareKey
  cases negative <;> simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.pow_eq,
    Bool.false_eq_true, ite_true, ite_false] <;> omega

/-- The fields of a word in terms of the exponent of its decoded significand. -/
theorem fields_eq_decoded (e f F : Nat) :
    e * F + f = (e - 1) * F + (if e = 0 then f else F + f) := by
  rcases e with _ | k
  · simp
  · have : (k + 1) * F = k * F + F := by rw [add_mul]; ac_rfl
    simp only [Nat.add_sub_cancel, Nat.add_one_ne_zero, ite_false]
    omega

/--
`compareCode` computes the reference comparison `Model.compare`, for every format descriptor and
all operands: NaNs are unordered, the zeros are equal, and infinities and finite values are
ordered by value.
-/
theorem compareCode_eq {fmt : FloatFormat} (x y : Model fmt) :
    decodeOrdering (compareCode fmt x.toNatBits y.toNatBits) = Model.compare x y := by
  have hux := fields_lt_two_pow_signPos x
  have huy := fields_lt_two_pow_signPos y
  have hFpos : 0 < 2 ^ fmt.fracWidth := Nat.two_pow_pos _
  have hsplit : 2 ^ (fmt.fracWidth + 1) = 2 * 2 ^ fmt.fracWidth := by rw [Nat.pow_succ]; ac_rfl
  unfold compareCode
  simp only [Nat.shiftRight_eq', Nat.land_eq, sign_toNatBits, magnitude_toNatBits, nanFlag_eq]
  by_cases hnan : Model.isNaN x = true ∨ Model.isNaN y = true
  · rw [(Model.compare_eq_none_iff x y).2 hnan]
    have hflag : Nat.beq (Nat.add (if Model.isNaN x then 1 else 0)
        (if Model.isNaN y then 1 else 0)) 0 = false := by
      rcases hnan with h | h
      · rw [h]; cases Model.isNaN y <;> rfl
      · rw [h]; cases Model.isNaN x <;> rfl
    rw [hflag]
    rfl
  · have hnx : Model.isNaN x = false := by
      cases h : Model.isNaN x
      · rfl
      · exact absurd (Or.inl h) hnan
    have hny : Model.isNaN y = false := by
      cases h : Model.isNaN y
      · rfl
      · exact absurd (Or.inr h) hnan
    rw [hnx, hny]
    change decodeOrdering (Nat.sub (Nat.add 1 (Nat.sub 1 (Nat.sub 1 (Nat.sub _ _))))
      (Nat.sub 1 (Nat.sub 1 (Nat.sub _ _)))) = _
    simp only [Nat.sub_eq, Nat.add_eq]
    rw [decodeOrdering_keys, compareKey_eq fmt _ _ (le_of_lt hux),
      compareKey_eq fmt _ _ (le_of_lt huy), Model.compare_eq_some_compareNonNaN x y hnx hny]
    congr 1
    -- An infinity lies beyond every finite word of its sign.
    have hinfinity : ∀ z : Model fmt, Model.isInfinite z = true →
        Model.expField z * 2 ^ fmt.fracWidth + Model.fracField z = infMagnitude fmt ∧
          maxFinite fmt < infMagnitude fmt := by
      intro z hz
      have hflag := infFlag_eq z
      rw [hz] at hflag
      unfold infFlag at hflag
      simp only [Nat.add_eq, Nat.sub_eq, ite_true] at hflag
      refine ⟨by omega, ?_⟩
      have hencoding : fmt.encoding = .ieee := by
        by_contra hne
        rw [Model.isInfinite_eq_false_of_encoding_ne_ieee hne z] at hz
        exact absurd hz (by decide)
      have hMFE : fmt.maxFiniteExpField = 2 ^ fmt.expWidth - 2 := by
        simp [FloatFormat.maxFiniteExpField, FloatFormat.Encoding.maxFiniteExponent, hencoding]
      have hfrac := fmt.maxFiniteFracField_lt_two_pow
      have hfour := fmt.four_le_two_pow_expWidth
      unfold infMagnitude maxFinite
      simp only [hencoding, hMFE, FloatFormat.expAllOnesNat]
      have hexpand : (2 ^ fmt.expWidth - 1) * 2 ^ fmt.fracWidth =
          (2 ^ fmt.expWidth - 2) * 2 ^ fmt.fracWidth + 2 ^ fmt.fracWidth := by
        obtain ⟨k, hk⟩ : ∃ k, 2 ^ fmt.expWidth = k + 2 := ⟨2 ^ fmt.expWidth - 2, by omega⟩
        rw [hk]
        simp only [Nat.add_sub_cancel]
        rw [show k + 2 - 1 = k + 1 by omega]
        rw [add_mul]; ac_rfl
      omega
    have hfinite : ∀ z : Model fmt, Model.isNaN z = false → Model.isInfinite z = false →
        Model.expField z * 2 ^ fmt.fracWidth + Model.fracField z ≤ maxFinite fmt := by
      intro z hzn hzi
      have hfin := Model.isFinite_eq_true_of_isNaN_eq_false_of_isInfinite_eq_false z hzn hzi
      have hflag := nonFinite_eq_zero_of_isFinite z hfin
      unfold nonFinite at hflag
      simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq] at hflag
      omega
    by_cases hxInf : Model.isInfinite x = true
    · obtain ⟨hxu, hmax⟩ := hinfinity x hxInf
      by_cases hyInf : Model.isInfinite y = true
      · obtain ⟨hyu, -⟩ := hinfinity y hyInf
        simp only [Model.compareNonNaN, hxInf, hyInf, dite_true, ite_true]
        cases hsx : Model.signBit x <;> cases hsy : Model.signBit y <;>
          simp only [Bool.false_eq_true, ↓reduceIte, BEq.rfl, Std.LawfulEqCmp.compare_eq_iff_eq,
            Nat.add_left_cancel_iff, beq_true, compare_gt_iff_gt, gt_iff_lt, beq_false,
            Bool.not_true, compare_lt_iff_lt] <;> omega
      · have hyi : Model.isInfinite y = false := Bool.eq_false_of_not_eq_true hyInf
        have hyle := hfinite y hny hyi
        simp only [Model.compareNonNaN, hxInf, hyi, dite_true, Bool.false_eq_true, ite_false]
        cases hsx : Model.signBit x <;> cases hsy : Model.signBit y <;>
          simp only [Bool.false_eq_true, ↓reduceIte, compare_gt_iff_gt, add_lt_add_iff_left,
            gt_iff_lt, compare_lt_iff_lt] <;> omega
    · have hxi : Model.isInfinite x = false := Bool.eq_false_of_not_eq_true hxInf
      have hxle := hfinite x hnx hxi
      by_cases hyInf : Model.isInfinite y = true
      · obtain ⟨hyu, hmax⟩ := hinfinity y hyInf
        simp only [Model.compareNonNaN, hxi, hyInf, dite_true, Bool.false_eq_true, dite_false]
        cases hsx : Model.signBit x <;> cases hsy : Model.signBit y <;>
          simp only [Bool.false_eq_true, ↓reduceIte, compare_lt_iff_lt, add_lt_add_iff_left,
            gt_iff_lt, compare_gt_iff_gt] <;> omega
      · -- Two finite values: the exact comparison of the decoded dyadics.
        have hyi : Model.isInfinite y = false := Bool.eq_false_of_not_eq_true hyInf
        have hfinx := Model.isFinite_eq_true_of_isNaN_eq_false_of_isInfinite_eq_false x hnx hxi
        have hfiny := Model.isFinite_eq_true_of_isNaN_eq_false_of_isInfinite_eq_false y hny hyi
        obtain ⟨dx, hdx, hsx, hmx, hex⟩ := toDyadic?_of_isFinite x hfinx
        obtain ⟨dy, hdy, hsy, hmy, hey⟩ := toDyadic?_of_isFinite y hfiny
        have hcompare := Model.compare_eq_some_cmpDyadic_of_toDyadic? x y hdx hdy
        rw [Model.compare_eq_some_compareNonNaN x y hnx hny] at hcompare
        rw [Option.some.inj hcompare, Model.cmpDyadic_eq_cmpDyadicAligned,
          show Model.cmpDyadicAligned dx dy = Numerics.Dyadic.compare dx dy from rfl,
          Numerics.Dyadic.compare_eq_compare_toRat,
          toRat_of_fields dx _ (Model.expField x - 1) fmt.minSubnormalExponent hmx
            (fun h => hex (by rw [hmx]; exact h)),
          toRat_of_fields dy _ (Model.expField y - 1) fmt.minSubnormalExponent hmy
            (fun h => hey (by rw [hmy]; exact h)),
          hsx, hsy]
        have hdecx := decoded_significand_lt x
        have hdecy := decoded_significand_lt y
        rw [hsplit] at hdecx hdecy
        have hnormx : 1 ≤ Model.expField x - 1 → 2 ^ fmt.fracWidth ≤
            (if Model.expField x = 0 then Model.fracField x
              else 2 ^ fmt.fracWidth + Model.fracField x) := by
          intro h
          rw [ite_eq_right (by omega)]
          omega
        have hnormy : 1 ≤ Model.expField y - 1 → 2 ^ fmt.fracWidth ≤
            (if Model.expField y = 0 then Model.fracField y
              else 2 ^ fmt.fracWidth + Model.fracField y) := by
          intro h
          rw [ite_eq_right (by omega)]
          omega
        have hzero : ∀ (e f : Nat), (if e = 0 then f else 2 ^ fmt.fracWidth + f) * 2 ^ (e - 1) = 0 ↔
            e * 2 ^ fmt.fracWidth + f = 0 := by
          intro e f
          rw [Nat.mul_eq_zero]
          rcases e with _ | k
          · simp
          · have hk : (k + 1) * 2 ^ fmt.fracWidth = k * 2 ^ fmt.fracWidth + 2 ^ fmt.fracWidth := by
              rw [add_mul]; ac_rfl
            have hpow := Nat.two_pow_pos (k + 1 - 1)
            simp only [Nat.add_one_ne_zero, ite_false]
            omega
        symm
        refine compare_signed_eq_compare_keys _ _ _ _ (2 ^ signPos fmt) _ _ _
          (by positivity) (le_of_lt hux) (le_of_lt huy) ?_ ?_ (hzero _ _) (hzero _ _)
        · rw [magnitude_lt_iff hdecx hdecy hnormx hnormy,
            ← fields_eq_decoded, ← fields_eq_decoded]
        · rw [magnitude_lt_iff hdecy hdecx hnormy hnormx,
            ← fields_eq_decoded, ← fields_eq_decoded]

/-! ## Classification -/

/-- A flag that is zero or one equals one exactly when its Boolean is set. -/
theorem beq_flag (b : Bool) : Nat.beq (if b then 1 else 0) 1 = b := by
  cases b <;> rfl

/-- `nanCode` is one exactly on the NaNs. -/
theorem nanCode_eq {fmt : FloatFormat} (x : Model fmt) :
    Nat.beq (nanCode fmt x.toNatBits) 1 = Model.isNaN x := by
  unfold nanCode
  simp only [Nat.shiftRight_eq', Nat.land_eq, sign_toNatBits, magnitude_toNatBits, nanFlag_eq,
    beq_flag]

/-- `infCode` is one exactly on the infinities. -/
theorem infCode_eq {fmt : FloatFormat} (x : Model fmt) :
    Nat.beq (infCode fmt x.toNatBits) 1 = Model.isInfinite x := by
  unfold infCode
  simp only [Nat.land_eq, magnitude_toNatBits, infFlag_eq, beq_flag]

/-- `zeroCode` is one exactly on the zeros. -/
theorem zeroCode_eq {fmt : FloatFormat} (x : Model fmt) :
    Nat.beq (zeroCode fmt x.toNatBits) 1 = Model.isZero x := by
  unfold zeroCode
  simp only [Nat.shiftRight_eq', Nat.land_eq, sign_toNatBits, magnitude_toNatBits, zeroFlag_eq,
    beq_flag]

/-- `finiteCode` is one exactly on the finite words. -/
theorem finiteCode_eq {fmt : FloatFormat} (x : Model fmt) :
    Nat.beq (finiteCode fmt x.toNatBits) 1 = Model.isFinite x := by
  unfold finiteCode
  simp only [Nat.shiftRight_eq', Nat.land_eq, Nat.sub_eq, sign_toNatBits, magnitude_toNatBits]
  cases hfinite : Model.isFinite x
  · have hne : nonFinite fmt (if Model.signBit x then 1 else 0)
        (Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x) ≠ 0 := by
      intro hzero
      rw [isFinite_of_nonFinite_eq_zero x hzero] at hfinite
      exact absurd hfinite (by decide)
    have hsub : 1 - nonFinite fmt (if Model.signBit x then 1 else 0)
        (Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x) = 0 := by omega
    rw [hsub]
    rfl
  · rw [nonFinite_eq_zero_of_isFinite x hfinite]
    rfl

/-- `signCode` is the sign bit. -/
theorem signCode_eq {fmt : FloatFormat} (x : Model fmt) :
    Nat.beq (signCode fmt x.toNatBits) 1 = Model.signBit x := by
  unfold signCode
  simp only [Nat.shiftRight_eq', sign_toNatBits, beq_flag]

/-! ## The six comparison predicates as tests on the code -/

/-- A comparison is "less" exactly when its code is zero. -/
theorem decodeOrdering_beq_lt (code : Nat) :
    (decodeOrdering code == some Ordering.lt) = Nat.beq code 0 := by
  rcases code with _ | _ | _ | code <;> rfl

/-- A comparison is "equal" exactly when its code is one. -/
theorem decodeOrdering_beq_eq (code : Nat) :
    (decodeOrdering code == some Ordering.eq) = Nat.beq code 1 := by
  rcases code with _ | _ | _ | code <;> rfl

/-- A comparison is "greater" exactly when its code is two. -/
theorem decodeOrdering_beq_gt (code : Nat) :
    (decodeOrdering code == some Ordering.gt) = Nat.beq code 2 := by
  rcases code with _ | _ | _ | code <;> rfl

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
