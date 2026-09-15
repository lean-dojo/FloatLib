/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.WideLimb.Addition.Runtime
public import FloatLib.Floats.ExecFloat.Backends.WideLimb.Round.Proof
public import FloatLib.Floats.ExecFloat.Backends.WideLimb.Finite.Proof

/-!
# Verified wide-limb addition and subtraction

The central theorem is `alignOrdered?_refines`: an accepted result of the alignment core is the
unsigned-scale exact sum `FiniteScaleAdd.roundSum` of the two signed magnitudes. Its proof follows
the two routes of the kernel. On the jammed route the limb value of the combined significand is
`shiftRightJam` of the exact aligned sum or difference (`shiftRightJam_add_mul_two_pow`,
`shiftRightJam_mul_two_pow_sub`), and the exact value has enough bits above the jam for
`Round.Proof.roundNormal?_jammed`. On the exact route the limb value is the exact sum or difference
and `roundNormal?_exact` applies; equal magnitudes of opposite sign give positive zero as the
specification demands.

`addNormal?_refines` decodes two normal stored values into the core and identifies the result with
`FiniteKernel.add?`; `toModel_add` and `toModel_sub` finish with the reference operations.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb

open FloatLib.Numerics

variable {fmt : FloatFormat}

/-! ## Rounding helpers -/

/-- An accepted rounding of an exact significand is the exact rounder. -/
theorem roundNormal?_exact (hexp : fmt.expWidth ≤ 32) (sign : Bool) (S : LimbArray) (T scale : Nat)
    (hS : S.toNat = T) (hT : T ≠ 0) (r : Value fmt) (hr : roundNormal? fmt sign S 0 scale = some r) :
    toModel r = FiniteProductRound.round fmt sign T scale := by
  have hjammed := roundNormal?_map_toModel hexp sign S 0 scale (by rw [hS]; exact hT)
  rw [hr, Option.map_some, hS] at hjammed
  symm
  exact round_eq_of_roundJammed sign T 0 scale hT (Or.inl rfl) (toModel r)
    (by rw [shiftRightJam_zero]; exact hjammed.symm)

/-- An accepted rounding of a jammed significand is the exact rounder on the exact value. -/
theorem roundNormal?_jammed (hexp : fmt.expWidth ≤ 32) (sign : Bool) (S : LimbArray)
    (T jam scale : Nat) (hS : S.toNat = shiftRightJam T jam)
    (hbig : 2 ^ (fmt.fracWidth + jam + 2) ≤ T) (r : Value fmt)
    (hr : roundNormal? fmt sign S jam scale = some r) :
    toModel r = FiniteProductRound.round fmt sign T scale := by
  have hT : T ≠ 0 := by
    have := Nat.two_pow_pos (fmt.fracWidth + jam + 2)
    omega
  have hSne : S.toNat ≠ 0 := by
    rw [hS]
    exact shiftRightJam_ne_zero T jam
      (le_trans (Nat.pow_le_pow_right (by decide) (by omega)) hbig)
  have hjammed := roundNormal?_map_toModel hexp sign S jam scale hSne
  rw [hr, Option.map_some, hS] at hjammed
  symm
  exact round_eq_of_roundJammed sign T jam scale hT (Or.inr hbig) (toModel r) hjammed.symm

/-! ## The alignment core -/

/-- Positive zero from the packing kernel. -/
theorem toModel_pack_zero (hexp : fmt.expWidth ≤ 32) :
    toModel (pack fmt false 0 (LimbArray.zero 0)) = posZero fmt := by
  rw [toModel_pack_of_lt _ _ _ hexp (by simp) (by simp)]
  simp

/-- A zero with a false sign bit is positive zero. -/
theorem zero_false (fmt : FloatFormat) : zero fmt false = posZero fmt := by
  simp [zero]

/--
An accepted result of the ordered alignment core is the unsigned-scale exact sum of its operands.
-/
theorem alignOrdered?_refines (h : Eligible fmt) (roundOffset : Nat) (aSign : Bool) (a : LimbArray)
    (sa : Nat) (bSign : Bool) (b : LimbArray) (sb : Nat) (hsb : sb ≤ sa)
    (ha : 2 ^ fmt.fracWidth ≤ a.toNat) (hb : 2 ^ fmt.fracWidth ≤ b.toNat) (r : Value fmt)
    (hr : alignOrdered? fmt roundOffset aSign a sa bSign b sb = some r) :
    toModel r = FiniteScaleAdd.roundSum fmt roundOffset bSign aSign b.toNat sb a.toNat sa := by
  have hfpos : 0 < 2 ^ fmt.fracWidth := Nat.two_pow_pos _
  have haNe : a.toNat ≠ 0 := by omega
  have hbNe : b.toNat ≠ 0 := by omega
  have hla : fmt.fracWidth ≤ a.toNat.log2 := (Nat.le_log2 haNe).mpr ha
  have haLow := Nat.log2_self_le haNe
  have haHigh := Nat.lt_log2_self (n := a.toNat)
  have hbLow := Nat.log2_self_le hbNe
  have hbHigh := Nat.lt_log2_self (n := b.toNat)
  have hbNe' : (b.toNat == 0) = false := by simpa using hbNe
  have haNe' : (a.toNat == 0) = false := by simpa using haNe
  have hspec : FiniteScaleAdd.roundSum fmt roundOffset bSign aSign b.toNat sb a.toNat sa =
      FiniteScaleAdd.roundMagnitudes fmt roundOffset bSign aSign b.toNat
        (a.toNat * 2 ^ (sa - sb)) sb := by
    unfold FiniteScaleAdd.roundSum
    rw [if_neg (by simp [hbNe']), if_neg (by simp [haNe']), if_pos hsb, Nat.shiftLeft_eq]
  rw [hspec]
  unfold alignOrdered? at hr
  rw [LimbArray.log2_eq a haNe, LimbArray.log2_eq b hbNe] at hr
  dsimp only at hr
  set d := sa - sb with hd
  set la := a.toNat.log2 with hlaDef
  set lb := b.toNat.log2 with hlbDef
  have hAd : (a.shiftLeft d).toNat = a.toNat * 2 ^ d := LimbArray.toNat_shiftLeft _ _
  unfold FiniteScaleAdd.roundMagnitudes FiniteScaleAdd.roundMagnitude
  by_cases hjam : 3 ≤ d ∧ lb + 2 ≤ la + d
  · rw [if_pos hjam] at hr
    obtain ⟨hd3, hlb⟩ := hjam
    set jam := d - 3 with hjamDef
    have hpow : 2 ^ d = 8 * 2 ^ jam := by
      rw [show d = jam + 3 by omega, pow_add]
      ring
    have hA8 : (a.shiftLeft 3).toNat = a.toNat * 8 := by
      rw [LimbArray.toNat_shiftLeft]
      rfl
    have hBj : (b.shiftRight jam).toNat = b.toNat / 2 ^ jam := LimbArray.toNat_shiftRight _ _
    have hsticky : b.anyBelow jam = decide (b.toNat % 2 ^ jam ≠ 0) := LimbArray.anyBelow_eq _ _
    have hAd8 : a.toNat * 2 ^ d = a.toNat * 8 * 2 ^ jam := by
      rw [hpow]
      ring
    have hbig : 2 ^ (fmt.fracWidth + jam + 2) ≤ 2 ^ (la + d - 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hAdLow : 2 ^ (la + d) ≤ a.toNat * 2 ^ d := by
      rw [pow_add]
      exact Nat.mul_le_mul_right _ haLow
    have hBlt : b.toNat < 2 ^ (la + d - 1) :=
      lt_of_lt_of_le hbHigh (Nat.pow_le_pow_right (by decide) (by omega))
    have hpow2 : 2 ^ (la + d) = 2 * 2 ^ (la + d - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    by_cases hsign : (aSign == bSign) = true
    · rw [if_pos hsign] at hr
      have hsignEq : aSign = bSign := beq_iff_eq.mp hsign
      have hsizePos : 0 < ((a.shiftLeft 3).add (b.shiftRight jam) 0).size := by
        simp
      have hS : (((a.shiftLeft 3).add (b.shiftRight jam)).orLowBit (b.anyBelow jam)).toNat =
          shiftRightJam (a.toNat * 2 ^ d + b.toNat) jam := by
        rw [hAd8, shiftRightJam_add_mul_two_pow, LimbArray.toNat_orLowBit _ hsizePos,
          LimbArray.toNat_add, hA8, hBj, hsticky, UInt32.toNat_zero, Nat.add_zero]
        by_cases hz : b.toNat % 2 ^ jam = 0
        · simp [hz]
        · simp [hz]
      have hTbig : 2 ^ (fmt.fracWidth + jam + 2) ≤ a.toNat * 2 ^ d + b.toNat := by omega
      have hround := roundNormal?_jammed h.exp_le aSign _ (a.toNat * 2 ^ d + b.toNat) jam
        (sb + roundOffset) hS hTbig r hr
      rw [hround, hsignEq, if_pos (by simp), Nat.add_comm]
    · rw [if_neg hsign] at hr
      have hsignNe : aSign ≠ bSign := fun heq => hsign (beq_iff_eq.mpr heq)
      have hBle : b.toNat ≤ a.toNat * 8 * 2 ^ jam := by
        rw [← hAd8]
        omega
      have hquot : b.toNat / 2 ^ jam < 2 ^ (la + 2) := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos jam), ← pow_add,
          show la + 2 + jam = la + d - 1 by omega]
        exact hBlt
      have hA4 : 2 ^ (la + 2) ≤ a.toNat * 4 := by
        rw [pow_add]
        exact Nat.mul_le_mul_right _ haLow
      have hborrowLe : b.toNat / 2 ^ jam + 1 ≤ a.toNat * 8 := by omega
      set borrow : UInt32 := if b.anyBelow jam then 1 else 0 with hborrowDef
      have hborrow : borrow.toNat = if b.toNat % 2 ^ jam = 0 then 0 else 1 := by
        rw [hborrowDef, hsticky]
        by_cases hz : b.toNat % 2 ^ jam = 0
        · simp [hz]
        · simp [hz]
      have hborrowLe1 : borrow.toNat ≤ 1 := by
        rw [hborrow]
        split <;> omega
      have hsubLe : (b.shiftRight jam).toNat + borrow.toNat ≤ (a.shiftLeft 3).toNat := by
        rw [hBj, hA8]
        omega
      have hsizePos : 0 < ((a.shiftLeft 3).sub (b.shiftRight jam) borrow).size := by
        simp
      have hS : (((a.shiftLeft 3).sub (b.shiftRight jam) borrow).orLowBit (b.anyBelow jam)).toNat =
          shiftRightJam (a.toNat * 2 ^ d - b.toNat) jam := by
        rw [hAd8, shiftRightJam_mul_two_pow_sub _ _ _ hBle, LimbArray.toNat_orLowBit _ hsizePos,
          LimbArray.toNat_sub _ _ _ hborrowLe1 hsubLe, hA8, hBj, hborrow, hsticky]
        by_cases hz : b.toNat % 2 ^ jam = 0
        · simp [hz]
        · simp [hz]
      have hTbig : 2 ^ (fmt.fracWidth + jam + 2) ≤ a.toNat * 2 ^ d - b.toNat := by omega
      have hround := roundNormal?_jammed h.exp_le aSign _ (a.toNat * 2 ^ d - b.toNat) jam
        (sb + roundOffset) hS hTbig r hr
      have hlt : b.toNat < a.toNat * 2 ^ d := by omega
      rw [hround, if_neg (by simpa using hsignNe.symm), if_neg (by simp; omega), if_pos hlt]
  · rw [if_neg hjam] at hr
    by_cases hsign : (aSign == bSign) = true
    · rw [if_pos hsign] at hr
      have hsignEq : aSign = bSign := beq_iff_eq.mp hsign
      have hS : ((a.shiftLeft d).add b).toNat = a.toNat * 2 ^ d + b.toNat := by
        rw [LimbArray.toNat_add, hAd, UInt32.toNat_zero, Nat.add_zero]
      have hround := roundNormal?_exact h.exp_le aSign _ _ (sb + roundOffset) hS (by omega) r hr
      rw [hround, hsignEq, if_pos (by simp), Nat.add_comm]
    · rw [if_neg hsign] at hr
      have hsignNe : aSign ≠ bSign := fun heq => hsign (beq_iff_eq.mpr heq)
      have hcmp := LimbArray.compare_eq (a.shiftLeft d) b
      rw [hAd] at hcmp
      rw [if_neg (by simpa using hsignNe.symm)]
      cases hord : (a.shiftLeft d).compare b with
      | eq =>
          rw [hord] at hcmp
          have heq : a.toNat * 2 ^ d = b.toNat := Nat.compare_eq_eq.mp hcmp.symm
          simp only [hord, Option.some.injEq] at hr
          have hzeroSign : (bSign && aSign) = false := by
            apply Bool.eq_false_iff.mpr
            intro hboth
            obtain ⟨hb, ha⟩ := Bool.and_eq_true_iff.mp hboth
            exact hsignNe (ha.trans hb.symm)
          rw [← hr, toModel_pack_zero h.exp_le, if_pos (by simp [heq]), hzeroSign,
            zero_false]
      | gt =>
          rw [hord] at hcmp
          have hgt : b.toNat < a.toNat * 2 ^ d := Nat.compare_eq_gt.mp hcmp.symm
          simp only [hord] at hr
          have hS : ((a.shiftLeft d).sub b).toNat = a.toNat * 2 ^ d - b.toNat := by
            rw [LimbArray.toNat_sub _ _ _ (by simp) (by rw [hAd]; simp; omega), hAd,
              UInt32.toNat_zero, Nat.sub_zero]
          have hround := roundNormal?_exact h.exp_le aSign _ _ (sb + roundOffset) hS (by omega) r hr
          rw [hround, if_neg (by simp; omega), if_pos hgt]
      | lt =>
          rw [hord] at hcmp
          have hlt : a.toNat * 2 ^ d < b.toNat := Nat.compare_eq_lt.mp hcmp.symm
          simp only [hord] at hr
          have hS : (b.sub (a.shiftLeft d)).toNat = b.toNat - a.toNat * 2 ^ d := by
            rw [LimbArray.toNat_sub _ _ _ (by simp) (by rw [hAd]; simp; omega), hAd,
              UInt32.toNat_zero, Nat.sub_zero]
          have hround := roundNormal?_exact h.exp_le bSign _ _ (sb + roundOffset) hS (by omega) r hr
          rw [hround, if_neg (by simp; omega), if_neg (by omega)]

/-- An accepted result of the alignment core is the unsigned-scale exact sum of its operands. -/
theorem alignAndRound?_refines (h : Eligible fmt) (roundOffset : Nat) (aSign : Bool) (a : LimbArray)
    (sa : Nat) (bSign : Bool) (b : LimbArray) (sb : Nat)
    (ha : 2 ^ fmt.fracWidth ≤ a.toNat) (hb : 2 ^ fmt.fracWidth ≤ b.toNat) (r : Value fmt)
    (hr : alignAndRound? fmt roundOffset aSign a sa bSign b sb = some r) :
    toModel r = FiniteScaleAdd.roundSum fmt roundOffset aSign bSign a.toNat sa b.toNat sb := by
  unfold alignAndRound? at hr
  by_cases hlt : sa < sb
  · rw [if_pos hlt] at hr
    exact alignOrdered?_refines h roundOffset bSign b sb aSign a sa (Nat.le_of_lt hlt) hb ha r hr
  · rw [if_neg hlt] at hr
    rw [alignOrdered?_refines h roundOffset aSign a sa bSign b sb (Nat.le_of_not_lt hlt) ha hb r hr]
    exact roundSum_comm h.isIEEE roundOffset bSign aSign b.toNat sb a.toNat sa

/-! ## Addition and subtraction of stored values -/

/-- The decoded components of a normal stored value. -/
theorem decode?_normal (h : Eligible fmt) (v : Value fmt)
    (hfinite : expField v ≠ fmt.expAllOnesNat) (hnormal : expField v ≠ 0) :
    FiniteKernel.decode? (toModel v) =
      some ⟨signBit v, expField v, (normalMantissa v).toNat⟩ := by
  rw [decode?_toModel v h.isIEEE h.exp_le hfinite, decodeMantissa_eq_normalMantissa v hnormal]

/-- The decoded components of a normal stored value, possibly negated. -/
theorem decode?_signed (h : Eligible fmt) (negate : Bool) (v : Value fmt)
    (hfinite : expField v ≠ fmt.expAllOnesNat) (hnormal : expField v ≠ 0) :
    FiniteKernel.decode? (if negate then neg (toModel v) else toModel v) =
      some ⟨Bool.xor (signBit v) negate, expField v, (normalMantissa v).toNat⟩ := by
  cases negate
  · simp only [Bool.false_eq_true, if_false, Bool.xor_false]
    rw [decode?_toModel v h.isIEEE h.exp_le hfinite, decodeMantissa_eq_normalMantissa v hnormal]
  · simp only [if_true, Bool.xor_true]
    rw [decode?_neg h.isIEEE, decode?_toModel v h.isIEEE h.exp_le hfinite,
      decodeMantissa_eq_normalMantissa v hnormal, Option.map_some]

/-- An accepted normal sum is the compact finite addition of the operand models. -/
theorem addNormal?_refines (h : Eligible fmt) (negateY : Bool) (x y r : Value fmt)
    (hr : addNormal? fmt negateY x y = some r) :
    FiniteKernel.add? (toModel x) (if negateY then neg (toModel y) else toModel y) =
      some (toModel r) := by
  unfold addNormal? at hr
  by_cases hcond : (expWord x == 0 || expWord x == expAllOnes fmt ||
      expWord y == 0 || expWord y == expAllOnes fmt) = true
  · rw [if_pos hcond] at hr
    exact absurd hr (by simp)
  · rw [if_neg hcond] at hr
    simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hcond
    obtain ⟨⟨⟨hx0, hxAll⟩, hy0⟩, hyAll⟩ := hcond
    obtain ⟨hxe0, hxeFinite⟩ := normalExponent_of_expWord h x hx0 hxAll
    obtain ⟨hye0, hyeFinite⟩ := normalExponent_of_expWord h y hy0 hyAll
    have hxBounds := normalMantissa_bounds x
    have hyBounds := normalMantissa_bounds y
    have hsum := alignAndRound?_refines h (FiniteKernel.finiteScaleOffset fmt) (signBit x)
      (normalMantissa x) ((expWord x).toNat - 1) (Bool.xor (signBit y) negateY) (normalMantissa y)
      ((expWord y).toNat - 1) hxBounds.1 hyBounds.1 r hr
    unfold FiniteKernel.add?
    rw [decode?_normal h x hxeFinite hxe0, decode?_signed h negateY y hyeFinite hye0]
    simp only [Option.some.injEq]
    rw [← FiniteKernel.addComponentsImpl_eq]
    unfold FiniteKernel.addComponentsImpl
    rw [if_pos h.isIEEE, hsum]
    have hxe0' : (expField x == 0) = false := by simpa using hxe0
    have hye0' : (expField y == 0) = false := by simpa using hye0
    simp only [FiniteKernel.scale, hxe0', hye0', Bool.false_eq_true, if_false]
    rfl

/-- Wide-limb addition is the reference addition of the operand models. -/
theorem toModel_add (h : Eligible fmt) (x y : Value fmt) :
    toModel (add fmt x y) = Spec.add (toModel x) (toModel y) := by
  unfold add
  cases hfast : addNormal? fmt false x y with
  | none =>
      simp only
      rw [toModel_ofModel]
  | some r =>
      simp only
      have hadd := addNormal?_refines h false x y r hfast
      simp only [Bool.false_eq_true, if_false] at hadd
      exact (spec_add_of_add?_eq_some _ _ _ hadd).symm

/-- Wide-limb subtraction is the reference subtraction of the operand models. -/
theorem toModel_sub (h : Eligible fmt) (x y : Value fmt) :
    toModel (sub fmt x y) = Spec.sub (toModel x) (toModel y) := by
  unfold sub
  cases hfast : addNormal? fmt true x y with
  | none =>
      simp only
      rw [toModel_ofModel]
  | some r =>
      simp only
      have hadd := addNormal?_refines h true x y r hfast
      simp only [if_true] at hadd
      exact (spec_add_of_add?_eq_some _ _ _ hadd).symm

end FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb
