/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Div
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.OperationStatus
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.RationalStatus

import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Order

/-!
# Kernel path: the IEEE status of division

`divStatus fmt mode a b` is the status number of the quotient of the values encoded by `a` and
`b`: the five exception flags and the ternary value of
`Model.div x y (mode := mode) (status := true)`.

For two finite operands and a nonzero divisor the exact quotient is a rational number. Its
status is the status of its sticky dyadic (`RationalStatus.lean`): the floor of the quotient in
units of a quarter of the least subnormal number, doubled, plus one when a remainder is left.
One division of two shifted significands gives that floor and that remainder, and `roundStatus`
gives the flags and the ternary value from the sticky dyadic and the delivered word.

A nonzero finite value divided by zero raises divide by zero, with the ternary value of the
delivered word against the exact infinity. Zero divided by zero and an infinity divided by an
infinity are invalid, and so is a signaling NaN. `divStatus_eq` holds for every format
descriptor, every rounding direction and all operands.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

/--
The status number of a nonzero finite value divided by zero: the divide-by-zero flag, and the
ternary value of the delivered word `w` against the exact infinity of the sign `sign`
(`infinityTernary`).
-/
def divideByZeroStatus (fmt : FloatFormat) (sign w : Nat) : Nat :=
  Nat.add 2 (Nat.mul 32 (infinityTernary fmt sign w))

/--
The status number of the quotient of the values encoded by `a` and `b`, rounded in the direction
`mode`, when `w` is the word of the rounded quotient. `divStatus` is this number at
`div fmt mode a b`.
-/
def divStatusWith (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b w : Nat) : Nat :=
  (fun sa sb ua ub =>
    Bool.casesOn (motive := fun _ => Nat)
      (Nat.beq (Nat.add (nonFinite fmt sa ua) (nonFinite fmt sb ub)) 0)
      ((fun infA infB nanA nanB =>
          invalidStatus
            (Nat.add
              (Nat.add (Nat.mul nanA (signalingFlag fmt a)) (Nat.mul nanB (signalingFlag fmt b)))
              (Nat.mul (Nat.sub 1 (Nat.add nanA nanB)) (Nat.mul infA infB))))
        (infFlag fmt ua) (infFlag fmt ub) (nanFlag fmt sa ua) (nanFlag fmt sb ub))
      ((fun ha hb =>
          (fun ma mb =>
            Bool.casesOn (motive := fun _ => Nat) (Nat.beq mb 0)
              ((fun K =>
                  (fun num den =>
                    roundStatus fmt mode (Nat.xor sa sb)
                      (Nat.add (Nat.mul 2 (Nat.div num den))
                        (Nat.sub 1 (Nat.sub 1 (Nat.mod num den))))
                      1 w)
                    (Nat.shiftLeft ma (Nat.sub K hb)) (Nat.shiftLeft mb (Nat.sub hb K)))
                (Nat.add (Nat.add ha fmt.exponentBias) (Nat.add fmt.fracWidth 1)))
              (Bool.casesOn (motive := fun _ => Nat) (Nat.beq ma 0)
                (divideByZeroStatus fmt (Nat.xor sa sb) w)
                (invalidStatus 1)))
            (Nat.sub ua (Nat.shiftLeft ha fmt.fracWidth))
            (Nat.sub ub (Nat.shiftLeft hb fmt.fracWidth)))
        (Nat.sub (Nat.shiftRight ua fmt.fracWidth) 1)
        (Nat.sub (Nat.shiftRight ub fmt.fracWidth) 1)))
    (Nat.shiftRight a (signPos fmt)) (Nat.shiftRight b (signPos fmt))
    (Nat.land a (magnitudeMask fmt)) (Nat.land b (magnitudeMask fmt))

/--
The status number of the quotient of the values encoded by `a` and `b`, rounded in the direction
`mode` (`divStatus_eq`). See the module documentation.
-/
def divStatus (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b : Nat) : Nat :=
  divStatusWith fmt mode a b (div fmt mode a b)

/-! ## The sticky quotient of two significands -/

/--
The floor and the remainder of one division of shifted significands are the sticky pair of the
exact quotient `(ma / mb) * 2 ^ (ha - hb)` in units of `2 ^ (minSubnormalExponent - 2)`.
-/
theorem sticky_quotient (fmt : FloatFormat) (ma mb ha hb : Nat) (hmb : mb ≠ 0) :
    Sticky (Model.scaledRatToReal ma mb ((ha : Int) - (hb : Int)))
      ((2 : ℝ) ^ (fmt.minSubnormalExponent - 2))
      ((ma <<< (ha + fmt.exponentBias + (fmt.fracWidth + 1) - hb)) /
        (mb <<< (hb - (ha + fmt.exponentBias + (fmt.fracWidth + 1)))))
      (1 - (1 - (ma <<< (ha + fmt.exponentBias + (fmt.fracWidth + 1) - hb)) %
        (mb <<< (hb - (ha + fmt.exponentBias + (fmt.fracWidth + 1)))))) := by
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  generalize hA : ha + fmt.exponentBias + (fmt.fracWidth + 1) - hb = A
  generalize hB : hb - (ha + fmt.exponentBias + (fmt.fracWidth + 1)) = B
  have hden : 0 < mb <<< B := by
    rw [Nat.shiftLeft_eq]
    exact Nat.mul_pos (Nat.pos_of_ne_zero hmb) (Nat.two_pow_pos _)
  have hdenR : (0 : ℝ) < ((mb <<< B : ℕ) : ℝ) := by exact_mod_cast hden
  have hu : (0 : ℝ) < (2 : ℝ) ^ (fmt.minSubnormalExponent - 2) := zpow_pos (by norm_num) _
  -- The exact quotient is the ratio of the shifted significands in these units.
  have hx : Model.scaledRatToReal ma mb ((ha : Int) - (hb : Int)) =
      ((ma <<< A : ℕ) : ℝ) / ((mb <<< B : ℕ) : ℝ) *
        (2 : ℝ) ^ (fmt.minSubnormalExponent - 2) := by
    have hmbR : (mb : ℝ) ≠ 0 := by exact_mod_cast hmb
    have hexp : (ha : Int) - (hb : Int) =
        (A : Int) - (B : Int) + (fmt.minSubnormalExponent - 2) := by
      simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
        Int.ofNat_eq_natCast]
      omega
    simp only [Model.scaledRatToReal, bpow_eq_zpow]
    rw [hexp, zpow_add₀ htwo, zpow_sub₀ htwo, zpow_natCast, zpow_natCast, Nat.shiftLeft_eq,
      Nat.shiftLeft_eq]
    push_cast
    field_simp
  generalize ma <<< A = num at hx ⊢
  generalize mb <<< B = den at hx hden hdenR ⊢
  have hfloor : num / den * den ≤ num := Nat.div_mul_le_self num den
  have hceil : num < (num / den + 1) * den := by
    have := Nat.div_add_mod num den
    have hmod := Nat.mod_lt num hden
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hx]
    apply mul_le_mul_of_nonneg_right _ hu.le
    rw [le_div_iff₀ hdenR]
    exact_mod_cast hfloor
  · rw [hx]
    apply mul_lt_mul_of_pos_right _ hu
    rw [div_lt_iff₀ hdenR]
    exact_mod_cast hceil
  · by_cases hrem : num % den = 0
    · left
      refine ⟨by rw [hrem], ?_⟩
      have hexact : num = num / den * den := by
        have := Nat.div_add_mod num den
        rw [hrem, Nat.add_zero, Nat.mul_comm] at this
        exact this.symm
      rw [hx]
      congr 1
      rw [div_eq_iff hdenR.ne']
      exact_mod_cast hexact
    · right
      refine ⟨by omega, ?_⟩
      intro hEq
      rw [hx] at hEq
      have hq : ((num : ℝ) / (den : ℝ)) = ((num / den : ℕ) : ℝ) :=
        mul_right_cancel₀ hu.ne' hEq
      rw [div_eq_iff hdenR.ne'] at hq
      have hnat : num = num / den * den := by exact_mod_cast hq
      have := Nat.div_add_mod num den
      rw [Nat.mul_comm] at this
      omega

/-! ## Correctness -/

/--
`divideByZeroStatus` decodes to the divide-by-zero flag and the ternary value of the delivered
value against the exact infinity.
-/
theorem divideByZeroStatus_eq {fmt : FloatFormat} (negative : Bool) (value : Model fmt) :
    decodeStatus (divideByZeroStatus fmt (if negative then 1 else 0) value.toNatBits) =
        { divideByZero := true } ∧
      decodeTernary (divideByZeroStatus fmt (if negative then 1 else 0) value.toNatBits) =
        Model.exactInfinityTernary negative value := by
  unfold divideByZeroStatus infinityTernary Model.exactInfinityTernary
  simp only [Nat.shiftRight_eq', Nat.land_eq, Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.xor_eq,
    sign_toNatBits, magnitude_toNatBits, infFlag_eq]
  cases Model.isInfinite value <;> cases Model.signBit value <;> cases negative <;>
    exact ⟨by decide +kernel, by decide +kernel⟩

/--
`divStatus` computes the flags and the ternary value of the reference division
`Model.div x y (mode := mode) (status := true)`, for every format descriptor, every rounding
direction and all operands.
-/
theorem divStatus_eq {fmt : FloatFormat} (mode : Model.IEEERoundingMode) (x y : Model fmt) :
    decodeStatus (divStatus fmt mode x.toNatBits y.toNatBits) =
        (Model.div x y (mode := mode) (status := true)).status ∧
      decodeTernary (divStatus fmt mode x.toNatBits y.toNatBits) =
        (Model.div x y (mode := mode) (status := true)).ternary := by
  have hfx := Model.fracField_lt_pow2 x
  have hfy := Model.fracField_lt_pow2 y
  have hresult : div fmt mode x.toNatBits y.toNatBits =
      (Model.div x y (mode := mode)).toNatBits := div_eq_spec mode x y
  unfold divStatus divStatusWith
  simp only [Nat.shiftRight_eq', Nat.land_eq, Nat.shiftLeft_eq', Nat.sub_eq, Nat.add_eq,
    Nat.mul_eq, Nat.xor_eq, div_def, mod_def, sign_toNatBits, magnitude_toNatBits,
    fields_shiftRight _ _ _ hfx, fields_shiftRight _ _ _ hfy, fields_sub_shiftLeft, xor_sign,
    infFlag_eq, nanFlag_eq, nanFlag_mul_signalingFlag, hresult]
  by_cases hfinite : Model.isFinite x = true ∧ Model.isFinite y = true
  · obtain ⟨hfinx, hfiny⟩ := hfinite
    obtain ⟨dx, hdx, hnx, hsx, hex⟩ := toDyadic?_of_isFinite x hfinx
    obtain ⟨dy, hdy, hny, hsy, hey⟩ := toDyadic?_of_isFinite y hfiny
    rw [nonFinite_eq_zero_of_isFinite x hfinx, nonFinite_eq_zero_of_isFinite y hfiny,
      show Nat.beq (0 + 0) 0 = true from rfl, ← hsx, ← hsy, ← hnx, ← hny]
    by_cases hy0 : dy.significand = 0
    · rw [hy0, show Nat.beq 0 0 = true from rfl]
      by_cases hx0 : dx.significand = 0
      · rw [hx0, show Nat.beq 0 0 = true from rfl]
        have hstatus : Model.div x y (mode := mode) (status := true) =
            Model.outcomeWithInvalid (Model.invalidResult fmt) true := by
          rw [← Model.Internal.Status.div_eq]
          unfold Model.Internal.Status.div
          simp [hdx, hdy, hx0, hy0]
        rw [hstatus]
        exact invalidStatus_eq _ _ _ (by decide)
      · rw [beq_zero_of_ne hx0]
        have hvalue : Model.div x y (mode := mode) =
            Model.nativeOverflow fmt (Bool.xor dx.negative dy.negative) := by
          rw [div_of_finite mode x y dx dy hdx hdy]
          simp [hy0, hx0]
        have hstatus : Model.div x y (mode := mode) (status := true) =
            { value := Model.nativeOverflow fmt (Bool.xor dx.negative dy.negative)
              status := { divideByZero := true }
              ternary := Model.exactInfinityTernary (Bool.xor dx.negative dy.negative)
                (Model.nativeOverflow fmt (Bool.xor dx.negative dy.negative)) } := by
          rw [← Model.Internal.Status.div_eq]
          unfold Model.Internal.Status.div
          simp [hdx, hdy, hx0, hy0]
        rw [hstatus, hvalue]
        exact divideByZeroStatus_eq _ _
    · rw [beq_zero_of_ne hy0]
      -- The quotient of two finite values with a nonzero divisor.
      have houtcome := Model.div_status_of_toDyadic_nonzero mode hdx hdy hy0
      have hvalueEq : Model.Internal.Directed.roundRatScaled fmt mode
            (Bool.xor dx.negative dy.negative) dx.significand dy.significand
            (dx.exponent - dy.exponent) = Model.div x y (mode := mode) := by
        have h := congrArg (fun outcome => outcome.value) houtcome
        dsimp only at h
        rw [Model.value_div] at h
        exact h.symm
      rw [houtcome]
      dsimp only
      rw [hvalueEq]
      have hpos : ∀ exponent : Int, dx.significand ≠ 0 →
          0 < Model.scaledRatToReal dx.significand dy.significand exponent := by
        intro exponent hx0
        unfold Model.scaledRatToReal
        have h1 : (0 : ℝ) < (dx.significand : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hx0
        have h2 : (0 : ℝ) < (dy.significand : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hy0
        exact mul_pos (div_pos h1 h2) (Model.bpow_pos exponent)
      have hsticky := sticky_quotient fmt dx.significand dy.significand (Model.expField x - 1)
        (Model.expField y - 1) hy0
      have hexponent : Model.scaledRatToReal dx.significand dy.significand
            (((Model.expField x - 1 : Nat) : Int) - ((Model.expField y - 1 : Nat) : Int)) =
          Model.scaledRatToReal dx.significand dy.significand (dx.exponent - dy.exponent) := by
        by_cases hx0 : dx.significand = 0
        · simp [Model.scaledRatToReal, hx0]
        · rw [hex hx0, hey hy0]
          congr 1
          omega
      rw [hexponent] at hsticky
      rw [rationalRoundingStatusScaled_sticky fmt mode _ _ _ _ _ _ hy0 hsticky,
        rationalTernaryScaled_sticky fmt _ _ _ _ _ _ hy0 hsticky]
      refine roundStatus_eq fmt mode _ (if Bool.xor dx.negative dy.negative then 1 else 0) _ 1
        (by split <;> omega) ?_ _ ?_
      · rw [toRat_mk]
        congr 1
        · cases Bool.xor dx.negative dy.negative <;> simp
        · congr 1
          push_cast
          omega
      · intro hE
        by_cases hx0 : dx.significand = 0
        · rw [div_of_finite mode x y dx dy hdx hdy, ite_eq_right hy0, ite_eq_left hx0]
          exact Model.isFinite_eq_true_of_isZero_eq_true _ (Model.isZero_zero fmt _)
        · exfalso
          obtain ⟨_, -, hbit⟩ := hsticky
          have hx := hpos (dx.exponent - dy.exponent) hx0
          rcases hbit with ⟨-, hEq⟩ | ⟨hs, -⟩
          · have hq : (dx.significand <<<
                (Model.expField x - 1 + fmt.exponentBias + (fmt.fracWidth + 1) -
                  (Model.expField y - 1))) /
                (dy.significand <<< (Model.expField y - 1 -
                  (Model.expField x - 1 + fmt.exponentBias + (fmt.fracWidth + 1)))) = 0 := by
              omega
            rw [hq, Nat.cast_zero, zero_mul] at hEq
            order
          · omega
  · have hguard : nonFinite fmt (if Model.signBit x then 1 else 0)
          (Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x) +
        nonFinite fmt (if Model.signBit y then 1 else 0)
          (Model.expField y * 2 ^ fmt.fracWidth + Model.fracField y) ≠ 0 := by
      intro h
      obtain ⟨h1, h2⟩ := Nat.eq_zero_of_add_eq_zero h
      exact hfinite ⟨isFinite_of_nonFinite_eq_zero x h1, isFinite_of_nonFinite_eq_zero y h2⟩
    rw [beq_zero_of_ne hguard]
    have hstatus : Model.div x y (mode := mode) (status := true) =
        Model.outcomeWithInvalid (Model.Internal.Directed.div mode x y)
          (Model.isSignaling x || Model.isSignaling y ||
            (!(Model.isNaN x || Model.isNaN y) && (Model.isInfinite x && Model.isInfinite y))) := by
      rw [← Model.Internal.Status.div_eq]
      unfold Model.Internal.Status.div
      cases hdx : Model.toDyadic? x <;> cases hdy : Model.toDyadic? y
      · rfl
      · rfl
      · rfl
      · exact absurd ⟨isFinite_of_toDyadic? hdx, isFinite_of_toDyadic? hdy⟩ hfinite
    rw [hstatus]
    refine invalidStatus_eq _ _ _ ?_
    cases Model.isSignaling x <;> cases Model.isSignaling y <;> cases Model.isNaN x <;>
      cases Model.isNaN y <;> cases Model.isInfinite x <;> cases Model.isInfinite y <;> decide

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
