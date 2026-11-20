/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.OperationStatus
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Sqrt

import Mathlib.Tactic.Positivity

/-!
# Kernel path: the IEEE status of the square root

`sqrtStatus fmt mode a` is the status number of the square root of the value encoded by `a`: the
five exception flags and the ternary value of `Model.sqrt x (mode := mode) (status := true)`.

For a finite positive nonzero operand in a format with `fracWidth + 1 < exponentBias` the root
is a normal number, so it never underflows, and the checked integer root of `Sqrt.lean` decides
the rest. The result is inexact exactly when the scaled significand is not a square, and then the
ternary value says whether the delivered root is the integer root (less) or its successor
(greater): the reference compares the square of the delivered root with the operand
(`Model.dyadicSqrtTernary`), which on the naturals of the checked path is the comparison of
`(r + up) * (r + up)` with the scaled significand.

A NaN raises invalid when it is signaling, a negative nonzero operand raises invalid, and the
zeros and the positive infinity raise nothing (`sqrtStatusSpecial`). A format with a smaller bias
and a root that fails its check take the status of the reference square root, encoded by
`statusCode`, so `sqrtStatus_eq` holds for every descriptor, every rounding direction and every
operand.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

/--
The status number of the reference square root of the value encoded by `a`, which the kernel
evaluates when the checked path is left.
-/
def sqrtStatusReference (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a : Nat) : Nat :=
  (fun outcome => statusCode outcome.status outcome.ternary)
    (Model.Internal.Status.sqrt (Model.ofNatBits (fmt := fmt) a) mode)

/--
The status number of the square root of a word outside the checked path: invalid for a signaling
NaN and for a negative nonzero value, nothing for a quiet NaN, a zero and the positive infinity.
A positive finite nonzero value takes `sqrtStatusReference`.
-/
def sqrtStatusSpecial (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a : Nat) : Nat :=
  (fun s u =>
    Bool.casesOn (motive := fun _ => Nat) (Nat.beq (nanFlag fmt s u) 0)
      (invalidStatus (signalingFlag fmt a))
      (Bool.casesOn (motive := fun _ => Nat)
        (Nat.beq (Nat.add (Nat.add s (infFlag fmt u)) (zeroFlag fmt s u)) 0)
        (invalidStatus (Nat.mul s (Nat.sub 1 (zeroFlag fmt s u))))
        (sqrtStatusReference fmt mode a)))
    (Nat.shiftRight a (signPos fmt)) (Nat.land a (magnitudeMask fmt))

/--
The status number of a root that is a normal number: inexact when the remainder `rem` of the
integer root is not zero, with the ternary value equal for a zero remainder and otherwise less or
greater as the root stays or rounds up (`up` is zero or one, and zero for a zero remainder).
-/
def rootStatus (rem up : Nat) : Nat :=
  (fun inexact =>
    Nat.add (Nat.mul 16 inexact) (Nat.mul 32 (Nat.add (Nat.sub 1 inexact) (Nat.mul 2 up))))
    (Nat.sub 1 (Nat.sub 1 rem))

/--
The status number of the square root of the scaled significand `N`: `special` unless `guard` is
zero and the Newton root passes its check.
-/
def sqrtStatusCore (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (N guard special : Nat) :
    Nat :=
  (fun x =>
    (fun r =>
      Bool.casesOn (motive := fun _ => Nat)
        (Nat.beq
          (Nat.add guard
            (Nat.add (Nat.sub (Nat.mul r r) N)
              (Nat.sub (Nat.succ N) (Nat.mul (Nat.succ r) (Nat.succ r)))))
          0)
        special
        ((fun rem => rootStatus rem (rootUp mode r rem)) (Nat.sub N (Nat.mul r r))))
      (Nat.sub x (Nat.sub 1 (Nat.sub 1 (Nat.sub (Nat.mul x x) N)))))
    (newtonRoot fmt N)

/--
The status number of the square root of the value encoded by `a`, rounded in the direction
`mode` (`sqrtStatus_eq`). See the module documentation.
-/
def sqrtStatus (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a : Nat) : Nat :=
  (fun s u =>
    (fun h =>
      (fun m =>
        (fun L =>
          (fun num =>
            sqrtStatusCore fmt mode
              (Nat.shiftLeft m
                (Nat.sub (Nat.add (Nat.land num 1) (Nat.succ (Nat.mul 2 fmt.fracWidth))) L))
              (Nat.add
                (Nat.add (Nat.add (nonFinite fmt s u) s)
                  (Nat.add (Nat.sub 1 m)
                    (Nat.sub (Nat.add fmt.fracWidth 2) fmt.exponentBias)))
                (Nat.sub (Nat.succ (Nat.shiftRight num 1)) fmt.maxFiniteExpField))
              (sqrtStatusSpecial fmt mode a))
            (Nat.add (Nat.add L h) (Nat.sub fmt.exponentBias fmt.fracWidth)))
          (significandLength fmt.fracWidth m))
        (Nat.sub u (Nat.shiftLeft h fmt.fracWidth)))
      (Nat.sub (Nat.shiftRight u fmt.fracWidth) 1))
    (Nat.shiftRight a (signPos fmt)) (Nat.land a (magnitudeMask fmt))

/-! ## The reference status -/

/-- `sqrtStatusReference` is the status of the reference square root. -/
theorem sqrtStatusReference_eq {fmt : FloatFormat} (mode : Model.IEEERoundingMode)
    (x : Model fmt) :
    decodeStatus (sqrtStatusReference fmt mode x.toNatBits) =
        (Model.Internal.Status.sqrt x mode).status ∧
      decodeTernary (sqrtStatusReference fmt mode x.toNatBits) =
        (Model.Internal.Status.sqrt x mode).ternary := by
  unfold sqrtStatusReference
  rw [Model.ofNatBits_toNatBits]
  exact And.intro (decodeStatus_statusCode _ _) (decodeTernary_statusCode _ _)

/-! ## Operands outside the checked path -/

/--
`sqrtStatusSpecial` computes the flags and the ternary value of the reference square root, for
every operand.
-/
theorem sqrtStatusSpecial_eq {fmt : FloatFormat} (mode : Model.IEEERoundingMode)
    (x : Model fmt) :
    decodeStatus (sqrtStatusSpecial fmt mode x.toNatBits) =
        (Model.Internal.Status.sqrt x mode).status ∧
      decodeTernary (sqrtStatusSpecial fmt mode x.toNatBits) =
        (Model.Internal.Status.sqrt x mode).ternary := by
  have hreference := sqrtStatusReference_eq mode x
  unfold sqrtStatusSpecial
  simp only [Nat.shiftRight_eq', Nat.land_eq, Nat.add_eq, Nat.sub_eq, Nat.mul_eq,
    sign_toNatBits, magnitude_toNatBits, infFlag_eq, nanFlag_eq, zeroFlag_eq]
  cases hnan : Model.isNaN x
  · have hsnan := Model.isSignaling_eq_false_of_isNaN_eq_false x hnan
    simp only [Bool.false_eq_true, ite_false, show Nat.beq 0 0 = true from rfl]
    cases hsign : Model.signBit x
    · cases hinf : Model.isInfinite x
      · have hfinite := Model.isFinite_eq_true_of_isNaN_eq_false_of_isInfinite_eq_false x hnan hinf
        obtain ⟨d, hd, -, -, -⟩ := toDyadic?_of_isFinite x hfinite
        have hzeroEq := Model.isZero_eq_beq_zero_of_toDyadic?_some hd
        cases hzero : Model.isZero x
        · simp only [Bool.false_eq_true, ite_false, show Nat.beq (0 + 0 + 0) 0 = true from rfl]
          exact hreference
        · simp only [ite_true, Bool.false_eq_true, ite_false,
            show Nat.beq (0 + 0 + 1) 0 = false from rfl]
          have hstatus : Model.Internal.Status.sqrt x mode =
              Model.outcomeWithInvalid (Model.Internal.Directed.sqrt mode x) false := by
            unfold Model.Internal.Status.sqrt
            rw [hzero] at hzeroEq
            simp only [hsign, hd, Bool.false_eq_true, ite_false, ← hzeroEq, ite_true]
          rw [hstatus]
          exact invalidStatus_eq _ _ _ (by decide)
      · simp only [ite_true, Bool.false_eq_true, ite_false]
        have hfinite : Model.isFinite x = false := by
          cases h : Model.isFinite x
          · rfl
          · rw [Model.isInfinite_eq_false_of_isFinite_eq_true x h] at hinf
            exact absurd hinf (by decide)
        have hstatus : Model.Internal.Status.sqrt x mode =
            Model.outcomeWithInvalid (Model.Internal.Directed.sqrt mode x) false := by
          unfold Model.Internal.Status.sqrt
          simp only [hsign, toDyadic?_eq_none_of_isFinite_eq_false x hfinite, hsnan,
            Bool.false_eq_true, ite_false]
        rw [hstatus]
        cases Model.isZero x <;> exact invalidStatus_eq _ _ _ (by decide)
    · have hstatus : Model.Internal.Status.sqrt x mode =
          Model.outcomeWithInvalid (Model.Internal.Directed.sqrt mode x) (!Model.isZero x) := by
        unfold Model.Internal.Status.sqrt
        simp only [hsign, hnan, ite_true, Bool.false_eq_true, ite_false]
      rw [hstatus]
      cases Model.isInfinite x <;> cases Model.isZero x <;>
        exact invalidStatus_eq _ _ _ (by decide)
  · simp only [ite_true, show Nat.beq 1 0 = false from rfl]
    rw [signalingFlag_eq x hnan]
    have hfinite : Model.isFinite x = false := by
      cases h : Model.isFinite x
      · rfl
      · rw [Model.isNaN_eq_false_of_isFinite_eq_true x h] at hnan
        exact absurd hnan (by decide)
    have hstatus : Model.Internal.Status.sqrt x mode =
        Model.outcomeWithInvalid (Model.Internal.Directed.sqrt mode x) (Model.isSignaling x) := by
      unfold Model.Internal.Status.sqrt
      cases hsign : Model.signBit x
      · simp only [toDyadic?_eq_none_of_isFinite_eq_false x hfinite, Bool.false_eq_true,
          ite_false]
      · simp only [hnan, ite_true]
    rw [hstatus]
    cases Model.isSignaling x <;> exact invalidStatus_eq _ _ _ (by decide)

/-! ## The checked root -/

/-- No direction rounds a root with a zero remainder up. -/
theorem rootUp_zero (mode : Model.IEEERoundingMode) (r : Nat) : rootUp mode r 0 = 0 := by
  cases mode <;> simp [rootUp]

/-- The rounding increment of a root is zero or one. -/
theorem rootUp_le_one (mode : Model.IEEERoundingMode) (r rem : Nat) : rootUp mode r rem ≤ 1 := by
  unfold rootUp
  cases mode <;> simp only [Nat.sub_eq] <;> omega

/--
`sqrtStatusCore` returns `special`, or, with a zero guard, the status of the integer root of `N`
rounded in the direction `mode`.
-/
theorem sqrtStatusCore_eq (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (N guard special : Nat) :
    sqrtStatusCore fmt mode N guard special = special ∨
      (guard = 0 ∧ sqrtStatusCore fmt mode N guard special =
        rootStatus (N - Nat.sqrt N * Nat.sqrt N)
          (rootUp mode (Nat.sqrt N) (N - Nat.sqrt N * Nat.sqrt N))) := by
  unfold sqrtStatusCore
  dsimp only
  generalize newtonRoot fmt N = x
  generalize Nat.sub x (Nat.sub 1 (Nat.sub 1 (Nat.sub (Nat.mul x x) N))) = r
  cases hcheck : Nat.beq
      (Nat.add guard
        (Nat.add (Nat.sub (Nat.mul r r) N)
          (Nat.sub (Nat.succ N) (Nat.mul (Nat.succ r) (Nat.succ r)))))
      0
  · exact Or.inl rfl
  · have hzero : guard + (r * r - N + (N + 1 - (r + 1) * (r + 1))) = 0 :=
      Nat.eq_of_beq_eq_true hcheck
    obtain ⟨hguard, _⟩ := Nat.eq_zero_of_add_eq_zero hzero
    have hr : r = Nat.sqrt N := Nat.eq_sqrt.mpr ⟨by omega, by omega⟩
    refine Or.inr ⟨hguard, ?_⟩
    rw [← hr]
    rfl

/-! ## The delivered root as an exact value -/

/--
A value whose encoding is `t * 2 ^ fracWidth + M`, for a significand `M` of `fracWidth + 1` bits
or the next power of two and a finite exponent field, is finite and positive: its exact value is
`M * 2 ^ (t + minSubnormalExponent)`, and its exponent field is not zero.
-/
theorem toRat_of_bits {fmt : FloatFormat} (value : Model fmt) (t M : Nat)
    (hlow : 2 ^ fmt.fracWidth ≤ M) (hhigh : M ≤ 2 ^ (fmt.fracWidth + 1))
    (ht : t + 2 ≤ fmt.maxFiniteExpField)
    (hbits : value.toNatBits = t * 2 ^ fmt.fracWidth + M) :
    ∃ actual : Numerics.Dyadic, Model.toDyadic? value = some actual ∧
      actual.toRat = (M : ℚ) * (2 : ℚ) ^ ((t : Int) + fmt.minSubnormalExponent) ∧
      Model.expField value ≠ 0 := by
  have hF := Nat.two_pow_pos fmt.fracWidth
  have hf := Model.fracField_lt_pow2 value
  have hsplit : 2 ^ (fmt.fracWidth + 1) = 2 ^ fmt.fracWidth + 2 ^ fmt.fracWidth := by
    rw [Nat.pow_succ]
    omega
  have hfields := toNatBits_eq_fields value
  have hlt := fields_lt_two_pow_signPos value
  have hword : t * 2 ^ fmt.fracWidth + M ≤ maxFinite fmt := by
    have h := (le_maxFinite_iff fmt (t + 2) 0 hF).mpr (by
      rcases Nat.lt_or_ge (t + 2) fmt.maxFiniteExpField with h | h
      · exact Or.inl h
      · exact Or.inr ⟨by omega, Nat.zero_le _⟩)
    have hexpand : (t + 2) * 2 ^ fmt.fracWidth =
        t * 2 ^ fmt.fracWidth + 2 ^ fmt.fracWidth + 2 ^ fmt.fracWidth := by
      rw [Nat.add_mul]
      omega
    omega
  have hmax : maxFinite fmt < 2 ^ signPos fmt := by
    have he := fmt.maxFiniteExpField_lt_two_pow
    have hfrac := fmt.maxFiniteFracField_lt_two_pow
    unfold maxFinite signPos
    rw [Nat.pow_add]
    calc fmt.maxFiniteExpField * 2 ^ fmt.fracWidth + fmt.maxFiniteFracField
        < fmt.maxFiniteExpField * 2 ^ fmt.fracWidth + 2 ^ fmt.fracWidth := by omega
      _ = (fmt.maxFiniteExpField + 1) * 2 ^ fmt.fracWidth := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ 2 ^ fmt.expWidth * 2 ^ fmt.fracWidth := Nat.mul_le_mul_right _ he
  have hsign : Model.signBit value = false := by
    cases hs : Model.signBit value
    · rfl
    · rw [hs] at hfields
      simp only [ite_true] at hfields
      omega
  rw [hsign] at hfields
  simp only [Bool.false_eq_true, ite_false, Nat.zero_add] at hfields
  have hmagnitude : Model.expField value * 2 ^ fmt.fracWidth + Model.fracField value =
      t * 2 ^ fmt.fracWidth + M := by rw [← hfields, hbits]
  have hfinite : Model.isFinite value = true := by
    apply isFinite_of_nonFinite_eq_zero
    rw [hsign, hmagnitude]
    unfold nonFinite
    simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Bool.false_eq_true, ite_false]
    rw [Nat.sub_eq_zero_of_le hword, Nat.zero_sub, Nat.mul_zero]
  obtain ⟨actual, hactual, hnegative, hsignificand, hexponent⟩ :=
    toDyadic?_of_isFinite value hfinite
  -- The fields of the value, by the two shapes of the significand.
  have hcases : (Model.expField value = t + 1 ∧
        Model.fracField value = M - 2 ^ fmt.fracWidth ∧ M < 2 ^ (fmt.fracWidth + 1)) ∨
      (Model.expField value = t + 2 ∧ Model.fracField value = 0 ∧
        M = 2 ^ (fmt.fracWidth + 1)) := by
    by_cases hcarry : M = 2 ^ (fmt.fracWidth + 1)
    · right
      have hexp : Model.expField value = t + 2 := by
        have h := fields_shiftRight (Model.expField value) (Model.fracField value)
          fmt.fracWidth hf
        rw [hmagnitude, hcarry, hsplit, ← Nat.add_assoc,
          show t * 2 ^ fmt.fracWidth + 2 ^ fmt.fracWidth + 2 ^ fmt.fracWidth =
            (t + 2) * 2 ^ fmt.fracWidth + 0 by rw [Nat.add_mul]; omega,
          fields_shiftRight _ _ _ hF] at h
        exact h.symm
      refine ⟨hexp, ?_, hcarry⟩
      rw [hexp, hcarry, hsplit, Nat.add_mul] at hmagnitude
      omega
    · left
      have hMlt : M < 2 ^ (fmt.fracWidth + 1) := by omega
      have hexp : Model.expField value = t + 1 := by
        have h := fields_shiftRight (Model.expField value) (Model.fracField value)
          fmt.fracWidth hf
        rw [hmagnitude,
          show t * 2 ^ fmt.fracWidth + M =
            (t + 1) * 2 ^ fmt.fracWidth + (M - 2 ^ fmt.fracWidth) by rw [Nat.add_mul]; omega,
          fields_shiftRight _ _ _ (by omega)] at h
        exact h.symm
      refine ⟨hexp, ?_, hMlt⟩
      rw [hexp, Nat.add_mul] at hmagnitude
      omega
  have htwo : (2 : ℚ) ≠ 0 := by norm_num
  refine ⟨actual, hactual, ?_, by rcases hcases with ⟨h, -, -⟩ | ⟨h, -, -⟩ <;> omega⟩
  obtain ⟨negative, significand, exponent⟩ := actual
  dsimp only at hnegative hsignificand hexponent
  rw [toRat_mk, hnegative, hsign]
  simp only [Bool.false_eq_true, ite_false, one_mul]
  rcases hcases with ⟨hexp, hfrac, hMlt⟩ | ⟨hexp, hfrac, hcarry⟩
  · have hsig : significand = M := by
      rw [hsignificand, hexp, hfrac]
      simp only [Nat.succ_ne_zero, ite_false]
      omega
    have hsigne : significand ≠ 0 := by omega
    rw [hexponent hsigne, hsig, hexp, Nat.add_sub_cancel]
  · have hsig : significand = 2 ^ fmt.fracWidth := by
      rw [hsignificand, hexp, hfrac]
      simp
    have hsigne : significand ≠ 0 := by omega
    rw [hexponent hsigne, hsig, hexp, hcarry,
      show ((t + 2 - 1 : Nat) : Int) + fmt.minSubnormalExponent =
        ((t : Int) + fmt.minSubnormalExponent) + 1 by omega,
      zpow_add₀ htwo, zpow_one]
    push_cast
    rw [pow_succ]
    ring

/-- The square of a dyadic, as the reference square-root status forms it, has the squared value. -/
theorem square_toRat (a : Numerics.Dyadic) :
    Numerics.Dyadic.toRat ⟨false, a.significand * a.significand, a.exponent + a.exponent⟩ =
      a.toRat * a.toRat := by
  have htwo : (2 : ℚ) ≠ 0 := by norm_num
  obtain ⟨negative, significand, exponent⟩ := a
  rw [toRat_mk, toRat_mk, zpow_add₀ htwo]
  push_cast
  cases negative <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> ring

/--
The exact value of a radicand `m * 2 ^ (scale + minSubnormalExponent)` on the scale of its root:
the scaled significand of `sqrt` times the square of the unit of the exponent field `num / 2`.
-/
theorem radicand_toRat (fmt : FloatFormat) (m scale : Nat) (hm : m ≠ 0)
    (hmlt : m < 2 ^ (fmt.fracWidth + 1)) (hbias : fmt.fracWidth + 1 ≤ fmt.exponentBias)
    (num : Nat) (hnum : num = m.log2 + 1 + scale + (fmt.exponentBias - fmt.fracWidth)) :
    (m : ℚ) * (2 : ℚ) ^ ((scale : Int) + fmt.minSubnormalExponent) =
      ((m <<< (num % 2 + (2 * fmt.fracWidth + 1) - (m.log2 + 1)) : ℕ) : ℚ) *
        (2 : ℚ) ^ ((((num / 2 - 1 : Nat) : Int) + fmt.minSubnormalExponent) +
          (((num / 2 - 1 : Nat) : Int) + fmt.minSubnormalExponent)) := by
  have htwo : (2 : ℚ) ≠ 0 := by norm_num
  have hleading : m.log2 ≤ fmt.fracWidth := by
    have := (Nat.log2_lt hm).2 hmlt
    omega
  have hexponent : (scale : Int) + fmt.minSubnormalExponent =
      ((num % 2 + (2 * fmt.fracWidth + 1) - (m.log2 + 1) : Nat) : Int) +
        ((((num / 2 - 1 : Nat) : Int) + fmt.minSubnormalExponent) +
          (((num / 2 - 1 : Nat) : Int) + fmt.minSubnormalExponent)) := by
    simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
      Int.ofNat_eq_natCast]
    omega
  rw [hexponent, zpow_add₀ htwo, zpow_natCast, Nat.shiftLeft_eq]
  push_cast
  ring

/-! ## Correctness -/

/--
`sqrtStatus` computes the flags and the ternary value of the reference square root
`Model.sqrt x (mode := mode) (status := true)`, for every format descriptor, every rounding
direction and every operand.
-/
theorem sqrtStatus_eq {fmt : FloatFormat} (mode : Model.IEEERoundingMode) (x : Model fmt) :
    decodeStatus (sqrtStatus fmt mode x.toNatBits) =
        (Model.sqrt x (mode := mode) (status := true)).status ∧
      decodeTernary (sqrtStatus fmt mode x.toNatBits) =
        (Model.sqrt x (mode := mode) (status := true)).ternary := by
  have hfx := Model.fracField_lt_pow2 x
  have hspecial := sqrtStatusSpecial_eq mode x
  rw [← Model.Internal.Status.sqrt_eq]
  unfold sqrtStatus
  simp only [Nat.shiftRight_eq', Nat.land_eq, Nat.shiftLeft_eq', Nat.sub_eq, Nat.add_eq,
    Nat.mul_eq, Nat.succ_eq_add_one, sign_toNatBits, magnitude_toNatBits,
    fields_shiftRight _ _ _ hfx, fields_sub_shiftLeft]
  rcases sqrtStatusCore_eq fmt mode _ _ (sqrtStatusSpecial fmt mode x.toNatBits) with
    hcore | ⟨hguard, hcore⟩
  · rw [hcore]
    exact hspecial
  rw [hcore]
  obtain ⟨hrest, hfield⟩ := Nat.eq_zero_of_add_eq_zero hguard
  obtain ⟨hclass, hvalue⟩ := Nat.eq_zero_of_add_eq_zero hrest
  obtain ⟨hnonFinite, hsignBit⟩ := Nat.eq_zero_of_add_eq_zero hclass
  obtain ⟨hnonzero, hslow⟩ := Nat.eq_zero_of_add_eq_zero hvalue
  obtain ⟨d, hd, hnegative, hsignificand, hexponent⟩ :=
    toDyadic?_of_isFinite x (isFinite_of_nonFinite_eq_zero x hnonFinite)
  have hmlt := decoded_significand_lt x
  rw [← hsignificand] at hmlt hnonzero hfield ⊢
  have hm : d.significand ≠ 0 := by omega
  have hsign : Model.signBit x = false := by
    cases hs : Model.signBit x
    · rfl
    · simp [hs] at hsignBit
  have hbias2 : fmt.fracWidth + 1 < fmt.exponentBias := by lia
  have hbias : fmt.fracWidth + 1 ≤ fmt.exponentBias := by omega
  have hlen := significandLength_eq hmlt
  rw [ite_eq_right hm] at hlen
  rw [hlen] at hfield ⊢
  rw [Nat.shiftRight_eq_div_pow, Nat.pow_one] at hfield
  rw [Nat.and_one_is_mod]
  have hzero : Model.isZero x = false := by
    rw [Model.isZero_eq_beq_zero_of_toDyadic?_some hd]
    simpa using hm
  have hdyadic : d = ⟨d.negative, d.significand,
      ((Model.expField x - 1 : Nat) : Int) + fmt.minSubnormalExponent⟩ := by
    rw [← hexponent hm]
  have hf := fmt.fracWidth_pos
  have hleading : d.significand.log2 ≤ fmt.fracWidth := by
    have := (Nat.log2_lt hm).2 hmlt
    omega
  have hq : (d.significand.log2 + 1 + (Model.expField x - 1) +
      (fmt.exponentBias - fmt.fracWidth)) / 2 + 1 ≤ fmt.maxFiniteExpField := by omega
  -- The delivered root and its encoding.
  have hroot : Model.Internal.Directed.sqrt mode x = positiveRoot fmt mode d := by
    rw [Model.Internal.Directed.sqrt_eq]
    exact sqrt_of_positive mode x d hd hzero hsign
  have hbits := positiveRoot_bits fmt mode d.negative d.significand (Model.expField x - 1) hm
    hmlt hbias hq
  rw [← hdyadic, ← hroot] at hbits
  have hradicand := radicand_toRat fmt d.significand (Model.expField x - 1) hm hmlt hbias _ rfl
  generalize hnum : d.significand.log2 + 1 + (Model.expField x - 1) +
      (fmt.exponentBias - fmt.fracWidth) = num at hq hbits hradicand ⊢
  generalize hshift : num % 2 + (2 * fmt.fracWidth + 1) - (d.significand.log2 + 1) = shift
    at hbits hradicand ⊢
  obtain ⟨-, -, hrootLow, hrootHigh⟩ :=
    Model.sqrt_shiftLeft_bounds fmt.fracWidth d.significand shift hm (by omega) (by omega)
  generalize d.significand <<< shift = N at hbits hradicand hrootLow hrootHigh ⊢
  have hup := rootUp_le_one mode (Nat.sqrt N) (N - Nat.sqrt N * Nat.sqrt N)
  have hupZero := rootUp_zero mode (Nat.sqrt N)
  obtain ⟨hsqrtLow, hsqrtHigh⟩ := Nat.eq_sqrt.mp (rfl : Nat.sqrt N = Nat.sqrt N)
  unfold directedRoot at hbits
  generalize hupDef : rootUp mode (Nat.sqrt N) (N - Nat.sqrt N * Nat.sqrt N) = up
    at hbits hup ⊢
  obtain ⟨actual, hactual, hactualRat, hexpField⟩ :=
    toRat_of_bits (Model.Internal.Directed.sqrt mode x) (num / 2 - 1) (Nat.sqrt N + up)
      (by omega) (by omega) (by omega) hbits
  -- The ternary value is the comparison of the squared root with the scaled significand.
  have hternary : Model.dyadicSqrtTernary d (Model.Internal.Directed.sqrt mode x) =
      compare ((Nat.sqrt N + up) * (Nat.sqrt N + up)) N := by
    unfold Model.dyadicSqrtTernary
    rw [hactual]
    refine cmpDyadic_eq_compare _ d _ N
      ((((num / 2 - 1 : Nat) : Int) + fmt.minSubnormalExponent) +
        (((num / 2 - 1 : Nat) : Int) + fmt.minSubnormalExponent)) ?_ ?_
    · have hdouble : ∀ e : Int, (2 : ℚ) ^ (e + e) = (2 : ℚ) ^ e * (2 : ℚ) ^ e :=
        fun e => zpow_add₀ (by norm_num) e e
      rw [square_toRat, hactualRat, hdouble]
      push_cast
      ring
    · rw [hdyadic, toRat_mk, hnegative, hsign]
      simp only [Bool.false_eq_true, ite_false, one_mul]
      exact hradicand
  have htiny : Model.isTinyAfterRounding (Model.Internal.Directed.sqrt mode x) = false := by
    unfold Model.isTinyAfterRounding
    simp [hexpField]
  have hstatus : Model.Internal.Status.sqrt x mode =
      { value := Model.Internal.Directed.sqrt mode x
        status :=
          { underflow := false
            inexact := compare ((Nat.sqrt N + up) * (Nat.sqrt N + up)) N != .eq }
        ternary := compare ((Nat.sqrt N + up) * (Nat.sqrt N + up)) N } := by
    unfold Model.Internal.Status.sqrt
    simp only [hsign, hd, hternary, htiny, hbias2, Bool.false_eq_true, ite_false, ite_true,
      beq_iff_eq, hm, ite_self]
  rw [hstatus]
  unfold rootStatus
  simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq]
  by_cases hrem : N - Nat.sqrt N * Nat.sqrt N = 0
  · obtain rfl : up = 0 := by rw [← hupDef, hrem, hupZero]
    have hexact : (Nat.sqrt N + 0) * (Nat.sqrt N + 0) = N := by
      rw [Nat.add_zero]
      omega
    rw [hrem, hexact, compare_eq_iff_eq.mpr rfl]
    exact ⟨by decide +kernel, by decide +kernel⟩
  · have hinexact : 1 - (1 - (N - Nat.sqrt N * Nat.sqrt N)) = 1 := by omega
    rw [hinexact]
    obtain rfl | rfl : up = 0 ∨ up = 1 := by omega
    · have hlt : (Nat.sqrt N + 0) * (Nat.sqrt N + 0) < N := by
        rw [Nat.add_zero]
        omega
      rw [compare_lt_iff_lt.mpr hlt]
      exact ⟨by decide +kernel, by decide +kernel⟩
    · have hgt : N < (Nat.sqrt N + 1) * (Nat.sqrt N + 1) := hsqrtHigh
      rw [compare_gt_iff_gt.mpr hgt]
      exact ⟨by decide +kernel, by decide +kernel⟩

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
