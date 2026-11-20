/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Integer
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.OperationStatus

import Mathlib.Tactic.Positivity

/-!
# Kernel path: the IEEE status of rounding to an integral value

`roundToIntegralStatus fmt mode a` is the status number of the value encoded by `a` rounded to an
integer in the direction `mode`: the exception flags and the ternary value of
`Model.roundToIntegral x mode (status := true)`.

For a finite value in a conventional IEEE format whose finite range holds every integer of its
precision (`fracWidth + exponentBias ≤ maxFiniteExpField`, which every interchange format
satisfies) no overflow is possible. The result is inexact exactly when the value has bits below
the units place, and the ternary value compares the delivered value with the operand, which
`roundStatus` computes from the exact operand and the delivered word. An infinity raises
nothing, and a NaN raises invalid when it is signaling. Every other format takes the status of
the reference rounding, encoded by `statusCode`, so `roundToIntegralStatus_eq` holds for every
descriptor, every rounding direction and every operand.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

/--
The status number of the reference integral rounding of the value encoded by `a`, which the
kernel evaluates for a format outside the checked path.
-/
def roundToIntegralStatusReference (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a : Nat) :
    Nat :=
  (fun outcome => statusCode outcome.status outcome.ternary)
    (Model.Internal.Status.roundToIntegral (Model.ofNatBits (fmt := fmt) a) mode)

/--
The status number of the value encoded by `a` rounded to an integer in the direction `mode`,
when `w` is the word of the rounded value. `roundToIntegralStatus` is this number at
`roundToIntegral fmt mode a`.
-/
def roundToIntegralStatusWith (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a w : Nat) :
    Nat :=
  (fun s u =>
    Bool.casesOn (motive := fun _ => Nat) (Nat.beq (nonFinite fmt s u) 0)
      (invalidStatus (Nat.mul (nanFlag fmt s u) (signalingFlag fmt a)))
      (Bool.casesOn (motive := fun _ => Nat)
        (fmt.isIEEE &&
          Nat.ble (Nat.add fmt.fracWidth fmt.exponentBias) fmt.maxFiniteExpField)
        (roundToIntegralStatusReference fmt mode a)
        ((fun h =>
          (fun m =>
            Nat.add
              (Nat.mul 16
                (Nat.sub 1 (Nat.sub 1
                  (Nat.mod m
                    (Nat.pow 2
                      (Nat.sub (Nat.add fmt.exponentBias fmt.fracWidth) (Nat.succ h)))))))
              (Nat.mul 32
                (Nat.shiftRight
                  (roundStatus fmt mode s (Nat.shiftLeft m (Nat.add h 2)) 0 w)
                  5)))
            (Nat.sub u (Nat.shiftLeft h fmt.fracWidth)))
          (Nat.sub (Nat.shiftRight u fmt.fracWidth) 1))))
    (Nat.shiftRight a (signPos fmt)) (Nat.land a (magnitudeMask fmt))

/--
The status number of the value encoded by `a` rounded to an integer in the direction `mode`
(`roundToIntegralStatus_eq`). See the module documentation.
-/
def roundToIntegralStatus (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a : Nat) : Nat :=
  roundToIntegralStatusWith fmt mode a (roundToIntegral fmt mode a)

/-- `roundToIntegralStatusReference` is the status of the reference integral rounding. -/
theorem roundToIntegralStatusReference_eq {fmt : FloatFormat} (mode : Model.IEEERoundingMode)
    (x : Model fmt) :
    decodeStatus (roundToIntegralStatusReference fmt mode x.toNatBits) =
        (Model.Internal.Status.roundToIntegral x mode).status ∧
      decodeTernary (roundToIntegralStatusReference fmt mode x.toNatBits) =
        (Model.Internal.Status.roundToIntegral x mode).ternary := by
  unfold roundToIntegralStatusReference
  rw [Model.ofNatBits_toNatBits]
  exact And.intro (decodeStatus_statusCode _ _) (decodeTernary_statusCode _ _)

/--
A status number with the inexact flag `inexact` (zero or one) and the ternary code `ternary`
decodes to that flag alone.
-/
theorem decodeStatus_inexact (inexact ternary : Nat) (hinexact : inexact ≤ 1) :
    decodeStatus (16 * inexact + 32 * ternary) = { inexact := decide (inexact = 1) } := by
  have h0 : (16 * inexact + 32 * ternary) % 2 = 0 := by omega
  have h1 : (16 * inexact + 32 * ternary) / 2 % 2 = 0 := by omega
  have h2 : (16 * inexact + 32 * ternary) / 4 % 2 = 0 := by omega
  have h3 : (16 * inexact + 32 * ternary) / 8 % 2 = 0 := by omega
  have h4 : (16 * inexact + 32 * ternary) / 16 % 2 = inexact := by omega
  unfold decodeStatus
  simp only [Nat.land_eq, Nat.shiftRight_eq', Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow,
    show (2 : Nat) ^ 1 = 2 from rfl, show (2 : Nat) ^ 2 = 4 from rfl,
    show (2 : Nat) ^ 3 = 8 from rfl, show (2 : Nat) ^ 4 = 16 from rfl, h0, h1, h2, h3, h4]
  obtain rfl | rfl : inexact = 0 ∨ inexact = 1 := by omega
  · rfl
  · rfl

/-- The ternary value of a status number is read off the number above its five flags. -/
theorem decodeTernary_shift (inexact code : Nat) (hinexact : inexact ≤ 1) :
    decodeTernary (16 * inexact + 32 * (code >>> 5)) = decodeTernary code := by
  unfold decodeTernary
  have hshift : (16 * inexact + 32 * (code >>> 5)) >>> 5 = code >>> 5 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
    omega
  change (fun ternary => _) (Nat.shiftRight (16 * inexact + 32 * (code >>> 5)) 5) =
    (fun ternary => _) (Nat.shiftRight code 5)
  rw [show Nat.shiftRight (16 * inexact + 32 * (code >>> 5)) 5 = Nat.shiftRight code 5 from
    hshift]

/-- The integer of a zero is zero. -/
theorem roundDyadicToInt_zero (mode : Model.IEEERoundingMode) (negative : Bool)
    (exponent : Int) : Model.roundDyadicToInt mode ⟨negative, 0, exponent⟩ = 0 := by
  unfold Model.roundDyadicToInt
  simp

/--
`roundToIntegralStatus` computes the flags and the ternary value of the reference integral rounding
`Model.roundToIntegral x mode (status := true)`, for every format descriptor, every rounding
direction and every operand.
-/
theorem roundToIntegralStatus_eq {fmt : FloatFormat} (mode : Model.IEEERoundingMode)
    (x : Model fmt) :
    decodeStatus (roundToIntegralStatus fmt mode x.toNatBits) =
        (Model.roundToIntegral x mode (status := true)).status ∧
      decodeTernary (roundToIntegralStatus fmt mode x.toNatBits) =
        (Model.roundToIntegral x mode (status := true)).ternary := by
  have hfx := Model.fracField_lt_pow2 x
  change decodeStatus (roundToIntegralStatus fmt mode x.toNatBits) =
      (Model.Internal.Status.roundToIntegral x mode).status ∧
    decodeTernary (roundToIntegralStatus fmt mode x.toNatBits) =
      (Model.Internal.Status.roundToIntegral x mode).ternary
  unfold roundToIntegralStatus roundToIntegralStatusWith
  simp only [Nat.shiftRight_eq', Nat.land_eq, Nat.shiftLeft_eq', Nat.sub_eq, Nat.add_eq,
    Nat.mul_eq, Nat.succ_eq_add_one, Nat.pow_eq, mod_def, sign_toNatBits, magnitude_toNatBits,
    fields_shiftRight _ _ _ hfx, fields_sub_shiftLeft, nanFlag_eq, nanFlag_mul_signalingFlag]
  cases hd : Model.toDyadic? x with
  | none =>
    have hfinite := isFinite_eq_false_of_toDyadic? hd
    have hguard : nonFinite fmt (if Model.signBit x then 1 else 0)
        (Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x) ≠ 0 := by
      intro h
      rw [isFinite_of_nonFinite_eq_zero x h] at hfinite
      exact absurd hfinite (by decide)
    rw [beq_zero_of_ne hguard]
    unfold Model.Internal.Status.roundToIntegral Model.exactValue
    rw [hd]
    cases hinf : Model.isInfinite x
    · simp only [Bool.false_eq_true, ite_false]
      cases Model.isSignaling x <;> exact invalidStatus_eq _ _ _ (by decide)
    · have hsnan : Model.isSignaling x = false := by
        apply Model.isSignaling_eq_false_of_isNaN_eq_false
        rw [isNaN_eq_not_isFinite_and_not_isInfinite, hinf]
        simp
      simp only [ite_true, hsnan]
      exact invalidStatus_eq _ _ _ (by decide)
  | some d =>
    have hfinite := isFinite_of_toDyadic? hd
    rw [nonFinite_eq_zero_of_isFinite x hfinite, show Nat.beq 0 0 = true from rfl]
    cases hieee : (fmt.isIEEE &&
        Nat.ble (fmt.fracWidth + fmt.exponentBias) fmt.maxFiniteExpField)
    · exact roundToIntegralStatusReference_eq mode x
    · obtain ⟨d', hd', hnegative, hsignificand, hexponent⟩ := toDyadic?_of_isFinite x hfinite
      obtain rfl : d' = d := Option.some.inj (hd'.symm.trans hd)
      have hrange : (fmt.isIEEE &&
          decide (fmt.fracWidth + fmt.exponentBias ≤ fmt.maxFiniteExpField)) = true := by
        rw [Bool.and_eq_true] at hieee ⊢
        exact ⟨hieee.1, decide_eq_true (Nat.le_of_ble_eq_true hieee.2)⟩
      -- The delivered value and its encoding.
      have hvalueEq : (Model.Internal.Status.roundToIntegral x mode).value =
          Model.roundToIntegral x mode := rfl
      have hbits := roundToIntegral_eq_spec mode x
      have hstatus : Model.Internal.Status.roundToIntegral x mode =
          { value := Model.roundToIntegral x mode
            status := { inexact := !Model.dyadicIsIntegral d' }
            ternary := Model.dyadicTernary d' (Model.roundToIntegral x mode) } := by
        rw [← hvalueEq]
        unfold Model.Internal.Status.roundToIntegral
        rw [Model.exactValue_eq_finite_of_toDyadic?_eq_some hd]
        simp only [hrange, ite_true]
      rw [hstatus]
      -- The ternary value, from the exact operand and the delivered word.
      have hrat := decoded_toRat x d' hd 0
      simp only [Nat.add_zero] at hrat
      have hzero : (if Model.expField x = 0 then Model.fracField x
            else 2 ^ fmt.fracWidth + Model.fracField x) <<< (Model.expField x - 1 + 2) = 0 →
          Model.isFinite (Model.roundToIntegral x mode) = true := by
        intro hE
        have hsig : d'.significand = 0 := by
          rw [hsignificand]
          rw [Nat.shiftLeft_eq] at hE
          rcases Nat.eq_zero_or_pos (if Model.expField x = 0 then Model.fracField x
              else 2 ^ fmt.fracWidth + Model.fracField x) with h | h
          · exact h
          · exact absurd hE (Nat.mul_ne_zero h.ne' (Nat.two_pow_pos _).ne')
        rw [roundToIntegral_of_finite mode x d' hd]
        have hint : Model.roundDyadicToInt mode d' = 0 := by
          obtain ⟨negative, significand, exponent⟩ := d'
          dsimp only at hsig
          subst hsig
          exact roundDyadicToInt_zero mode negative exponent
        rw [ite_eq_left hint]
        exact Model.isFinite_eq_true_of_isZero_eq_true _ (Model.isZero_zero fmt _)
      obtain ⟨-, hternary⟩ := roundStatus_eq fmt mode d'
        (if Model.signBit x then 1 else 0) _ 0 (by split <;> omega)
        (by simpa only [Nat.cast_zero, sub_zero] using hrat) (Model.roundToIntegral x mode) hzero
      rw [hbits]
      -- The inexact flag: bits below the units place.
      have hinexact : (1 - (1 - (if Model.expField x = 0 then Model.fracField x
            else 2 ^ fmt.fracWidth + Model.fracField x) %
            2 ^ (fmt.exponentBias + fmt.fracWidth - (Model.expField x - 1 + 1))) = 1) ↔
          (!Model.dyadicIsIntegral d') = true := by
        rw [← hsignificand]
        by_cases hsig : d'.significand = 0
        · have hintegral : Model.dyadicIsIntegral d' = true := by
            unfold Model.dyadicIsIntegral
            simp [hsig]
          rw [hintegral, hsig, Nat.zero_mod]
          decide
        · have hexp := hexponent hsig
          rw [Bool.not_eq_true', ← Bool.not_eq_true, Model.dyadicIsIntegral_iff, hexp]
          by_cases hle : fmt.exponentBias + fmt.fracWidth ≤ Model.expField x - 1 + 1
          · obtain ⟨left, hleft⟩ : ∃ left : Nat, ((Model.expField x - 1 : Nat) : Int) +
                fmt.minSubnormalExponent = Int.ofNat left := by
              refine ⟨Model.expField x - 1 + 1 - (fmt.exponentBias + fmt.fracWidth), ?_⟩
              simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
                Int.ofNat_eq_natCast]
              omega
            rw [hleft, show fmt.exponentBias + fmt.fracWidth - (Model.expField x - 1 + 1) = 0 by
              omega, Nat.pow_zero, Nat.mod_one]
            simp
          · obtain ⟨right, hright, hshift⟩ : ∃ right : Nat,
                ((Model.expField x - 1 : Nat) : Int) + fmt.minSubnormalExponent =
                  Int.negSucc right ∧
                fmt.exponentBias + fmt.fracWidth - (Model.expField x - 1 + 1) = right + 1 := by
              refine ⟨fmt.exponentBias + fmt.fracWidth - (Model.expField x - 1 + 1) - 1, ?_,
                by omega⟩
              rw [Int.negSucc_eq]
              simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
                Int.ofNat_eq_natCast]
              omega
            rw [hright, hshift]
            change 1 - (1 - d'.significand % 2 ^ (right + 1)) = 1 ↔
              ¬ 2 ^ (right + 1) ∣ d'.significand
            rw [Nat.dvd_iff_mod_eq_zero]
            omega
      constructor
      · rw [decodeStatus_inexact _ _ (by omega)]
        congr 1
        exact Bool.eq_iff_iff.mpr (by rw [decide_eq_true_iff]; exact hinexact)
      · rw [decodeTernary_shift _ _ (by omega)]
        exact hternary

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
