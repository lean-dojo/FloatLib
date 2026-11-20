/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.DivStatus
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Literal
import Mathlib.Tactic.Order

/-!
# Kernel path: the IEEE status of rounding a rational number

`ratioStatus fmt mode sign num den` is the status number of `± num / den` rounded in the
direction `mode`: the five exception flags and the ternary value of
`Model.ofRat fmt q (mode := mode) (status := true)` for the rational number `q = ± num / den`.

The exact value is a rational number, as for a quotient of two floating-point values, so its
status is the status of its sticky dyadic (`RationalStatus.lean`). One division of the shifted
numerator by the denominator gives the floor of the value in units of a quarter of the least
subnormal number and tells whether a remainder is left, and `roundStatus` gives the flags and
the ternary value from that pair and the delivered word.

`ratioStatus_eq` holds for every format descriptor, every rounding direction, every numerator
and every nonzero denominator. `ofRat_status_eq` states it for every rational number.

`ratioStatusWith fmt mode sign num den w` is the same number as a function of the delivered word
`w`. A statement about the value and the flags of one rounded ratio gives it the word it has
already computed.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

/--
The status number of `± num / den` rounded in the direction `mode`, for a nonzero denominator,
when `w` is the word of the rounded ratio. `ratioStatus` is this number at
`ofRatio fmt mode sign num den`. See the module documentation.
-/
def ratioStatusWith (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (sign num den w : Nat) :
    Nat :=
  (fun shifted =>
    roundStatus fmt mode sign
      (Nat.add (Nat.mul 2 (Nat.div shifted den)) (Nat.sub 1 (Nat.sub 1 (Nat.mod shifted den))))
      1 w)
    (Nat.shiftLeft num (Nat.add fmt.exponentBias (Nat.add fmt.fracWidth 1)))

/--
The status number of `± num / den` rounded in the direction `mode`, for a nonzero denominator
(`ratioStatus_eq`).
-/
def ratioStatus (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (sign num den : Nat) : Nat :=
  ratioStatusWith fmt mode sign num den (ofRatio fmt mode sign num den)

/--
`ratioStatus` computes the flags and the ternary value of delivering the reference rounding of
`± num / den` for that exact value, for every format descriptor, every rounding direction, every
numerator and every nonzero denominator.
-/
theorem ratioStatus_eq (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (negative : Bool)
    (num den : Nat) (hden : den ≠ 0) :
    decodeStatus (ratioStatus fmt mode (signNat negative) num den) =
        Model.rationalRoundingStatusScaled fmt mode negative num den 0
          (Model.Internal.Directed.roundRat fmt mode negative num den) ∧
      decodeTernary (ratioStatus fmt mode (signNat negative) num den) =
        Model.rationalTernaryScaled negative num den 0
          (Model.Internal.Directed.roundRat fmt mode negative num den) := by
  have hsticky := sticky_quotient fmt num den 0 0 hden
  simp only [Nat.zero_add, Nat.sub_zero, Nat.zero_sub, Nat.shiftLeft_zero, Nat.cast_zero,
    sub_zero] at hsticky
  unfold ratioStatus ratioStatusWith
  simp only [Nat.shiftLeft_eq', Nat.add_eq, Nat.mul_eq, Nat.sub_eq, div_def, mod_def]
  rw [ofRatio_eq_directed, rationalRoundingStatusScaled_sticky fmt mode _ _ _ _ _ _ hden hsticky,
    rationalTernaryScaled_sticky fmt _ _ _ _ _ _ hden hsticky]
  refine roundStatus_eq fmt mode _ (signNat negative) _ 1 (by unfold signNat; split <;> omega)
    ?_ _ ?_
  · rw [toRat_mk]
    congr 1
    · cases negative <;> simp [signNat]
    · congr 1
      push_cast
      omega
  · intro hE
    have hnum : num = 0 := by
      by_contra hnum
      obtain ⟨_, -, hbit⟩ := hsticky
      have hx : 0 < Model.scaledRatToReal num den 0 := by
        unfold Model.scaledRatToReal
        have h1 : (0 : ℝ) < (num : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hnum
        have h2 : (0 : ℝ) < (den : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hden
        exact mul_pos (div_pos h1 h2) (Model.bpow_pos 0)
      rcases hbit with ⟨-, hEq⟩ | ⟨hs, -⟩
      · have hq : (num <<< (fmt.exponentBias + (fmt.fracWidth + 1))) / den = 0 := by omega
        rw [hq, Nat.cast_zero, zero_mul] at hEq
        order
      · omega
    subst hnum
    rw [directedRat_zero fmt mode negative den hden]
    exact Model.isFinite_eq_true_of_isZero_eq_true _ (Model.isZero_zero fmt _)

/--
The flags and the ternary value of `Model.ofRat fmt q (mode := mode) (status := true)` are
decoded from the status number of the numerator and the denominator of `q`, for every format
descriptor, every rounding direction and every rational number.
-/
theorem ofRat_status_eq (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (q : ℚ) :
    (Model.ofRat fmt q (mode := mode) (status := true)).status =
        decodeStatus (ratioStatus fmt mode (signNat (decide (q.num < 0))) q.num.natAbs q.den) ∧
      (Model.ofRat fmt q (mode := mode) (status := true)).ternary =
        decodeTernary (ratioStatus fmt mode (signNat (decide (q.num < 0))) q.num.natAbs q.den) :=
  have h := ratioStatus_eq fmt mode (decide (q.num < 0)) q.num.natAbs q.den q.den_nz
  And.intro h.1.symm h.2.symm

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
