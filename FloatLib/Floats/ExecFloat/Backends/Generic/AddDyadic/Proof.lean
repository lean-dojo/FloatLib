/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Generic.AddDyadic.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Rounding
import FloatLib.Numerics.Exact.Dyadic.Arithmetic.Proof

/-!
# Correctness of signed-magnitude dyadic addition

At runtime, dyadic significands are aligned and their natural-number magnitudes combined by sign.
`Internal.addDyadic_eq` identifies this implementation with exact dyadic addition, cancellation and
the signed-zero rule included.

Its `@[csimp]` theorem `addDyadic_eq_internal` supplies the equality that the compiler substitution
needs, and the remaining public lemmas describe the equal- and adjacent-exponent cases that native
arithmetic refinements use.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

private theorem natAbs_natCast_add (left right : Nat) :
    ((left : Int) + (right : Int)).natAbs = left + right := by
  rw [← Int.natCast_add left right, Int.natAbs_natCast]

/--
Adding two nonzero dyadics with the same sign and exponent adds their significands.
-/
theorem addDyadic_sameSign_sameExponent
    (sign : Bool) (left right : Nat) (exponent : Int)
    (hleft : left ≠ 0) (hright : right ≠ 0) :
    addDyadic
        { negative := sign, significand := left, exponent := exponent }
        { negative := sign, significand := right, exponent := exponent } =
      { negative := sign, significand := left + right, exponent := exponent } := by
  simpa [addDyadic] using
    Numerics.Dyadic.add_same_sign_same_exponent
      sign left right exponent hleft hright

/--
Adding equal-exponent dyadics of opposite signs subtracts the smaller magnitude from the larger
left one.

The result keeps the sign of the larger magnitude and needs no rounding or exponent adjustment. A
zero smaller magnitude leaves the larger operand unchanged.
-/
theorem addDyadic_oppositeSign_sameExponent_largeLeft
    (largeSign smallSign : Bool) (large small : Nat) (exponent : Int)
    (hsign : largeSign ≠ smallSign) (hlt : small < large) :
    addDyadic
        { negative := largeSign, significand := large, exponent }
        { negative := smallSign, significand := small, exponent } =
      { negative := largeSign, significand := large - small, exponent } := by
  simpa [addDyadic] using
    Numerics.Dyadic.add_opposite_sign_same_exponent_large_left
      largeSign smallSign large small exponent hsign hlt

/--
Adding equal-exponent dyadics of opposite signs subtracts the smaller left magnitude from the
larger right one.
-/
theorem addDyadic_oppositeSign_sameExponent_largeRight
    (smallSign largeSign : Bool) (small large : Nat) (exponent : Int)
    (hsign : smallSign ≠ largeSign) (hlt : small < large) :
    addDyadic
        { negative := smallSign, significand := small, exponent }
        { negative := largeSign, significand := large, exponent } =
      { negative := largeSign, significand := large - small, exponent } := by
  simpa [addDyadic] using
    Numerics.Dyadic.add_opposite_sign_same_exponent_large_right
      smallSign largeSign small large exponent hsign hlt

/-- Equal magnitudes with opposite signs cancel to canonical positive zero. -/
theorem addDyadic_oppositeSign_sameExponent_eq_zero
    (leftSign rightSign : Bool) (magnitude : Nat) (exponent : Int)
    (hsign : leftSign ≠ rightSign) :
    addDyadic
        { negative := leftSign, significand := magnitude, exponent }
        { negative := rightSign, significand := magnitude, exponent } =
      { negative := false, significand := 0, exponent := 0 } := by
  simpa [addDyadic] using
    Numerics.Dyadic.add_opposite_sign_same_exponent_eq_zero
      leftSign rightSign magnitude exponent hsign

/-- Opposite signs with the larger left operand one exponent higher give `2 * large - small`. -/
theorem addDyadic_oppositeSign_adjacentExponent_largeLeft
    (largeSign smallSign : Bool) (large small : Nat) (exponent : Int)
    (hsmall : small ≠ 0)
    (hsign : largeSign ≠ smallSign) (hlt : small < large.shiftLeft 1) :
    addDyadic
        { negative := largeSign, significand := large, exponent := exponent + 1 }
        { negative := smallSign, significand := small, exponent } =
      { negative := largeSign
        significand := large.shiftLeft 1 - small
        exponent } := by
  simpa [addDyadic] using
    Numerics.Dyadic.add_opposite_sign_adjacent_exponent_large_left
      largeSign smallSign large small exponent hsmall hsign hlt

/-- Opposite signs with the larger right operand one exponent higher give `2 * large - small`. -/
theorem addDyadic_oppositeSign_adjacentExponent_largeRight
    (smallSign largeSign : Bool) (small large : Nat) (exponent : Int)
    (hsmall : small ≠ 0)
    (hsign : smallSign ≠ largeSign) (hlt : small < large.shiftLeft 1) :
    addDyadic
        { negative := smallSign, significand := small, exponent }
        { negative := largeSign, significand := large, exponent := exponent + 1 } =
      { negative := largeSign
        significand := large.shiftLeft 1 - small
        exponent } := by
  simpa [addDyadic] using
    Numerics.Dyadic.add_opposite_sign_adjacent_exponent_large_right
      smallSign largeSign small large exponent hsmall hsign hlt

/--
Align the right dyadic magnitude to the left exponent without changing the exact sum.

A zero right magnitude stays zero after the shift, and both sums return the left operand.
-/
theorem addDyadic_alignRightOffset
    (offset : Nat) (xSign ySign : Bool)
    (xMagnitude yMagnitude xScale yScale : Nat)
    (hx : xMagnitude ≠ 0)
    (hscale : xScale ≤ yScale) :
    Model.addDyadic
        { negative := xSign
          significand := xMagnitude
          exponent := Int.ofNat xScale - Int.ofNat offset }
        { negative := ySign
          significand := yMagnitude
          exponent := Int.ofNat yScale - Int.ofNat offset } =
      Model.addDyadic
        { negative := xSign
          significand := xMagnitude
          exponent := Int.ofNat xScale - Int.ofNat offset }
        { negative := ySign
          significand := yMagnitude <<< (yScale - xScale)
          exponent := Int.ofNat xScale - Int.ofNat offset } := by
  have hscaleInt :
      Int.ofNat xScale - Int.ofNat offset ≤
        Int.ofNat yScale - Int.ofNat offset := by
    simp only [Int.ofNat_eq_natCast]
    omega
  have hshift :
      Int.toNat
          ((Int.ofNat yScale - Int.ofNat offset) -
            (Int.ofNat xScale - Int.ofNat offset)) =
        yScale - xScale := by
    simp only [Int.ofNat_eq_natCast]
    omega
  simpa [Model.addDyadic, hshift] using
    Numerics.Dyadic.add_align_right_to_left_exponent
      xSign ySign xMagnitude yMagnitude
      (Int.ofNat xScale - Int.ofNat offset)
      (Int.ofNat yScale - Int.ofNat offset)
      hx hscaleInt

/--
Align the left dyadic magnitude to the right exponent without changing the exact sum.

A zero left magnitude stays zero after the shift, and both sums return the right operand.
-/
theorem addDyadic_alignLeftOffset
    (offset : Nat) (xSign ySign : Bool)
    (xMagnitude yMagnitude xScale yScale : Nat)
    (hy : yMagnitude ≠ 0)
    (hscale : yScale < xScale) :
    Model.addDyadic
        { negative := xSign
          significand := xMagnitude
          exponent := Int.ofNat xScale - Int.ofNat offset }
        { negative := ySign
          significand := yMagnitude
          exponent := Int.ofNat yScale - Int.ofNat offset } =
      Model.addDyadic
        { negative := xSign
          significand := xMagnitude <<< (xScale - yScale)
          exponent := Int.ofNat yScale - Int.ofNat offset }
        { negative := ySign
          significand := yMagnitude
          exponent := Int.ofNat yScale - Int.ofNat offset } := by
  have hscaleInt :
      Int.ofNat yScale - Int.ofNat offset <
        Int.ofNat xScale - Int.ofNat offset := by
    simp only [Int.ofNat_eq_natCast]
    omega
  have hshift :
      Int.toNat
          ((Int.ofNat xScale - Int.ofNat offset) -
            (Int.ofNat yScale - Int.ofNat offset)) =
        xScale - yScale := by
    simp only [Int.ofNat_eq_natCast]
    omega
  simpa [Model.addDyadic, hshift] using
    Numerics.Dyadic.add_align_left_to_right_exponent
      xSign ySign xMagnitude yMagnitude
      (Int.ofNat xScale - Int.ofNat offset)
      (Int.ofNat yScale - Int.ofNat offset)
      hy hscaleInt

/--
Signed-magnitude combination is symmetric in its operands, including the sign of an exact
cancellation, which is the conjunction of the two signs.
-/
private theorem addDyadicMagnitudes_comm (leftSign rightSign : Bool) (left right : Nat)
    (exponent : Int) :
    addDyadicMagnitudes leftSign rightSign left right exponent =
      addDyadicMagnitudes rightSign leftSign right left exponent := by
  unfold addDyadicMagnitudes
  by_cases hsign : leftSign = rightSign
  · subst hsign
    simp [Nat.add_comm]
  · have hsign' : ¬rightSign = leftSign := fun h => hsign h.symm
    by_cases heq : left = right
    · subst heq
      simp [hsign, hsign', Bool.and_comm]
    · by_cases hlt : left < right
      · simp [hsign, hsign', heq, hlt, Nat.not_lt_of_gt hlt, Ne.symm heq]
      · have hgt : right < left := by omega
        simp [hsign, hsign', heq, hlt, hgt, Ne.symm heq]

private theorem addDyadicMagnitudes_eq
    (leftSign rightSign : Bool) (left right : Nat) (exponent : Int)
    (hleft : left ≠ 0) (hright : right ≠ 0) :
    addDyadicMagnitudes leftSign rightSign left right exponent =
      let leftInt : Int := if leftSign then -(Int.ofNat left) else Int.ofNat left
      let rightInt : Int := if rightSign then -(Int.ofNat right) else Int.ofNat right
      let sum := leftInt + rightInt
      if sum == 0 then
        { negative := leftSign && rightSign, significand := 0, exponent := 0 }
      else
        { negative := sum < 0, significand := Int.natAbs sum, exponent := exponent } := by
  -- The mixed-sign case with the negative operand on the right.
  have hmixed (left right : Nat) :
      addDyadicMagnitudes false true left right exponent =
        let sum : Int := Int.ofNat left + -(Int.ofNat right)
        if sum == 0 then
          { negative := false && true, significand := 0, exponent := 0 }
        else
          { negative := sum < 0, significand := Int.natAbs sum, exponent := exponent } := by
    by_cases heq : left = right
    · subst right
      simp [addDyadicMagnitudes]
    · by_cases hlt : left < right
      · have hsumNeg : (left : Int) + -(right : Int) < 0 := by omega
        have hsumNe : (left : Int) + -(right : Int) ≠ 0 := by omega
        have hnatAbs : ((left : Int) + -(right : Int)).natAbs = right - left := by omega
        simp [addDyadicMagnitudes, heq, hlt, hsumNeg, hsumNe, hnatAbs]
      · have hsumNe : (left : Int) + -(right : Int) ≠ 0 := by omega
        have hnatAbs : ((left : Int) + -(right : Int)).natAbs = left - right := by omega
        simp [addDyadicMagnitudes, heq, hlt, hsumNe, hnatAbs]
  cases leftSign <;> cases rightSign
  · have hsumPos : (0 : Int) < (left : Int) + right := by
      have hleftPos : 0 < left := Nat.pos_of_ne_zero hleft
      have hrightPos : 0 < right := Nat.pos_of_ne_zero hright
      omega
    have hsumNe : (left : Int) + right ≠ 0 := by omega
    have hsumNonneg : (0 : Int) ≤ (left : Int) + right := by omega
    simp [addDyadicMagnitudes, hsumNe, hsumNonneg, natAbs_natCast_add]
  · exact hmixed left right
  · -- Exchanging the operands gives the case above.
    rw [addDyadicMagnitudes_comm, hmixed right left]
    simp only [Bool.false_and, Bool.true_and, ite_true, Bool.false_eq_true, ite_false,
      Int.add_comm (Int.ofNat right)]
  · have hsumNeg : -(left : Int) + -(right : Int) < 0 := by
      have hleftPos : 0 < left := Nat.pos_of_ne_zero hleft
      have hrightPos : 0 < right := Nat.pos_of_ne_zero hright
      omega
    have hsumNe : -(left : Int) + -(right : Int) ≠ 0 := by omega
    have hnatAbs :
        (-(left : Int) + -(right : Int)).natAbs = left + right := by
      have hsumEq :
          -(left : Int) + -(right : Int) = -((left : Int) + (right : Int)) := by
        omega
      rw [hsumEq, Int.natAbs_neg]
      exact natAbs_natCast_add left right
    simp [addDyadicMagnitudes, hsumNeg, hsumNe, hnatAbs]

/-- Signed-magnitude dyadic addition equals `Model.addDyadic`. -/
theorem Internal.addDyadic_eq (a b : Numerics.Dyadic) :
    Internal.addDyadic a b = Model.addDyadic a b := by
  unfold Internal.addDyadic Model.addDyadic Numerics.Dyadic.add Numerics.Dyadic.addFields
  simp only [beq_iff_eq]
  by_cases ha : a.significand = 0
  · simp [ha]
  by_cases hb : b.significand = 0
  · simp [ha, hb]
  by_cases hexponent : a.exponent ≤ b.exponent
  · simp only [ha, hb, hexponent, ite_false, ite_true]
    have hshift :
        Nat.shiftLeft b.significand (b.exponent - a.exponent).toNat ≠ 0 := by
      simp [Nat.shiftLeft_eq, hb]
    simpa only [beq_iff_eq] using
      addDyadicMagnitudes_eq a.negative b.negative a.significand
        (Nat.shiftLeft b.significand (b.exponent - a.exponent).toNat) a.exponent
        ha hshift
  · simp only [ha, hb, hexponent, ite_false]
    have hshift :
        Nat.shiftLeft a.significand (a.exponent - b.exponent).toNat ≠ 0 := by
      simp [Nat.shiftLeft_eq, ha]
    simpa only [beq_iff_eq] using
      addDyadicMagnitudes_eq a.negative b.negative
        (Nat.shiftLeft a.significand (a.exponent - b.exponent).toNat) b.significand b.exponent
        hshift hb

/-- Exact dyadic addition is commutative, including its signed-zero rule. -/
theorem addDyadic_comm (a b : Numerics.Dyadic) :
    addDyadic a b = addDyadic b a := by
  exact Numerics.Dyadic.add_comm a b

/-- Compiled code runs exact dyadic addition as the signed-magnitude `Internal.addDyadic`. -/
@[csimp] theorem addDyadic_eq_internal :
    addDyadic = Internal.addDyadic := by
  funext a b
  exact (Internal.addDyadic_eq a b).symm

end FloatLib.Floats.Formats.BinaryInterchange.Model
