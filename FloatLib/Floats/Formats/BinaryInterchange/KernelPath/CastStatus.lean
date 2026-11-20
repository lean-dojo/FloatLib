/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Cast
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.OperationStatus

/-!
# Kernel path: the IEEE status of a cast

`castStatus src dst mode a` is the status number of the cast into `dst` of the value that the
word `a` encodes in `src`: the five exception flags and the ternary value of
`Model.cast src dst x mode (status := true)`.

A finite value is its own exact result, so `roundStatus` gives the flags and the ternary value
from its significand on the scale of `dst` and the delivered word. An infinity raises nothing
when `dst` delivers an infinity, and overflow and inexact when `dst` has none and delivers a NaN
or its largest finite value. A NaN raises invalid when it is signaling or when `dst` has no NaN
to deliver. `castStatus_eq` holds for every pair of format descriptors, every rounding
direction and every value.

`castStatusWith src dst mode a w` is the same number as a function of the delivered word `w`. A
statement about the value and the flags of one cast gives it the word it has already computed.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

/--
The status number of the cast into `dst` of the value that `a` encodes in `src`, rounded in the
direction `mode`, when `w` is the word of the cast. `castStatus` is this number at
`cast src dst mode a`. See the module documentation.
-/
def castStatusWith (src dst : FloatFormat) (mode : Model.IEEERoundingMode) (a w : Nat) : Nat :=
  (fun sa ua =>
    Bool.casesOn (motive := fun _ => Nat) (Nat.beq (nonFinite src sa ua) 0)
      ((fun sw uw =>
          Bool.casesOn (motive := fun _ => Nat) (Nat.beq (infFlag src ua) 0)
            (Nat.add (Nat.mul 20 (Nat.sub 1 (infFlag dst uw)))
              (Nat.mul 32 (infinityTernary dst sa w)))
            (invalidStatus (Nat.add (signalingFlag src a) (Nat.sub 1 (nanFlag dst sw uw)))))
        (Nat.shiftRight w (signPos dst)) (Nat.land w (magnitudeMask dst)))
      ((fun ha =>
          roundStatus dst mode sa
            (Nat.shiftLeft (Nat.sub ua (Nat.shiftLeft ha src.fracWidth))
              (Nat.add
                (Nat.add ha
                  (Nat.sub (Nat.add dst.exponentBias dst.fracWidth)
                    (Nat.add src.exponentBias src.fracWidth)))
                2))
            (Nat.sub (Nat.add src.exponentBias src.fracWidth)
              (Nat.add dst.exponentBias dst.fracWidth))
            w)
        (Nat.sub (Nat.shiftRight ua src.fracWidth) 1)))
    (Nat.shiftRight a (signPos src)) (Nat.land a (magnitudeMask src))

/--
The status number of the cast into `dst` of the value that `a` encodes in `src`, rounded in the
direction `mode` (`castStatus_eq`).
-/
def castStatus (src dst : FloatFormat) (mode : Model.IEEERoundingMode) (a : Nat) : Nat :=
  castStatusWith src dst mode a (cast src dst mode a)

/-- The cast of a finite value with a zero significand is finite. -/
theorem isFinite_cast_zero {src dst : FloatFormat} (mode : Model.IEEERoundingMode)
    (x : Model src) (d : Numerics.Dyadic) (hd : Model.toDyadic? x = some d)
    (hzero : d.significand = 0) : Model.isFinite (Model.cast src dst x mode) = true := by
  have hfinite := isFinite_of_toDyadic? hd
  cases hwidens : widens src dst
  · rw [cast_of_finite mode x d hd hwidens]
    obtain ⟨negative, significand, exponent⟩ := d
    dsimp only at hzero
    subst hzero
    rw [roundDyadic_zero]
    exact Model.isFinite_eq_true_of_isZero_eq_true _ (Model.isZero_zero dst _)
  · obtain ⟨hexp, hbias, hencoding, hfrac⟩ := of_decide_eq_true hwidens
    rw [Model.cast_eq_widenExact_of_compatibleWidening x hexp hbias hencoding hfrac hfinite mode]
    exact Model.isFinite_widenExact x hexp hbias hencoding hfrac hfinite

/--
`castStatus` computes the flags and the ternary value of the reference cast
`Model.cast src dst x mode (status := true)`, for every pair of format descriptors, every
rounding direction and every value.
-/
theorem castStatus_eq {src dst : FloatFormat} (mode : Model.IEEERoundingMode) (x : Model src) :
    decodeStatus (castStatus src dst mode x.toNatBits) =
        (Model.cast src dst x mode (status := true)).status ∧
      decodeTernary (castStatus src dst mode x.toNatBits) =
        (Model.cast src dst x mode (status := true)).ternary := by
  have hfx := Model.fracField_lt_pow2 x
  change decodeStatus (castStatus src dst mode x.toNatBits) =
      (Model.Internal.Status.cast src dst x mode).status ∧
    decodeTernary (castStatus src dst mode x.toNatBits) =
      (Model.Internal.Status.cast src dst x mode).ternary
  unfold castStatus castStatusWith infinityTernary Model.Internal.Status.cast
  simp only [Nat.shiftRight_eq', Nat.land_eq, Nat.shiftLeft_eq', Nat.sub_eq, Nat.add_eq,
    Nat.mul_eq, Nat.xor_eq, cast_eq_spec mode x, Model.Internal.Directed.cast_eq,
    sign_toNatBits, magnitude_toNatBits, fields_shiftRight _ _ _ hfx, fields_sub_shiftLeft,
    infFlag_eq, nanFlag_eq]
  by_cases hfinite : Model.isFinite x = true
  · obtain ⟨d, hd, -, -, -⟩ := toDyadic?_of_isFinite x hfinite
    have hnan := Model.isNaN_eq_false_of_isFinite_eq_true x hfinite
    have hinf := Model.isInfinite_eq_false_of_isFinite_eq_true x hfinite
    rw [nonFinite_eq_zero_of_isFinite x hfinite, show Nat.beq 0 0 = true from rfl]
    simp only [hnan, hinf, Bool.false_eq_true, dite_false]
    rw [Model.finiteDyadic_eq_of_toDyadic hfinite hd]
    have hvalue : d.toRat =
        (if (if Model.signBit x then 1 else 0 : Nat) = 1 then -1 else 1) *
          (((if Model.expField x = 0 then Model.fracField x
              else 2 ^ src.fracWidth + Model.fracField x) <<<
            (Model.expField x - 1 +
              (dst.exponentBias + dst.fracWidth - (src.exponentBias + src.fracWidth)) + 2) : ℕ) :
            ℚ) *
          (2 : ℚ) ^ (dst.minSubnormalExponent -
            ((src.exponentBias + src.fracWidth - (dst.exponentBias + dst.fracWidth) : ℕ) : Int) -
            2) := by
      rw [decoded_toRat x d hd
        (dst.exponentBias + dst.fracWidth - (src.exponentBias + src.fracWidth))]
      congr 2
      simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
        Int.ofNat_eq_natCast]
      omega
    refine roundStatus_eq dst mode d _ _ _ (by split <;> omega) hvalue _ ?_
    intro hE
    exact isFinite_cast_zero mode x d hd
      (significand_eq_zero_of_toRat _ (toRat_eq_zero_of_magnitude hvalue hE))
  · have hfalse : Model.isFinite x = false := Bool.eq_false_of_not_eq_true hfinite
    have hguard : nonFinite src (if Model.signBit x then 1 else 0)
        (Model.expField x * 2 ^ src.fracWidth + Model.fracField x) ≠ 0 :=
      fun h => hfinite (isFinite_of_nonFinite_eq_zero x h)
    rw [beq_zero_of_ne hguard]
    have hclass : Model.isNaN x = !Model.isInfinite x := by
      rw [isNaN_eq_not_isFinite_and_not_isInfinite, hfalse]
      rfl
    by_cases hnan : Model.isNaN x = true
    · have hinf : Model.isInfinite x = false := by
        rw [hnan] at hclass
        cases hinf : Model.isInfinite x
        · rfl
        · rw [hinf] at hclass
          exact absurd hclass (by decide)
      simp only [hnan, hinf, ite_false, Bool.false_eq_true, dite_true,
        show Nat.beq 0 0 = true from rfl]
      rw [signalingFlag_eq x hnan]
      refine invalidStatus_eq _ _ _ ?_
      cases Model.isSignaling x <;> cases Model.isNaN (Model.cast src dst x mode) <;> decide
    · have hnanFalse : Model.isNaN x = false := Bool.eq_false_of_not_eq_true hnan
      have hinf : Model.isInfinite x = true := by
        rw [hnanFalse] at hclass
        cases hinf : Model.isInfinite x
        · rw [hinf] at hclass
          exact absurd hclass (by decide)
        · rfl
      simp only [hnanFalse, hinf, ite_true, Bool.false_eq_true, dite_false, dite_true,
        show Nat.beq 1 0 = false from rfl]
      unfold Model.exactInfinityTernary
      cases Model.isInfinite (Model.cast src dst x mode) <;>
        simp only [Bool.false_eq_true, ite_true, ite_false] <;>
        cases Model.signBit (Model.cast src dst x mode) <;> cases Model.signBit x <;>
        exact ⟨by decide +kernel, by decide +kernel⟩

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
