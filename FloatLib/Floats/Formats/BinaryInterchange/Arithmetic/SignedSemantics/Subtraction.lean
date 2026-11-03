/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.SignedSemantics.Core
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Semantics

/-!
# Correctness of binary subtraction

Subtraction is implemented as addition of the negated right operand. These theorems connect that
implementation to exact real subtraction followed by one nearest-even rounding step. A difference
with a zero operand, and `x - x` of a finite `x`, does not round (`toReal_sub_of_isZero_left`,
`toReal_sub_of_isZero_right`, `toReal_sub_self`). By decoded value, a finite `x - x` decodes to
`some 0` (`toRat?_sub_self`), and a difference whose exact value is the decoded value of some
encoding decodes to that value (`toRat?_sub_of_representable`).
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-- Nearest-even subtraction is nearest-even addition of the negated subtrahend. -/
private theorem sub_eq_add_neg {fmt : FloatFormat} (x y : Model fmt) :
    sub x y = add x (neg y) :=
  calc
    sub x y = Spec.sub x y := Proof.sub_eq_spec x y
    _ = Spec.add x (neg y) := rfl
    _ = add x (neg y) := (Proof.add_eq_spec x (neg y)).symm

/--
Under a conventional IEEE descriptor a finite difference has finite operands, since subtraction
adds the negated subtrahend.
-/
theorem isFinite_of_isFinite_sub {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    {x y : Model fmt} (h : isFinite (sub x y) = true) :
    isFinite x = true ∧ isFinite y = true := by
  rw [sub_eq_add_neg] at h
  simpa using isFinite_of_isFinite_add hfmt h

/--
Finite operands whose exact real difference is within the destination's largest finite magnitude
cannot overflow under nearest-even subtraction.
-/
theorem isFinite_sub_of_abs_toReal_sub_le_posMaxFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hbound : |toReal x - toReal y| ≤ toReal (posMaxFinite fmt)) :
    isFinite (sub x y) = true := by
  have hyneg : isFinite (neg y) = true := by simpa using hy
  rw [sub_eq_add_neg]
  apply isFinite_add_of_abs_toReal_add_le_posMaxFinite x (neg y) hfmt hx hyneg
  rw [toReal_neg y hy]
  simpa [_root_.sub_eq_add_neg] using hbound

/--
The triangle bound `|x| + |y| ≤ maxFinite` is a symbolic sufficient condition for finite
nearest-even subtraction.
-/
theorem isFinite_sub_of_abs_add_le_posMaxFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hbound : |toReal x| + |toReal y| ≤ toReal (posMaxFinite fmt)) :
    isFinite (sub x y) = true := by
  apply isFinite_sub_of_abs_toReal_sub_le_posMaxFinite x y hfmt hx hy
  calc
    |toReal x - toReal y| = |toReal x + -toReal y| := by ring_nf
    _ ≤ |toReal x| + |-toReal y| := abs_add_le _ _
    _ = |toReal x| + |toReal y| := by rw [abs_neg]
    _ ≤ toReal (posMaxFinite fmt) := hbound

/--
Finite subtraction is exact real subtraction followed by one nearest-even format rounding.

The hypothesis `hfin` excludes overflow by asking that the executable difference be finite, and it
forces finite operands; `toReal_sub_eq_roundAt_of_abs_add_le_posMaxFinite` supplies it from a
bound on the operands.
-/
theorem toReal_sub_eq_roundAt {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hfin : isFinite (sub x y) = true) :
    toReal (sub x y) = roundAt fmt (toReal x - toReal y) := by
  have hy := (isFinite_of_isFinite_sub hfmt hfin).2
  rw [sub_eq_add_neg] at hfin ⊢
  rw [toReal_add_eq_roundAt x (neg y) hfmt hfin, toReal_neg y hy]
  ring_nf

/--
Finite subtraction under a symbolic triangle bound is exact real subtraction followed by one
nearest-even format rounding.
-/
theorem toReal_sub_eq_roundAt_of_abs_add_le_posMaxFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hbound : |toReal x| + |toReal y| ≤ toReal (posMaxFinite fmt)) :
    toReal (sub x y) = roundAt fmt (toReal x - toReal y) :=
  toReal_sub_eq_roundAt x y hfmt
    (isFinite_sub_of_abs_add_le_posMaxFinite x y hfmt hx hy hbound)

/-- Subtracting a finite value from a zero is exact negation. -/
theorem toReal_sub_of_isZero_left {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true) (hx : isZero x = true) (hy : isFinite y = true) :
    toReal (sub x y) = -toReal y := by
  have hxf := isFinite_eq_true_of_isZero_eq_true x hx
  have h0 := toReal_eq_zero_of_isZero x hx
  have hout := isFinite_sub_of_abs_toReal_sub_le_posMaxFinite x y hfmt hxf hy (by
    rw [h0, zero_sub, abs_neg]
    exact abs_toReal_le_posMaxFinite_of_isFinite y hy)
  rw [toReal_sub_eq_roundAt x y hfmt hout, h0, zero_sub, roundAt_neg,
    IEEERoundingMode.negate, roundAt_toReal_eq y hy]

/-- Subtracting a zero from a finite value is exact. -/
theorem toReal_sub_of_isZero_right {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true) (hx : isFinite x = true) (hy : isZero y = true) :
    toReal (sub x y) = toReal x := by
  have hyf := isFinite_eq_true_of_isZero_eq_true y hy
  have h0 := toReal_eq_zero_of_isZero y hy
  have hout := isFinite_sub_of_abs_toReal_sub_le_posMaxFinite x y hfmt hx hyf
    (by rw [h0, sub_zero]; exact abs_toReal_le_posMaxFinite_of_isFinite x hx)
  rw [toReal_sub_eq_roundAt x y hfmt hout, h0, sub_zero, roundAt_toReal_eq x hx]

/-- Subtracting a finite value from itself gives exactly zero. -/
theorem toReal_sub_self {fmt : FloatFormat} {x : Model fmt} (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) : toReal (sub x x) = 0 := by
  have hout := isFinite_sub_of_abs_toReal_sub_le_posMaxFinite x x hfmt hx hx (by
    rw [sub_self, abs_zero]
    exact (abs_nonneg _).trans (abs_toReal_le_posMaxFinite_of_isFinite x hx))
  rw [toReal_sub_eq_roundAt x x hfmt hout, sub_self, roundAt_zero]

section Decoded

variable {fmt : FloatFormat} {x y z : Model fmt}

/--
If the exact difference of two decoded values is the decoded value of some `z`, the rounded
difference decodes to that exact difference.
-/
theorem toRat?_sub_of_representable (hfmt : fmt.isIEEE = true) {p q : ℚ}
    (hx : toRat? x = some p) (hy : toRat? y = some q) (hz : toRat? z = some (p - q)) :
    toRat? (sub x y) = some (p - q) := by
  have hxf := Algebraic.isFinite_of_toRat?_eq_some hx
  have hyf := Algebraic.isFinite_of_toRat?_eq_some hy
  have hzf := Algebraic.isFinite_of_toRat?_eq_some hz
  have hexact : toReal x - toReal y = toReal z := by
    rw [Algebraic.toReal_of_toRat?_eq_some hx, Algebraic.toReal_of_toRat?_eq_some hy,
      Algebraic.toReal_of_toRat?_eq_some hz, Rat.cast_sub]
  have hout := isFinite_sub_of_abs_toReal_sub_le_posMaxFinite x y hfmt hxf hyf
    (by rw [hexact]; exact abs_toReal_le_posMaxFinite_of_isFinite z hzf)
  refine Algebraic.toRat?_eq_some_of_toReal_eq hout ?_
  rw [toReal_sub_eq_roundAt x y hfmt hout, hexact, roundAt_toReal_eq z hzf,
    Algebraic.toReal_of_toRat?_eq_some hz]

/-- Subtracting a finite value from itself gives a value that decodes to zero. -/
theorem toRat?_sub_self (hfmt : fmt.isIEEE = true) (hx : isFinite x = true) :
    toRat? (sub x x) = some 0 :=
  Algebraic.toRat?_eq_some_of_toReal_eq
    (isFinite_sub_of_abs_toReal_sub_le_posMaxFinite x x hfmt hx hx (by
      rw [sub_self, abs_zero]
      exact (abs_nonneg _).trans (abs_toReal_le_posMaxFinite_of_isFinite x hx)))
    (by rw [toReal_sub_self hfmt hx, Rat.cast_zero])

end Decoded

end Model
end FloatLib.Floats.Formats.BinaryInterchange
