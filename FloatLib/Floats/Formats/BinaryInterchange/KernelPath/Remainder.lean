/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.FormatOf
public meta import FloatLib.Tactic.IeeeExtrema
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Runtime

/-!
# `remainder` on encodings

IEEE 754-2019 §5.3.1 `remainder` delivers `x - n * y` for the integer `n` nearest to `x / y`,
ties to even. The reference `Model.remainder` decodes two finite operands, forms the exact
remainder `Model.remainderDyadic` (by modular exponentiation when the exponents are far apart)
and encodes it, which is exact.

`remainder fmt a b` computes the encoding of the result from the two encodings: finite words
with a nonzero divisor are decoded with `KernelPath.decode`, the exact remainder is the
reference's, and `KernelPath.roundDyadic` encodes it; a NaN, an infinity and a zero divisor go
to the reference operation on the decoded words. `remainder_eq_spec` proves it equal to the
encoding of `Model.remainder x y`, for every format descriptor and all operands.

`Value.remainder` is the operation on stored values, with `Value.remainder_eq_lift` and the
rule `Value.toNat_remainder`.

With its status, the reference delivers the same value and the `invalid` flag of a signaling
NaN, an infinite dividend or a zero divisor. `remainderInvalid fmt a b` computes that flag on
the two encodings, and `remainder_status_eq` proves the outcome of the reference equal to the
value with this flag, for every format descriptor and all operands.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

/--
Encoding of the IEEE remainder of the values that `a` and `b` encode (`remainder_eq_spec`):
the exact remainder of two finite words with a nonzero divisor, encoded without rounding, and
the reference rule otherwise.
-/
def remainder (fmt : FloatFormat) (a b : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (bothFinite fmt fmt a b)
    (Model.remainder (Model.ofNatBits a : Model fmt) (Model.ofNatBits b)).toNatBits
    (if hdivisor : (decode fmt b).significand = 0 then
      (Model.remainder (Model.ofNatBits a : Model fmt) (Model.ofNatBits b)).toNatBits
    else
      (fun exact : Numerics.Dyadic =>
        Bool.casesOn (motive := fun _ => Nat) (Nat.beq exact.significand 0)
          (roundDyadic fmt .nearest exact) (zeroWord fmt (decode fmt a).negative))
        (Model.remainderDyadic (decode fmt a) (decode fmt b) hdivisor))

/--
`remainder` computes the encoding of `Model.remainder x y`, for every format descriptor and
all operands.
-/
theorem remainder_eq_spec {fmt : FloatFormat} (x y : Model fmt) :
    remainder fmt x.toNatBits y.toNatBits = (Model.remainder x y).toNatBits := by
  unfold remainder
  rw [bothFinite_eq, Model.ofNatBits_toNatBits, Model.ofNatBits_toNatBits]
  cases hx : Model.isFinite x
  · rfl
  · cases hy : Model.isFinite y
    · rfl
    · by_cases hdivisor : (decode fmt y.toNatBits).significand = 0
      · rw [dite_eq_left hdivisor]
        rfl
      · have hdx := Model.exactValue_eq_finite_of_toDyadic?_eq_some (toDyadic?_eq_decode x hx)
        have hdy := Model.exactValue_eq_finite_of_toDyadic?_eq_some (toDyadic?_eq_decode y hy)
        rw [dite_eq_right hdivisor]
        change _ = (Model.Internal.Status.remainder x y).value.toNatBits
        unfold Model.Internal.Status.remainder
        simp only [hdx, hdy, hdivisor, dite_false, Model.outcomeWithInvalid]
        by_cases hzero : (Model.remainderDyadic (decode fmt x.toNatBits)
            (decode fmt y.toNatBits) hdivisor).significand = 0
        · simp only [hzero, beq_self_eq_true, ite_true]
          rw [zeroWord_eq]
          rfl
        · have hbeq : ((Model.remainderDyadic (decode fmt x.toNatBits)
              (decode fmt y.toNatBits) hdivisor).significand == 0) = false := by
            simpa using hzero
          simp only [hbeq, Bool.false_eq_true, ite_false, beq_zero_eq_false hzero,
            roundDyadic_nearest_eq]
          rfl

/--
Whether `remainder` signals `invalid` on the words `a` and `b` (`remainder_status_eq`): one of
them is a signaling NaN, or neither is a NaN and the dividend is infinite or the divisor is
zero.
-/
def remainderInvalid (fmt : FloatFormat) (a b : Nat) : Bool :=
  Bool.or (Bool.or (Nat.beq (signalingCode fmt a) 1) (Nat.beq (signalingCode fmt b) 1))
    (Bool.and
      (Bool.and (Bool.not (Nat.beq (nanCode fmt a) 1)) (Bool.not (Nat.beq (nanCode fmt b) 1)))
      (Bool.or (Nat.beq (infCode fmt a) 1) (Nat.beq (zeroCode fmt b) 1)))

/--
The exact value of a word is finite, an infinity or a NaN, with the classification that goes
with each.
-/
theorem exactValue_cases {fmt : FloatFormat} (z : Model fmt) :
    (∃ d, Model.exactValue z = .finite d ∧ Model.isNaN z = false ∧
        Model.isSignaling z = false ∧ Model.isInfinite z = false ∧
        Model.isZero z = decide (d.significand = 0)) ∨
      (Model.exactValue z = .infinity (Model.signBit z) ∧ Model.isNaN z = false ∧
        Model.isSignaling z = false ∧ Model.isInfinite z = true ∧ Model.isZero z = false) ∨
      (Model.exactValue z =
          .nan (Model.signBit z) (Model.isSignaling z) (Model.fracField z) ∧
        Model.isNaN z = true ∧ Model.isInfinite z = false) := by
  cases hdecode : Model.toDyadic? z with
  | some d =>
      have hfinite := Model.isFinite_eq_true_of_toDyadic?_some hdecode
      have hnan := Model.isNaN_eq_false_of_isFinite_eq_true z hfinite
      refine Or.inl ⟨d, Model.exactValue_eq_finite_of_toDyadic?_eq_some hdecode, hnan,
        Model.isSignaling_eq_false_of_isNaN_eq_false z hnan,
        Model.isInfinite_eq_false_of_isFinite_eq_true z hfinite, ?_⟩
      by_cases hsignificand : d.significand = 0
      · rw [Model.isZero_eq_true_of_toDyadic?_some_of_mant_eq_zero hdecode hsignificand,
          decide_eq_true hsignificand]
      · rw [decide_eq_false hsignificand]
        cases hzero : Model.isZero z
        · rfl
        · have hd := Model.toDyadic?_eq_zero_of_isZero_eq_true z hzero
          rw [hdecode] at hd
          exact absurd (by rw [Option.some.inj hd]) hsignificand
  | none =>
      cases hinfinite : Model.isInfinite z
      · refine Or.inr (Or.inr ⟨?_,
          Model.isNaN_eq_true_of_toDyadic?_eq_none_of_isInfinite_eq_false hdecode hinfinite,
          rfl⟩)
        unfold Model.exactValue
        rw [hdecode, hinfinite]
        rfl
      · have hnan := Model.isNaN_eq_false_of_isInfinite_eq_true z hinfinite
        refine Or.inr (Or.inl ⟨?_, hnan, Model.isSignaling_eq_false_of_isNaN_eq_false z hnan,
          rfl, Model.isZero_eq_false_of_isInfinite_eq_true z hinfinite⟩)
        unfold Model.exactValue
        rw [hdecode, hinfinite]
        rfl

/--
The outcome of `remainder` with its status is the value of `remainder` with the `invalid` flag
that `remainderInvalid` computes on the two encodings, for every format descriptor and all
operands.
-/
theorem remainder_status_eq {fmt : FloatFormat} (x y : Model fmt) :
    Model.Internal.Status.remainder x y =
      Model.outcomeWithInvalid (Model.remainder x y)
        (remainderInvalid fmt x.toNatBits y.toNatBits) := by
  have hvalue : Model.remainder x y = (Model.Internal.Status.remainder x y).value := rfl
  rw [hvalue]
  unfold remainderInvalid
  rw [signalingCode_eq, signalingCode_eq, nanCode_eq, nanCode_eq, infCode_eq, zeroCode_eq]
  unfold Model.Internal.Status.remainder
  rcases exactValue_cases x with
    ⟨dx, hx, hnx, hsx, hix, -⟩ | ⟨hx, hnx, hsx, hix, -⟩ | ⟨hx, hnx, hix⟩ <;>
  rcases exactValue_cases y with
    ⟨dy, hy, hny, hsy, -, hzy⟩ | ⟨hy, hny, hsy, -, hzy⟩ | ⟨hy, hny, -⟩
  · by_cases hdivisor : dy.significand = 0 <;>
      simp [hx, hy, hnx, hny, hsx, hsy, hix, hzy, hdivisor, Model.outcomeWithInvalid]
  · simp [hx, hy, hnx, hny, hsx, hsy, hix, hzy, Model.outcomeWithInvalid]
  · cases hsignaling : Model.isSignaling y <;>
      simp [hx, hy, hnx, hny, hsx, hsignaling, hix, Model.outcomeWithInvalid]
  · simp [hx, hy, hnx, hny, hsx, hsy, hix, hzy, Model.outcomeWithInvalid]
  · simp [hx, hy, hnx, hny, hsx, hsy, hix, hzy, Model.outcomeWithInvalid]
  · cases hsignaling : Model.isSignaling y <;>
      simp [hx, hy, hnx, hny, hsx, hsignaling, hix, Model.outcomeWithInvalid]
  · cases hsignaling : Model.isSignaling x <;>
      simp [hx, hy, hnx, hny, hsy, hsignaling, hix, Model.outcomeWithInvalid]
  · cases hsignaling : Model.isSignaling x <;>
      simp [hx, hy, hnx, hny, hsy, hsignaling, hix, Model.outcomeWithInvalid]
  · cases hsignalingX : Model.isSignaling x <;> cases hsignalingY : Model.isSignaling y <;>
      simp [hx, hy, hnx, hny, hsignalingX, hsignalingY, hix, Model.outcomeWithInvalid]

namespace Value

universe u

variable {F : Type u} [EncodedFormat F] {format : FloatFormat} [view : NatView F format]

/-- Kernel `remainder` of two stored values (IEEE 754-2019 §5.3.1). -/
selection remainder := (KernelPath.remainder format), (fun x y => Model.remainder x y),
  remainder_eq_spec

end Value

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
