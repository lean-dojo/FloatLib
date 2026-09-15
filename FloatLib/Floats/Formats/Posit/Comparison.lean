/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Model.Basic
public import Mathlib.Data.FinEnum

/-!
# Standard posit comparisons and finite enumeration

The Posit Standard (2022) defines comparisons by regarding the complete encoded words as
two's-complement signed integers. In particular, NaR compares as the least encoded value and two
NaR words compare equal. This is an ordering of *posit values*, including NaR; it is deliberately
not presented as an order embedding into `Rat` or `Real`, because NaR has no real denotation.

This module transports Lean's proved `BitVec.toInt` order to `Model format`. It also exposes the
exact equivalence with `BitVec format.bits` and derives Mathlib's `FinEnum`/`Fintype`
infrastructure from that equivalence. Exhaustive proofs can therefore enumerate the model without
maintaining a second list of encodings.

## References

* Posit Working Group, *Standard for Posit Arithmetic (2022)*, March 2, 2022,
  Section 5.3, <https://posithub.org/docs/posit_standard-2.pdf>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit

namespace Model

variable {format : Format}

/-- Representation-preserving equivalence between a posit model and its complete encoded word. -/
def bitsEquiv (format : Format) : Model format ≃ BitVec format.bits where
  toFun value := value.bits
  invFun bits := ofBits bits
  left_inv value := by cases value; rfl
  right_inv _ := rfl

/--
Canonical finite enumeration inherited from exact-width bit vectors.

The enumeration is by unsigned word, which is useful for encoding tables and exhaustive
conformance checks. The `LinearOrder` below is separately the standard's signed comparison order.
-/
instance : FinEnum (Model format) :=
  FinEnum.ofEquiv (BitVec format.bits) (bitsEquiv format)

/-- The number of posit words is exactly `2 ^ format.bits`, including zero and NaR. -/
@[simp] theorem finEnum_card (format : Format) :
    FinEnum.card (Model format) = 2 ^ format.bits :=
  rfl

/-- Interpret the complete posit word as a two's-complement signed integer. -/
@[inline] def signedCode (value : Model format) : Int :=
  value.bits.toInt

/-- Signed-code interpretation is injective at a fixed width. -/
theorem signedCode_injective :
    Function.Injective (@signedCode format) := by
  intro left right equality
  cases left with
  | mk leftBits =>
      cases right with
      | mk rightBits =>
          apply congrArg ofBits
          exact BitVec.eq_of_toInt_eq equality

/--
The standard total order on posit words.

This instance makes ordinary Lean notation (`<`, `≤`, `min`, `max`, sorting, intervals) agree
with Posit Standard comparisons. NaR is included as the least word; numerical theorems that must
exclude NaR should state that premise explicitly or use `toRat?`.

The order is transported along `signedCode`, but the `DecidableEq` field reuses the derived
instance so that the model has a single decidable equality.
-/
instance : LinearOrder (Model format) where
  __ := PartialOrder.lift signedCode signedCode_injective
  le_total left right := le_total (signedCode left) (signedCode right)
  toDecidableLE left right :=
    inferInstanceAs (Decidable (signedCode left ≤ signedCode right))
  toDecidableLT left right :=
    inferInstanceAs (Decidable (signedCode left < signedCode right))
  toDecidableEq := inferInstance

/-- Standard equality comparison. -/
@[inline] def compareEqual (left right : Model format) : Bool :=
  left == right

/-- Standard inequality comparison. -/
@[inline] def compareNotEqual (left right : Model format) : Bool :=
  left != right

/-- Standard strict-less comparison, executed directly on the encoded words. -/
@[inline] def compareLess (left right : Model format) : Bool :=
  left.bits.slt right.bits

/-- Standard less-or-equal comparison, executed directly on the encoded words. -/
@[inline] def compareLessEqual (left right : Model format) : Bool :=
  left.bits.sle right.bits

/-- Standard strict-greater comparison, executed by reversing strict-less. -/
@[inline] def compareGreater (left right : Model format) : Bool :=
  right.bits.slt left.bits

/-- Standard greater-or-equal comparison, executed by reversing less-or-equal. -/
@[inline] def compareGreaterEqual (left right : Model format) : Bool :=
  right.bits.sle left.bits

/-- Boolean equality agrees exactly with equality in the posit model. -/
@[simp] theorem compareEqual_eq_true_iff (left right : Model format) :
    compareEqual left right = true ↔ left = right := by
  simp [compareEqual]

/-- Boolean inequality agrees exactly with inequality in the posit model. -/
@[simp] theorem compareNotEqual_eq_true_iff (left right : Model format) :
    compareNotEqual left right = true ↔ left ≠ right := by
  simp [compareNotEqual]

/-- Encoded strict-less comparison agrees with the standard signed-word order. -/
@[simp] theorem compareLess_eq_true_iff (left right : Model format) :
    compareLess left right = true ↔ left < right := by
  exact BitVec.slt_iff_toInt_lt

/-- Encoded less-or-equal comparison agrees with the standard signed-word order. -/
@[simp] theorem compareLessEqual_eq_true_iff (left right : Model format) :
    compareLessEqual left right = true ↔ left ≤ right := by
  exact BitVec.sle_iff_toInt_le

/-- Encoded strict-greater comparison agrees with the standard signed-word order. -/
@[simp] theorem compareGreater_eq_true_iff (left right : Model format) :
    compareGreater left right = true ↔ left > right := by
  exact BitVec.slt_iff_toInt_lt

/-- Encoded greater-or-equal comparison agrees with the standard signed-word order. -/
@[simp] theorem compareGreaterEqual_eq_true_iff (left right : Model format) :
    compareGreaterEqual left right = true ↔ left ≥ right := by
  exact BitVec.sle_iff_toInt_le

/-- Equality of NaR with itself follows the standard's encoded comparison rule. -/
@[simp] theorem compareEqual_nar_nar (format : Format) :
    compareEqual (nar format) (nar format) = true := by
  simp

end Model

end FloatLib.Floats.Formats.Posit
