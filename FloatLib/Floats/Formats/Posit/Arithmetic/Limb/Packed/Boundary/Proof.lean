/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Decode.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.Boundary.Runtime
public import FloatLib.Floats.Formats.Posit.Model.Basic
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Rounding.Proof
import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Decode.Proof

/-!
# Range and refinement laws for packed two-limb boundaries

The abstract theorems in this module let operation proofs reason about decoded options without
unfolding the packed decoder. Re-encoding agrees with a model-valued operation whenever the
NaR code and finite kernel agree separately, and a native two-operand kernel that returns the NaR
word on NaR inputs is a binary boundary over the decoded operands. The last section specializes
the binary laws to two-limb rounding of an exact dyadic operation, the shape shared by packed
addition, subtraction and multiplication.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeLimbPacked.Boundary

variable {format : Format}

/-- A unary boundary is in range when both its NaR code and finite kernel are in range. -/
theorem unaryCode_lt
    {narCode bound : Nat}
    (operation : FloatLib.Numerics.Dyadic → Nat)
    (value : Option FloatLib.Numerics.Dyadic)
    (hnarCode : narCode < bound)
    (hoperation : ∀ finite, operation finite < bound) :
    unaryCode narCode operation value < bound := by
  cases value with
  | none => exact hnarCode
  | some finite => exact hoperation finite

/-- A binary boundary is in range when its NaR code and every finite result are in range. -/
theorem binaryCode_lt
    {narCode bound : Nat}
    (operation :
      FloatLib.Numerics.Dyadic → FloatLib.Numerics.Dyadic → Nat)
    (left right : Option FloatLib.Numerics.Dyadic)
    (hnarCode : narCode < bound)
    (hoperation :
      ∀ leftValue rightValue, operation leftValue rightValue < bound) :
    binaryCode narCode operation left right < bound := by
  cases left with
  | none => exact hnarCode
  | some leftValue =>
      cases right with
      | none => exact hnarCode
      | some rightValue => exact hoperation leftValue rightValue

/-- A ternary boundary is in range when its NaR code and every finite result are in range. -/
theorem ternaryCode_lt
    {narCode bound : Nat}
    (operation :
      FloatLib.Numerics.Dyadic → FloatLib.Numerics.Dyadic →
        FloatLib.Numerics.Dyadic → Nat)
    (left right third : Option FloatLib.Numerics.Dyadic)
    (hnarCode : narCode < bound)
    (hoperation :
      ∀ leftValue rightValue thirdValue,
        operation leftValue rightValue thirdValue < bound) :
    ternaryCode narCode operation left right third < bound := by
  cases left with
  | none => exact hnarCode
  | some leftValue =>
      cases right with
      | none => exact hnarCode
      | some rightValue =>
          cases third with
          | none => exact hnarCode
          | some thirdValue =>
              exact hoperation leftValue rightValue thirdValue

/--
Re-encoding a unary boundary agrees with its model-valued operation when the NaR code and finite
kernel do. The decoded option remains abstract throughout the proof.
-/
theorem ofNatBits_unaryCode
    (narCode : Nat)
    (operation : FloatLib.Numerics.Dyadic → Nat)
    (semantic : FloatLib.Numerics.Dyadic → Model format)
    (value : Option FloatLib.Numerics.Dyadic)
    (hnarCode :
      Model.ofNatBits (format := format) narCode = Model.nar format)
    (hoperation :
      ∀ finite,
        Model.ofNatBits (format := format) (operation finite) =
          semantic finite) :
    Model.ofNatBits (format := format)
        (unaryCode narCode operation value) =
      unaryResult (Model.nar format) semantic value := by
  cases value with
  | none => exact hnarCode
  | some finite => exact hoperation finite

/--
Unary refinement with separate encoded and semantic decoder results. Keeping their equality as an
argument avoids rewriting inside a concrete packed-decoder expression in operation modules.
-/
theorem ofNatBits_unaryCode_of_eq
    (narCode : Nat)
    (operation : FloatLib.Numerics.Dyadic → Nat)
    (semantic : FloatLib.Numerics.Dyadic → Model format)
    (encodedValue semanticValue : Option FloatLib.Numerics.Dyadic)
    (hvalue : encodedValue = semanticValue)
    (hnarCode :
      Model.ofNatBits (format := format) narCode = Model.nar format)
    (hoperation :
      ∀ finite,
        Model.ofNatBits (format := format) (operation finite) =
          semantic finite) :
    Model.ofNatBits (format := format)
        (unaryCode narCode operation encodedValue) =
      unaryResult (Model.nar format) semantic semanticValue := by
  subst hvalue
  exact ofNatBits_unaryCode narCode operation semantic encodedValue hnarCode hoperation

/--
A native two-operand kernel whose continuation refines `operation` on decoded fields, and which
returns the NaR word when either input is NaR, computes the binary boundary over the decoded
inputs.
-/
theorem withTwoDyadicFields_toNat_eq_binaryCode
    (heligible : NativeLimb.Eligible format)
    (left right : FloatLib.Numerics.FixedWord.UInt128)
    (continuation :
      Bool → FloatLib.Numerics.FixedWord.UInt128 → Int →
      Bool → FloatLib.Numerics.FixedWord.UInt128 → Int →
        FloatLib.Numerics.FixedWord.UInt128)
    (operation :
      FloatLib.Numerics.Dyadic → FloatLib.Numerics.Dyadic → Nat)
    (hrefine :
      ∀ leftNegative leftSignificand leftExponent
          rightNegative rightSignificand rightExponent,
        (continuation
            leftNegative leftSignificand leftExponent
            rightNegative rightSignificand rightExponent).toNat =
          operation
            ⟨leftNegative, leftSignificand.toNat, leftExponent⟩
            ⟨rightNegative, rightSignificand.toNat, rightExponent⟩) :
    (NativeLimb.withTwoDyadicFields format left right
        (NativeLimb.signMaskWord format) continuation).toNat =
      binaryCode format.signMaskNat operation
        (NativeLimb.toDyadic? format left)
        (NativeLimb.toDyadic? format right) := by
  rw [NativeLimb.map_withTwoDyadicFields_eq_match_toDyadic?
      FloatLib.Numerics.FixedWord.UInt128.toNat format left right
      (NativeLimb.signMaskWord format) continuation
      (fun leftNegative leftSignificand leftExponent
          rightNegative rightSignificand rightExponent =>
        operation
          ⟨leftNegative, leftSignificand, leftExponent⟩
          ⟨rightNegative, rightSignificand, rightExponent⟩)
      hrefine,
    NativeLimb.signMaskWord_toNat format heligible]
  unfold binaryCode binaryResult
  cases NativeLimb.toDyadic? format left with
  | none => rfl
  | some leftValue =>
      cases NativeLimb.toDyadic? format right <;> rfl

/--
Re-encoding a binary boundary agrees with its model-valued operation when the NaR code and finite
kernel do.
-/
theorem ofNatBits_binaryCode
    (narCode : Nat)
    (operation :
      FloatLib.Numerics.Dyadic → FloatLib.Numerics.Dyadic → Nat)
    (semantic :
      FloatLib.Numerics.Dyadic → FloatLib.Numerics.Dyadic →
        Model format)
    (left right : Option FloatLib.Numerics.Dyadic)
    (hnarCode :
      Model.ofNatBits (format := format) narCode = Model.nar format)
    (hoperation :
      ∀ leftValue rightValue,
        Model.ofNatBits (format := format)
            (operation leftValue rightValue) =
          semantic leftValue rightValue) :
    Model.ofNatBits (format := format)
        (binaryCode narCode operation left right) =
      binaryResult (Model.nar format) semantic left right := by
  cases left with
  | none => exact hnarCode
  | some leftValue =>
      cases right with
      | none => exact hnarCode
      | some rightValue => exact hoperation leftValue rightValue

/--
Binary refinement with separate encoded and semantic decoder results. The equalities are consumed
by this small abstract theorem rather than by each packed operation proof.
-/
theorem ofNatBits_binaryCode_of_eq
    (narCode : Nat)
    (operation :
      FloatLib.Numerics.Dyadic → FloatLib.Numerics.Dyadic → Nat)
    (semantic :
      FloatLib.Numerics.Dyadic → FloatLib.Numerics.Dyadic →
        Model format)
    (encodedLeft encodedRight semanticLeft semanticRight :
      Option FloatLib.Numerics.Dyadic)
    (hleft : encodedLeft = semanticLeft)
    (hright : encodedRight = semanticRight)
    (hnarCode :
      Model.ofNatBits (format := format) narCode = Model.nar format)
    (hoperation :
      ∀ leftValue rightValue,
        Model.ofNatBits (format := format)
            (operation leftValue rightValue) =
          semantic leftValue rightValue) :
    Model.ofNatBits (format := format)
        (binaryCode narCode operation encodedLeft encodedRight) =
      binaryResult (Model.nar format)
        semantic semanticLeft semanticRight := by
  subst hleft hright
  exact ofNatBits_binaryCode narCode operation semantic encodedLeft encodedRight
    hnarCode hoperation

/--
Re-encoding a ternary boundary agrees with its model-valued operation when the NaR code and finite
kernel do.
-/
theorem ofNatBits_ternaryCode
    (narCode : Nat)
    (operation :
      FloatLib.Numerics.Dyadic → FloatLib.Numerics.Dyadic →
        FloatLib.Numerics.Dyadic → Nat)
    (semantic :
      FloatLib.Numerics.Dyadic → FloatLib.Numerics.Dyadic →
        FloatLib.Numerics.Dyadic → Model format)
    (left right third : Option FloatLib.Numerics.Dyadic)
    (hnarCode :
      Model.ofNatBits (format := format) narCode = Model.nar format)
    (hoperation :
      ∀ leftValue rightValue thirdValue,
        Model.ofNatBits (format := format)
            (operation leftValue rightValue thirdValue) =
          semantic leftValue rightValue thirdValue) :
    Model.ofNatBits (format := format)
        (ternaryCode narCode operation left right third) =
      ternaryResult (Model.nar format) semantic left right third := by
  cases left with
  | none => exact hnarCode
  | some leftValue =>
      cases right with
      | none => exact hnarCode
      | some rightValue =>
          cases third with
          | none => exact hnarCode
          | some thirdValue =>
              exact hoperation leftValue rightValue thirdValue

/-- Ternary refinement with distinct packed and semantic decoder results. -/
theorem ofNatBits_ternaryCode_of_eq
    (narCode : Nat)
    (operation :
      FloatLib.Numerics.Dyadic → FloatLib.Numerics.Dyadic →
        FloatLib.Numerics.Dyadic → Nat)
    (semantic :
      FloatLib.Numerics.Dyadic → FloatLib.Numerics.Dyadic →
        FloatLib.Numerics.Dyadic → Model format)
    (encodedLeft encodedRight encodedThird semanticLeft semanticRight
      semanticThird : Option FloatLib.Numerics.Dyadic)
    (hleft : encodedLeft = semanticLeft)
    (hright : encodedRight = semanticRight)
    (hthird : encodedThird = semanticThird)
    (hnarCode :
      Model.ofNatBits (format := format) narCode = Model.nar format)
    (hoperation :
      ∀ leftValue rightValue thirdValue,
        Model.ofNatBits (format := format)
            (operation leftValue rightValue thirdValue) =
          semantic leftValue rightValue thirdValue) :
    Model.ofNatBits (format := format)
        (ternaryCode narCode operation
          encodedLeft encodedRight encodedThird) =
      ternaryResult (Model.nar format)
        semantic semanticLeft semanticRight semanticThird := by
  subst hleft hright hthird
  exact ofNatBits_ternaryCode narCode operation semantic
    encodedLeft encodedRight encodedThird hnarCode hoperation

/-! ## Boundaries around two-limb rounding -/

/--
A binary boundary around two-limb rounding of an exact dyadic operation is always a complete posit
code: NaR inputs give the NaR word and every finite result is a rounded code.
-/
theorem binaryCode_roundCodeNat_lt_modulus
    (heligible : NativeLimb.Eligible format)
    (operation :
      FloatLib.Numerics.Dyadic → FloatLib.Numerics.Dyadic → FloatLib.Numerics.Dyadic)
    (left right : Option FloatLib.Numerics.Dyadic) :
    binaryCode format.signMaskNat
        (fun leftValue rightValue =>
          NativeLimbRounding.roundCodeNat format heligible (operation leftValue rightValue))
        left right < format.modulus :=
  binaryCode_lt _ left right format.signMaskNat_lt_modulus fun leftValue rightValue =>
    NativeLimbRounding.roundCodeNat_lt_modulus format heligible (operation leftValue rightValue)

/--
Over two decoded in-range words, re-encoding a binary boundary around two-limb rounding gives the
model-valued boundary around the model-valued two-limb rounder.
-/
theorem ofNatBits_binaryCode_roundCodeNat
    (heligible : NativeLimb.Eligible format)
    (operation :
      FloatLib.Numerics.Dyadic → FloatLib.Numerics.Dyadic → FloatLib.Numerics.Dyadic)
    (left right : FloatLib.Numerics.FixedWord.UInt128)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) :
    Model.ofNatBits (format := format)
        (binaryCode format.signMaskNat
          (fun leftValue rightValue =>
            NativeLimbRounding.roundCodeNat format heligible (operation leftValue rightValue))
          (NativeLimb.toDyadic? format left) (NativeLimb.toDyadic? format right)) =
      binaryResult (Model.nar format)
        (fun leftValue rightValue =>
          NativeLimbRounding.round format heligible (operation leftValue rightValue))
        (Model.ofNatBits (format := format) left.toNat).toDyadic?
        (Model.ofNatBits (format := format) right.toNat).toDyadic? :=
  ofNatBits_binaryCode_of_eq _ _ _ _ _ _ _
    (NativeLimb.toDyadic?_eq_model format left heligible hleft)
    (NativeLimb.toDyadic?_eq_model format right heligible hright) rfl
    fun leftValue rightValue =>
      NativeLimbRounding.ofNatBits_roundCodeNat format heligible (operation leftValue rightValue)

end FloatLib.Floats.Formats.Posit.Model.NativeLimbPacked.Boundary
