/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.Boundary.Runtime
public import FloatLib.Floats.Formats.Posit.Model.Basic

/-!
# Range and refinement laws for packed two-limb boundaries

The abstract theorems in this module let operation proofs reason about decoded options without
unfolding the packed decoder. Re-encoding agrees with a model-valued operation whenever the
NaR code and finite kernel agree separately.
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
  calc
    Model.ofNatBits (format := format)
        (unaryCode narCode operation encodedValue) =
        unaryResult (Model.nar format) semantic encodedValue :=
      ofNatBits_unaryCode
        narCode operation semantic encodedValue hnarCode hoperation
    _ = unaryResult (Model.nar format) semantic semanticValue :=
      congrArg (unaryResult (Model.nar format) semantic) hvalue

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
  calc
    Model.ofNatBits (format := format)
        (binaryCode narCode operation encodedLeft encodedRight) =
        binaryResult (Model.nar format)
          semantic encodedLeft encodedRight :=
      ofNatBits_binaryCode
        narCode operation semantic encodedLeft encodedRight
        hnarCode hoperation
    _ =
        binaryResult (Model.nar format)
          semantic semanticLeft encodedRight :=
      congrArg
        (fun left =>
          binaryResult (Model.nar format)
            semantic left encodedRight)
        hleft
    _ =
        binaryResult (Model.nar format)
          semantic semanticLeft semanticRight :=
      congrArg
        (fun right =>
          binaryResult (Model.nar format)
            semantic semanticLeft right)
        hright

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
  calc
    Model.ofNatBits (format := format)
        (ternaryCode narCode operation
          encodedLeft encodedRight encodedThird) =
        ternaryResult (Model.nar format)
          semantic encodedLeft encodedRight encodedThird :=
      ofNatBits_ternaryCode
        narCode operation semantic
        encodedLeft encodedRight encodedThird
        hnarCode hoperation
    _ =
        ternaryResult (Model.nar format)
          semantic semanticLeft encodedRight encodedThird :=
      congrArg
        (fun left =>
          ternaryResult (Model.nar format)
            semantic left encodedRight encodedThird)
        hleft
    _ =
        ternaryResult (Model.nar format)
          semantic semanticLeft semanticRight encodedThird :=
      congrArg
        (fun right =>
          ternaryResult (Model.nar format)
            semantic semanticLeft right encodedThird)
        hright
    _ =
        ternaryResult (Model.nar format)
          semantic semanticLeft semanticRight semanticThird :=
      congrArg
        (fun third =>
          ternaryResult (Model.nar format)
            semantic semanticLeft semanticRight third)
        hthird

end FloatLib.Floats.Formats.Posit.Model.NativeLimbPacked.Boundary
