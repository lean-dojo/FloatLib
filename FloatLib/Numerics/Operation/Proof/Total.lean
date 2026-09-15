/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Operation.Semantics
public import FloatLib.Numerics.Core.Proof

/-!
# Proof-indexed total operations

`Total1`, `Total2`, and `Total3` describe operations whose semantics cover every encoded input,
including exceptional numerical values. This file supplies the uniform ways to apply those
contracts either to raw codes or to proof-indexed values.

The helpers are intentionally regular across arities. Generic automation can expose a denotation,
rewrite it to an independently stated result, or run the same executable function while retaining
its semantic index. Format families therefore do not need local copies of these proof bridges.
-/

@[expose] public section

namespace FloatLib.Numerics.Operation

namespace Total1

/-- Apply a total unary refinement to a concrete input. -/
theorem denote {A B : NumericalSystem} {run : A.Code → B.Code}
    {spec : NumericalValue A.Scalar → NumericalValue B.Scalar}
    (hrefines : Total1 A B run spec) (code : A.Code) :
    B.denote (run code) = spec (A.denote code) :=
  hrefines code

/--
Apply a total unary refinement while leaving the displayed result independent of the contract's
chosen specification. This is the stable shape used by generic automation.
-/
theorem denote_eq {A B : NumericalSystem} {run : A.Code → B.Code}
    {spec : NumericalValue A.Scalar → NumericalValue B.Scalar}
    {expected : NumericalValue B.Scalar}
    (hrefines : Total1 A B run spec) (code : A.Code)
    (hspec : spec (A.denote code) = expected) :
    B.denote (run code) = expected := by
  rw [denote hrefines code, hspec]

/-- Apply a total unary refinement to a proof-indexed complete value. -/
@[inline] def applyAt {A B : NumericalSystem} {run : A.Code → B.Code}
    {spec : NumericalValue A.Scalar → NumericalValue B.Scalar}
    (hrefines : Total1 A B run spec) {value : NumericalValue A.Scalar}
    (code : A.At value) : B.At (spec value) :=
  ⟨run code.1, by rw [hrefines code.1, code.2]⟩

end Total1

namespace Total2

/-- Apply a total two-input refinement to concrete inputs. -/
theorem denote {A B C : NumericalSystem} {run : A.Code → B.Code → C.Code}
    {spec : NumericalValue A.Scalar → NumericalValue B.Scalar → NumericalValue C.Scalar}
    (hrefines : Total2 A B C run spec) (left : A.Code) (right : B.Code) :
    C.denote (run left right) = spec (A.denote left) (B.denote right) :=
  hrefines left right

/-- Apply a total two-input refinement with an independently stated result. -/
theorem denote_eq {A B C : NumericalSystem} {run : A.Code → B.Code → C.Code}
    {spec : NumericalValue A.Scalar → NumericalValue B.Scalar → NumericalValue C.Scalar}
    {expected : NumericalValue C.Scalar}
    (hrefines : Total2 A B C run spec) (left : A.Code) (right : B.Code)
    (hspec : spec (A.denote left) (B.denote right) = expected) :
    C.denote (run left right) = expected := by
  rw [denote hrefines left right, hspec]

/-- Apply a total two-input refinement to proof-indexed complete values. -/
@[inline] def applyAt {A B C : NumericalSystem} {run : A.Code → B.Code → C.Code}
    {spec : NumericalValue A.Scalar → NumericalValue B.Scalar → NumericalValue C.Scalar}
    (hrefines : Total2 A B C run spec)
    {leftValue : NumericalValue A.Scalar} {rightValue : NumericalValue B.Scalar}
    (left : A.At leftValue) (right : B.At rightValue) :
    C.At (spec leftValue rightValue) :=
  ⟨run left.1 right.1, by rw [hrefines left.1 right.1, left.2, right.2]⟩

end Total2

namespace Total3

/-- Apply a total three-input refinement to concrete inputs. -/
theorem denote {A B C D : NumericalSystem}
    {run : A.Code → B.Code → C.Code → D.Code}
    {spec : NumericalValue A.Scalar → NumericalValue B.Scalar →
      NumericalValue C.Scalar → NumericalValue D.Scalar}
    (hrefines : Total3 A B C D run spec)
    (first : A.Code) (second : B.Code) (third : C.Code) :
    D.denote (run first second third) =
      spec (A.denote first) (B.denote second) (C.denote third) :=
  hrefines first second third

/-- Apply a total three-input refinement with an independently stated result. -/
theorem denote_eq {A B C D : NumericalSystem}
    {run : A.Code → B.Code → C.Code → D.Code}
    {spec : NumericalValue A.Scalar → NumericalValue B.Scalar →
      NumericalValue C.Scalar → NumericalValue D.Scalar}
    {expected : NumericalValue D.Scalar}
    (hrefines : Total3 A B C D run spec)
    (first : A.Code) (second : B.Code) (third : C.Code)
    (hspec :
      spec (A.denote first) (B.denote second) (C.denote third) = expected) :
    D.denote (run first second third) = expected := by
  rw [denote hrefines first second third, hspec]

/-- Apply a total three-input refinement to proof-indexed complete values. -/
@[inline] def applyAt {A B C D : NumericalSystem}
    {run : A.Code → B.Code → C.Code → D.Code}
    {spec : NumericalValue A.Scalar → NumericalValue B.Scalar →
      NumericalValue C.Scalar → NumericalValue D.Scalar}
    (hrefines : Total3 A B C D run spec)
    {firstValue : NumericalValue A.Scalar} {secondValue : NumericalValue B.Scalar}
    {thirdValue : NumericalValue C.Scalar}
    (first : A.At firstValue) (second : B.At secondValue) (third : C.At thirdValue) :
    D.At (spec firstValue secondValue thirdValue) :=
  ⟨run first.1 second.1 third.1, by
    rw [hrefines first.1 second.1 third.1, first.2, second.2, third.2]⟩

end Total3

end FloatLib.Numerics.Operation
