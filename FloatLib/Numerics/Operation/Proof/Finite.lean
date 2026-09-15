/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Operation.Semantics
public import FloatLib.Numerics.Core.Proof

/-!
# Proof-indexed finite operations

Application lemmas for finite-operation contracts, including acceptance predicates on input and
output codes, such as a floating-point result remaining finite.

`Finite1`, `Finite2`, and `Finite3` state that running a code-level operation on represented
finite inputs produces the specified finite scalar result. This module turns those contracts into
the forms users normally need: a denotation equation or a new proof-indexed value.

The `If` families require a proof of the acceptance predicate for the actual input and output
codes. Given that proof and the input denotations, the refinement contract determines the
output's finite scalar value.
-/

@[expose] public section

namespace FloatLib.Numerics.Operation

universe u v w x y z u₁ v₁

/-! ## Unconditional finite-operation contracts -/

namespace Finite1

/--
Lift a commuting decoder equation to a finite unary-operation refinement.

This is the standard proof principle for formats whose codes all denote ordinary finite values.
-/
theorem ofFinite {CodeA : Type u} {ScalarA : Type v}
    {CodeB : Type w} {ScalarB : Type x}
    {decodeA : CodeA → ScalarA} {decodeB : CodeB → ScalarB}
    {run : CodeA → CodeB} {spec : ScalarA → ScalarB}
    (correct : ∀ code, decodeB (run code) = spec (decodeA code)) :
    Finite1 (NumericalSystem.ofFinite decodeA) (NumericalSystem.ofFinite decodeB)
      run spec := by
  intro code value hvalue
  rw [NumericalSystem.ofFinite_represents_iff] at hvalue ⊢
  simpa [hvalue] using correct code

/-- Apply a finite unary refinement to a represented concrete input. -/
theorem denote {A B : NumericalSystem} {run : A.Code → B.Code}
    {spec : A.Scalar → B.Scalar} (hrefines : Finite1 A B run spec)
    {code : A.Code} {value : A.Scalar} (hcode : A.Represents code value) :
    B.denote (run code) = .finite (spec value) :=
  hrefines code value hcode

/-- Observe a finite unary operation with an independently stated scalar result. -/
theorem denote_eq {A B : NumericalSystem} {run : A.Code → B.Code}
    {spec : A.Scalar → B.Scalar} {expected : B.Scalar}
    (hrefines : Finite1 A B run spec) {value : A.Scalar}
    (code : A.AtFinite value)
    (hspec : spec value = expected) :
    B.denote (run code.1) = .finite expected := by
  rw [denote hrefines code.2, hspec]

/-- Apply a finite unary refinement to a proof-indexed finite value. -/
@[inline] def applyAt {A B : NumericalSystem} {run : A.Code → B.Code}
    {spec : A.Scalar → B.Scalar} (hrefines : Finite1 A B run spec)
    {value : A.Scalar} (code : A.AtFinite value) : B.AtFinite (spec value) :=
  ⟨run code.1, denote hrefines code.2⟩

end Finite1

namespace Finite2

/--
Lift a commuting two-input decoder equation to a finite binary-operation refinement.

Input and output code types may differ, so this also covers scale-changing operations.
-/
theorem ofFinite {CodeA : Type u} {ScalarA : Type v}
    {CodeB : Type w} {ScalarB : Type x}
    {CodeC : Type y} {ScalarC : Type z}
    {decodeA : CodeA → ScalarA} {decodeB : CodeB → ScalarB}
    {decodeC : CodeC → ScalarC} {run : CodeA → CodeB → CodeC}
    {spec : ScalarA → ScalarB → ScalarC}
    (correct : ∀ left right,
      decodeC (run left right) = spec (decodeA left) (decodeB right)) :
    Finite2 (NumericalSystem.ofFinite decodeA) (NumericalSystem.ofFinite decodeB)
      (NumericalSystem.ofFinite decodeC) run spec := by
  intro left right x y hx hy
  rw [NumericalSystem.ofFinite_represents_iff] at hx hy ⊢
  simpa [hx, hy] using correct left right

/-- Apply a finite two-input refinement to represented concrete inputs. -/
theorem denote {A B C : NumericalSystem} {run : A.Code → B.Code → C.Code}
    {spec : A.Scalar → B.Scalar → C.Scalar} (hrefines : Finite2 A B C run spec)
    {left : A.Code} {right : B.Code} {leftValue : A.Scalar} {rightValue : B.Scalar}
    (hleft : A.Represents left leftValue) (hright : B.Represents right rightValue) :
    C.denote (run left right) = .finite (spec leftValue rightValue) :=
  hrefines left right leftValue rightValue hleft hright

/--
Observe a finite two-input operation with an independently stated scalar result.

The proof-indexed inputs determine both semantic operands before automation selects the operation
contract. This prevents independent metavariables for the operands from drifting across proof
search branches.
-/
theorem denote_eq {A B C : NumericalSystem} {run : A.Code → B.Code → C.Code}
    {spec : A.Scalar → B.Scalar → C.Scalar} {expected : C.Scalar}
    (hrefines : Finite2 A B C run spec)
    {leftValue : A.Scalar} {rightValue : B.Scalar}
    (left : A.AtFinite leftValue) (right : B.AtFinite rightValue)
    (hspec : spec leftValue rightValue = expected) :
    C.denote (run left.1 right.1) = .finite expected := by
  rw [denote hrefines left.2 right.2, hspec]

/-- Apply a finite two-input refinement to proof-indexed finite values. -/
@[inline] def applyAt {A B C : NumericalSystem} {run : A.Code → B.Code → C.Code}
    {spec : A.Scalar → B.Scalar → C.Scalar} (hrefines : Finite2 A B C run spec)
    {leftValue : A.Scalar} {rightValue : B.Scalar}
    (left : A.AtFinite leftValue) (right : B.AtFinite rightValue) :
    C.AtFinite (spec leftValue rightValue) :=
  ⟨run left.1 right.1, denote hrefines left.2 right.2⟩

end Finite2

namespace Finite3

/-- Lift a commuting three-input decoder equation to a finite ternary-operation refinement. -/
theorem ofFinite {CodeA : Type u} {ScalarA : Type v}
    {CodeB : Type w} {ScalarB : Type x}
    {CodeC : Type y} {ScalarC : Type z}
    {CodeD : Type u₁} {ScalarD : Type v₁}
    {decodeA : CodeA → ScalarA} {decodeB : CodeB → ScalarB}
    {decodeC : CodeC → ScalarC} {decodeD : CodeD → ScalarD}
    {run : CodeA → CodeB → CodeC → CodeD}
    {spec : ScalarA → ScalarB → ScalarC → ScalarD}
    (correct : ∀ first second third,
      decodeD (run first second third) =
        spec (decodeA first) (decodeB second) (decodeC third)) :
    Finite3 (NumericalSystem.ofFinite decodeA) (NumericalSystem.ofFinite decodeB)
      (NumericalSystem.ofFinite decodeC) (NumericalSystem.ofFinite decodeD) run spec := by
  intro first second third x y z hx hy hz
  rw [NumericalSystem.ofFinite_represents_iff] at hx hy hz ⊢
  simpa [hx, hy, hz] using correct first second third

/-- Apply a finite three-input refinement to represented concrete inputs. -/
theorem denote {A B C D : NumericalSystem}
    {run : A.Code → B.Code → C.Code → D.Code}
    {spec : A.Scalar → B.Scalar → C.Scalar → D.Scalar}
    (hrefines : Finite3 A B C D run spec)
    {first : A.Code} {second : B.Code} {third : C.Code}
    {firstValue : A.Scalar} {secondValue : B.Scalar} {thirdValue : C.Scalar}
    (hfirst : A.Represents first firstValue)
    (hsecond : B.Represents second secondValue)
    (hthird : C.Represents third thirdValue) :
    D.denote (run first second third) =
      .finite (spec firstValue secondValue thirdValue) :=
  hrefines first second third firstValue secondValue thirdValue hfirst hsecond hthird

/-- Observe a finite three-input operation with an independently stated scalar result. -/
theorem denote_eq {A B C D : NumericalSystem}
    {run : A.Code → B.Code → C.Code → D.Code}
    {spec : A.Scalar → B.Scalar → C.Scalar → D.Scalar} {expected : D.Scalar}
    (hrefines : Finite3 A B C D run spec)
    {firstValue : A.Scalar} {secondValue : B.Scalar} {thirdValue : C.Scalar}
    (first : A.AtFinite firstValue) (second : B.AtFinite secondValue)
    (third : C.AtFinite thirdValue)
    (hspec : spec firstValue secondValue thirdValue = expected) :
    D.denote (run first.1 second.1 third.1) = .finite expected := by
  rw [denote hrefines first.2 second.2 third.2, hspec]

/-- Apply a finite three-input refinement to proof-indexed finite values. -/
@[inline] def applyAt {A B C D : NumericalSystem}
    {run : A.Code → B.Code → C.Code → D.Code}
    {spec : A.Scalar → B.Scalar → C.Scalar → D.Scalar}
    (hrefines : Finite3 A B C D run spec)
    {firstValue : A.Scalar} {secondValue : B.Scalar} {thirdValue : C.Scalar}
    (first : A.AtFinite firstValue) (second : B.AtFinite secondValue)
    (third : C.AtFinite thirdValue) :
    D.AtFinite (spec firstValue secondValue thirdValue) :=
  ⟨run first.1 second.1 third.1, denote hrefines first.2 second.2 third.2⟩

end Finite3

/-! ## Finite-operation contracts with a code-level acceptance condition -/

namespace Finite1If

/-- Apply a condition-aware finite unary refinement to a represented concrete input. -/
theorem denote {A B : NumericalSystem} {run : A.Code → B.Code}
    {spec : A.Scalar → B.Scalar} {accept : A.Code → B.Code → Prop}
    (hrefines : Finite1If A B run spec accept)
    {code : A.Code} {value : A.Scalar} (hcode : A.Represents code value)
    (haccept : accept code (run code)) :
    B.denote (run code) = .finite (spec value) :=
  hrefines code value hcode haccept

/-- Observe a condition-aware finite unary operation with an independently stated result. -/
theorem denote_eq {A B : NumericalSystem} {run : A.Code → B.Code}
    {spec : A.Scalar → B.Scalar} {accept : A.Code → B.Code → Prop}
    {expected : B.Scalar}
    (hrefines : Finite1If A B run spec accept) {value : A.Scalar}
    (code : A.AtFinite value)
    (haccept : accept code.1 (run code.1)) (hspec : spec value = expected) :
    B.denote (run code.1) = .finite expected := by
  rw [denote hrefines code.2 haccept, hspec]

/-- Apply a condition-aware finite unary refinement to a proof-indexed value. -/
@[inline] def applyAt {A B : NumericalSystem} {run : A.Code → B.Code}
    {spec : A.Scalar → B.Scalar} {accept : A.Code → B.Code → Prop}
    (hrefines : Finite1If A B run spec accept) {value : A.Scalar}
    (code : A.AtFinite value) (haccept : accept code.1 (run code.1)) :
    B.AtFinite (spec value) :=
  ⟨run code.1, denote hrefines code.2 haccept⟩

end Finite1If

namespace Finite2If

/-- Apply a condition-aware finite two-input refinement to represented concrete inputs. -/
theorem denote {A B C : NumericalSystem} {run : A.Code → B.Code → C.Code}
    {spec : A.Scalar → B.Scalar → C.Scalar}
    {accept : A.Code → B.Code → C.Code → Prop}
    (hrefines : Finite2If A B C run spec accept)
    {left : A.Code} {right : B.Code} {leftValue : A.Scalar} {rightValue : B.Scalar}
    (hleft : A.Represents left leftValue) (hright : B.Represents right rightValue)
    (haccept : accept left right (run left right)) :
    C.denote (run left right) = .finite (spec leftValue rightValue) :=
  hrefines left right leftValue rightValue hleft hright haccept

/-- Observe a condition-aware finite two-input operation with an independently stated result. -/
theorem denote_eq {A B C : NumericalSystem} {run : A.Code → B.Code → C.Code}
    {spec : A.Scalar → B.Scalar → C.Scalar}
    {accept : A.Code → B.Code → C.Code → Prop} {expected : C.Scalar}
    (hrefines : Finite2If A B C run spec accept)
    {leftValue : A.Scalar} {rightValue : B.Scalar}
    (left : A.AtFinite leftValue) (right : B.AtFinite rightValue)
    (haccept : accept left.1 right.1 (run left.1 right.1))
    (hspec : spec leftValue rightValue = expected) :
    C.denote (run left.1 right.1) = .finite expected := by
  rw [denote hrefines left.2 right.2 haccept, hspec]

/-- Apply a condition-aware finite two-input refinement to proof-indexed values. -/
@[inline] def applyAt {A B C : NumericalSystem} {run : A.Code → B.Code → C.Code}
    {spec : A.Scalar → B.Scalar → C.Scalar}
    {accept : A.Code → B.Code → C.Code → Prop}
    (hrefines : Finite2If A B C run spec accept)
    {leftValue : A.Scalar} {rightValue : B.Scalar}
    (left : A.AtFinite leftValue) (right : B.AtFinite rightValue)
    (haccept : accept left.1 right.1 (run left.1 right.1)) :
    C.AtFinite (spec leftValue rightValue) :=
  ⟨run left.1 right.1, denote hrefines left.2 right.2 haccept⟩

end Finite2If

namespace Finite3If

/-- Apply a condition-aware finite three-input refinement to represented concrete inputs. -/
theorem denote {A B C D : NumericalSystem}
    {run : A.Code → B.Code → C.Code → D.Code}
    {spec : A.Scalar → B.Scalar → C.Scalar → D.Scalar}
    {accept : A.Code → B.Code → C.Code → D.Code → Prop}
    (hrefines : Finite3If A B C D run spec accept)
    {first : A.Code} {second : B.Code} {third : C.Code}
    {firstValue : A.Scalar} {secondValue : B.Scalar} {thirdValue : C.Scalar}
    (hfirst : A.Represents first firstValue)
    (hsecond : B.Represents second secondValue)
    (hthird : C.Represents third thirdValue)
    (haccept : accept first second third (run first second third)) :
    D.denote (run first second third) =
      .finite (spec firstValue secondValue thirdValue) :=
  hrefines first second third firstValue secondValue thirdValue
    hfirst hsecond hthird haccept

/-- Observe a condition-aware finite three-input operation with an independent result. -/
theorem denote_eq {A B C D : NumericalSystem}
    {run : A.Code → B.Code → C.Code → D.Code}
    {spec : A.Scalar → B.Scalar → C.Scalar → D.Scalar}
    {accept : A.Code → B.Code → C.Code → D.Code → Prop} {expected : D.Scalar}
    (hrefines : Finite3If A B C D run spec accept)
    {firstValue : A.Scalar} {secondValue : B.Scalar} {thirdValue : C.Scalar}
    (first : A.AtFinite firstValue) (second : B.AtFinite secondValue)
    (third : C.AtFinite thirdValue)
    (haccept : accept first.1 second.1 third.1 (run first.1 second.1 third.1))
    (hspec : spec firstValue secondValue thirdValue = expected) :
    D.denote (run first.1 second.1 third.1) = .finite expected := by
  rw [denote hrefines first.2 second.2 third.2 haccept, hspec]

/-- Apply a condition-aware finite three-input refinement to proof-indexed values. -/
@[inline] def applyAt {A B C D : NumericalSystem}
    {run : A.Code → B.Code → C.Code → D.Code}
    {spec : A.Scalar → B.Scalar → C.Scalar → D.Scalar}
    {accept : A.Code → B.Code → C.Code → D.Code → Prop}
    (hrefines : Finite3If A B C D run spec accept)
    {firstValue : A.Scalar} {secondValue : B.Scalar} {thirdValue : C.Scalar}
    (first : A.AtFinite firstValue) (second : B.AtFinite secondValue)
    (third : C.AtFinite thirdValue)
    (haccept : accept first.1 second.1 third.1 (run first.1 second.1 third.1)) :
    D.AtFinite (spec firstValue secondValue thirdValue) :=
  ⟨run first.1 second.1 third.1,
    denote hrefines first.2 second.2 third.2 haccept⟩

end Finite3If

end FloatLib.Numerics.Operation
