/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Operation.Semantics
public import FloatLib.Numerics.Core.Proof

/-!
# Proof-indexed checked operations

Application lemmas for operations returning `Option`. A refinement proof shows that represented
finite inputs cannot take the failure branch, with optional scalar preconditions when required.

These lemmas connect an executable checker to a proof-indexed caller. At the raw-code level,
failure remains explicit. Once the caller supplies represented finite inputs and, for the `On`
variants, the scalar precondition, the refinement theorem proves that `none` is impossible and
returns a value carrying its denotation proof.

Unary, binary, and ternary versions provide `map_denote` for the denotation equation and
`applyAt` for constructing a proof-indexed result. The unconditional contracts also provide
`exists_result` to recover a successful code and its denotation.
-/

@[expose] public section

namespace FloatLib.Numerics.Operation

private theorem exists_code_of_map_denote_eq
    {B : NumericalSystem} {result : Option B.Code}
    {value : NumericalValue B.Scalar}
    (hresult : Option.map B.denote result = some value) :
    ∃ code, result = some code ∧ B.denote code = value :=
  Option.map_eq_some_iff.mp hresult

namespace Internal

/--
Extract the successful code from a checked computation whose refinement proof rules out failure.

This is the shared implementation of the arity-specific `applyAt` functions below. Inlining
preserves the direct checked-operation runtime path after proof erasure.
-/
@[inline] def atOfCheckedResult
    {B : NumericalSystem} (result : Option B.Code)
    {value : NumericalValue B.Scalar}
    (hresult : Option.map B.denote result = some value) :
    B.At value := by
  cases result with
  | none => simp at hresult
  | some code =>
      exact ⟨code, by simpa using hresult⟩

end Internal

/-! ## Checked operations with no additional precondition -/

namespace Checked1

/-- Observe a checked unary operation on a proof-indexed finite input. -/
theorem map_denote {A B : NumericalSystem} {run : A.Code → Option B.Code}
    {spec : A.Scalar → NumericalValue B.Scalar} (hrefines : Checked1 A B run spec)
    {value : A.Scalar} (code : A.AtFinite value) :
    Option.map B.denote (run code.1) = some (spec value) :=
  hrefines code.1 value code.2

/-- Observe a checked unary operation with an independently stated result. -/
theorem map_denote_eq {A B : NumericalSystem} {run : A.Code → Option B.Code}
    {spec : A.Scalar → NumericalValue B.Scalar} {expected : NumericalValue B.Scalar}
    (hrefines : Checked1 A B run spec)
    {value : A.Scalar} (code : A.AtFinite value)
    (hspec : spec value = expected) :
    Option.map B.denote (run code.1) = some expected := by
  rw [map_denote hrefines code, hspec]

/-- A checked unary refinement succeeds on every represented finite input. -/
theorem exists_result {A B : NumericalSystem} {run : A.Code → Option B.Code}
    {spec : A.Scalar → NumericalValue B.Scalar} (hrefines : Checked1 A B run spec)
    {value : A.Scalar} (code : A.AtFinite value) :
    ∃ result, run code.1 = some result ∧ B.denote result = spec value :=
  exists_code_of_map_denote_eq (map_denote hrefines code)

/-- Apply a checked unary refinement to a represented input, discharging the impossible failure. -/
@[inline] def applyAt {A B : NumericalSystem} {run : A.Code → Option B.Code}
    {spec : A.Scalar → NumericalValue B.Scalar} (hrefines : Checked1 A B run spec)
    {value : A.Scalar} (code : A.AtFinite value) : B.At (spec value) :=
  Internal.atOfCheckedResult (run code.1) (map_denote hrefines code)

end Checked1

namespace Checked2

/-- Observe a checked two-input operation on proof-indexed finite inputs. -/
theorem map_denote {A B C : NumericalSystem}
    {run : A.Code → B.Code → Option C.Code}
    {spec : A.Scalar → B.Scalar → NumericalValue C.Scalar}
    (hrefines : Checked2 A B C run spec)
    {leftValue : A.Scalar} {rightValue : B.Scalar}
    (left : A.AtFinite leftValue) (right : B.AtFinite rightValue) :
    Option.map C.denote (run left.1 right.1) = some (spec leftValue rightValue) :=
  hrefines left.1 right.1 leftValue rightValue left.2 right.2

/-- Observe a checked two-input operation with an independently stated result. -/
theorem map_denote_eq {A B C : NumericalSystem}
    {run : A.Code → B.Code → Option C.Code}
    {spec : A.Scalar → B.Scalar → NumericalValue C.Scalar}
    {expected : NumericalValue C.Scalar}
    (hrefines : Checked2 A B C run spec)
    {leftValue : A.Scalar} {rightValue : B.Scalar}
    (left : A.AtFinite leftValue) (right : B.AtFinite rightValue)
    (hspec : spec leftValue rightValue = expected) :
    Option.map C.denote (run left.1 right.1) = some expected := by
  rw [map_denote hrefines left right, hspec]

/-- A checked two-input refinement succeeds on represented finite inputs. -/
theorem exists_result {A B C : NumericalSystem}
    {run : A.Code → B.Code → Option C.Code}
    {spec : A.Scalar → B.Scalar → NumericalValue C.Scalar}
    (hrefines : Checked2 A B C run spec)
    {leftValue : A.Scalar} {rightValue : B.Scalar}
    (left : A.AtFinite leftValue) (right : B.AtFinite rightValue) :
    ∃ result, run left.1 right.1 = some result ∧
      C.denote result = spec leftValue rightValue :=
  exists_code_of_map_denote_eq (map_denote hrefines left right)

/-- Apply a checked two-input refinement, discharging the impossible failure. -/
@[inline] def applyAt {A B C : NumericalSystem}
    {run : A.Code → B.Code → Option C.Code}
    {spec : A.Scalar → B.Scalar → NumericalValue C.Scalar}
    (hrefines : Checked2 A B C run spec)
    {leftValue : A.Scalar} {rightValue : B.Scalar}
    (left : A.AtFinite leftValue) (right : B.AtFinite rightValue) :
    C.At (spec leftValue rightValue) :=
  Internal.atOfCheckedResult (run left.1 right.1) (map_denote hrefines left right)

end Checked2

namespace Checked3

/-- Observe a checked three-input operation on proof-indexed finite inputs. -/
theorem map_denote {A B C D : NumericalSystem}
    {run : A.Code → B.Code → C.Code → Option D.Code}
    {spec : A.Scalar → B.Scalar → C.Scalar → NumericalValue D.Scalar}
    (hrefines : Checked3 A B C D run spec)
    {firstValue : A.Scalar} {secondValue : B.Scalar} {thirdValue : C.Scalar}
    (first : A.AtFinite firstValue) (second : B.AtFinite secondValue)
    (third : C.AtFinite thirdValue) :
    Option.map D.denote (run first.1 second.1 third.1) =
      some (spec firstValue secondValue thirdValue) :=
  hrefines first.1 second.1 third.1 firstValue secondValue thirdValue
    first.2 second.2 third.2

/-- Observe a checked three-input operation with an independently stated result. -/
theorem map_denote_eq {A B C D : NumericalSystem}
    {run : A.Code → B.Code → C.Code → Option D.Code}
    {spec : A.Scalar → B.Scalar → C.Scalar → NumericalValue D.Scalar}
    {expected : NumericalValue D.Scalar}
    (hrefines : Checked3 A B C D run spec)
    {firstValue : A.Scalar} {secondValue : B.Scalar} {thirdValue : C.Scalar}
    (first : A.AtFinite firstValue) (second : B.AtFinite secondValue)
    (third : C.AtFinite thirdValue)
    (hspec : spec firstValue secondValue thirdValue = expected) :
    Option.map D.denote (run first.1 second.1 third.1) = some expected := by
  rw [map_denote hrefines first second third, hspec]

/-- A checked three-input refinement succeeds on represented finite inputs. -/
theorem exists_result {A B C D : NumericalSystem}
    {run : A.Code → B.Code → C.Code → Option D.Code}
    {spec : A.Scalar → B.Scalar → C.Scalar → NumericalValue D.Scalar}
    (hrefines : Checked3 A B C D run spec)
    {firstValue : A.Scalar} {secondValue : B.Scalar} {thirdValue : C.Scalar}
    (first : A.AtFinite firstValue) (second : B.AtFinite secondValue)
    (third : C.AtFinite thirdValue) :
    ∃ result, run first.1 second.1 third.1 = some result ∧
      D.denote result = spec firstValue secondValue thirdValue :=
  exists_code_of_map_denote_eq (map_denote hrefines first second third)

/-- Apply a checked three-input refinement, discharging the impossible failure. -/
@[inline] def applyAt {A B C D : NumericalSystem}
    {run : A.Code → B.Code → C.Code → Option D.Code}
    {spec : A.Scalar → B.Scalar → C.Scalar → NumericalValue D.Scalar}
    (hrefines : Checked3 A B C D run spec)
    {firstValue : A.Scalar} {secondValue : B.Scalar} {thirdValue : C.Scalar}
    (first : A.AtFinite firstValue) (second : B.AtFinite secondValue)
    (third : C.AtFinite thirdValue) :
    D.At (spec firstValue secondValue thirdValue) :=
  Internal.atOfCheckedResult (run first.1 second.1 third.1)
    (map_denote hrefines first second third)

end Checked3

/-! ## Checked operations under a scalar precondition -/

namespace Checked1On

/-- Observe a preconditioned checked unary operation on a proof-indexed finite input. -/
theorem map_denote {A B : NumericalSystem} {run : A.Code → Option B.Code}
    {spec : A.Scalar → NumericalValue B.Scalar} {pre : A.Scalar → Prop}
    (hrefines : Checked1On A B run spec pre) {value : A.Scalar}
    (hpre : pre value) (code : A.AtFinite value) :
    Option.map B.denote (run code.1) = some (spec value) :=
  hrefines code.1 value hpre code.2

/-- Observe a preconditioned checked unary operation with an independent result. -/
theorem map_denote_eq {A B : NumericalSystem} {run : A.Code → Option B.Code}
    {spec : A.Scalar → NumericalValue B.Scalar} {pre : A.Scalar → Prop}
    {expected : NumericalValue B.Scalar}
    (hrefines : Checked1On A B run spec pre) {value : A.Scalar}
    (hpre : pre value) (code : A.AtFinite value)
    (hspec : spec value = expected) :
    Option.map B.denote (run code.1) = some expected := by
  rw [map_denote hrefines hpre code, hspec]

/-- Apply a preconditioned checked unary refinement to a represented input. -/
@[inline] def applyAt {A B : NumericalSystem} {run : A.Code → Option B.Code}
    {spec : A.Scalar → NumericalValue B.Scalar} {pre : A.Scalar → Prop}
    (hrefines : Checked1On A B run spec pre) {value : A.Scalar}
    (hpre : pre value) (code : A.AtFinite value) : B.At (spec value) :=
  Internal.atOfCheckedResult (run code.1) (map_denote hrefines hpre code)

end Checked1On

namespace Checked2On

/-- Observe a preconditioned checked two-input operation on proof-indexed finite inputs. -/
theorem map_denote {A B C : NumericalSystem}
    {run : A.Code → B.Code → Option C.Code}
    {spec : A.Scalar → B.Scalar → NumericalValue C.Scalar}
    {pre : A.Scalar → B.Scalar → Prop}
    (hrefines : Checked2On A B C run spec pre)
    {leftValue : A.Scalar} {rightValue : B.Scalar}
    (hpre : pre leftValue rightValue)
    (left : A.AtFinite leftValue) (right : B.AtFinite rightValue) :
    Option.map C.denote (run left.1 right.1) = some (spec leftValue rightValue) :=
  hrefines left.1 right.1 leftValue rightValue hpre left.2 right.2

/-- Observe a preconditioned checked two-input operation with an independent result. -/
theorem map_denote_eq {A B C : NumericalSystem}
    {run : A.Code → B.Code → Option C.Code}
    {spec : A.Scalar → B.Scalar → NumericalValue C.Scalar}
    {pre : A.Scalar → B.Scalar → Prop} {expected : NumericalValue C.Scalar}
    (hrefines : Checked2On A B C run spec pre)
    {leftValue : A.Scalar} {rightValue : B.Scalar}
    (hpre : pre leftValue rightValue)
    (left : A.AtFinite leftValue) (right : B.AtFinite rightValue)
    (hspec : spec leftValue rightValue = expected) :
    Option.map C.denote (run left.1 right.1) = some expected := by
  rw [map_denote hrefines hpre left right, hspec]

/-- Apply a preconditioned checked two-input refinement to represented inputs. -/
@[inline] def applyAt {A B C : NumericalSystem}
    {run : A.Code → B.Code → Option C.Code}
    {spec : A.Scalar → B.Scalar → NumericalValue C.Scalar}
    {pre : A.Scalar → B.Scalar → Prop}
    (hrefines : Checked2On A B C run spec pre)
    {leftValue : A.Scalar} {rightValue : B.Scalar}
    (hpre : pre leftValue rightValue)
    (left : A.AtFinite leftValue) (right : B.AtFinite rightValue) :
    C.At (spec leftValue rightValue) :=
  Internal.atOfCheckedResult (run left.1 right.1) (map_denote hrefines hpre left right)

end Checked2On

namespace Checked3On

/-- Observe a preconditioned checked three-input operation on proof-indexed finite inputs. -/
theorem map_denote {A B C D : NumericalSystem}
    {run : A.Code → B.Code → C.Code → Option D.Code}
    {spec : A.Scalar → B.Scalar → C.Scalar → NumericalValue D.Scalar}
    {pre : A.Scalar → B.Scalar → C.Scalar → Prop}
    (hrefines : Checked3On A B C D run spec pre)
    {firstValue : A.Scalar} {secondValue : B.Scalar} {thirdValue : C.Scalar}
    (hpre : pre firstValue secondValue thirdValue)
    (first : A.AtFinite firstValue) (second : B.AtFinite secondValue)
    (third : C.AtFinite thirdValue) :
    Option.map D.denote (run first.1 second.1 third.1) =
      some (spec firstValue secondValue thirdValue) :=
  hrefines first.1 second.1 third.1 firstValue secondValue thirdValue
    hpre first.2 second.2 third.2

/-- Observe a preconditioned checked three-input operation with an independent result. -/
theorem map_denote_eq {A B C D : NumericalSystem}
    {run : A.Code → B.Code → C.Code → Option D.Code}
    {spec : A.Scalar → B.Scalar → C.Scalar → NumericalValue D.Scalar}
    {pre : A.Scalar → B.Scalar → C.Scalar → Prop}
    {expected : NumericalValue D.Scalar}
    (hrefines : Checked3On A B C D run spec pre)
    {firstValue : A.Scalar} {secondValue : B.Scalar} {thirdValue : C.Scalar}
    (hpre : pre firstValue secondValue thirdValue)
    (first : A.AtFinite firstValue) (second : B.AtFinite secondValue)
    (third : C.AtFinite thirdValue)
    (hspec : spec firstValue secondValue thirdValue = expected) :
    Option.map D.denote (run first.1 second.1 third.1) = some expected := by
  rw [map_denote hrefines hpre first second third, hspec]

/-- Apply a preconditioned checked three-input refinement to represented inputs. -/
@[inline] def applyAt {A B C D : NumericalSystem}
    {run : A.Code → B.Code → C.Code → Option D.Code}
    {spec : A.Scalar → B.Scalar → C.Scalar → NumericalValue D.Scalar}
    {pre : A.Scalar → B.Scalar → C.Scalar → Prop}
    (hrefines : Checked3On A B C D run spec pre)
    {firstValue : A.Scalar} {secondValue : B.Scalar} {thirdValue : C.Scalar}
    (hpre : pre firstValue secondValue thirdValue)
    (first : A.AtFinite firstValue) (second : B.AtFinite secondValue)
    (third : C.AtFinite thirdValue) :
    D.At (spec firstValue secondValue thirdValue) :=
  Internal.atOfCheckedResult (run first.1 second.1 third.1)
    (map_denote hrefines hpre first second third)

end Checked3On

end FloatLib.Numerics.Operation
