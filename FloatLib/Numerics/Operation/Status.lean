/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Operation.Semantics

/-!
# Status-bearing numerical operation contracts

Status-bearing operations differ in their concrete result structures: IEEE arithmetic returns
exception flags, checked integer operations may report overflow, and quantizers may report
saturation. These contracts express correctness in terms of result and status projections,
without imposing a common runtime wrapper.
-/

@[expose] public section

namespace FloatLib.Numerics.Operation

universe u v

/-- Complete semantics of a unary operation whose concrete result carries a code and status. -/
def WithStatus1 (A B : NumericalSystem) {Outcome : Type u} {Status : Type v}
    (run : A.Code → Outcome) (value : Outcome → B.Code) (status : Outcome → Status)
    (post : NumericalValue A.Scalar → NumericalValue B.Scalar → Status → Prop) : Prop :=
  Refines1 A run fun input outcome =>
    post input (B.denote (value outcome)) (status outcome)

/-- Complete semantics of a two-input operation whose result carries a code and status. -/
def WithStatus2 (A B C : NumericalSystem) {Outcome : Type u} {Status : Type v}
    (run : A.Code → B.Code → Outcome) (value : Outcome → C.Code)
    (status : Outcome → Status)
    (post : NumericalValue A.Scalar → NumericalValue B.Scalar →
      NumericalValue C.Scalar → Status → Prop) : Prop :=
  Refines2 A B run fun left right outcome =>
    post left right (C.denote (value outcome)) (status outcome)

/-- Complete semantics of a three-input operation whose result carries a code and status. -/
def WithStatus3 (A B C D : NumericalSystem) {Outcome : Type u} {Status : Type v}
    (run : A.Code → B.Code → C.Code → Outcome) (value : Outcome → D.Code)
    (status : Outcome → Status)
    (post : NumericalValue A.Scalar → NumericalValue B.Scalar →
      NumericalValue C.Scalar → NumericalValue D.Scalar → Status → Prop) : Prop :=
  Refines3 A B C run fun first second third outcome =>
    post first second third (D.denote (value outcome)) (status outcome)

/-- Finite semantics of a unary status-bearing operation. -/
def WithStatusFinite1 (A B : NumericalSystem) {Outcome : Type u} {Status : Type v}
    (run : A.Code → Outcome) (value : Outcome → B.Code) (status : Outcome → Status)
    (post : A.Scalar → B.Scalar → Status → Prop) : Prop :=
  RefinesFinite1 A run fun input outcome =>
    ∃ output, B.Represents (value outcome) output ∧ post input output (status outcome)

/-- Finite semantics of a two-input status-bearing operation. -/
def WithStatusFinite2 (A B C : NumericalSystem) {Outcome : Type u} {Status : Type v}
    (run : A.Code → B.Code → Outcome) (value : Outcome → C.Code)
    (status : Outcome → Status)
    (post : A.Scalar → B.Scalar → C.Scalar → Status → Prop) : Prop :=
  RefinesFinite2 A B run fun left right outcome =>
    ∃ output, C.Represents (value outcome) output ∧
      post left right output (status outcome)

/-- Finite semantics of a three-input status-bearing operation. -/
def WithStatusFinite3 (A B C D : NumericalSystem) {Outcome : Type u} {Status : Type v}
    (run : A.Code → B.Code → C.Code → Outcome) (value : Outcome → D.Code)
    (status : Outcome → Status)
    (post : A.Scalar → B.Scalar → C.Scalar → D.Scalar → Status → Prop) : Prop :=
  RefinesFinite3 A B C run fun first second third outcome =>
    ∃ output, D.Represents (value outcome) output ∧
      post first second third output (status outcome)

end FloatLib.Numerics.Operation
