/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Operation.Semantics

/-!
# Status-bearing numerical operation contracts

Operations that carry a status differ in their concrete result structures. IEEE arithmetic returns
exception flags, checked integer operations may report overflow, and quantizers may report
saturation, so these contracts state correctness through result and status projections and impose no
common runtime wrapper.

Complete variants `RefinesStatus1`-`RefinesStatus3` constrain every input and every outcome,
exceptional ones included. Finite variants `RefinesStatusFinite1`-`RefinesStatusFinite3` take finite
inputs and also assert that the result code represents a finite value. So an operation that
overflows to infinity or returns NaN on some finite input, flag or not, can't satisfy them, and its
exceptional outcomes need a complete variant.
-/

@[expose] public section

namespace FloatLib.Numerics.Operation

universe u v

/-- Complete semantics of a unary operation whose concrete result carries a code and status. -/
def RefinesStatus1 (A B : NumericalSystem) {Outcome : Type u} {Status : Type v}
    (run : A.Code → Outcome) (value : Outcome → B.Code) (status : Outcome → Status)
    (post : NumericalValue A.Scalar → NumericalValue B.Scalar → Status → Prop) : Prop :=
  Refines1 A run fun input outcome =>
    post input (B.denote (value outcome)) (status outcome)

/-- Complete semantics of a two-input operation whose result carries a code and status. -/
def RefinesStatus2 (A B C : NumericalSystem) {Outcome : Type u} {Status : Type v}
    (run : A.Code → B.Code → Outcome) (value : Outcome → C.Code)
    (status : Outcome → Status)
    (post : NumericalValue A.Scalar → NumericalValue B.Scalar →
      NumericalValue C.Scalar → Status → Prop) : Prop :=
  Refines2 A B run fun left right outcome =>
    post left right (C.denote (value outcome)) (status outcome)

/-- Complete semantics of a three-input operation whose result carries a code and status. -/
def RefinesStatus3 (A B C D : NumericalSystem) {Outcome : Type u} {Status : Type v}
    (run : A.Code → B.Code → C.Code → Outcome) (value : Outcome → D.Code)
    (status : Outcome → Status)
    (post : NumericalValue A.Scalar → NumericalValue B.Scalar →
      NumericalValue C.Scalar → NumericalValue D.Scalar → Status → Prop) : Prop :=
  Refines3 A B C run fun first second third outcome =>
    post first second third (D.denote (value outcome)) (status outcome)

/-- Finite semantics of a unary status-bearing operation: a finite input gives a result code
representing a finite value, and `post` relates it and the status to the input. -/
def RefinesStatusFinite1 (A B : NumericalSystem) {Outcome : Type u} {Status : Type v}
    (run : A.Code → Outcome) (value : Outcome → B.Code) (status : Outcome → Status)
    (post : A.Scalar → B.Scalar → Status → Prop) : Prop :=
  RefinesFinite1 A run fun input outcome =>
    ∃ output, B.Represents (value outcome) output ∧ post input output (status outcome)

/-- Finite semantics of a two-input status-bearing operation: finite inputs give a result code
representing a finite value, and `post` relates it and the status to the inputs. -/
def RefinesStatusFinite2 (A B C : NumericalSystem) {Outcome : Type u} {Status : Type v}
    (run : A.Code → B.Code → Outcome) (value : Outcome → C.Code)
    (status : Outcome → Status)
    (post : A.Scalar → B.Scalar → C.Scalar → Status → Prop) : Prop :=
  RefinesFinite2 A B run fun left right outcome =>
    ∃ output, C.Represents (value outcome) output ∧
      post left right output (status outcome)

/-- Finite semantics of a three-input status-bearing operation: finite inputs give a result code
representing a finite value, and `post` relates it and the status to the inputs. -/
def RefinesStatusFinite3 (A B C D : NumericalSystem) {Outcome : Type u} {Status : Type v}
    (run : A.Code → B.Code → C.Code → Outcome) (value : Outcome → D.Code)
    (status : Outcome → Status)
    (post : A.Scalar → B.Scalar → C.Scalar → D.Scalar → Status → Prop) : Prop :=
  RefinesFinite3 A B C run fun first second third outcome =>
    ∃ output, D.Represents (value outcome) output ∧
      post first second third output (status outcome)

end FloatLib.Numerics.Operation
