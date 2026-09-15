/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Core.System

/-!
# Contracts for numerical operations

Relations between executable functions and their denotations, starting with indexed inputs and
specializing to unary, binary, and ternary functions. The contracts distinguish total, finite,
checked, cast, and quantizer semantics. They live in `Prop` and add no runtime data.

See `Operation.Status` for result flags, `Operation.Context` for rounding policies, and
`Operation.Entropy` for explicit randomness. `Operation.Proof` contains application and
composition lemmas.
-/

@[expose] public section

namespace FloatLib.Numerics.Operation

universe u v

/-! ## Indexed input contracts -/

/-- Runtime inputs indexed by their numerical systems. -/
abbrev InputCodes {ι : Type u} (inputs : ι → NumericalSystem) :=
  (i : ι) → (inputs i).Code

/-- Complete denotations of indexed numerical inputs. -/
abbrev InputValues {ι : Type u} (inputs : ι → NumericalSystem) :=
  (i : ι) → NumericalValue (inputs i).Scalar

/-- Ordinary finite scalar values indexed by their numerical systems. -/
abbrev InputScalars {ι : Type u} (inputs : ι → NumericalSystem) :=
  (i : ι) → (inputs i).Scalar

/-- Every indexed runtime input represents its corresponding finite scalar. -/
def InputsRepresent {ι : Type u} (inputs : ι → NumericalSystem)
    (codes : InputCodes inputs) (values : InputScalars inputs) : Prop :=
  ∀ i, (inputs i).Represents (codes i) (values i)

/--
An executable operation satisfies a relational contract over the complete denotations of all
inputs.

`Result` is deliberately unconstrained: it may be a code, an `Option`, a status-bearing result,
an entropy-producing computation, or a block value.
-/
def Refines {ι : Type u} (inputs : ι → NumericalSystem) {Result : Type v}
    (run : InputCodes inputs → Result)
    (post : InputValues inputs → Result → Prop) : Prop :=
  ∀ codes, post (fun i => (inputs i).denote (codes i)) (run codes)

/-- An executable operation satisfies a relational contract on represented finite inputs. -/
def RefinesFinite {ι : Type u} (inputs : ι → NumericalSystem) {Result : Type v}
    (run : InputCodes inputs → Result)
    (post : InputScalars inputs → Result → Prop) : Prop :=
  ∀ codes values, InputsRepresent inputs codes values → post values (run codes)

/-! ## Unary, binary, and ternary relations -/

/-- A unary executable operation satisfies a relation on complete input denotations. -/
def Refines1 (A : NumericalSystem) {Result : Type u} (run : A.Code → Result)
    (post : NumericalValue A.Scalar → Result → Prop) : Prop :=
  ∀ a, post (A.denote a) (run a)

/-- A two-input executable operation satisfies a relation on complete input denotations. -/
def Refines2 (A B : NumericalSystem) {Result : Type u}
    (run : A.Code → B.Code → Result)
    (post : NumericalValue A.Scalar → NumericalValue B.Scalar → Result → Prop) : Prop :=
  ∀ a b, post (A.denote a) (B.denote b) (run a b)

/-- A three-input executable operation satisfies a relation on complete input denotations. -/
def Refines3 (A B C : NumericalSystem) {Result : Type u}
    (run : A.Code → B.Code → C.Code → Result)
    (post : NumericalValue A.Scalar → NumericalValue B.Scalar →
      NumericalValue C.Scalar → Result → Prop) : Prop :=
  ∀ a b c, post (A.denote a) (B.denote b) (C.denote c) (run a b c)

/-- A unary executable operation satisfies a relation on represented finite inputs. -/
def RefinesFinite1 (A : NumericalSystem) {Result : Type u} (run : A.Code → Result)
    (post : A.Scalar → Result → Prop) : Prop :=
  ∀ a x, A.Represents a x → post x (run a)

/-- A two-input executable operation satisfies a relation on represented finite inputs. -/
def RefinesFinite2 (A B : NumericalSystem) {Result : Type u}
    (run : A.Code → B.Code → Result)
    (post : A.Scalar → B.Scalar → Result → Prop) : Prop :=
  ∀ a b x y, A.Represents a x → B.Represents b y → post x y (run a b)

/-- A three-input executable operation satisfies a relation on represented finite inputs. -/
def RefinesFinite3 (A B C : NumericalSystem) {Result : Type u}
    (run : A.Code → B.Code → C.Code → Result)
    (post : A.Scalar → B.Scalar → C.Scalar → Result → Prop) : Prop :=
  ∀ a b c x y z,
    A.Represents a x → B.Represents b y → C.Represents c z → post x y z (run a b c)

/-! ## Total, finite, checked, and quantizer semantics -/

/-- Correctness of a unary total operation, including exceptional values. -/
def Total1 (A B : NumericalSystem) (run : A.Code → B.Code)
    (spec : NumericalValue A.Scalar → NumericalValue B.Scalar) : Prop :=
  Refines1 A run fun x result => B.denote result = spec x

/-- Correctness of a two-input total operation, including exceptional values. -/
def Total2 (A B C : NumericalSystem) (run : A.Code → B.Code → C.Code)
    (spec : NumericalValue A.Scalar → NumericalValue B.Scalar → NumericalValue C.Scalar) :
    Prop :=
  Refines2 A B run fun x y result => C.denote result = spec x y

/-- Correctness of a three-input total operation, including exceptional values. -/
def Total3 (A B C D : NumericalSystem) (run : A.Code → B.Code → C.Code → D.Code)
    (spec : NumericalValue A.Scalar → NumericalValue B.Scalar →
      NumericalValue C.Scalar → NumericalValue D.Scalar) : Prop :=
  Refines3 A B C run fun x y z result => D.denote result = spec x y z

/-- Correctness of a unary operation on represented finite inputs. -/
def Finite1 (A B : NumericalSystem) (run : A.Code → B.Code)
    (spec : A.Scalar → B.Scalar) : Prop :=
  RefinesFinite1 A run fun x result => B.Represents result (spec x)

/-- Correctness of a two-input operation on represented finite inputs. -/
def Finite2 (A B C : NumericalSystem) (run : A.Code → B.Code → C.Code)
    (spec : A.Scalar → B.Scalar → C.Scalar) : Prop :=
  RefinesFinite2 A B run fun x y result => C.Represents result (spec x y)

/-- Correctness of a three-input operation on represented finite inputs. -/
def Finite3 (A B C D : NumericalSystem) (run : A.Code → B.Code → C.Code → D.Code)
    (spec : A.Scalar → B.Scalar → C.Scalar → D.Scalar) : Prop :=
  RefinesFinite3 A B C run fun x y z result => D.Represents result (spec x y z)

/--
Correctness of a unary operation when a predicate on the concrete input and result holds.

The predicate captures executable side conditions such as a floating-point result remaining
finite. It is proof-only and does not change the direct runtime function.
-/
def Finite1If (A B : NumericalSystem) (run : A.Code → B.Code)
    (spec : A.Scalar → B.Scalar) (accept : A.Code → B.Code → Prop) : Prop :=
  ∀ a x, A.Represents a x → accept a (run a) → B.Represents (run a) (spec x)

/--
Correctness of a two-input operation when a predicate on its concrete inputs and result holds.
-/
def Finite2If (A B C : NumericalSystem) (run : A.Code → B.Code → C.Code)
    (spec : A.Scalar → B.Scalar → C.Scalar)
    (accept : A.Code → B.Code → C.Code → Prop) : Prop :=
  ∀ a b x y, A.Represents a x → B.Represents b y →
    accept a b (run a b) → C.Represents (run a b) (spec x y)

/--
Correctness of a three-input operation when a predicate on its concrete inputs and result holds.
-/
def Finite3If (A B C D : NumericalSystem)
    (run : A.Code → B.Code → C.Code → D.Code)
    (spec : A.Scalar → B.Scalar → C.Scalar → D.Scalar)
    (accept : A.Code → B.Code → C.Code → D.Code → Prop) : Prop :=
  ∀ a b c x y z,
    A.Represents a x → B.Represents b y → C.Represents c z →
      accept a b c (run a b c) → D.Represents (run a b c) (spec x y z)

/-- Correctness of a checked unary operation on represented finite inputs. -/
def Checked1 (A B : NumericalSystem) (run : A.Code → Option B.Code)
    (spec : A.Scalar → NumericalValue B.Scalar) : Prop :=
  RefinesFinite1 A run fun x result => Option.map B.denote result = some (spec x)

/-- Correctness of a checked two-input operation on represented finite inputs. -/
def Checked2 (A B C : NumericalSystem) (run : A.Code → B.Code → Option C.Code)
    (spec : A.Scalar → B.Scalar → NumericalValue C.Scalar) : Prop :=
  RefinesFinite2 A B run fun x y result => Option.map C.denote result = some (spec x y)

/-- Correctness of a checked three-input operation on represented finite inputs. -/
def Checked3 (A B C D : NumericalSystem)
    (run : A.Code → B.Code → C.Code → Option D.Code)
    (spec : A.Scalar → B.Scalar → C.Scalar → NumericalValue D.Scalar) : Prop :=
  RefinesFinite3 A B C run fun x y z result =>
    Option.map D.denote result = some (spec x y z)

/-- A checked unary operation is correct whenever its scalar precondition holds. -/
def Checked1On (A B : NumericalSystem) (run : A.Code → Option B.Code)
    (spec : A.Scalar → NumericalValue B.Scalar) (pre : A.Scalar → Prop) : Prop :=
  ∀ a x, pre x → A.Represents a x → Option.map B.denote (run a) = some (spec x)

/-- A checked two-input operation is correct whenever its scalar precondition holds. -/
def Checked2On (A B C : NumericalSystem) (run : A.Code → B.Code → Option C.Code)
    (spec : A.Scalar → B.Scalar → NumericalValue C.Scalar)
    (pre : A.Scalar → B.Scalar → Prop) : Prop :=
  ∀ a b x y, pre x y → A.Represents a x → B.Represents b y →
    Option.map C.denote (run a b) = some (spec x y)

/-- A checked three-input operation is correct whenever its scalar precondition holds. -/
def Checked3On (A B C D : NumericalSystem)
    (run : A.Code → B.Code → C.Code → Option D.Code)
    (spec : A.Scalar → B.Scalar → C.Scalar → NumericalValue D.Scalar)
    (pre : A.Scalar → B.Scalar → C.Scalar → Prop) : Prop :=
  ∀ a b c x y z, pre x y z →
    A.Represents a x → B.Represents b y → C.Represents c z →
      Option.map D.denote (run a b c) = some (spec x y z)

/-- A conversion implements `embed` on every represented value accepted by `pre`. -/
def CastFiniteOn (A B : NumericalSystem) (run : A.Code → B.Code)
    (embed : A.Scalar → B.Scalar) (pre : A.Scalar → Prop) : Prop :=
  ∀ code x, pre x → A.Represents code x → B.Represents (run code) (embed x)

/-- A quantizer implements a named rounding map on values satisfying `pre`. -/
def QuantizerOn (S : NumericalSystem) (quantize : S.Scalar → S.Code)
    (round : S.Scalar → S.Scalar) (pre : S.Scalar → Prop) : Prop :=
  ∀ x, pre x → S.Represents (quantize x) (round x)

end FloatLib.Numerics.Operation
