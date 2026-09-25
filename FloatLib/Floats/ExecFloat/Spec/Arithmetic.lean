/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Core.Operations

/-!
# Reference arithmetic for `ExecFloat`

Names for the six reference operations supplied by arithmetic capabilities. Use them with the
refinement equations in `ExecFloat.Proof` to reason about an executable arithmetic expression.

Each reference operation is the `spec` field of the format's `Capability`, and `Capability` is
indexed by the planning policy `[Backend.PolicyFor F]` because the same class also stores the
selected implementation. Each refinement theorem refers to the specification in the current
instance. Policy independence across distinct instances requires them to supply the same
specification; the capability class imposes no separate law relating those instances. The default
`PolicyFor` instance is normally inferred at use sites.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Spec

open FloatLib.Numerics

universe u

variable {F : Type u} [FloatLib.Floats.ExecFloat.Backend.PolicyFor F]
    [EncodedFormat F]

/--
Reference definition of addition for this format.

Proofs use this definition to state the required result. Numerical code should normally call
`ExecFloat.add` or use `+`.
-/
def add [FloatLib.Floats.ExecFloat.Add F]
    (left right : FloatLib.Floats.ExecFloat F) : FloatLib.Floats.ExecFloat F :=
  FloatLib.Floats.ExecFloat.Add.spec left right

/--
Reference definition of subtraction for this format.

Proofs use this definition to state the required result. Numerical code should normally call
`ExecFloat.sub` or use `-`.
-/
def sub [FloatLib.Floats.ExecFloat.Sub F]
    (left right : FloatLib.Floats.ExecFloat F) : FloatLib.Floats.ExecFloat F :=
  FloatLib.Floats.ExecFloat.Sub.spec left right

/--
Reference definition of multiplication for this format.

Proofs use this definition to state the required result. Numerical code should normally call
`ExecFloat.mul` or use `*`.
-/
def mul [FloatLib.Floats.ExecFloat.Mul F]
    (left right : FloatLib.Floats.ExecFloat F) : FloatLib.Floats.ExecFloat F :=
  FloatLib.Floats.ExecFloat.Mul.spec left right

/--
Reference definition of division for this format.

Proofs use this definition to state the required result. Numerical code should normally call
`ExecFloat.div` or use `/`.
-/
def div [FloatLib.Floats.ExecFloat.Div F]
    (left right : FloatLib.Floats.ExecFloat F) : FloatLib.Floats.ExecFloat F :=
  FloatLib.Floats.ExecFloat.Div.spec left right

/--
Reference definition of square root for this format.

Proofs use this definition to state the required result. Numerical code should normally call
`ExecFloat.sqrt` or use `value.sqrt`.
-/
def sqrt [FloatLib.Floats.ExecFloat.Sqrt F]
    (value : FloatLib.Floats.ExecFloat F) : FloatLib.Floats.ExecFloat F :=
  FloatLib.Floats.ExecFloat.Sqrt.spec value

/--
Reference definition of fused multiply-add for this format.

Proofs use this definition to state the result required by the installed capability. Numerical code
should normally call `ExecFloat.fma` or use `left.fma right addend`.
-/
def fma [FloatLib.Floats.ExecFloat.Fma F]
    (left right addend : FloatLib.Floats.ExecFloat F) : FloatLib.Floats.ExecFloat F :=
  FloatLib.Floats.ExecFloat.Fma.spec left right addend

end FloatLib.Floats.ExecFloat.Spec
