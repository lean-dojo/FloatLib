/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Proof.Arithmetic

/-!
# The six execution equations as one proposition

The operation typeclasses already require every executable kernel to carry its refinement proof.
`FullArithmeticCertificate` collects those six refinement statements, indexed by the shared
operation enum, and `fullArithmeticCertificate` proves it from the six capability instances.

Don't read more into the bundle than it says. It packages `ExecFloat.Proof.add_eq_spec` and its five
siblings, nothing more. It holds for every format that has all six capabilities, because each
capability carries its equation, so it can't tell a correct format from one whose stored
specification is wrong, and a format missing a capability can't even state it. Formats supporting
only some of the operations use the individual `*_eq_spec` theorems.

Each equation says that a public operation equals the specification stored by its format capability,
while what that specification computes, and whether it conforms to a standard, is the subject of
separate format-family theorems.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Proof

open FloatLib.Numerics

universe u

/-- Pointwise specification-refinement proposition for one universal operation. -/
def OperationRefines
    (F : Type u)
    [FloatLib.Floats.ExecFloat.Backend.PolicyFor F]
    [EncodedFormat F]
    [FloatLib.Floats.ExecFloat.Add F]
    [FloatLib.Floats.ExecFloat.Sub F]
    [FloatLib.Floats.ExecFloat.Mul F]
    [FloatLib.Floats.ExecFloat.Div F]
    [FloatLib.Floats.ExecFloat.Sqrt F]
    [FloatLib.Floats.ExecFloat.Fma F] :
    FloatLib.Floats.ExecFloat.Backend.Operation → Prop
  | .add =>
    ∀ left right : FloatLib.Floats.ExecFloat F,
      FloatLib.Floats.ExecFloat.add left right =
        FloatLib.Floats.ExecFloat.Spec.add left right
  | .sub =>
    ∀ left right : FloatLib.Floats.ExecFloat F,
      FloatLib.Floats.ExecFloat.sub left right =
        FloatLib.Floats.ExecFloat.Spec.sub left right
  | .mul =>
    ∀ left right : FloatLib.Floats.ExecFloat F,
      FloatLib.Floats.ExecFloat.mul left right =
        FloatLib.Floats.ExecFloat.Spec.mul left right
  | .div =>
    ∀ left right : FloatLib.Floats.ExecFloat F,
      FloatLib.Floats.ExecFloat.div left right =
        FloatLib.Floats.ExecFloat.Spec.div left right
  | .sqrt =>
    ∀ value : FloatLib.Floats.ExecFloat F,
      FloatLib.Floats.ExecFloat.sqrt value =
        FloatLib.Floats.ExecFloat.Spec.sqrt value
  | .fma =>
    ∀ left right addend : FloatLib.Floats.ExecFloat F,
      FloatLib.Floats.ExecFloat.fma left right addend =
        FloatLib.Floats.ExecFloat.Spec.fma left right addend

/--
The six execution equations of one format, indexed by `Backend.Operation`.

Indexing by the operation saves a second six-field record parallel to the executable capability
hierarchy. The proposition relates execution to the specifications the capabilities store, and it
says nothing about what those specifications compute.
-/
abbrev FullArithmeticCertificate
    (F : Type u)
    [FloatLib.Floats.ExecFloat.Backend.PolicyFor F]
    [EncodedFormat F]
    [FloatLib.Floats.ExecFloat.Add F]
    [FloatLib.Floats.ExecFloat.Sub F]
    [FloatLib.Floats.ExecFloat.Mul F]
    [FloatLib.Floats.ExecFloat.Div F]
    [FloatLib.Floats.ExecFloat.Sqrt F]
    [FloatLib.Floats.ExecFloat.Fma F] : Prop :=
  ∀ operation, OperationRefines F operation

/--
Every format with all six operation capabilities satisfies `FullArithmeticCertificate`: the
proof collects the refinement equation each capability carries.
-/
theorem fullArithmeticCertificate
    (F : Type u)
    [FloatLib.Floats.ExecFloat.Backend.PolicyFor F]
    [EncodedFormat F]
    [FloatLib.Floats.ExecFloat.Add F]
    [FloatLib.Floats.ExecFloat.Sub F]
    [FloatLib.Floats.ExecFloat.Mul F]
    [FloatLib.Floats.ExecFloat.Div F]
    [FloatLib.Floats.ExecFloat.Sqrt F]
    [FloatLib.Floats.ExecFloat.Fma F] :
    FullArithmeticCertificate F := by
  intro operation
  cases operation with
  | add => exact add_eq_spec
  | sub => exact sub_eq_spec
  | mul => exact mul_eq_spec
  | div => exact div_eq_spec
  | sqrt => exact sqrt_eq_spec
  | fma => exact fma_eq_spec

end FloatLib.Floats.ExecFloat.Proof
