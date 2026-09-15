/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Proof.Arithmetic

/-!
# Certificate for all six core arithmetic operations

The operation typeclasses already require every executable kernel to carry its refinement proof.
`FullArithmeticCertificate` collects those six refinement statements, indexed by the shared
operation enum.

Users can request this bundle when they want one machine-checked answer to “which core operations
are certified for this format?” Formats supporting only a subset of operations continue to expose
their individual `ExecFloat.Proof.*_eq_spec` theorems.

The certificate covers the universal execution boundary: each public operation equals the
specification stored by its format capability. Standards conformance and denotational properties
of that specification require separate format-family theorems.
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
Kernel-checked refinement evidence for every universal arithmetic operation on one format.

Indexing by `Backend.Operation` avoids a second six-field record parallel to the executable
capability hierarchy. This proposition certifies execution against the installed specifications;
it does not replace format-specific theorems about what those specifications mean.
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
Collect the refinement proofs supplied by the six operation capabilities.
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
