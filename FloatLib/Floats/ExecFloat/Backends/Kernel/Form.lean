/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Tactic.DirectForm
public import FloatLib.Tactic.FormRule

/-!
# Kernel forms: the operation that Lean's kernel evaluates for a family

A public operation such as `x + y` runs the implementation that the planner selects, and Lean's
kernel pays for that selection on every evaluation: it compares the estimates of the candidates
before it reaches the arithmetic, and the selected implementation is written for compiled code.
A family says which proved form of an operation the kernel should evaluate instead, with one
instance per operation next to its capability:

* `KernelForm F operation form`: `form` equals the reference operation of the capability in
  scope. The ten rules below, tagged `@[kernel_optimize]`, rewrite the public operation and its
  notation to `form`, for every format with such an instance. `form_rule` generates them from
  one line each: `add_eq_form` to `fma_eq_form` for the six functions, and `add_notation_eq_form`
  to `div_notation_eq_form` for the four infix operators.
* `DirectReference F operation`: the form is the reference operation itself. This is for a format
  whose reference operation is already a direct computation on its stored code (exact fixed
  point adds two integer coefficients, a logarithmic value adds two exponents, a P3109 value is
  one projection of an exact result).

The rules declare no cost, so a rule that a format tags with a cost for the same operation (the
binary formats, with their operations on encodings) is tried first. The kernel cost of a form is
that of the family's instance, and `benchmarks/suite/Families.lean` measures it for each family.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.KernelPath

open FloatLib.Numerics

universe u

/--
`KernelForm F operation form`: Lean's kernel should evaluate the operation of `F` as `form`, which
equals the reference operation of the capability in scope. `float_decide` rewrites the public
operation to `form`.
-/
class KernelForm (F : Type u) [EncodedFormat F] [Backend.PolicyFor F]
    (operation : Backend.Operation) [capability : Capability F operation]
    (form : outParam (OperationSignature F operation)) : Prop where
  /-- The reference operation of the capability is `form`. -/
  spec_eq : capability.spec = form

/--
The reference operation of the capability of `operation` on `F` is the form that Lean's kernel
should evaluate.
-/
class DirectReference (F : Type u) [EncodedFormat F] [Backend.PolicyFor F]
    (operation : Backend.Operation) [Capability F operation] : Prop

variable {F : Type u} [Backend.PolicyFor F] [EncodedFormat F]

/-! ## A direct reference is its own form -/

direct_form [Add] .add Spec.add "addition"
direct_form [Sub] .sub Spec.sub "subtraction"
direct_form [Mul] .mul Spec.mul "multiplication"
direct_form [Div] .div Spec.div "division"
direct_form [Sqrt] .sqrt Spec.sqrt "square root"
direct_form [Fma] .fma Spec.fma "fused multiply-add"

/-! ## The public operation is its kernel form -/

form_rule add_eq_form [Add] .add (x y) : ExecFloat.add x y := Proof.add_eq_spec,
  "The public addition"
form_rule sub_eq_form [Sub] .sub (x y) : ExecFloat.sub x y := Proof.sub_eq_spec,
  "The public subtraction"
form_rule mul_eq_form [Mul] .mul (x y) : ExecFloat.mul x y := Proof.mul_eq_spec,
  "The public multiplication"
form_rule div_eq_form [Div] .div (x y) : ExecFloat.div x y := Proof.div_eq_spec,
  "The public division"
form_rule sqrt_eq_form [Sqrt] .sqrt (x) : ExecFloat.sqrt x := Proof.sqrt_eq_spec,
  "The public square root"
form_rule fma_eq_form [Fma] .fma (x y z) : ExecFloat.fma x y z := Proof.fma_eq_spec,
  "The public fused multiply-add"
form_rule add_notation_eq_form [Add] .add (x y) : x + y := Proof.add_notation_eq_spec, "`x + y`"
form_rule sub_notation_eq_form [Sub] .sub (x y) : x - y := Proof.sub_notation_eq_spec, "`x - y`"
form_rule mul_notation_eq_form [Mul] .mul (x y) : x * y := Proof.mul_notation_eq_spec, "`x * y`"
form_rule div_notation_eq_form [Div] .div (x y) : x / y := Proof.div_notation_eq_spec, "`x / y`"

end FloatLib.Floats.ExecFloat.KernelPath
