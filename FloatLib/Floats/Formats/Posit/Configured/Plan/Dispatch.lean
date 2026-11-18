/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Tactic.PlanCapability
public import FloatLib.Tactic.PlannedCapability
public import FloatLib.Tactic.PortfolioCapability

/-!
# Static Posit storage-plan dispatch

A public posit picks its carrier from a width known in its type. This module turns the chosen
`StoragePlan` constructor into one capability per operation, each certified on its own. We index
the capabilities by operation so that a monomorphic public call reduces to its first-order backend
and never allocates a package of unrelated function fields.

What a call ends up running depends on the plan:

* An abstract or custom codec gets the representation-independent candidate set.
* A closed public width reduces its carrier match at compile time, and packed-word, packed-pair,
  and wide plans then name their single proved kernel.
* Byte plans keep a policy-sensitive choice between exhaustive tables and direct arithmetic,
  because setup cost and residency depend on the width, the operation's arity, and the workload
  policy.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured.Plan

open FloatLib.Floats.ExecFloat
open FloatLib.Floats.ExecFloat.Backend

plan_capability Add add binary ByteDispatch.add_fun_eq_spec "Addition" for Spec.addition :=
  let heligible : Model.NativeLimb.Eligible format := width_le
  Capability.ofCertified .add <| Certified.binary
    (storedNativeLimbEstimate (format := format) .add)
    Spec.addition
    (Backend.storedNativeLimbAdd width_le heligible)
    (Backend.storedNativeLimbAdd_eq_spec width_le heligible)

plan_capability Sub sub binary ByteDispatch.sub_fun_eq_spec "Subtraction" for Spec.subtraction :=
  let heligible : Model.NativeLimb.Eligible format := width_le
  Capability.ofCertified .sub <| Certified.binary
    (storedNativeLimbEstimate (format := format) .sub)
    Spec.subtraction
    (Backend.storedNativeLimbSub width_le heligible)
    (Backend.storedNativeLimbSub_eq_spec width_le heligible)

plan_capability Mul mul binary ByteDispatch.mul_fun_eq_spec "Multiplication" for
    Spec.multiplication :=
  let heligible : Model.NativeLimb.Eligible format := width_le
  Capability.ofCertified .mul <| Certified.binary
    (storedNativeLimbEstimate (format := format) .mul)
    Spec.multiplication
    (Backend.storedNativeLimbMul width_le heligible)
    (Backend.storedNativeLimbMul_eq_spec width_le heligible)

plan_capability Div div binary ByteDispatch.div_fun_eq_spec "Division" for Spec.division :=
  Capability.ofCertified .div <| Certified.binary
    (dyadicEstimate (.pair width_le) .div)
    Spec.division
    (Backend.storedNativeLimbDiv width_le)
    (Backend.storedNativeLimbDiv_eq_spec width_le)

plan_capability Sqrt sqrt unary ByteDispatch.sqrt_fun_eq_spec "Square-root" for Spec.sqrt :=
  Capability.ofCertified .sqrt <| Certified.unary
    (storedNativeLimbEstimate (format := format) .sqrt)
    Spec.sqrt
    (Backend.storedNativeLimbSqrt width_le)
    (Backend.storedNativeLimbSqrt_eq_spec width_le)

plan_capability Fma fma ternary ByteDispatch.fma_fun_eq_spec "Fused-multiply-add" for Spec.fma :=
  let heligible : Model.NativeLimb.Eligible format := width_le
  Capability.ofCertified .fma <| Certified.ternary
    (storedNativeLimbEstimate (format := format) .fma)
    Spec.fma
    (Backend.storedNativeLimbFma width_le heligible)
    (Backend.storedNativeLimbFma_eq_spec width_le heligible)

end FloatLib.Floats.Formats.Posit.Configured.Plan

namespace FloatLib.Floats.Formats.Posit.Configured

/-!
Built-in storage-plan instances take priority over the representation-independent instance, which
has a low priority: they are static capabilities, served by `Capability.ofStatic`. Their
inline constructors, one per operation, specialize a closed public width to one carrier and one
first-order executor. Custom codecs keep the generic certified candidate portfolios below. Every
instance takes the portfolio of candidates tagged `@[compiler_optimize]` for its reference
operation: a built-in plan keeps its static kernel where no tagged candidate applies
(`Capability.Static`), and a custom codec selects among its own candidates and the tagged ones.
-/

planned_capability add for Spec.addition
planned_capability sub for Spec.subtraction
planned_capability mul for Spec.multiplication
planned_capability div for Spec.division
planned_capability sqrt for Spec.sqrt
planned_capability fma for Spec.fma

portfolio_capability Add add Format for Spec.addition
portfolio_capability Sub sub Format for Spec.subtraction
portfolio_capability Mul mul Format for Spec.multiplication
portfolio_capability Div div Format for Spec.division
portfolio_capability Sqrt sqrt Format for Spec.sqrt
portfolio_capability Fma fma Format for Spec.fma

end FloatLib.Floats.Formats.Posit.Configured
