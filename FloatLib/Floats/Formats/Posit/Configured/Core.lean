/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Spec
public import FloatLib.Floats.Formats.Posit.Configured.Storage.Family.Proof

/-!
# Configured posit semantic core

Configured posit operations lift the exact model through the statically selected public carrier.
These specifications are independent of optimized execution backends: clients that only need the
configured type and its independent specification should not depend on planner or kernel
implementation details.

Carrier packing is proved inverse to model decoding in `Configured.Storage.Family.Proof`.
Consequently these definitions do not depend on whether a closed width selected `UInt8`, `UInt16`,
`UInt32`, `UInt64`, two limbs, or the exact-width wide model.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured

open FloatLib.Floats.ExecFloat

namespace Spec

/-
The `noinline` and `nospecialize` attributes keep the reference decode/encode path from being
duplicated at each caller with a concrete `ModelCodec`. They affect code generation only;
the definitions remain available to proofs.
-/

/-- Independent exact configured addition specification. -/
@[noinline, nospecialize] def add {format : Format} {plan : StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] :=
  ModelCodec.liftBinary (F := Family format code plan) (Model := Model format) (plan := plan) Model.Spec.add

/-- Independent exact configured subtraction specification. -/
@[noinline, nospecialize] def sub {format : Format} {plan : StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] :=
  ModelCodec.liftBinary (F := Family format code plan) (Model := Model format) (plan := plan) Model.Spec.sub

/-- Independent exact configured multiplication specification. -/
@[noinline, nospecialize] def mul {format : Format} {plan : StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] :=
  ModelCodec.liftBinary (F := Family format code plan) (Model := Model format) (plan := plan) Model.Spec.mul

/-- Independent exact configured division specification. -/
@[noinline, nospecialize] def div {format : Format} {plan : StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] :=
  ModelCodec.liftBinary (F := Family format code plan) (Model := Model format) (plan := plan) Model.Spec.div

/-- Independent exact configured square-root specification. -/
@[noinline, nospecialize] def sqrt {format : Format} {plan : StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] :=
  ModelCodec.liftUnary (F := Family format code plan) (Model := Model format) (plan := plan) Model.Spec.sqrt

/-- Independent exact configured fused-multiply-add specification. -/
@[noinline, nospecialize] def fma {format : Format} {plan : StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] :=
  ModelCodec.liftTernary (F := Family format code plan) (Model := Model format) (plan := plan) Model.Spec.fma

end Spec

end FloatLib.Floats.Formats.Posit.Configured
