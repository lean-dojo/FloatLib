/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Spec
public import FloatLib.Floats.Formats.Posit.Configured.Storage.Family.Proof

/-!
# Configured posit semantic core

Each configured posit operation is specified here by lifting the exact model operation through
the statically selected public carrier. None of these specifications mentions an optimized
backend. If all you need is the configured type and its independent specification, import this
module and you won't depend on any planner or kernel detail.

Carrier packing is proved inverse to model decoding in `Configured.Storage.Family.Proof`. So the
definitions mean the same thing whether a closed width picked `UInt8`, `UInt16`, `UInt32`,
`UInt64`, two limbs, or the exact-width wide model.
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

/--
Posit Standard (2022), §5.4: `Model.Spec.addition` on decoded words,
rounding the exact sum once and propagating NaR.
-/
@[noinline, nospecialize] def addition {format : Format} {plan : StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] :=
  ModelCodec.liftBinary (F := Family format code plan) (Model := Model format) (plan := plan)
    Model.Spec.addition

/--
Posit Standard (2022), §5.4: `Model.Spec.subtraction` on decoded words,
rounding the exact difference once and propagating NaR.
-/
@[noinline, nospecialize] def subtraction {format : Format} {plan : StoragePlan format} {code :
    Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] :=
  ModelCodec.liftBinary (F := Family format code plan) (Model := Model format) (plan := plan)
    Model.Spec.subtraction

/--
Posit Standard (2022), §5.4: `Model.Spec.multiplication` on decoded words,
rounding the exact product once and propagating NaR.
-/
@[noinline, nospecialize] def multiplication {format : Format} {plan : StoragePlan format} {code
    : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] :=
  ModelCodec.liftBinary (F := Family format code plan) (Model := Model format) (plan := plan)
    Model.Spec.multiplication

/--
Posit Standard (2022), §5.4: `Model.Spec.division` on decoded words,
rounding the exact quotient once and returning NaR for NaR input or a zero divisor.
-/
@[noinline, nospecialize] def division {format : Format} {plan : StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] :=
  ModelCodec.liftBinary (F := Family format code plan) (Model := Model format) (plan := plan)
    Model.Spec.division

/--
Posit Standard (2022), §5.5: `Model.Spec.sqrt` on the decoded word,
rounding the real root once and returning NaR for NaR or a negative input.
-/
@[noinline, nospecialize] def sqrt {format : Format} {plan : StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] :=
  ModelCodec.liftUnary (F := Family format code plan) (Model := Model format) (plan := plan)
    Model.Spec.sqrt

/--
FloatLib FMA extension with Posit Standard (2022), §4.1 rounding:
`Model.Spec.fma` on decoded words rounds `left * right + addend` once and propagates NaR.
-/
@[noinline, nospecialize] def fma {format : Format} {plan : StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] :=
  ModelCodec.liftTernary (F := Family format code plan) (Model := Model format) (plan := plan)
    Model.Spec.fma

end Spec

end FloatLib.Floats.Formats.Posit.Configured
