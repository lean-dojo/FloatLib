/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.KernelPath
public import FloatLib.Tactic.CompilerOptimize
public meta import Lean.Elab.Command
public meta import Lean.Elab.Term

/-!
# PositStandard generators

The commands expand into declarations checked in the importing module.
-/

public meta section

namespace FloatLib.Floats.ExecFloat.Posit

open FloatLib.Floats.Formats.Posit

set_option hygiene false in
/-- Expand `standard_arithmetic` into its checked family declarations. -/
macro (name := standardArithmetic) doc:docComment "standard_arithmetic " name:ident "("
    args:ident* ")"
    " for " operation:term " using " run:term " spec " spec:term
    equalityDoc:docComment " theorem " equality:ident : command =>
  `($doc:docComment
    -- The codec and the policy are indices of the capability that instance search finds.
    @[inline, nolint unusedArguments]
    def $name {format : Format} {plan : Configured.StoragePlan format} {code : Type}
        [ModelCodec plan (Model format) code]
        [Backend.PolicyFor (Configured.Family format code plan)]
        [capability : Capability (Configured.Family format code plan) $operation]
        [Capability.HasSpec capability ($spec (format := format) (plan := plan) (code := code))]
        ($args* : ExecFloat (Configured.Family format code plan)) :
        ExecFloat (Configured.Family format code plan) :=
      $run $args*
    $equalityDoc:docComment
    theorem $equality {format : Format} {plan : Configured.StoragePlan format} {code : Type}
        [ModelCodec plan (Model format) code]
        [Backend.PolicyFor (Configured.Family format code plan)]
        [capability : Capability (Configured.Family format code plan) $operation]
        [Capability.HasSpec capability ($spec (format := format) (plan := plan) (code := code))] :
        $name (format := format) (plan := plan) (code := code) = $spec :=
      (Capability.run_eq_spec (F := Configured.Family format code plan)
        (operation := $operation)).trans (Capability.HasSpec.spec_eq (cap := capability)))


set_option hygiene false in
/-- Expand `standard_compare` into its checked family declarations. -/
macro (name := standardCompare) doc:docComment "standard_compare " name:ident " := "
    operation:term : command =>
  `($doc:docComment
    @[inline] def $name {format : Format} {plan : Configured.StoragePlan format} {code : Type}
        [ModelCodec plan (Model format) code]
        (left right : ExecFloat (Configured.Family format code plan)) : Bool :=
      $operation (toModel left) (toModel right))


end FloatLib.Floats.ExecFloat.Posit
