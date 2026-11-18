/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Core.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.Estimates
public import FloatLib.Tactic.CompilerOptimize

/-!
# The `candidate_set` command

This frontend generates the declarations documented below. Its expansions are checked
in the importing mathematical module.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan

open FloatLib.Floats.ExecFloat
open FloatLib.Floats.ExecFloat.Backend

set_option hygiene false in
/--
`candidate_set Op op kind "name"` and `candidate_set Op op kind routed "name"` declare
`⟨op⟩Candidates`: the complete certified portfolio of one operation for a configured carrier.
Its alternatives are the optional direct kernels followed by the structural candidate of the
descriptor's route, when it has one, and its baseline is the generic kernel.

The structural candidate is the word kernel `Backend.word⟨Op⟩`. `routed` is for an operation
whose fixed-limb route has a kernel of its own, `Backend.fixedLimb⟨Op⟩` (square root and fused
multiply-add).
-/
macro "candidate_set " upper:ident lower:ident kind:ident routed:(&" routed")? name:str :
    command => do
  let op := upper.getId.toString
  let operation := Lean.mkIdent (`FloatLib.Floats.ExecFloat.Backend.Operation ++ lower.getId)
  let spec := Lean.mkIdent (`Spec ++ lower.getId)
  let certified := Lean.mkIdent (`Certified ++ kind.getId)
  let backend (text : String) := Lean.mkIdent (`Backend ++ Lean.Name.mkSimple text)
  let word ← `($certified (structuralEstimate plan $operation route)
    $spec $(backend s!"word{op}") $(backend s!"word{op}_eq_spec"))
  let structural ← if routed.isSome then
      `(match route with
        | .fixedLimbs =>
            $certified (structuralEstimate plan $operation route)
              $spec $(backend s!"fixedLimb{op}") $(backend s!"fixedLimb{op}_eq_spec")
        | .fixedFormat | .nativeWord => $word)
    else pure word
  `($(ExecFloat.generatedDoc s!"Complete certified {name.getString} portfolio for a configured \
        carrier and \
      optional direct kernels."):docComment
    @[nospecialize] def $(Lean.mkIdent (lower.getId.appendAfter "Candidates"))
        (format : FloatFormat) (plan : StoragePlan format)
        {code : Type} [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]
        (direct : List (Certified (@$spec format plan code inferInstance)) := []) :
        CandidateSet (Certified (@$spec format plan code inferInstance)) where
      alternatives := direct ++
        (Descriptor.Plan.structuralRoute? format $operation).toList.map (fun route => $structural)
      baseline :=
        $certified (genericEstimate plan $operation)
          $spec $(backend s!"generic{op}") $(backend s!"generic{op}_eq_spec"))

end FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan
