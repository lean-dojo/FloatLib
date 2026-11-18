/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Executable.ModelCodec
public import FloatLib.Tactic.CompilerOptimize

/-!
# The `portfolio_capability` command

This frontend generates the declarations documented below. Its expansions are checked
in the importing mathematical module.
-/

public meta section

open FloatLib.Numerics

set_option hygiene false in
/--
`portfolio_capability Op op FormatType for Spec.op` declares, in the namespace of a family, the
    capability
`⟨op⟩Capability` of one operation for the family on any carrier `code`, an instance of
`ExecFloat.⟨Op⟩ (Family format code plan)` at priority 100. The planner selects among the
baseline and the named alternatives of `Plan.⟨op⟩Candidates format plan` and the candidates
tagged `@[compiler_optimize]` for the reference operation `Spec.⟨op⟩` (`Capability.ofTagged`).

`Family`, `StoragePlan`, `Model`, `Spec.⟨op⟩` and `Plan.⟨op⟩Candidates` are the family's own
names, read where the command is used, and `FormatType` is the type of its descriptors.
-/
macro "portfolio_capability " upper:ident lower:ident
    formatType:ident " for " specification:ident : command => do
  let candidates := Lean.mkIdent (`Plan ++ lower.getId.appendAfter "Candidates")
  let operation := Lean.mkIdent (`FloatLib.Floats.ExecFloat.Backend.Operation ++ lower.getId)
  let spec := specification
  let capabilityClass := Lean.mkIdent (`FloatLib.Floats.ExecFloat ++ upper.getId)
  let text := s!"The `{lower.getId}` capability of the family on any carrier: the planner selects \
    among `Plan.{lower.getId}Candidates` and the candidates tagged `@[compiler_optimize]` for \
    `Spec.{lower.getId}`."
  `($(FloatLib.Floats.ExecFloat.generatedDoc text):docComment
    instance (priority := 100) $(Lean.mkIdent (lower.getId.appendAfter "Capability"))
        (format : $formatType) (plan : StoragePlan format) (code : Type)
        [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]
        [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Family format code plan)]
        [portfolio : FloatLib.Floats.ExecFloat.Backend.Portfolio
          (@$spec format plan code inferInstance)] :
        $capabilityClass (Family format code plan) :=
      FloatLib.Floats.ExecFloat.Capability.ofTagged $operation portfolio
        ($candidates format plan).baseline
        (named := ($candidates format plan).alternatives))
