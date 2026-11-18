/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.Candidates
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Storage.Codecs

/-!
# The `fixed_format` command

This frontend generates the declarations documented below. Its expansions are checked
in the importing mathematical module.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan

open FloatLib.Floats.ExecFloat
open FloatLib.Floats.ExecFloat.Backend

set_option hygiene false in
/--
`fixed_format bits Op op kind "name"` declares, for one operation of binary32 or binary64 on its
machine word:

* `software⟨Op⟩⟨bits⟩Certified`: the certified fixed-word kernel, tagged
  `@[compiler_optimize direct]`;
* `binary⟨bits⟩⟨Op⟩Candidates`: every certified software implementation considered for the
  operation;
* `selectCertified_binary⟨bits⟩⟨Op⟩Candidates`: under every policy that portfolio selects the
  fixed-word kernel.
-/
macro "fixed_format " bits:num upper:ident lower:ident kind:ident name:str : command => do
  let n := bits.getNat
  let op := upper.getId.toString
  let format := Lean.mkIdent (`FloatFormat ++ Lean.Name.mkSimple s!"binary{n}")
  let wordPlan := Lean.mkIdent (`StoragePlan ++ Lean.Name.mkSimple s!"word{n}")
  let operation := Lean.mkIdent (`FloatLib.Floats.ExecFloat.Backend.Operation ++ lower.getId)
  let spec := Lean.mkIdent (`Spec ++ lower.getId)
  let certified := Lean.mkIdent (`Certified ++ kind.getId)
  let kernel := Lean.mkIdent (`Backend ++ Lean.Name.mkSimple s!"word{op}")
  let kernelEq := Lean.mkIdent (`Backend ++ Lean.Name.mkSimple s!"word{op}_eq_spec")
  let software := Lean.mkIdent (Lean.Name.mkSimple s!"software{op}{n}Certified")
  let candidates := Lean.mkIdent (Lean.Name.mkSimple s!"binary{n}{op}Candidates")
  let familyCandidates := Lean.mkIdent (lower.getId.appendAfter "Candidates")
  let selected := Lean.mkIdent (Lean.Name.mkSimple s!"selectCertified_binary{n}{op}Candidates")
  let what := s!"binary{n} {name.getString}"
  `($(ExecFloat.generatedDoc s!"Certified fixed-word {what}."):docComment
    @[compiler_optimize direct]
    def $software (width_le : ($format).bitWidth ≤ $bits) :
        Certified
          (@$spec $format ($wordPlan width_le) (Code ($wordPlan width_le)) inferInstance) :=
      $certified (structuralEstimate ($wordPlan width_le) $operation .fixedFormat)
        $spec $kernel $kernelEq

    $(ExecFloat.generatedDoc
      s!"Every certified software implementation considered for {what}."):docComment
    def $candidates (width_le : ($format).bitWidth ≤ $bits) :
        CandidateSet
          (Certified
            (@$spec $format ($wordPlan width_le) (Code ($wordPlan width_le)) inferInstance)) :=
      $familyCandidates $format ($wordPlan width_le)

    $(ExecFloat.generatedDoc s!"Under every policy the {what} portfolio selects the certified \
          software \
      kernel."):docComment
    theorem $selected (policy : Policy) (width_le : ($format).bitWidth ≤ $bits) :
        selectCertified policy ($candidates width_le) = $software width_le := by
      unfold $candidates $familyCandidates
      rw [show Descriptor.Plan.structuralRoute? $format $operation = some .fixedFormat from rfl]
      exact selectCertified_structuralFixedFormat policy ($wordPlan width_le) $operation _ _
        rfl rfl (by decide))

end FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan
