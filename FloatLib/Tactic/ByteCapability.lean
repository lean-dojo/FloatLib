/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.Execution.Capability
public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.Backend.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.Plan.Proof

/-!
# The `byte_capability` command

This frontend generates the declarations documented below. Its expansions are checked
in the importing mathematical module.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.StaticByte
namespace Plans
namespace Internal

open FloatLib.Floats.ExecFloat

set_option hygiene false in
/--
`byte_capability Op op table execute execute_eq (arguments) "name"` declares
`Internal.⟨op⟩Capability`: the capability of one operation of a static-byte family from a named
kernel `run` with its proof `run = Spec.⟨op⟩`, with the certified profile selection `execute`
between the `table` candidate of `run` and the exact baseline. `execute_eq` states that
`execute` computes the reference operation.
-/
macro "byte_capability " upper:ident lower:ident table:ident execute:ident
    executeEq:ident " (" arguments:ident* ") " name:str : command => do
  let operation := Lean.mkIdent (`FloatLib.Floats.ExecFloat.Backend.Operation ++ lower.getId)
  let spec := Lean.mkIdent (`Spec ++ lower.getId)
  let capabilityClass := Lean.mkIdent (`FloatLib.Floats.ExecFloat ++ upper.getId)
  let binders : Lean.TSyntaxArray `term := arguments.map fun argument => ⟨argument.raw⟩
  let runType ← arguments.foldlM (init := ← `(FloatLib.Floats.ExecFloat F)) fun type _ =>
    `(FloatLib.Floats.ExecFloat F → $type)
  `($(ExecFloat.generatedDoc s!"Construct a static-byte {name.getString} capability with \
        certified profile \
      selection."):docComment
    @[always_inline, instance_reducible] def $(Lean.mkIdent (lower.getId.appendAfter "Capability"))
        {F : Type u} [Family F]
        [FloatLib.Floats.ExecFloat.Backend.PolicyFor F]
        (name : String)
        (selection : BuiltinSelection (Family.format (F := F)) name $operation)
        (run : $runType)
        (run_eq_spec : ∀ $arguments*, run $binders* = $spec $binders*) :
        $capabilityClass F :=
      Capability.ofCandidates $operation $spec
        ($table name $operation $spec run run_eq_spec)
        ($execute name $operation selection $spec run)
        (by
          funext $binders*
          exact $executeEq name $operation selection $spec run run_eq_spec $binders*))

end Internal

end Plans

end FloatLib.Floats.Formats.BinaryInterchange.StaticByte
