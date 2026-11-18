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
# The `byte_table_capability` command

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
`byte_table_capability Op op Certified lookup lookup_eq (arguments) "a name"` declares
`Internal.⟨op⟩TableCapability`: the capability of one operation from a certified byte table.
The executable table lookup `lookup` and its refinement proof `lookup_eq` are derived from the
same certificate, so a format package cannot accidentally pair a kernel with the wrong theorem.
-/
macro "byte_table_capability " upper:ident lower:ident certified:ident lookupTable:ident
    lookupEq:ident " (" arguments:ident* ") " name:str : command => do
  let operation := Lean.mkIdent (`FloatLib.Floats.ExecFloat.Backend.Operation ++ lower.getId)
  let spec := Lean.mkIdent (`Spec ++ lower.getId)
  let modelSpec := Lean.mkIdent
    (`FloatLib.Floats.Formats.BinaryInterchange.Model.Spec ++ lower.getId)
  let capabilityClass := Lean.mkIdent (`FloatLib.Floats.ExecFloat ++ upper.getId)
  let certifiedTable := Lean.mkIdent
    (`FloatLib.Floats.ExecFloat.Backend.TinyTable ++ certified.getId)
  let binders : Lean.TSyntaxArray `term := arguments.map fun argument => ⟨argument.raw⟩
  `($(ExecFloat.generatedDoc s!"Construct {name.getString} capability from a certified byte \
      table."):docComment
    @[always_inline, instance_reducible]
    def $(Lean.mkIdent (lower.getId.appendAfter "TableCapability"))
        {F : Type u} [Family F]
        [FloatLib.Floats.ExecFloat.Backend.PolicyFor F]
        (name : String)
        (selection : BuiltinSelection (Family.format (F := F)) name $operation)
        (width_le_eight : (Family.format (F := F)).bitWidth ≤ 8)
        (table : $certifiedTable
          (encoding (Family.format (F := F)) width_le_eight)
          $modelSpec) :
        $capabilityClass F :=
      $(Lean.mkIdent (lower.getId.appendAfter "Capability")) name selection
        ($lookupTable (F := F)
          (modelSpec := $modelSpec)
          width_le_eight table)
        (fun $binders* => by
          simpa only [$spec:ident] using
            ($lookupEq (F := F)
              (modelSpec := $modelSpec)
              width_le_eight table $binders*)))

end Internal

end Plans

end FloatLib.Floats.Formats.BinaryInterchange.StaticByte
