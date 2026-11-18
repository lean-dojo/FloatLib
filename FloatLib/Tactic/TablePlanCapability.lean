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
# The `table_plan_capability` command

This frontend generates the declarations documented below. Its expansions are checked
in the importing mathematical module.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.StaticByte
namespace Plans

open FloatLib.Floats.ExecFloat

set_option hygiene false in
/--
`table_plan_capability Op op "name"` declares the static capability of one operation for a
static-byte family with a `TablePlan`: the planning profile chooses between the plan's certified
table and the exact baseline.
-/
macro "table_plan_capability " upper:ident lower:ident name:str : command => do
  let op := upper.getId.toString
  let operation := Lean.mkIdent (`FloatLib.Floats.ExecFloat.Backend.Operation ++ lower.getId)
  let spec := Lean.mkIdent (`Spec ++ lower.getId)
  let field (suffix : String) := Lean.mkIdent (`plan ++ lower.getId.appendAfter suffix)
  let text := s!"{name.getString.capitalize} for a static-byte family with a `TablePlan`: the \
    planning profile chooses between the plan's certified {name.getString} table and the exact \
    baseline."
  `($(ExecFloat.generatedDoc text):docComment
    @[always_inline, instance_reducible] instance (priority := 200)
        $(Lean.mkIdent (Lean.Name.mkSimple s!"tablePlan{op}Capability"))
        (F : Type u) [Family F] [plan : TablePlan F]
        [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor F] :
        FloatLib.Floats.ExecFloat.Capability.Static (F := F) $operation
          ($spec (F := F)) where
      spec_eq := rfl
      capability :=
        $(Lean.mkIdent (`Internal ++ lower.getId.appendAfter "TableCapability"))
          $(field "Name") $(field "Selection")
          (Family.width_le_eight (F := F)) $(field "Table"))

end Plans

end FloatLib.Floats.Formats.BinaryInterchange.StaticByte
