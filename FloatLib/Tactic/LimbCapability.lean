/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.Execution.Capability
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Direct.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.FirstOrder

/-!
# The `limb_capability` command

This frontend generates the declarations documented below. Its expansions are checked
in the importing mathematical module.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.Configured

set_option hygiene false in
/--
`limb_capability Op op "name"` declares the static capability of one operation for the concrete
limb carrier: the automatic capability of the limb plan.
-/
macro "limb_capability " upper:ident lower:ident name:str : command => do
  let op := upper.getId.toString
  let operation := Lean.mkIdent (`FloatLib.Floats.ExecFloat.Backend.Operation ++ lower.getId)
  let spec := Lean.mkIdent (`Spec ++ lower.getId)
  let text := s!"Policy-selected {name.getString} for the concrete limb carrier."
  `($(ExecFloat.generatedDoc text):docComment
    @[always_inline] instance (priority := 210)
        $(Lean.mkIdent (Lean.Name.mkSimple s!"limb{op}Capability"))
        (format : FloatFormat) (width_gt : 128 < format.bitWidth)
        [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor
          (Family format (Model.WideLimb.Value format) (.limbs width_gt))] :
        FloatLib.Floats.ExecFloat.Capability.Static
          (F := Family format (Model.WideLimb.Value format) (.limbs width_gt)) $operation
          (@$spec format (.limbs width_gt) (Code (.limbs width_gt)) inferInstance) :=
      $(Lean.mkIdent (Lean.Name.mkSimple s!"automatic{op}Capability")) format (.limbs width_gt))

end FloatLib.Floats.Formats.BinaryInterchange.Configured
