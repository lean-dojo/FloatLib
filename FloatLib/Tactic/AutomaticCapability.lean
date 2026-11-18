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
# The `automatic_capability` command

This frontend generates the declarations documented below. Its expansions are checked
in the importing mathematical module.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.Configured

set_option hygiene false in
/--
`automatic_capability Op op candidates (arguments) := direct, direct_eq` declares the static
capability of one operation on a built-in carrier `Code plan`. Its `execute` calls `direct` when
the structural candidate is selected under the policy in scope, `Backend.generic⟨Op⟩` when the
generic kernel is, and the memoized selection among `candidates` otherwise. `direct_eq` states
that `direct` computes the structural candidate's result.
-/
macro "automatic_capability " upper:ident lower:ident candidates:ident
    " (" arguments:ident* ")" " := " direct:ident ", " directEq:ident : command => do
  let op := upper.getId.toString
  let plan (text : String) := Lean.mkIdent (`Plan ++ Lean.Name.mkSimple text)
  let generic := Lean.mkIdent (`Backend ++ Lean.Name.mkSimple s!"generic{op}")
  let firstOrder := plan s!"select_{lower.getId}_run_of_firstOrder"
  let firstOrderGeneric := plan s!"select_{lower.getId}_run_of_firstOrderGeneric"
  let operation := Lean.mkIdent (`FloatLib.Floats.ExecFloat.Backend.Operation ++ lower.getId)
  let spec := Lean.mkIdent (`Spec ++ lower.getId)
  let binders : Lean.TSyntaxArray `term := arguments.map fun argument => ⟨argument.raw⟩
  let text := s!"The static `{lower.getId}` capability of a built-in carrier `Code plan`: the \
    structural or the generic kernel where the policy selects it first, the memoized selection \
    among `{candidates.getId}` otherwise."
  `($(ExecFloat.generatedDoc text):docComment
    @[always_inline] instance (priority := 200)
        $(Lean.mkIdent (Lean.Name.mkSimple s!"automatic{op}Capability"))
        (format : FloatFormat) (plan : StoragePlan format)
        [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor
          (Family format (Code plan) plan)] :
        FloatLib.Floats.ExecFloat.Capability.Static (F := Family format (Code plan) plan)
          $operation (@$spec format plan (Code plan) inferInstance) where
      spec_eq := rfl
      capability :=
      let selection := Thunk.mk fun _ =>
        FloatLib.Floats.ExecFloat.Backend.selectCertified planning.policy
          ($candidates format plan)
      { spec := $spec
        candidates := $candidates format plan
        selection := selection
        execute := fun $binders* =>
          if Plan.firstOrderSelected planning.policy plan $operation then
            $direct $binders*
          else if Plan.firstOrderGenericSelected planning.policy plan $operation then
            $generic $binders*
          else
            selection.get.run $binders*
        execute_eq_implementation := by
          funext $binders*
          split
          · rename_i h
            rw [$directEq:ident, ← $firstOrder planning.policy plan h]
            rfl
          · split
            · rename_i h
              rw [← $firstOrderGeneric planning.policy plan h]
              rfl
            · rfl })

end FloatLib.Floats.Formats.BinaryInterchange.Configured
