/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.Automatic

/-!
# The `first_order` command

This frontend generates the declarations documented below. Its expansions are checked
in the importing mathematical module.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.Configured
namespace Plan

open FloatLib.Floats.ExecFloat.Backend

set_option hygiene false in
/--
`first_order Op op kind := direct` and `first_order Op op kind routed := direct` declare, for one
operation, the two facts that let a capability call a kernel directly:

* `select_⟨op⟩_run_of_firstOrder`: when the structural candidate is selected under the policy,
  the planner's choice among `automatic⟨Op⟩Candidates` runs `direct`;
* `select_⟨op⟩_run_of_firstOrderGeneric`: when the generic kernel is selected, it runs
  `Backend.generic⟨Op⟩`.

`routed` is for an operation whose structural candidate depends on the descriptor's route
(square root and fused multiply-add, with `direct` the function `structuralSqrt` or
`structuralFma`): the proof then splits on the route.
-/
macro "first_order " upper:ident lower:ident kind:ident routed:(&" routed")? " := "
    direct:ident : command => do
  let op := upper.getId.toString
  let name := lower.getId.toString
  let operation := Lean.mkIdent (`FloatLib.Floats.ExecFloat.Backend.Operation ++ lower.getId)
  let automatic := Lean.mkIdent (Lean.Name.mkSimple s!"automatic{op}Candidates")
  let candidates := Lean.mkIdent (lower.getId.appendAfter "Candidates")
  let certified := Lean.mkIdent (`Certified ++ kind.getId)
  let generic := Lean.mkIdent (`Backend ++ Lean.Name.mkSimple s!"generic{op}")
  let structural ← if routed.isSome then
      `(tactic| cases route <;>
        simp [$automatic:ident, $candidates:ident, selectCertified,
          considerCertified, hr, $certified:ident, $direct:ident, h])
    else
      `(tactic| simp [$automatic:ident, $candidates:ident, selectCertified,
        considerCertified, hr, $certified:ident, h])
  let fallback ← if routed.isSome then
      `(tactic| cases route <;>
        simp [$automatic:ident, $candidates:ident, selectCertified,
          considerCertified, hr, $certified:ident, h])
    else
      `(tactic| simp [$automatic:ident, $candidates:ident, selectCertified,
        considerCertified, hr, $certified:ident, h])
  let text := s!"A direct {name} call names the selected candidate's function."
  `($(ExecFloat.generatedDoc text):docComment
    theorem $(Lean.mkIdent (Lean.Name.mkSimple s!"select_{name}_run_of_firstOrder"))
        {format : FloatFormat} (policy : Policy) (plan : StoragePlan format)
        (h : firstOrderSelected policy plan $operation = true) :
        (selectCertified policy ($automatic format plan)).run =
          @$direct format plan (Code plan) inferInstance := by
      rw [firstOrderSelected, Bool.and_eq_true] at h
      obtain ⟨hs, h⟩ := h
      cases plan <;> simp only [StoragePlan.firstOrderDispatch] at hs
      all_goals try contradiction
      all_goals
        unfold structuralSelected at h
        cases hr : Descriptor.Plan.structuralRoute? format $operation with
        | none => simp [hr] at h
        | some route =>
          simp only [hr] at h
          $structural:tactic

    $(ExecFloat.generatedDoc s!"The direct generic {name} call names the selected candidate's \
      function."):docComment
    theorem $(Lean.mkIdent (Lean.Name.mkSimple s!"select_{name}_run_of_firstOrderGeneric"))
        {format : FloatFormat} (policy : Policy) (plan : StoragePlan format)
        (h : firstOrderGenericSelected policy plan $operation = true) :
        (selectCertified policy ($automatic format plan)).run =
          @$generic format plan (Code plan) inferInstance := by
      cases plan <;> simp only [firstOrderGenericSelected] at h
      all_goals try contradiction
      all_goals
        unfold structuralSelected at h
        cases hr : Descriptor.Plan.structuralRoute? format $operation with
        | none =>
          simp [$automatic:ident, $candidates:ident, selectCertified, hr, $certified:ident]
        | some route =>
          simp only [hr, Bool.not_eq] at h
          $fallback:tactic)

end Plan

end FloatLib.Floats.Formats.BinaryInterchange.Configured
