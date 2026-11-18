/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import Lean.Elab.Command

/-!
# Posit kernel-form instances

The command generates one proved instance from a general backend equality.
-/

public meta section

namespace FloatLib.Floats.Formats.Posit.Configured

set_option hygiene false in
/-- Generate a kernel form from a descriptor-parametric operation equality. -/
macro (name := positForm) doc:docComment "posit_form " operation:term:max " := " form:ident
    " for " spec:ident " by " equality:ident " (" args:ident* ")" : command =>
  `($doc:docComment
    instance [capability : Capability (Family format code plan) $operation]
        [Capability.HasSpec capability (@$spec format plan code inferInstance)] :
        KernelPath.KernelForm (Family format code plan) $operation $form where
      spec_eq := (Capability.HasSpec.spec_eq (cap := capability)).trans <| by
        funext $args*
        exact ($equality $args*).symm)

end FloatLib.Floats.Formats.Posit.Configured
