/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.Execution.Proof
public import FloatLib.Tactic.KernelOptimize

/-!
# The `direct_form` command

This frontend generates the declarations documented below. Its expansions are checked
in the importing mathematical module.
-/

public meta section

namespace FloatLib.Floats.ExecFloat.KernelPath

open FloatLib.Numerics

set_option hygiene false in
/--
`direct_form [Class] operation spec "name"` declares the instance that a direct reference
operation is its own kernel form: `spec`, the reference operation of `Class`.
-/
macro "direct_form " "[" cls:ident "] " operation:term:max spec:ident name:str : command =>
  `($(ExecFloat.generatedDoc s!"The kernel form of a direct reference {name.getString} is the \
        reference \
      {name.getString}."):docComment
    -- The two instance arguments are the conditions under which instance search takes the instance.
    @[nolint unusedArguments]
    instance [$cls F] [DirectReference F $operation] : KernelForm F $operation $spec := ⟨rfl⟩)

end FloatLib.Floats.ExecFloat.KernelPath
