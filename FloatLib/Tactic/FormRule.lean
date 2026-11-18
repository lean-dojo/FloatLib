/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.Execution.Proof
public import FloatLib.Tactic.KernelOptimize

/-!
# The `form_rule` command

This frontend generates the declarations documented below. Its expansions are checked
in the importing mathematical module.
-/

public meta section

namespace FloatLib.Floats.ExecFloat.KernelPath

open FloatLib.Numerics

set_option hygiene false in
/--
`form_rule rule [Class] operation (arguments) : lhs := lemma, "name"` declares `rule`, tagged
`@[kernel_optimize]`: in a format with a kernel form for `operation`, the public operation `lhs`
is that form at the same arguments. `lemma` states that `lhs` is the reference operation.
-/
macro "form_rule " rule:ident " [" cls:ident "] " operation:term:max " (" args:ident* ")"
    " : " lhs:term " := " proofName:ident ", " name:str : command =>
  let text := s!"{name.getString} in a format with a kernel form is that form."
  `($(ExecFloat.generatedDoc text):docComment
    @[kernel_optimize] theorem $rule [$cls F] {form : OperationSignature F $operation}
        [KernelForm F $operation form] ($args* : FloatLib.Floats.ExecFloat F) :
        $lhs = form $args* :=
      ($proofName $args*).trans (congrArg (fun f : OperationSignature F $operation ↦ f $args*)
        (KernelForm.spec_eq (F := F) (operation := $operation) (form := form))))

end FloatLib.Floats.ExecFloat.KernelPath
