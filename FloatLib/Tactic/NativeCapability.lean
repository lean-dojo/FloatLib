/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.Execution.Capability
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Direct.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.NativeCandidates
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Type

/-!
# The `native_capability` command

This frontend generates the declarations documented below. Its expansions are checked
in the importing mathematical module.
-/

public meta section

namespace FloatLib.Floats
namespace ExecFloat.Binary

open FloatLib.Floats.Formats.BinaryInterchange

set_option hygiene false in
/--
`native_capability bits (e f) Op op := execute, proof` declares the static capability of one
operation of binary32 or binary64, attached to the public family `Binary.Family e f`. It names
the fixed-format certificate `Plan.software⟨Op⟩⟨bits⟩Certified`, which the planner selects among
`Plan.binary⟨bits⟩⟨Op⟩Candidates` under every policy
(`Plan.selectCertified_binary⟨bits⟩⟨Op⟩Candidates`), and runs `execute`, which `proof` shows to
be that certificate's kernel.

The instances are attached to the parameterized families and not to a storage-plan constructor:
Lean's typeclass index keeps `Binary.Family 8 23` and `Binary.Family 11 52` but does not always
unfold their computed `forKnownWidth` plans during instance search.
-/
macro "native_capability " bits:num " (" e:num f:num ") " upper:ident lower:ident " := "
    execute:term ", " proof:term : command => do
  let op := upper.getId.toString
  let n := bits.getNat
  let plan (text : String) := Lean.mkIdent (`Configured.Plan ++ Lean.Name.mkSimple text)
  let operation := Lean.mkIdent (`FloatLib.Floats.ExecFloat.Backend.Operation ++ lower.getId)
  let spec := Lean.mkIdent (`Configured.Spec ++ lower.getId)
  let instanceName := Lean.mkIdent (Lean.Name.mkSimple s!"binary{n}{op}Capability")
  let text := s!"The static `{lower.getId}` capability of binary{n}: the kernel of \
    `Plan.software{op}{n}Certified`, which the planner selects under every policy."
  `($(ExecFloat.generatedDoc text):docComment
    @[always_inline] instance (priority := 400) $instanceName
        {planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor (Family $e $f)} :
        FloatLib.Floats.ExecFloat.Capability.Static (F := Family $e $f) $operation
          ($spec : FloatLib.Floats.ExecFloat.OperationSignature (Family $e $f) $operation) where
      spec_eq := rfl
      capability :=
        { spec := $spec
          candidates := $(plan s!"binary{n}{op}Candidates") _
          implementation := $(plan s!"software{op}{n}Certified") _
          implementation_is_selected :=
            ($(plan s!"selectCertified_binary{n}{op}Candidates") planning.policy _).symm
          execute := $execute
          execute_eq_implementation := $proof })

end ExecFloat.Binary

end FloatLib.Floats
