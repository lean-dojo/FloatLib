/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.Execution.Capability
public import FloatLib.Floats.Formats.Posit.Configured.Backend.FixedWords.Word16.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Backend.FixedWords.Word32.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Backend.FixedWords.Word64.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Plan.ByteDispatch.Proof

/-!
# The `plan_capability` command

This frontend generates the declarations documented below. Its expansions are checked
in the importing mathematical module.
-/

public meta section

namespace FloatLib.Floats.Formats.Posit.Configured.Plan

open FloatLib.Floats.ExecFloat
open FloatLib.Floats.ExecFloat.Backend

set_option hygiene false in
/--
`plan_capability Op op kind byte_eq "Name" for Spec.op := pair` declares
    `⟨op⟩CapabilityForPlan`: the
capability of one operation chosen by matching on the storage-plan constructor.

The byte plan keeps its policy-sensitive table portfolio, whose dispatch `ByteDispatch.⟨op⟩`
computes the reference operation by `byte_eq`. Every other built-in plan has one
first-order winner, and its capability is built from that operation's kernel alone: the word
kernels `Backend.Word16`, `Word32` and `Word64`, the capability `pair` of the two-word plan
(with `width_le` its width proof), and the dyadic kernel of the wide plan. The definition is
inlined on purpose, so a closed public width reduces the plan match at compile time and leaves
only the named carrier kernel in the generated hot path.
-/
macro "plan_capability " upper:ident lower:ident kind:ident byteEq:ident
    name:str " for " specification:ident " := "
    pair:term : command => do
  let op := upper.getId.toString
  let operation := Lean.mkIdent (`FloatLib.Floats.ExecFloat.Backend.Operation ++ lower.getId)
  let spec := specification
  let capabilityClass := Lean.mkIdent (`FloatLib.Floats.ExecFloat ++ upper.getId)
  let certified := Lean.mkIdent (`Certified ++ kind.getId)
  let word (width suffix : String) :=
    Lean.mkIdent ((`Backend ++ Lean.Name.mkSimple width) ++ lower.getId.appendAfter suffix)
  let dyadic (suffix : String) :=
    Lean.mkIdent (`Backend ++ Lean.Name.mkSimple s!"dyadic{op}{suffix}")
  `($(ExecFloat.generatedDoc s!"{name.getString} capability chosen by matching on the storage-plan \
      constructor."):docComment
    @[always_inline, instance_reducible]
    def $(Lean.mkIdent (lower.getId.appendAfter "CapabilityForPlan"))
        (format : Format) (plan : StoragePlan format)
        [planning : PolicyFor (Family format (Code plan) plan)] :
        $capabilityClass (Family format (Code plan) plan) :=
      match plan, planning with
      | .byte width_le, planning =>
          Capability.ofCandidates $operation
            $spec ($(Lean.mkIdent (lower.getId.appendAfter "ByteCandidates")) format width_le)
            ($(Lean.mkIdent (`ByteDispatch ++ lower.getId.appendAfter "Selected"))
              (ByteDispatch.select planning.policy format width_le $operation)
              width_le ($(Lean.mkIdent (`ByteTable ++ lower.getId.appendAfter "Table")) width_le))
            ($byteEq planning.policy width_le)
      | .word16 width_le, _planning =>
          Capability.ofCertified $operation <| $certified
            (storedNativeWordEstimate (.word16 width_le) $operation)
            $spec
            ($(word "Word16" "") width_le)
            ($(word "Word16" "_eq_spec") width_le)
      | .word32 width_le, _planning =>
          Capability.ofCertified $operation <| $certified
            (storedNativeWordEstimate (.word32 width_le) $operation)
            $spec
            ($(word "Word32" "") width_le)
            ($(word "Word32" "_eq_spec") width_le)
      | .word64 width_le, _planning =>
          Capability.ofCertified $operation <| $certified
            (storedNativeWordEstimate (.word64 width_le) $operation)
            $spec
            ($(word "Word64" "") width_le)
            ($(word "Word64" "_eq_spec") width_le)
      | .pair width_le, _planning => $pair
      | .wide, _planning =>
          Capability.ofCertified $operation <| $certified
            (dyadicEstimate (.wide : StoragePlan format) $operation)
            $spec $(dyadic "") $(dyadic "_eq_spec"))

end FloatLib.Floats.Formats.Posit.Configured.Plan
