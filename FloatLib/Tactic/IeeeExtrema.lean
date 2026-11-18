/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Predicates
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.MagnitudeExtrema.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Runtime
public meta import Lean.Elab.Command
public meta import Lean.Elab.Term

/-!
# IeeeExtrema generators

The commands expand into declarations checked in the importing module.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Value

open FloatLib.Numerics
open FloatLib.Floats.Formats.BinaryInterchange.KernelPath

set_option hygiene false in
/--
`selection name := flat, model, h` declares the kernel selection `name` between two stored
values: the definition (the flat selection `flat` between the two encodings), `name_eq_lift` (it
is the model operation `model` carried through the family's conversions, where `h` proves that
`flat` computes the encodings of `model`) and the rule `toNat_name` (its encoding is `flat` on
the encodings of the operands).
-/
macro (name := selection) doc:docComment "selection " name:ident " := " flat:term ", "
    model:term ", " h:term :
    command => do
  let eqLift := Lean.mkIdent (name.getId.appendAfter "_eq_lift")
  let toNatName := Lean.mkIdent (Lean.Name.mkSimple ("toNat_" ++ name.getId.toString))
  `($doc:docComment
    def $name (x y : FloatLib.Floats.ExecFloat F) : FloatLib.Floats.ExecFloat F :=
      binary $flat $model $h x y
    /-- The kernel selection is the model operation carried through the family's conversions. -/
    theorem $eqLift (x y : FloatLib.Floats.ExecFloat F) :
        $name x y = NatView.liftBinary $model x y :=
      binary_eq _ _ _ x y
    /-- The encoding of the selection is the flat selection between the two encodings. -/
    @[kernel_optimize] theorem $toNatName (x y : FloatLib.Floats.ExecFloat F) :
        toNat ($name x y) = $flat (toNat x) (toNat y) :=
      toNat_binary _ _ _ x y)


end FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Value
