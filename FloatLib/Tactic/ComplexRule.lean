/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Tactic.Roundoff.Extension
public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Core
public import FloatLib.Floats.Formats.BinaryInterchange.Model.RealSemantics

/-!
# The `complex_rule` command

This frontend generates the declarations documented below. Its expansions are checked
in the importing mathematical module.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.ExecComplex

/--
`complex_rule name (binders) : value := re, im` declares the two observation equalities
`name_re : toReal value.re = toReal re` and `name_im : toReal value.im = toReal im`, both by
unfolding the complex operation, and registers them with `roundoff`.
-/
macro "complex_rule " name:ident binders:bracketedBinder* " : " value:term " := "
    re:term ", " im:term : command => do
  let reName := Lean.mkIdent (name.getId.appendAfter "_re")
  let imName := Lean.mkIdent (name.getId.appendAfter "_im")
  `(/-- The real component of this complex operation is the stated scalar expression. -/
    @[roundoff_rule] theorem $reName $binders* :
        Model.toReal ($value).re = Model.toReal $re := rfl
    /-- The imaginary component of this complex operation is the stated scalar expression. -/
    @[roundoff_rule] theorem $imName $binders* :
        Model.toReal ($value).im = Model.toReal $im := rfl)

end FloatLib.Floats.Formats.BinaryInterchange.ExecComplex
