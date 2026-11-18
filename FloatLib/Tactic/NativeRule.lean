/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Tactic.Roundoff.Extension
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Real

/-!
# The `native_rule` command

A native carrier, such as Lean's `Float32`, is read by `roundoff` through its import into a
configured format, such as `ExecFloat.Binary.ofFloat32` into binary32. For each binary operation
the library proves that the import of the native result is the configured operation on the
imports when the imports are finite. `native_rule` states that agreement as the two rules that
`roundoff` reads: the real value of the import, and its finiteness.
-/

public meta section

namespace FloatLib.Floats.ExecFloat.Binary

/--
`native_rule name : conversion carrier into target, op := agreement by finiteness` declares, for the
binary operation `op` of the native carrier `carrier` that `conversion` imports into the
configured type `target`, the two rules

* `toReal_name : isFinite (conversion x) = true → isFinite (conversion y) = true →
  toReal (conversion (op x y)) = toReal (op (conversion x) (conversion y))` and
* `isFinite_name`, which concludes `isFinite (conversion (op x y)) = true` from the same premises
  and the finiteness of `op (conversion x) (conversion y)`,

and registers both with `roundoff`. `agreement x y hx hy` proves
`conversion (op x y) = op (conversion x) (conversion y)` from the native finiteness tests of `x`
and `y`, and `finiteness x` equates the finiteness of `conversion x` with that test.
-/
macro "native_rule " name:ident " : " conversion:ident carrier:ident " into " target:ident ", "
    op:ident " := " agreement:ident " by " finiteness:ident : command => do
  let value := Lean.mkIdent (Lean.Name.mkSimple s!"toReal_{name.getId}")
  let finite := Lean.mkIdent (Lean.Name.mkSimple s!"isFinite_{name.getId}")
  `(/-- The import of this native operation on values with finite imports has the real value of
    the configured operation on the imports. -/
    @[roundoff_rule] theorem $value {x y : $carrier}
        (hx : isFinite ($conversion x : $target) = true)
        (hy : isFinite ($conversion y : $target) = true) :
        toReal ($conversion ($op x y) : $target) =
          toReal ($op ($conversion x : $target) ($conversion y : $target)) :=
      congrArg toReal
        ($agreement x y (($finiteness x).symm.trans hx) (($finiteness y).symm.trans hy))
    /-- The import of this native operation on values with finite imports is finite when the
    configured operation on the imports is. -/
    @[roundoff_rule] theorem $finite {x y : $carrier}
        (hx : isFinite ($conversion x : $target) = true)
        (hy : isFinite ($conversion y : $target) = true)
        (hresult : isFinite ($op ($conversion x : $target) ($conversion y : $target)) = true) :
        isFinite ($conversion ($op x y) : $target) = true :=
      (congrArg isFinite
        ($agreement x y (($finiteness x).symm.trans hx) (($finiteness y).symm.trans hy))).trans
          hresult)

end FloatLib.Floats.ExecFloat.Binary
