/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Kernel.Loop -- shake: keep
public import FloatLib.Kernels.Execution.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.CastStatus
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Fast.Multiplication
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Fast.ShortAddition
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.IntegerStatus
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Lift
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.LiteralStatus
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.SqrtStatus
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.ToRat
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.TotalOrder
public import FloatLib.Tactic.FloatDecide -- shake: keep
public import FloatLib.Tactic.KernelInline
public import FloatLib.Tactic.KernelRefl

/-!
# The `specialize_directions` command

This frontend generates the declarations documented below. Its expansions are checked
in the importing mathematical module.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath
namespace Flat

open FloatLib.Numerics

set_option hygiene false in
/--
`specialize_directions op [args]` declares, for each of the six rounding directions `d`, the
operation `op.d`: the flat operation `op` with the direction fixed, which keeps the rounding code
of that direction only, and the rule `op.d_eq : op fmt .d args = op.d fmt args` that
`float_decide` rewrites with when the direction is a literal.
-/
macro defDoc:docComment ruleDoc:docComment "specialize_directions " op:ident
    " [" args:ident* "]" : command => do
  let directions := #[`nearest, `nearestAway, `towardZero, `up, `down, `away]
  let commands ← directions.mapM fun direction => do
    let name := Lean.mkIdent (op.getId ++ direction)
    let ruleName := Lean.mkIdent (op.getId ++ direction.appendAfter "_eq")
    let constructor := Lean.mkIdent
      (`FloatLib.Floats.Formats.BinaryInterchange.Model.IEEERoundingMode ++ direction)
    `($defDoc:docComment
      noncomputable def $name (fmt : FloatFormat) ($args* : Nat) : Nat :=
        kernel_inline% [$op] ($op fmt $constructor $args*)

      $ruleDoc:docComment
      @[kernel_optimize] theorem $ruleName (fmt : FloatFormat) ($args* : Nat) :
          $op fmt $constructor $args* = $name fmt $args* :=
        rewrite_rule kernel_refl%)
  return ⟨Lean.mkNullNode commands⟩

end Flat

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
