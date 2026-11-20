/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Tactic.InlineShort
public import FloatLib.Tactic.KernelOptimize
public import FloatLib.Tactic.KernelRefl

/-!
# The `specialize_sums` command

This frontend generates the declarations documented below. Its expansions are checked
in the importing mathematical module.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath
namespace Flat

set_option hygiene false in
/--
`specialize_sums` declares, for each of the six rounding directions `d`, the carry path
`addCarry.d`, the same-sign path `addSame.d`, the addition `add.d` and the subtraction `sub.d`
with the direction fixed, each falling back to the paths of the same direction, and the rules
`add.d_eq` and `sub.d_eq` that `float_decide` rewrites with when the direction is a literal.
-/
macro (name := specializeSums) "specialize_sums" : command => do
  let directions := #[`nearest, `nearestAway, `towardZero, `up, `down, `away]
  let commands ← directions.mapM fun direction => do
    let carry := Lean.mkIdent (`addCarry ++ direction)
    let ordered := Lean.mkIdent (`addOrdered ++ direction)
    let same := Lean.mkIdent (`addSame ++ direction)
    let sum := Lean.mkIdent (`add ++ direction)
    let sumRule := Lean.mkIdent (`add ++ direction.appendAfter "_eq")
    let difference := Lean.mkIdent (`sub ++ direction)
    let differenceRule := Lean.mkIdent (`sub ++ direction.appendAfter "_eq")
    let constructor := Lean.mkIdent
      (`FloatLib.Floats.Formats.BinaryInterchange.Model.IEEERoundingMode ++ direction)
    `(/-- The carry path of addition on encodings in one rounding direction. -/
      noncomputable def $carry (fmt : FloatFormat) (a b : Nat) : Nat :=
        kernel_inline% [KernelPath.addCarryWith, KernelPath.roundUp]
          (KernelPath.addCarryWith fmt $constructor a b ($ordered fmt a b))

      /-- The same-sign path of addition on encodings in one rounding direction. -/
      noncomputable def $same (fmt : FloatFormat) (a b : Nat) : Nat :=
        kernel_inline% [KernelPath.addSameWith, KernelPath.roundUpShift]
          (KernelPath.addSameWith fmt $constructor a b ($carry fmt a b))

      /-- Addition on encodings in one rounding direction, with the code of that direction. -/
      noncomputable def $sum (fmt : FloatFormat) (a b : Nat) : Nat :=
        kernel_inline% [KernelPath.bySign]
          (KernelPath.bySign fmt a b ($same fmt a b) ($ordered fmt a b))

      /-- The flat addition in a literal direction is its specialization to that direction. -/
      @[kernel_optimize] theorem $sumRule (fmt : FloatFormat) (a b : Nat) :
          add fmt $constructor a b = $sum fmt a b :=
        rewrite_rule kernel_refl%

      /-- Subtraction on encodings in one rounding direction, with the code of that direction. -/
      noncomputable def $difference (fmt : FloatFormat) (a b : Nat) : Nat :=
        (fun negated =>
          kernel_inline% [KernelPath.bySign]
            (KernelPath.bySign fmt a negated ($same fmt a negated) ($ordered fmt a negated)))
          (inline_short% (KernelPath.neg fmt b))

      /-- The flat subtraction in a literal direction is its specialization to that direction. -/
      @[kernel_optimize] theorem $differenceRule (fmt : FloatFormat) (a b : Nat) :
          sub fmt $constructor a b = $difference fmt a b :=
        rewrite_rule kernel_refl%)
  return ⟨Lean.mkNullNode commands⟩

end Flat

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
