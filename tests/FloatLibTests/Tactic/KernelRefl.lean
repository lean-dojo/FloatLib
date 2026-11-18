/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Kernel.Exact
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Value
public import FloatLib.Tactic.KernelInline
public import FloatLib.Tactic.KernelNotation
public import FloatLib.Tactic.KernelPrepare
public import FloatLib.Tactic.KernelProj
public import FloatLib.Tactic.KernelRefl

/-!
# Tests of the elaborators that kernel operations are written with

A flattened sum reduces to its staged form (`kernel_inline%`, `kernel_refl%`), and false
equations and non-equations are rejected. A primitive projection is its projection function
(`kernel_proj%`), the kernel's function forms become notation (`kernel_notation`), the tagged
rules prepare a function once (`kernel_prepare%`), and `kernel_operation` has declared each
operation of the binary kernel path with its three theorems.
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.KernelPath

/-- A sum written with a helper. -/
def stagedSum (a b : Nat) : Nat :=
  Nat.add (Nat.mul 2 a) b

/-- The same sum with the helper unfolded. -/
noncomputable def flatSum (a b : Nat) : Nat :=
  kernel_inline% [stagedSum] (stagedSum a b)

/-- `kernel_refl%` proves that a flat form is its staged form, by the kernel's check alone. -/
example (a b : Nat) : flatSum a b = stagedSum a b :=
  kernel_refl%

/--
error: (kernel) application type mismatch
  id (Eq.refl 2)
argument has type
  2 = 2
but function has type
  2 = 3 → 2 = 3
-/
#guard_msgs in
/-- An equation that does not hold by reduction is refused when the declaration is added. -/
example : (2 : Nat) = 3 :=
  kernel_refl%

/--
error: `kernel_refl%` proves an equation, and the expected type is
  True
-/
#guard_msgs in
/-- A statement that is not an equation is refused by the elaborator. -/
example : True :=
  kernel_refl%

/-! ## `kernel_proj%`, `kernel_notation`, `kernel_prepare%` and `kernel_operation` -/

/-- Field zero of a subtype value, as a primitive projection, is its `val`. -/
example (x : { n : Nat // n < 8 }) : kernel_proj% x 0 = x.val := rfl

/-- `kernel_notation` writes `Nat.add` and `Nat.mul` as `+` and `*`, on which `omega` works. -/
example (a b : Nat) : stagedSum a b = b + a + a := by
  unfold stagedSum
  kernel_notation
  omega

/-- The tagged rules applied once to a function, stored with the equality to the function. -/
noncomputable def preparedProduct : { run : Int → Int → Int // run = fun a b => a * b + a } :=
  kernel_prepare% (fun (a b : Int) => a * b + a)

/-- The prepared function computes what the original computes. -/
example : preparedProduct.val 3 4 = 15 := by
  rw [preparedProduct.property]
  decide

/-! `kernel_operation` declares the operation, its equality with the lifted reference, the
encoding of its result and the rule for the public operation. -/

open FloatLib.Floats.Formats.BinaryInterchange.KernelPath in
#guard_msgs (drop info) in
#check @Value.add

open FloatLib.Floats.Formats.BinaryInterchange.KernelPath in
#guard_msgs (drop info) in
#check @Value.add_eq_lift

open FloatLib.Floats.Formats.BinaryInterchange.KernelPath in
#guard_msgs (drop info) in
#check @Value.toNat_add

open FloatLib.Floats.Formats.BinaryInterchange.KernelPath in
#guard_msgs (drop info) in
#check @Value.add_eq

end FloatLibTests.Conformance.BinaryInterchange.KernelPath
