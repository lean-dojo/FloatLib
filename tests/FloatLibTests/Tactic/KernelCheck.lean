/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.KernelPath
public import FloatLib.Numerics.Packed.Basic
public import FloatLib.Tactic.FloatDecide
public import FloatLib.Tactic.Interval
meta import FloatLib.Tactic.KernelCheck

/-!
# Statements checked by `KernelCheck.prove`

`float_decide` is `KernelCheck.prove` on the main goal, and `interval` checks its closed
conditions with it. Any caller may hand it a statement that is not a goal, and these tests check
what such a caller relies on: a tagged rule rewrites the statement before the kernel decides it,
a statement that no rule rewrites is decided as written, a false or open statement is refused
with the messages of `float_decide` under the caller's tactic name, a statement over all pairs of
a small index type becomes one loop, and a budget that runs out gives back the kernel's own error.
`mentionsStoredValue` is false on statements about numbers, packed rows included, and true on
statements about stored values.
-/

@[expose] public section

namespace FloatLibTests.Tactic.KernelCheck

open Lean Meta Elab Term
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange.KernelPath
open FloatLib.Tactic.KernelCheck

/-! ## A rule on a statement that is not a goal

`prove` gives a proof of the statement it was handed, and the proof goes through the tagged rule
`countUp_eq`. `float_decide` proves the same statement as a goal.
-/

/-- `n`, built one successor at a time, so that the kernel unfolds it `n` times. -/
def countUp : Nat → Nat
  | 0 => 0
  | n + 1 => countUp n + 1

/-- The kernel implementation of `countUp`: the number itself. -/
@[kernel_optimize (cost := 1)]
theorem countUp_eq (n : Nat) : countUp n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [countUp, ih]

/-- info: (true, true) -/
#guard_msgs in
#eval show TermElabM (Bool × Bool) from do
  let statement ← elabTermAndSynthesize (← `(countUp 1000000 + 1 = 1000001)) none
  let proof ← prove statement
  return (← isDefEq (← inferType proof) statement, proof.getUsedConstants.contains ``countUp_eq)

/-- The statement handed to `prove` above, as a goal of `float_decide`. -/
theorem countUp_million : countUp 1000000 + 1 = 1000001 := by float_decide

/-- info: 'FloatLibTests.Tactic.KernelCheck.countUp_million' depends on axioms: [propext] -/
#guard_msgs in
#print axioms countUp_million

example : (Nat.rec (motive := fun n => Fin (n + 1)) (0 : Fin 1) (fun _ v => v.succ) 3 : Fin 4).val
    + countUp 1000000 = 1000003 := by float_decide

/-! ## A statement that no rule rewrites

It is decided as written, raw literals included. Even if the caller has already stored a proof
of the same statement, the checker returns its own decision proof.
-/

/-- info: true -/
#guard_msgs in
#eval show MetaM Bool from do
  let statement ← mkEq (mkApp2 (mkConst ``Nat.ble) (mkRawNatLit 5) (mkRawNatLit 7))
    (mkConst ``Bool.true)
  return (← prove statement).isConst

/-- A true inequality proved with choice, to distinguish it from the kernel's decision. -/
private theorem withChoice : 23 < 41 := Classical.choice ⟨by decide⟩

/-- The same inequality, decided independently of the stored proof. -/
theorem independentlyChecked : 23 < 41 := by
  run_tac
    let goal ← Tactic.getMainGoal
    let statement ← goal.getType
    let cached ← mkAuxLemma [] statement (mkConst ``withChoice)
    unless (← collectAxioms cached).contains ``Classical.choice do
      throwError "the stored proof should depend on choice"
    goal.assign (← prove statement (maxHeartbeats := some 100))

/-- info: 'FloatLibTests.Tactic.KernelCheck.independentlyChecked' does not depend on any axioms -/
#guard_msgs in
#print axioms independentlyChecked

section

open FloatLib.Numerics.Interval

/-- With no subdivisions, the check passes exactly when the leaf passes. Putting `true` on the
left of the leaf test makes the rewrite visible in the proof. -/
@[local kernel_optimize (cost := 1)]
theorem checkZero_leaf {α : Type*} (e : FloatLib.Numerics.Interval.Expr) (B : Backend α)
    (relation : Relation) (box : Box) :
    (e.checkZero B relation box 0 = true) = (true = e.checkBoxZero B relation box) :=
  propext eq_comm

/-- `interval` passes its closed check through the tagged rule. -/
theorem intervalChecked (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : x + 1 < 3 := by interval

/-- info: true -/
#guard_msgs in
#eval show MetaM Bool from do
  let proof := (← getConstInfo ``intervalChecked).value! (allowOpaque := true)
  proof.getUsedConstants.anyM fun name => do
    let value := (← getConstInfo name).value? (allowOpaque := true)
    return value.any (·.getUsedConstants.contains ``checkZero_leaf)

end

/-! ## Refusals

A false statement and a statement with a local variable are refused with the messages of
`float_decide`, which name the tactic of the caller.
-/

/--
error: float_decide: the statement is false:
  1.5 + 2.25 = 3.5
-/
#guard_msgs in
#eval show TermElabM Unit from do
  discard <| prove (← elabTermAndSynthesize (← `((1.5 : Binary64) + 2.25 = 3.5)) none)

/--
error: float_decide: the statement mentions local variables or hypotheses, so it is not closed:
  x + 0 = x
-/
#guard_msgs in
#eval show TermElabM Unit from do
  withLocalDeclD `x (← elabTermAndSynthesize (← `(Binary32)) none) fun _ => do
    discard <| prove (← elabTermAndSynthesize (← `($(mkIdent `x) + 0 = $(mkIdent `x))) none)

/--
error: myCheck: the statement is false:
  1 < 0
-/
#guard_msgs in
#eval show TermElabM Unit from do
  discard <| prove (← elabTermAndSynthesize (← `((1 : Binary32) < 0)) none) (tactic := `myCheck)

/-! ## All pairs of a small index type

A statement over all pairs of `Fin 16` that uses the indices only as their values is checked as
one loop of `forall_fin_pairs` over the 256 pairs. One that adds the indices in `Fin 4` is
decided as it stands.
-/

/-- info: (true, false) -/
#guard_msgs in
#eval show TermElabM (Bool × Bool) from do
  let pairs ← prove (← elabTermAndSynthesize
    (← `(∀ a b : Fin 16, a.val * b.val = b.val * a.val)) none)
  let direct ← prove (← elabTermAndSynthesize (← `(∀ a b : Fin 4, a + b = b + a)) none)
  let loop := ``FloatLib.Floats.ExecFloat.KernelPath.forall_fin_pairs
  return (pairs.getUsedConstants.contains loop, direct.getUsedConstants.contains loop)

/-! ## Budgets

The binary64 expression below takes the kernel more than one thousand heartbeats. With that
budget `prove` fails with the kernel's own error, which a caller can tell apart from a false
statement, and without a budget it proves the statement.
-/

/-- error: (kernel) deterministic timeout -/
#guard_msgs in
#eval show TermElabM Unit from do
  let statement ← elabTermAndSynthesize
    (← `(toNat ((1.5 : Binary64) * 2.25 - 1 / 3) = 4614031643233310037)) none
  discard <| prove statement (maxHeartbeats := some 1)

/-- info: true -/
#guard_msgs in
#eval show TermElabM Bool from do
  let statement ← elabTermAndSynthesize
    (← `(toNat ((1.5 : Binary64) * 2.25 - 1 / 3) = 4614031643233310037)) none
  isDefEq (← inferType (← prove statement)) statement

/-! ## Statements about stored values

`mentionsStoredValue` is false on a statement about natural numbers, integers and rationals, on
the packed row of `[1, -2, 3]` in lanes of eight bits, and on a definition over natural numbers.
It is true on a binary32 equation, on a definition that names one stored value and on an
operation of the binary family over all indices of `Fin 4`.
-/

/-- One tenth in binary32. -/
def tenth : Binary32 := 0.1

/-- info: [false, false, false, true, true, true] -/
#guard_msgs in
#eval show TermElabM (List Bool) from do
  let statements := [
    ← `((2 : Nat) + 2 = 4 ∧ (1 / 3 : Int) = 0 ∧ (1 / 3 : Rat) + 1 / 3 = 2 / 3),
    ← `(FloatLib.Numerics.Packed.entries 8 3 8617601 = [1, -2, 3]),
    ← `(countUp 3 = 3),
    ← `((0.1 : Binary32) + 0.2 = 0.3),
    ← `(toNat tenth = 0x3dcccccd),
    ← `(∀ a : Fin 4, toNat (ofNat a : Binary32) = a)]
  statements.mapM fun statement => do
    mentionsStoredValue (← elabTermAndSynthesize statement none)

end FloatLibTests.Tactic.KernelCheck
