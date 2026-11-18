/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Kernel.Exact
public import FloatLib.Floats.ExecFloat.Backends.Kernel.Plumbing
public import FloatLib.Tactic.KernelTwin

/-!
# Checks of the kernel plumbing rules and of `kernel_twin`

The first sections check the list and option functions of `FloatLib.Numerics.Kernel.Seq` on
values worked out by hand, and each tagged rule of `Backends.Kernel.Plumbing` by rewriting a
statement with it and letting the kernel decide the result.

The last sections run `kernel_twin` on a small program written the way a checker is written: a
table filled by pushes, lookups, options and integer arithmetic. They check that the twin exists
with its equation, that the equation has no axioms beyond the standard three, that the kernel
evaluates the twin for a statement about the original, that a wrong statement is refused, that a
definition without a rewritable operation gets no twin, and the two errors of the command.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Numerics.KernelTwin

open FloatLib.Numerics.Kernel

/-! ### Lists and options -/

example : Seq.len ([] : List Nat) = 0 ∧ Seq.len [5, 6, 7] = 3 := by decide +kernel
example : Seq.nth? [5, 6, 7] 0 = some 5 ∧ Seq.nth? [5, 6, 7] 2 = some 7 ∧
    Seq.nth? [5, 6, 7] 3 = none ∧ Seq.nth? ([] : List Nat) 0 = none := by decide +kernel
example : Seq.getD [5, 6, 7] 0 9 = 5 ∧ Seq.getD [5, 6, 7] 2 9 = 7 ∧ Seq.getD [5, 6, 7] 3 9 = 9 ∧
    Seq.getD ([] : List Nat) 0 9 = 9 := by decide +kernel
example : Seq.snoc [5, 6] 7 = [5, 6, 7] ∧ Seq.snoc ([] : List Nat) 7 = [7] ∧
    Seq.snoc (Seq.snoc (Seq.snoc [] 1) 2) 3 = [1, 2, 3] := by decide +kernel
example : Seq.tabulate 4 (fun i => Nat.mul i.val i.val) = [0, 1, 4, 9] ∧
    Seq.tabulate 0 (fun i => i.val) = [] := by decide +kernel
example : Seq.mapIdx Nat.mul [5, 6, 7] = [0, 6, 14] ∧ Seq.mapIdx Nat.mul [] = [] := by
  decide +kernel
example : Seq.map Nat.succ [5, 6, 7] = [6, 7, 8] ∧ Seq.map Nat.succ [] = [] ∧
    Seq.zipWith Nat.mul [1, 2, 3] [4, 5, 6] = [4, 10, 18] ∧
    Seq.zipWith Nat.mul [1, 2, 3] [4, 5] = [4, 10] ∧ Seq.zipWith Nat.mul [1] [4, 5] = [4] ∧
    Seq.reverse [5, 6, 7] = [7, 6, 5] ∧ Seq.reverse ([] : List Nat) = [] ∧
    Seq.sum [5, 6, 7] = 18 ∧ Seq.sum [] = 0 := by decide +kernel
example : Seq.all (Nat.ble 5) [5, 6, 7] = true ∧ Seq.all (Nat.ble 6) [5, 6, 7] = false ∧
    Seq.all (Nat.ble 6) [] = true := by decide +kernel
-- `Seq.all₃` holds when the lengths agree and the predicate holds for every triple
example : Seq.all₃ (fun a b c => Nat.beq (Nat.add a b) c) [1, 2, 3] [4, 5, 6] [5, 7, 9] = true ∧
    Seq.all₃ (fun a b c => Nat.beq (Nat.add a b) c) [1, 2, 3] [4, 5, 6] [5, 7, 8] = false ∧
    Seq.all₃ (fun a b c => Nat.beq (Nat.add a b) c) [1, 2] [4, 5, 6] [5, 7, 9] = false ∧
    Seq.all₃ (fun a b c => Nat.beq (Nat.add a b) c) [1, 2, 3] [4, 5] [5, 7, 9] = false ∧
    Seq.all₃ (fun a b c => Nat.beq (Nat.add a b) c) [1, 2, 3] [4, 5, 6] [5, 7] = false ∧
    Seq.all₃ (fun a b c => Nat.beq (Nat.add a b) c) [] [] [] = true := by decide +kernel
example : Opt.bind (some 3) (fun x => some (Nat.succ x)) = some 4 ∧
    Opt.bind (none : Option Nat) (fun x => some (Nat.succ x)) = none ∧
    Opt.bind (some 3) (fun _ => (none : Option Nat)) = none ∧
    Opt.map Nat.succ (some 3) = some 4 ∧ Opt.map Nat.succ none = none ∧
    Opt.join (some (some 3)) = some 3 ∧ Opt.join (some (none : Option Nat)) = none ∧
    Opt.join (none : Option (Option Nat)) = none := by decide +kernel

/-! ### Each rule rewrites its operation, and the kernel decides the result -/

example : [5, 6, 7].length = 3 := by
  simp only [kernel_optimize]
  decide +kernel
example : (#[5, 6, 7].push 8).size = 4 := by
  simp only [kernel_optimize]
  decide +kernel
example : (#[5, 6, 7].push 8)[3]? = some 8 ∧ [5, 6, 7][1]? = some 6 ∧ #[5, 6, 7][3]? = none := by
  simp only [kernel_optimize]
  decide +kernel
example : (Array.ofFn (n := 50) fun i => i.val * i.val)[49]? = some 2401 := by
  simp only [kernel_optimize]
  decide +kernel
example : ((some 3).bind fun x => (some (x + 1)).map (· * 2)) = some 8 ∧
    (some (some 3)).join = some 3 := by
  simp only [kernel_optimize]
  decide +kernel
example : Nat.sqrt (10 ^ 40 + 1) = 10 ^ 20 := by
  simp only [kernel_optimize]
  decide +kernel
example : ([5, 6, 7].map (· + 1)).reverse = [8, 7, 6] ∧
    [5, 6, 7].mapIdx (· * ·) = [0, 6, 14] ∧ [5, 6, 7].getD 1 0 = 6 ∧ [5, 6, 7].getD 3 0 = 0 ∧
    List.zipWith (· * ·) [1, 2, 3] [4, 5, 6] = [4, 10, 18] ∧
    [5, 6, 7].all (· < 8) = true ∧ [5, 6, 7].sum = 18 := by
  simp only [kernel_optimize]
  decide +kernel

example : (#[5, 6, 7].map (· + 1)).reverse = #[8, 7, 6] ∧
    #[5, 6, 7].mapIdx (· * ·) = #[0, 6, 14] ∧
    #[5, 6, 7].getD 1 0 = 6 ∧ #[5, 6, 7].getD 3 0 = 0 ∧
    (#[1, 2, 3].zipWith (· * ·) #[4, 5]) = #[4, 10] ∧
    #[5, 6, 7].all (· < 8) = true ∧ (#[] : Array Nat).all (· < 8) = true ∧
    #[5, 6, 7].all (· < 7) 0 2 = true ∧
    #[5, 6, 7].all (· < 7) 1 8 = false ∧
    #[5, 6, 7].all (· < 0) 2 1 = true := by
  simp only [kernel_optimize]
  decide +kernel

/-! ### A program and its twin -/

/-- A table filled by pushes: the entry `n` is `n` plus the entry `n / 2` (the entry `0` is `0`),
so the entry `n` is the sum of `n`, `n / 2`, `n / 4`, … -/
def fill : Nat → Array Int → Array Int
  | 0, table => table
  | k + 1, table => fill k (table.push (table.size + (table[table.size / 2]?).getD 0))

/-- The entry `n` of the table of `n + 1` entries. -/
def entry (n : Nat) : Option Int := (fill (n + 1) #[])[n]?

/-- Whether the entry `n` exists and its square is `expected` plus the entry. -/
def check (n : Nat) (expected : Int) : Bool :=
  ((entry n).bind fun x => if x * x - x = expected then some true else none) == some true

/-- A definition that no rule changes. -/
def idle (n : Nat) : Nat := n + 1

/-- A composed array traversal, including its empty and out-of-bounds behavior. -/
def arrayProgram (a b : Array Nat) (i d : Nat) : Nat :=
  ((a.zipWith Nat.mul b).mapIdx Nat.add).reverse.getD i d

namespace Arrays

#guard_msgs (drop info) in
kernel_twin arrayProgram

/-- The generated body consists entirely of the shared list operations on the array entries. -/
example (a b : Array Nat) (i d : Nat) :
    FloatLibTests.Conformance.Numerics.KernelTwin.arrayProgram a b i d =
      Seq.getD (Seq.reverse (Seq.mapIdx Nat.add (Seq.zipWith Nat.mul a.toList b.toList))) i d :=
  rfl

end Arrays

namespace Twin

-- the count in the report includes the auxiliary definitions of the recursion
#guard_msgs (drop info) in
kernel_twin check within FloatLibTests

end Twin

/-- The equation of the twin, between the functions. -/
theorem check_eq : check = Twin.FloatLibTests.Conformance.Numerics.KernelTwin.check :=
  Twin.FloatLibTests.Conformance.Numerics.KernelTwin.check.twin_eq

/-- Every definition on the way has its own equation. -/
example : fill = Twin.FloatLibTests.Conformance.Numerics.KernelTwin.fill ∧
    entry = Twin.FloatLibTests.Conformance.Numerics.KernelTwin.entry :=
  ⟨Twin.FloatLibTests.Conformance.Numerics.KernelTwin.fill.twin_eq,
    Twin.FloatLibTests.Conformance.Numerics.KernelTwin.entry.twin_eq⟩

/--
info: 'FloatLibTests.Conformance.Numerics.KernelTwin.check_eq' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs (info, whitespace := lax) in
#print axioms check_eq

/-- A statement about the original, proved by evaluating the twin: the entry `100` is
`100 + 50 + 25 + 12 + 6 + 3 + 1 = 197`, and `197² - 197 = 38612`. -/
theorem check_100 : check 100 38612 = true := by
  rw [Twin.FloatLibTests.Conformance.Numerics.KernelTwin.check.twin_eq]
  decide +kernel

/-- The twin evaluates a wrong value to `false`: the negation is what is proved. -/
example : ¬ (check 100 38613 = true) := by
  rw [Twin.FloatLibTests.Conformance.Numerics.KernelTwin.check.twin_eq]
  decide +kernel

/-! ### Reversed and erased registrations -/

/-- A core list operation whose registered equality points back from its kernel form. -/
def length (l : List Nat) : Nat := l.length

namespace Reverse

#guard_msgs (drop info) in
kernel_twin length

/-- The generated body uses the reversed registration, without further simplification. -/
example (l : List Nat) :
    FloatLibTests.Conformance.Numerics.KernelTwin.length l = Seq.len l := rfl

end Reverse

section
attribute [-kernel_optimize] Seq.len_eq

namespace Erased

/-- info: kernel_twin: definitions examined: 1, rewritten: 0 -/
#guard_msgs in
kernel_twin length within FloatLibTests

end Erased
end

/-! ### What the command leaves alone, and its errors -/

namespace Twin

/-- info: kernel_twin: definitions examined: 1, rewritten: 0 -/
#guard_msgs in
kernel_twin idle within FloatLibTests

end Twin

/-- error: kernel_twin: `Nat.add` is not a definition in a module under [FloatLibTests] -/
#guard_msgs in
kernel_twin Nat.add within FloatLibTests

end FloatLibTests.Conformance.Numerics.KernelTwin

/-- error: kernel_twin: open a namespace first; the twins are declared in it -/
#guard_msgs in
kernel_twin FloatLibTests.Conformance.Numerics.KernelTwin.check within FloatLibTests
