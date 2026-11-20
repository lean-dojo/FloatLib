/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.RootProof
public import FloatLib.Numerics.Kernel.SeqProof
public import FloatLib.Tactic.KernelOptimize

/-!
# Kernel rules for lists, arrays, options, branches and the square root

A program that is evaluated by Lean's kernel pays for its plumbing as well as for its arithmetic.
The existing equality theorems are registered in reverse; the array bridge theorems here
state a core Lean function as an operation of `FloatLib.Numerics.Kernel.Seq`. The registered
costs guide the optimizer; they are estimates rather than bounds on evaluation time.

The rules cover length, lookup, map, indexed map, zip, all, reverse, natural-number sum,
option bind/map/join and `Nat.sqrt`. Arrays use the same list operations on their entries,
including maps, zips and reversal.

A branch `if a = b then x else y` on natural numbers costs the kernel about seventeen
microseconds, because it unfolds the `Decidable` instance; the recursor of `Bool` on `Nat.beq`
costs it under two. `ite_nat_eq`, `ite_nat_le`, `ite_nat_lt` and `ite_bool` state an `if` on an
equation or an order of natural numbers, or on a Boolean, as that recursor (an `if` on a
negation is turned around by core's `ite_not`), and `decide_nat_eq`, `decide_nat_le` and
`decide_nat_lt` state the decision as `Nat.beq` or `Nat.ble`. An `if` between two decidable
propositions is first stated through their decisions (`ite_prop`), so that it stays decidable.
An `if` on a Boolean literal is its branch (core's `Bool.false_and`, `Bool.true_and`,
`Bool.false_eq_true`, `ite_true` and `ite_false`), `bool_bne` and `bool_beq` compare two
Booleans by recursors, and `toNat_ofNat` reads the word of a natural number back as a remainder.
`Seq.tabulate` constructs a table in one pass. A push still copies the array's list, so repeated
pushes still require quadratic copying. The rules change operations, not the data structure.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.KernelPath.Plumbing

open FloatLib.Numerics.Kernel

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

attribute [kernel_optimize ← (cost := 1400)] Seq.len_eq

/-- `Array.size` is the kernel function `Seq.len` of the list of entries. -/
@[kernel_optimize (cost := 1400)]
theorem array_size (a : Array α) : a.size = Seq.len a.toList := (Seq.len_eq a.toList).symm

attribute [kernel_optimize ← (cost := 1300)] Seq.nth?_eq

/-- A lookup `a[i]?` in an array is the kernel function `Seq.nth?` on the list of entries. -/
@[kernel_optimize (cost := 1300)]
theorem array_getElem? (a : Array α) (i : Nat) : a[i]? = Seq.nth? a.toList i := by
  rw [Seq.nth?_eq, Array.getElem?_toList]

attribute [kernel_optimize ← (cost := 1200)] Seq.getD_eq

/-- A defaulted array lookup is `Seq.getD` on its entries, including out-of-bounds indices. -/
@[kernel_optimize]
theorem array_getD (a : Array α) (i : Nat) (d : α) :
    a.getD i d = Seq.getD a.toList i d := by
  rw [Seq.getD_eq, List.getD_eq_getElem?_getD, Array.getElem?_toList,
    Array.getD_eq_getD_getElem?]

/-- `Array.push` is the kernel function `Seq.snoc` on the list of entries. -/
@[kernel_optimize (cost := 900)]
theorem array_push (a : Array α) (x : α) : a.push x = ⟨Seq.snoc a.toList x⟩ := by
  apply Array.ext'
  rw [Array.toList_push, Seq.snoc_eq]

/-- `Array.ofFn` is the kernel function `Seq.tabulate`, which builds the entries in one pass. -/
@[kernel_optimize (cost := 1700)]
theorem array_ofFn {n : Nat} (f : Fin n → α) : Array.ofFn f = ⟨Seq.tabulate n f⟩ := by
  apply Array.ext'
  rw [Array.toList_ofFn, Seq.tabulate_eq]

attribute [kernel_optimize ← (cost := 850)] Seq.map_eq

/-- Mapping an array uses the same kernel traversal as mapping a list. -/
@[kernel_optimize]
theorem array_map (f : α → β) (a : Array α) :
    a.map f = ⟨Seq.map f a.toList⟩ := by
  apply Array.ext'
  rw [Array.toList_map, Seq.map_eq]

attribute [kernel_optimize ← (cost := 1600)] Seq.mapIdx_eq

/-- An indexed array map preserves the list traversal's zero-based indices. -/
@[kernel_optimize]
theorem array_mapIdx (f : Nat → α → β) (a : Array α) :
    a.mapIdx f = ⟨Seq.mapIdx f a.toList⟩ := by
  apply Array.ext'
  rw [Array.toList_mapIdx, Seq.mapIdx_eq]

attribute [kernel_optimize ← (cost := 1800)] Seq.zipWith_eq

/-- Zipping arrays stops at the shorter input, as `Seq.zipWith` does. -/
@[kernel_optimize]
theorem array_zipWith (f : α → β → γ) (a : Array α) (b : Array β) :
    a.zipWith f b = ⟨Seq.zipWith f a.toList b.toList⟩ := by
  apply Array.ext'
  rw [Array.toList_zipWith, Seq.zipWith_eq]

attribute [kernel_optimize ← (cost := 1100)] Seq.all_eq

/-- Testing an array range uses the list predicate fold on the same slice. Empty, reversed
and out-of-bounds ranges follow the core array conventions. -/
@[kernel_optimize]
theorem array_all (p : α → Bool) (a : Array α) (start stop : Nat) :
    a.all p start stop = Seq.all p ((a.toList.take stop).drop start) := by
  rw [Seq.all_eq, Bool.eq_iff_iff, Array.all_iff_forall, List.all_eq_true,
    List.forall_mem_iff_forall_getElem]
  constructor
  · intro h j hj
    have hj' : j < min stop a.size - start := by simpa using hj
    simpa only [List.getElem_drop, List.getElem_take, Array.getElem_toList] using
      h (start + j) (by omega) ⟨by omega, by omega⟩
  · intro h i hi hirange
    have hij : start + (i - start) = i := Nat.add_sub_of_le hirange.1
    have hj : i - start < ((a.toList.take stop).drop start).length := by
      simp only [List.length_drop, List.length_take, Array.length_toList]
      omega
    simpa only [List.getElem_drop, List.getElem_take, Array.getElem_toList, hij] using
      h (i - start) hj

attribute [kernel_optimize ← (cost := 800)] Seq.reverse_eq

/-- Reversing an array uses the kernel list reversal. -/
@[kernel_optimize]
theorem array_reverse (a : Array α) : a.reverse = ⟨Seq.reverse a.toList⟩ := by
  apply Array.ext'
  rw [Array.toList_reverse, Seq.reverse_eq]

attribute [kernel_optimize ← (cost := 1500)] Seq.sum_eq

attribute [kernel_optimize ← (cost := 3)] Opt.bind_eq

attribute [kernel_optimize ← (cost := 3)] Opt.map_eq

attribute [kernel_optimize ← (cost := 3)] Opt.join_eq

attribute [kernel_optimize ← (cost := 830)] isqrt_eq

/-! ## Branches on natural numbers -/

/-- An `if` on an equation of natural numbers is the recursor of `Bool` on `Nat.beq`. -/
@[kernel_optimize (cost := 2)]
theorem ite_nat_eq {α : Type u} (a b : Nat) [Decidable (a = b)] (x y : α) :
    (if a = b then x else y) = Bool.rec (motive := fun _ => α) y x (Nat.beq a b) := by
  cases hb : Nat.beq a b
  · exact ite_eq_right (Nat.ne_of_beq_eq_false hb)
  · exact ite_eq_left (Nat.eq_of_beq_eq_true hb)

/-- An `if` on an order of natural numbers is the recursor of `Bool` on `Nat.ble`. -/
@[kernel_optimize (cost := 2)]
theorem ite_nat_le {α : Type u} (a b : Nat) [Decidable (a ≤ b)] (x y : α) :
    (if a ≤ b then x else y) = Bool.rec (motive := fun _ => α) y x (Nat.ble a b) := by
  cases hb : Nat.ble a b
  · exact ite_eq_right (Nat.not_le_of_not_ble_eq_true (by rw [hb]; exact Bool.false_ne_true))
  · exact ite_eq_left (Nat.le_of_ble_eq_true hb)

/-- An `if` on a strict order of natural numbers is the recursor of `Bool` on `Nat.ble`. -/
@[kernel_optimize (cost := 2)]
theorem ite_nat_lt {α : Type u} (a b : Nat) [Decidable (a < b)] (x y : α) :
    (if a < b then x else y) = Bool.rec (motive := fun _ => α) y x (Nat.ble (Nat.succ a) b) := by
  cases hb : Nat.ble (Nat.succ a) b
  · exact ite_eq_right (Nat.not_le_of_not_ble_eq_true (by rw [hb]; exact Bool.false_ne_true))
  · exact ite_eq_left (Nat.le_of_ble_eq_true hb)

/-- An `if` on a Boolean is its recursor. -/
@[kernel_optimize (cost := 2)]
theorem ite_bool {α : Type u} (c : Bool) [Decidable (c = true)] (x y : α) :
    (if c = true then x else y) = Bool.rec (motive := fun _ => α) y x c := by
  cases c
  · exact ite_eq_right Bool.false_ne_true
  · exact ite_eq_left rfl

attribute [kernel_optimize] ite_not

/-!
An `if` whose condition is a Boolean literal is its branch: core's rules turn `false && b` into
`false`, `false = true` into `False`, and an `if` on `True` or `False` into its branch (`true =
true` is `True` by reflexivity).
-/
attribute [kernel_optimize] Bool.false_and Bool.true_and Bool.false_eq_true ite_true ite_false

/-- Whether two Booleans differ, as recursors: the test costs the kernel two steps where the
instance of `!=` costs it thirty microseconds. -/
@[kernel_optimize (cost := 2)]
theorem bool_bne (a b : Bool) :
    (a != b) = Bool.rec (motive := fun _ => Bool) b
      (Bool.rec (motive := fun _ => Bool) true false b) a := by
  cases a <;> cases b <;> rfl

/-- Whether two Booleans are equal, as recursors. -/
@[kernel_optimize (cost := 2)]
theorem bool_beq (a b : Bool) :
    (a == b) = Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) true false b) b a := by
  cases a <;> cases b <;> rfl

/-- The natural number of the word of a natural number is a remainder, by the kernel's
functions. -/
@[kernel_optimize (cost := 2)]
theorem toNat_ofNat (width n : Nat) :
    (BitVec.ofNat width n).toNat = Nat.mod n (Nat.pow 2 width) :=
  BitVec.toNat_ofNat ..

/--
An `if` between two decidable propositions holds when the recursor of `Bool` between their
decisions, on the decision of the condition, is `true`. The rule is tried before the rules for
an `if` between two values of a type, whose result between two propositions would have no
`Decidable` instance.
-/
@[kernel_optimize (cost := 1)]
theorem ite_prop (c p q : Prop) [Decidable c] [Decidable p] [Decidable q] :
    (if c then p else q) =
      (Bool.rec (motive := fun _ => Bool) (decide q) (decide p) (decide c) = true) := by
  cases hd : decide c
  · exact (ite_eq_right (of_decide_eq_false hd)).trans decide_eq_true_eq.symm
  · exact (ite_eq_left (of_decide_eq_true hd)).trans decide_eq_true_eq.symm

attribute [kernel_optimize] Bool.decide_eq_true

/-- Deciding an equation of natural numbers is `Nat.beq`. -/
@[kernel_optimize (cost := 1)]
theorem decide_nat_eq (a b : Nat) [Decidable (a = b)] : decide (a = b) = Nat.beq a b := by
  cases hb : Nat.beq a b
  · exact decide_eq_false (Nat.ne_of_beq_eq_false hb)
  · exact decide_eq_true (Nat.eq_of_beq_eq_true hb)

/-- Deciding an order of natural numbers is `Nat.ble`. -/
@[kernel_optimize (cost := 1)]
theorem decide_nat_le (a b : Nat) [Decidable (a ≤ b)] : decide (a ≤ b) = Nat.ble a b := by
  cases hb : Nat.ble a b
  · exact decide_eq_false (Nat.not_le_of_not_ble_eq_true (by rw [hb]; exact Bool.false_ne_true))
  · exact decide_eq_true (Nat.le_of_ble_eq_true hb)

/-- Deciding a strict order of natural numbers is `Nat.ble`. -/
@[kernel_optimize (cost := 1)]
theorem decide_nat_lt (a b : Nat) [Decidable (a < b)] :
    decide (a < b) = Nat.ble (Nat.succ a) b := by
  cases hb : Nat.ble (Nat.succ a) b
  · exact decide_eq_false (Nat.not_le_of_not_ble_eq_true (by rw [hb]; exact Bool.false_ne_true))
  · exact decide_eq_true (Nat.le_of_ble_eq_true hb)

end FloatLib.Floats.ExecFloat.KernelPath.Plumbing
