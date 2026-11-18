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
# Kernel rules for lists, arrays, options and the square root

A program that is evaluated by Lean's kernel pays for its plumbing as well as for its arithmetic.
The existing equality theorems are registered in reverse; the array bridge theorems here
state a core Lean function as an operation of `FloatLib.Numerics.Kernel.Seq`. The registered
costs guide the optimizer; they are estimates rather than bounds on evaluation time.

The rules cover length, lookup, map, indexed map, zip, all, reverse, natural-number sum,
option bind/map/join and `Nat.sqrt`. Arrays use the same list operations on their entries,
including maps, zips and reversal.
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

end FloatLib.Floats.ExecFloat.KernelPath.Plumbing
