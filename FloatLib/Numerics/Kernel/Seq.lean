/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.Strict

/-!
# Lists and options for Lean's kernel

Core's functions on lists, arrays and options are compiled from pattern matching. In kernel
evaluation, the resulting recursion matters: an array is represented by a list, and filling it by
repeated pushes copies each earlier prefix. The functions here expose the recursors directly and
provide a linear construction for a table whose entries are known by index.

The functions here do the same work by the recursors of `List`, `Nat` and `Option`:

* `Seq.len l`, the length;
* `Seq.nth? l i`, the entry `i` or `none`, and `Seq.getD l i d`, the
  entry `i` or `d`;
* `Seq.snoc l x`, the list `l ++ [x]`. The spine of the result is fully
  built, so a later push or lookup walks plain cells and not one suspended copy per earlier push;
* `Seq.tabulate n f`, the list `[f 0, …, f (n - 1)]` for `f : Fin n → α`, built in `n` steps;
* `Seq.map f l`, `Seq.mapIdx f l` (with the position of each member), `Seq.zipWith f la lb`,
  `Seq.all p l`, `Seq.reverse l` and, for naturals, `Seq.sum l`, which reduces each partial sum
  before the next (`strict`), so that the kernel holds one number and not a chain of suspended
  additions;
* `Seq.all₃ p la lb lc`: whether three lists have the same length and `p` holds for every
  triple, in one pass;
* `Opt.bind`, `Opt.map`, `Opt.join`, which are `Option.bind`, `Option.map` and `Option.join`.

Each is a named function and not a bare recursor: the kernel reduces a recursor whenever it
compares two terms, also in a proof about a program with free variables, where the reduction of
the scrutinee need not stop (a subtraction of two large literals with a variable between them is
peeled one successor at a time). A named function is unfolded only when the kernel evaluates it.

`FloatLib.Numerics.Kernel.SeqProof` proves them equal to the functions of core, and
`FloatLib.Floats.ExecFloat.Backends.Kernel.Plumbing` tags the rules that rewrite the functions of
core with them. Only `strict` is imported.
-/

@[expose] public section

namespace FloatLib.Numerics.Kernel

universe u v w

namespace Seq

/-- The length of `l` (`Seq.len_eq`). -/
noncomputable def len {α : Type u} (l : List α) : Nat :=
  List.rec 0 (fun _ _ n => Nat.succ n) l

/-- The entry `i` of `l`, or `none` if `l` has at most `i` entries (`Seq.nth?_eq`). -/
noncomputable def nth? {α : Type u} (l : List α) (i : Nat) : Option α :=
  List.rec (motive := fun _ => Nat → Option α) (fun _ => none)
    (fun a _ rest i => Nat.rec (some a) (fun j _ => rest j) i) l i

/-- The entry `i` of `l`, or `d` if `l` has at most `i` entries (`Seq.getD_eq`). -/
noncomputable def getD {α : Type u} (l : List α) (i : Nat) (d : α) : α :=
  List.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun a _ rest i => Nat.rec a (fun j _ => rest j) i) l i

/-- `snocWith l x k` is `k (l ++ [x])`: the cells of `l` are passed down and the new list is
built on the way back, so the result has no suspended part (`Seq.snocWith_eq`). -/
noncomputable def snocWith {α : Type u} (l : List α) (x : α) : (List α → List α) → List α :=
  List.rec (motive := fun _ => (List α → List α) → List α) (fun k => k (List.cons x List.nil))
    (fun a _ rest k => rest (fun t => k (List.cons a t))) l

/-- The list `l ++ [x]`, with its spine fully built (`Seq.snoc_eq`). -/
noncomputable def snoc {α : Type u} (l : List α) (x : α) : List α :=
  snocWith l x (fun t => t)

/-- `tabulateFrom f k h acc` puts `f 0, …, f (k - 1)` in front of `acc`
(`Seq.tabulateFrom_eq`). -/
noncomputable def tabulateFrom {α : Type u} {n : Nat} (f : Fin n → α) (k : Nat) :
    Nat.le k n → List α → List α :=
  Nat.rec (motive := fun k => Nat.le k n → List α → List α) (fun _ acc => acc)
    (fun k rest h acc => rest (Nat.le_of_succ_le h) (List.cons (f ⟨k, h⟩) acc)) k

/-- The list `[f 0, …, f (n - 1)]`, built from the last entry in `n` steps
(`Seq.tabulate_eq`). -/
noncomputable def tabulate {α : Type u} (n : Nat) (f : Fin n → α) : List α :=
  tabulateFrom f n (Nat.le_refl n) List.nil

/-- `f` on every member of a list (`Seq.map_eq`). -/
noncomputable def map {α : Type u} {β : Type v} (f : α → β) (l : List α) : List β :=
  List.rec (motive := fun _ => List β) List.nil (fun a _ rest => List.cons (f a) rest) l

/-- `f` on every member of a list with its position, each position reduced before it is passed
on (`Seq.mapIdx_eq`). -/
noncomputable def mapIdx {α : Type u} {β : Type v} (f : Nat → α → β) (l : List α) : List β :=
  List.rec (motive := fun _ => Nat → List β) (fun _ => List.nil)
    (fun a _ rest i => List.cons (f i a) (strict (Nat.succ i) rest)) l 0

/-- `f` on the pairs of two lists; it stops with the shorter one (`Seq.zipWith_eq`). -/
noncomputable def zipWith {α : Type u} {β : Type v} {γ : Type w} (f : α → β → γ) (la : List α)
    (lb : List β) : List γ :=
  List.rec (motive := fun _ => List β → List γ) (fun _ => List.nil)
    (fun a _ rest lb =>
      List.rec (motive := fun _ => List γ) List.nil
        (fun b tb _ => List.cons (f a b) (rest tb)) lb)
    la lb

/-- Whether `p` holds for every member (`Seq.all_eq`). -/
noncomputable def all {α : Type u} (p : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ rest => Bool.and (p a) rest) l

/-- Whether three lists have the same length and `p` holds for every triple
(`Seq.all₃_iff`). -/
noncomputable def all₃ {α : Type u} {β : Type v} {γ : Type w} (p : α → β → γ → Bool)
    (la : List α) (lb : List β) (lc : List γ) : Bool :=
  List.rec (motive := fun _ => List β → List γ → Bool)
    (fun lb lc =>
      List.rec (motive := fun _ => Bool)
        (List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) lc) (fun _ _ _ => false) lb)
    (fun a _ rest lb lc =>
      List.rec (motive := fun _ => Bool) false
        (fun b tb _ =>
          List.rec (motive := fun _ => Bool) false
            (fun c tc _ => Bool.and (p a b c) (rest tb tc)) lc)
        lb)
    la lb lc

/-- The list in the opposite order (`Seq.reverse_eq`). -/
noncomputable def reverse {α : Type u} (l : List α) : List α :=
  List.rec (motive := fun _ => List α → List α) (fun acc => acc)
    (fun a _ rest acc => rest (List.cons a acc)) l List.nil

/-- The sum of a list of naturals, each partial sum reduced before the next (`Seq.sum_eq`). -/
noncomputable def sum (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun x _ rest acc => strict (Nat.add acc x) rest) l 0

end Seq

/-- `o.bind f`, by the recursor of `Option` (`Opt.bind_eq`). -/
noncomputable def Opt.bind {α : Type u} {β : Type v} (o : Option α) (f : α → Option β) :
    Option β :=
  Option.rec none f o

/-- `o.map f`, by the recursor of `Option` (`Opt.map_eq`). -/
noncomputable def Opt.map {α : Type u} {β : Type v} (f : α → β) (o : Option α) : Option β :=
  Option.rec none (fun a => some (f a)) o

/-- `o.join`, by the recursor of `Option` (`Opt.join_eq`). -/
noncomputable def Opt.join {α : Type u} (o : Option (Option α)) : Option α :=
  Option.rec none (fun a => a) o

end FloatLib.Numerics.Kernel
