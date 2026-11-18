/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.Bits
public import FloatLib.Numerics.Kernel.Seq
public import FloatLib.Tactic.CompiledAs

/-!
# The kernel list and option functions are core's

* `Seq.len_eq`: `Seq.len l = l.length`.
* `Seq.nth?_eq`, `Seq.getD_eq`: `Seq.nth? l i = l[i]?` and `Seq.getD l i d = l.getD i d`.
* `Seq.snoc_eq`: `Seq.snoc l x = l ++ [x]`.
* `Seq.tabulate_eq`: `Seq.tabulate n f = List.ofFn f`.
* `Seq.map_eq`, `Seq.mapIdx_eq`, `Seq.zipWith_eq`, `Seq.all_eq`, `Seq.reverse_eq`, `Seq.sum_eq`:
  `Seq.map f l = l.map f`, `Seq.mapIdx f l = l.mapIdx f`,
  `Seq.zipWith f la lb = List.zipWith f la lb`, `Seq.all p l = l.all p`,
  `Seq.reverse l = l.reverse`, `Seq.sum l = l.sum`; `Seq.all_eq_true` states `Seq.all` on the
  members.
* `Seq.all₃_iff`: `Seq.all₃ p la lb lc = true` exactly when the three lists have the same length
  and `p` holds for the entries at every position.
* `Opt.bind_eq`, `Opt.map_eq`, `Opt.join_eq`: `Opt.bind o f = o.bind f`, `Opt.map f o = o.map f`,
  `Opt.join o = o.join`.

Each holds for every list, entry, option and function. The proofs use core only.
-/

@[expose] public section

namespace FloatLib.Numerics.Kernel

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

namespace Seq

/-- `len l` is the length of `l`. -/
theorem len_eq (l : List α) : len l = l.length := by
  induction l with
  | nil => rfl
  | cons _ l ih => exact congrArg Nat.succ ih

/-- `nth? l i` is the lookup `l[i]?`. -/
theorem nth?_eq (l : List α) (i : Nat) : nth? l i = l[i]? := by
  induction l generalizing i with
  | nil => rfl
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ j => exact (ih j).trans List.getElem?_cons_succ.symm

/-- The compiled implementation of list lookup, using core indexing. -/
def Compiled.nth? (l : List α) (i : Nat) : Option α := l[i]?

/-- Compiled code uses core list indexing. -/
compiled_as nth? := Compiled.nth? by nth?_eq

/-- `getD l i d` is `l.getD i d`. -/
theorem getD_eq (l : List α) (i : Nat) (d : α) : getD l i d = l.getD i d := by
  induction l generalizing i with
  | nil => exact List.getD_nil.symm
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ j => exact (ih j).trans List.getD_cons_succ.symm

/-- `snocWith l x k` applies `k` to `l ++ [x]`. -/
theorem snocWith_eq (l : List α) (x : α) (k : List α → List α) :
    snocWith l x k = k (l ++ [x]) := by
  induction l generalizing k with
  | nil => rfl
  | cons a _ ih => exact ih _

/-- `snoc l x` is `l ++ [x]`. -/
theorem snoc_eq (l : List α) (x : α) : snoc l x = l ++ [x] :=
  snocWith_eq l x _

/-- `tabulateFrom f k h acc` is the first `k` values of `f`, then `acc`. -/
theorem tabulateFrom_eq {n : Nat} (f : Fin n → α) (k : Nat) (h : k ≤ n) (acc : List α) :
    tabulateFrom f k h acc =
      List.ofFn (fun i : Fin k => f ⟨i.1, Nat.lt_of_lt_of_le i.2 h⟩) ++ acc := by
  induction k generalizing acc with
  | zero =>
    change acc = _
    rw [List.ofFn_zero, List.nil_append]
  | succ k ih =>
    change tabulateFrom f k (Nat.le_of_succ_le h) (f ⟨k, h⟩ :: acc) = _
    rw [ih, List.ofFn_succ_last, List.append_assoc]
    rfl

/-- `tabulate n f` is the list `List.ofFn f` of the values of `f`. -/
theorem tabulate_eq (n : Nat) (f : Fin n → α) : tabulate n f = List.ofFn f := by
  rw [tabulate, tabulateFrom_eq, List.append_nil]

/-- `map f l` is `l.map f`. -/
theorem map_eq (f : α → β) (l : List α) : map f l = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => exact congrArg (f a :: ·) ih

/-- `mapIdx f l` is `l.mapIdx f`. -/
theorem mapIdx_eq (f : Nat → α → β) (l : List α) : mapIdx f l = l.mapIdx f := by
  have aux : ∀ (l : List α) (i : Nat),
      List.rec (motive := fun _ => Nat → List β) (fun _ => List.nil)
        (fun a _ rest i => List.cons (f i a) (strict (Nat.succ i) rest)) l i =
      l.mapIdx (fun j => f (i + j)) := by
    intro l
    induction l with
    | nil => intro i; rfl
    | cons a l ih =>
      intro i
      change f i a :: strict (Nat.succ i) (List.rec (motive := fun _ => Nat → List β)
        (fun _ => List.nil) (fun a _ rest i => List.cons (f i a) (strict (Nat.succ i) rest)) l) = _
      rw [strict_eq, ih, List.mapIdx_cons]
      have e : (fun j => f (Nat.succ i + j)) = fun j => f (i + (j + 1)) := by
        funext j
        rw [Nat.succ_add, Nat.add_succ]
      rw [e]
      rfl
  have h := aux l 0
  have e : (fun j => f (0 + j)) = f := by
    funext j
    rw [Nat.zero_add]
  rwa [e] at h

/-- `zipWith f la lb` is `List.zipWith f la lb`. -/
theorem zipWith_eq (f : α → β → γ) : ∀ (la : List α) (lb : List β),
    zipWith f la lb = List.zipWith f la lb
  | [], _ => by
    change ([] : List γ) = _
    rw [List.zipWith_nil_left]
  | _ :: _, [] => by
    change ([] : List γ) = _
    rw [List.zipWith_nil_right]
  | a :: la, b :: lb => by
    change f a b :: zipWith f la lb = _
    rw [zipWith_eq f la lb, List.zipWith_cons_cons]

/-- `all p l` is `l.all p`. -/
theorem all_eq (p : α → Bool) (l : List α) : all p l = l.all p := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change Bool.and (p a) (all p l) = _
    rw [ih, List.all_cons]

/-- `all p l` holds exactly when `p` holds for every member. -/
theorem all_eq_true {p : α → Bool} {l : List α} : all p l = true ↔ ∀ a ∈ l, p a = true := by
  rw [all_eq, List.all_eq_true]

/-- `all₃ p la lb lc` holds exactly when the lists have the same length and `p` holds for the
entries at every position; `da`, `db`, `dc` stand for the entries beyond the ends, which are
never asked. -/
theorem all₃_iff {p : α → β → γ → Bool} (da : α) (db : β) (dc : γ) :
    ∀ {la : List α} {lb : List β} {lc : List γ}, all₃ p la lb lc = true ↔
      lb.length = la.length ∧ lc.length = la.length ∧
        ∀ j, j < la.length → p (la.getD j da) (lb.getD j db) (lc.getD j dc) = true
  | [], [], [] => ⟨fun _ => ⟨rfl, rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩, fun _ => rfl⟩
  | [], [], _ :: _ =>
    ⟨fun h => Bool.noConfusion h, fun h => Nat.noConfusion h.2.1⟩
  | [], _ :: _, _ => ⟨fun h => Bool.noConfusion h, fun h => Nat.noConfusion h.1⟩
  | _ :: _, [], _ => ⟨fun h => Bool.noConfusion h, fun h => Nat.noConfusion h.1⟩
  | _ :: _, _ :: _, [] => ⟨fun h => Bool.noConfusion h, fun h => Nat.noConfusion h.2.1⟩
  | a :: la, b :: lb, c :: lc => by
    have ih := all₃_iff (p := p) da db dc (la := la) (lb := lb) (lc := lc)
    change Bool.and (p a b c) (all₃ p la lb lc) = true ↔ _
    rw [Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h0, h1, h2, h3⟩
      refine ⟨congrArg Nat.succ h1, congrArg Nat.succ h2, ?_⟩
      intro j hj
      cases j with
      | zero => exact h0
      | succ j => exact h3 j (Nat.lt_of_succ_lt_succ hj)
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h3 0 (Nat.succ_pos _), Nat.succ.inj h1, Nat.succ.inj h2, ?_⟩
      intro j hj
      exact h3 (j + 1) (Nat.succ_lt_succ hj)

/-- `reverse l` is `l.reverse`. -/
theorem reverse_eq (l : List α) : reverse l = l.reverse := by
  have aux : ∀ (l acc : List α),
      List.rec (motive := fun _ => List α → List α) (fun acc => acc)
        (fun a _ rest acc => rest (a :: acc)) l acc = l.reverse ++ acc := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons a l ih =>
      intro acc
      change List.rec (motive := fun _ => List α → List α) (fun acc => acc)
        (fun a _ rest acc => rest (a :: acc)) l (a :: acc) = _
      rw [ih, List.reverse_cons, List.append_assoc]
      rfl
  have h := aux l []
  rwa [List.append_nil] at h

/-- `sum l` is `l.sum`. -/
theorem sum_eq (l : List Nat) : sum l = l.sum := by
  have aux : ∀ (l : List Nat) (acc : Nat),
      List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
        (fun x _ rest acc => strict (Nat.add acc x) rest) l acc = acc + l.sum := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons x l ih =>
      intro acc
      change strict (Nat.add acc x) (List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
        (fun x _ rest acc => strict (Nat.add acc x) rest) l) = _
      rw [strict_eq, ih, List.sum_cons]
      exact Nat.add_assoc acc x l.sum
  have h := aux l 0
  rwa [Nat.zero_add] at h

end Seq

/-- `Opt.bind o f` is `o.bind f`. -/
theorem Opt.bind_eq (o : Option α) (f : α → Option β) : Opt.bind o f = o.bind f := by
  cases o <;> rfl

/-- `Opt.map f o` is `o.map f`. -/
theorem Opt.map_eq (f : α → β) (o : Option α) : Opt.map f o = o.map f := by
  cases o <;> rfl

/-- `Opt.join o` is `o.join`. -/
theorem Opt.join_eq (o : Option (Option α)) : Opt.join o = o.join := by
  cases o <;> rfl

end FloatLib.Numerics.Kernel
