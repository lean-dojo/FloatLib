/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Packed.Machine

import Mathlib.Data.Nat.Bitwise
import Mathlib.Order.Basic

/-!
# Lane programs

A lane program (`Expr`) is an expression in the natural-number operations that Lean's kernel
computes natively: sums, truncated differences, products, bitwise operations, shifts, the two
comparisons as a choice between two values, and a binding that shares a value. It has two
meanings.

* `eval e env` is the number it denotes for the numbers `env i` of its variables. It is written
  with the bare operations (`Nat.add`, `Nat.shiftLeft`, `Bool.casesOn` on `Nat.beq`, …), so a
  definition that is made of these operations *is* `eval` of a program, by unfolding.
* `run F e rows` evaluates it on rows: every variable holds one number per lane, and each
  operation is a few kernel operations on whole rows (`Packed.Machine`).

`run_holds` proves that the two agree in every lane whose error is zero, for every program
whose `call` nodes are sound (`Expr.Sound`) and every frame. `lane_run` states it for rows given
as naturals. `forall_pairs` turns an equation between two programs on all pairs of indices below
`n` into one closed check of two rows of `n * n` lanes, which is how an exhaustive statement
about a small format is checked in one evaluation of each side, and `lane_pairsRow` states that
the row of one program on all pairs is the table of the function it denotes.

`eval_add` and its siblings are the denotation equations, one per node, from which
`Packed.Reify` builds the proof that a program denotes the term it was read from.
-/

@[expose] public section

namespace FloatLib.Numerics.Packed

/-- A lane program: an expression in the kernel's natural-number operations. -/
inductive Expr where
  /-- The variable with de Bruijn index `index`: zero is the innermost binding. -/
  | var (index : Nat)
  /-- A number, the same in every lane. -/
  | const (value : Nat)
  /-- `Nat.add`. -/
  | add (x y : Expr)
  /-- `Nat.sub`, truncated at zero. -/
  | sub (x y : Expr)
  /-- `Nat.mul`, computed for second factors below `2 ^ bound`. -/
  | mul (bound : Nat) (x y : Expr)
  /-- `Nat.mul`, computed for first factors below `2 ^ bound`. -/
  | mulLeft (bound : Nat) (x y : Expr)
  /-- `Nat.pow 2`. -/
  | pow2 (exponent : Expr)
  /-- `Nat.land`. -/
  | land (x y : Expr)
  /-- `Nat.lor`. -/
  | lor (x y : Expr)
  /-- `Nat.xor`. -/
  | xor (x y : Expr)
  /-- `Nat.shiftLeft`. -/
  | shiftLeft (x count : Expr)
  /-- `Nat.shiftRight`. -/
  | shiftRight (x count : Expr)
  /-- `Nat.shiftLeft` by a count that is the same in every lane: one step instead of a loop. -/
  | shiftLeftBy (x : Expr) (count : Nat)
  /-- `Nat.shiftRight` by a count that is the same in every lane. -/
  | shiftRightBy (x : Expr) (count : Nat)
  /-- `Bool.casesOn (Nat.beq a b) other equal`. -/
  | ifEq (a b equal other : Expr)
  /-- `Bool.casesOn (Nat.ble a b) other atMost`. -/
  | ifLe (a b atMost other : Expr)
  /-- `(fun x => body) value`: the value is computed once and bound to variable zero. -/
  | bind (value body : Expr)
  /--
  `function argument`, for a function that is not one of the operations above. On rows, the
  program `body` is run in its place, with the argument as its only variable, in the lanes whose
  argument is below `limit`; the other lanes are marked in the error row. `Expr.Sound` asks
  that `body` denotes the function below `limit`. With `limit = 0` any body will do, and every
  lane that uses the result is marked.
  -/
  | call (function : Nat → Nat) (limit : Nat) (body argument : Expr)

/-- An environment with one more variable: index zero is `head`. -/
def push {α : Type} (head : α) (tail : Nat → α) : Nat → α :=
  fun index => Nat.rec head (fun previous _ => tail previous) index

/-- The first variable of an extended environment. -/
@[simp] theorem push_zero {α : Type} (head : α) (tail : Nat → α) : push head tail 0 = head :=
  rfl

/-- The later variables of an extended environment. -/
@[simp] theorem push_succ {α : Type} (head : α) (tail : Nat → α) (index : Nat) :
    push head tail (index + 1) = tail index :=
  rfl

namespace Expr

/-- The number that a program denotes, for the numbers `env i` of its variables. -/
def eval : Expr → (Nat → Nat) → Nat
  | var index, env => env index
  | const value, _ => value
  | add x y, env => Nat.add (eval x env) (eval y env)
  | sub x y, env => Nat.sub (eval x env) (eval y env)
  | mul _ x y, env => Nat.mul (eval x env) (eval y env)
  | mulLeft _ x y, env => Nat.mul (eval x env) (eval y env)
  | pow2 exponent, env => Nat.pow 2 (eval exponent env)
  | land x y, env => Nat.land (eval x env) (eval y env)
  | lor x y, env => Nat.lor (eval x env) (eval y env)
  | xor x y, env => Nat.xor (eval x env) (eval y env)
  | shiftLeft x count, env => Nat.shiftLeft (eval x env) (eval count env)
  | shiftRight x count, env => Nat.shiftRight (eval x env) (eval count env)
  | shiftLeftBy x count, env => Nat.shiftLeft (eval x env) count
  | shiftRightBy x count, env => Nat.shiftRight (eval x env) count
  | ifEq a b equal other, env =>
      Bool.casesOn (motive := fun _ => Nat) (Nat.beq (eval a env) (eval b env)) (eval other env)
        (eval equal env)
  | ifLe a b atMost other, env =>
      Bool.casesOn (motive := fun _ => Nat) (Nat.ble (eval a env) (eval b env)) (eval other env)
        (eval atMost env)
  | bind value body, env => eval body (push (eval value env) env)
  | call function _ _ argument, env => function (eval argument env)

/--
Every `call` in the program has a body that denotes its function on the arguments below its
limit.
-/
def Sound : Expr → Prop
  | var _ | const _ => True
  | shiftLeftBy x _ | shiftRightBy x _ | pow2 x => Sound x
  | add x y | sub x y | mul _ x y | mulLeft _ x y | land x y | lor x y | xor x y | shiftLeft x y
  | shiftRight x y | bind x y => Sound x ∧ Sound y
  | ifEq a b c d | ifLe a b c d => Sound a ∧ Sound b ∧ Sound c ∧ Sound d
  | call function limit body argument =>
      (∀ value, value < limit → eval body (push value fun _ => 0) = function value) ∧
        Sound body ∧ Sound argument

/-- The program evaluated on rows: every variable holds one number per lane. -/
def run (F : Machine.Frame) : Expr → (Nat → Machine.Val) → Machine.Val
  | var index, env => env index
  | const value, _ => Machine.const F value
  | add x y, env => Machine.add F (run F x env) (run F y env)
  | sub x y, env => Machine.sub F (run F x env) (run F y env)
  | mul bound x y, env => Machine.mul F bound (run F x env) (run F y env)
  | mulLeft bound x y, env => Machine.mul F bound (run F y env) (run F x env)
  | pow2 exponent, env => Machine.shiftLeft F (Machine.const F 1) (run F exponent env)
  | land x y, env => Machine.land (run F x env) (run F y env)
  | lor x y, env => Machine.lor (run F x env) (run F y env)
  | xor x y, env => Machine.xor (run F x env) (run F y env)
  | shiftLeft x count, env => Machine.shiftLeft F (run F x env) (run F count env)
  | shiftRight x count, env => Machine.shiftRight F (run F x env) (run F count env)
  | shiftLeftBy x count, env => Machine.shlC F count (run F x env)
  | shiftRightBy x count, env => Machine.shrC F count (run F x env)
  | ifEq a b equal other, env =>
      Machine.select F (Machine.xor (run F a env) (run F b env)) (run F other env)
        (run F equal env)
  | ifLe a b atMost other, env =>
      Machine.select F (Machine.atLeast F (run F b env) (run F a env)) (run F atMost env)
        (run F other env)
  | bind value body, env => run F body (push (run F value env) env)
  | call _ limit body argument, env =>
      (fun value =>
        Machine.select F (Machine.atLeast F value (Machine.const F limit)) (Machine.poison F)
          (run F body (push value fun _ => Machine.const F 0)))
        (run F argument env)

/--
The two meanings of a program agree: when every variable row stands for its numbers, the row
that `run` computes stands for the numbers that `eval` denotes, lane by lane.
-/
theorem run_holds {F : Machine.Frame} (hF : F.Valid) (e : Expr) :
    e.Sound → ∀ (env : Nat → Machine.Val) (numbers : Nat → Nat → Nat),
      (∀ index, Machine.Holds F (numbers index) (env index)) →
        Machine.Holds F (fun k => eval e fun index => numbers index k) (run F e env) := by
  induction e with
  | var index => exact fun _ env numbers h => h index
  | const value => exact fun _ _ _ _ => Machine.const_holds hF value
  | add x y ihx ihy =>
      exact fun hs env numbers h =>
        Machine.add_holds hF (ihx hs.1 env numbers h) (ihy hs.2 env numbers h)
  | sub x y ihx ihy =>
      exact fun hs env numbers h =>
        Machine.sub_holds hF (ihx hs.1 env numbers h) (ihy hs.2 env numbers h)
  | mul bound x y ihx ihy =>
      exact fun hs env numbers h =>
        Machine.mul_holds hF bound (ihx hs.1 env numbers h) (ihy hs.2 env numbers h)
  | mulLeft bound x y ihx ihy =>
      exact fun hs env numbers h =>
        (Machine.mul_holds hF bound (ihy hs.2 env numbers h) (ihx hs.1 env numbers h)).congr
          fun k => Nat.mul_comm _ _
  | pow2 exponent ih =>
      exact fun hs env numbers h =>
        (Machine.shiftLeft_holds hF (Machine.const_holds hF 1) (ih hs env numbers h)).congr
          fun k => by
            change 1 <<< _ = Nat.pow 2 _
            rw [Nat.shiftLeft_eq, Nat.one_mul]
            rfl
  | land x y ihx ihy =>
      exact fun hs env numbers h =>
        Machine.land_holds (ihx hs.1 env numbers h) (ihy hs.2 env numbers h)
  | lor x y ihx ihy =>
      exact fun hs env numbers h =>
        Machine.lor_holds (ihx hs.1 env numbers h) (ihy hs.2 env numbers h)
  | xor x y ihx ihy =>
      exact fun hs env numbers h =>
        Machine.xor_holds (ihx hs.1 env numbers h) (ihy hs.2 env numbers h)
  | shiftLeft x count ihx ihc =>
      exact fun hs env numbers h =>
        Machine.shiftLeft_holds hF (ihx hs.1 env numbers h) (ihc hs.2 env numbers h)
  | shiftRight x count ihx ihc =>
      exact fun hs env numbers h =>
        Machine.shiftRight_holds hF (ihx hs.1 env numbers h) (ihc hs.2 env numbers h)
  | shiftLeftBy x count ih =>
      exact fun hs env numbers h => Machine.shlC_holds hF count (ih hs env numbers h)
  | shiftRightBy x count ih =>
      exact fun hs env numbers h => Machine.shrC_holds hF count (ih hs env numbers h)
  | call function limit body argument ihb iha =>
      intro hs env numbers h
      obtain ⟨hbody, hsb, hsa⟩ := hs
      have harg := iha hsa env numbers h
      have hinner := ihb hsb (push (run F argument env) fun _ => Machine.const F 0)
        (push (fun k => eval argument fun index => numbers index k) fun _ _ => 0) (fun index => by
          cases index with
          | zero => exact harg
          | succ index => exact Machine.const_holds hF 0)
      refine (Machine.select_holds hF
        (Machine.atLeast_holds hF harg (Machine.const_holds hF limit))
        (Machine.poison_holds hF fun k => function (eval argument fun index => numbers index k))
        hinner).congr fun k => ?_
      by_cases hlimit : limit ≤ eval argument fun index => numbers index k
      · rw [ite_eq_left hlimit, ite_eq_left (by decide)]
        rfl
      · rw [ite_eq_right hlimit, ite_eq_right (fun hne => hne rfl)]
        change eval body _ = function (eval argument fun index => numbers index k)
        rw [← hbody _ (Nat.lt_of_not_le hlimit)]
        congr 1
        funext index
        cases index <;> rfl
  | ifEq a b equal other iha ihb ihe iho =>
      intro hs env numbers h
      obtain ⟨hsa, hsb, hse, hso⟩ := hs
      have iha := iha hsa
      have ihb := ihb hsb
      have ihe := ihe hse
      have iho := iho hso
      refine (Machine.select_holds hF
        (Machine.xor_holds (iha env numbers h) (ihb env numbers h)) (iho env numbers h)
        (ihe env numbers h)).congr fun k => ?_
      change _ = Bool.casesOn (motive := fun _ => Nat) (Nat.beq _ _) _ _
      generalize eval a (fun index => numbers index k) = left
      generalize eval b (fun index => numbers index k) = right
      by_cases heq : left = right
      · subst heq
        rw [ite_eq_right (fun hne => hne (Nat.xor_self left)), Nat.beq_refl]
      · have hxor : left ^^^ right ≠ 0 := fun hzero => heq (by
          have hback : left ^^^ (left ^^^ right) = right := by
            rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
          rw [hzero, Nat.xor_zero] at hback
          exact hback)
        rw [ite_eq_left hxor,
          show Nat.beq left right = false from by
            cases hb : Nat.beq left right
            · rfl
            · exact absurd (Nat.eq_of_beq_eq_true hb) heq]
  | ifLe a b atMost other iha ihb iht iho =>
      intro hs env numbers h
      obtain ⟨hsa, hsb, hst, hso⟩ := hs
      have iha := iha hsa
      have ihb := ihb hsb
      have iht := iht hst
      have iho := iho hso
      refine (Machine.select_holds hF
        (Machine.atLeast_holds hF (ihb env numbers h) (iha env numbers h)) (iht env numbers h)
        (iho env numbers h)).congr fun k => ?_
      change _ = Bool.casesOn (motive := fun _ => Nat) (Nat.ble _ _) _ _
      generalize eval a (fun index => numbers index k) = left
      generalize eval b (fun index => numbers index k) = right
      by_cases hle : left ≤ right
      · rw [ite_eq_left hle, ite_eq_left (by decide), Nat.ble_eq_true_of_le hle]
      · rw [ite_eq_right hle, ite_eq_right (fun hne => hne rfl),
          show Nat.ble left right = false from by
            cases hb : Nat.ble left right
            · rfl
            · exact absurd (Nat.le_of_ble_eq_true hb) hle]
  | bind value body ihv ihb =>
      intro hs env numbers h
      have ihv := ihv hs.1
      have hbody := ihb hs.2 (push (run F value env) env)
        (push (fun k => eval value fun index => numbers index k) numbers) (fun index => by
          cases index with
          | zero => exact ihv env numbers h
          | succ index => exact h index)
      refine hbody.congr fun k => ?_
      change eval body _ = eval body _
      congr 1
      funext index
      cases index <;> rfl

/-!
### Denotation equations

One equation per node: a program denotes a term when its parts denote the parts of the term.
`Packed.Reify` builds the proof that a program denotes the term it was read from out of these
equations, so that Lean's kernel matches the two and does not unfold an operation on an open
term.
-/

/-- A constant denotes its value. -/
theorem eval_const (env : Nat → Nat) (value : Nat) : eval (const value) env = value := rfl

/-- `add` denotes `Nat.add` of what its parts denote. -/
theorem eval_add (env : Nat → Nat) (x y : Expr) (a b : Nat) (hx : eval x env = a)
    (hy : eval y env = b) : eval (add x y) env = Nat.add a b := by
  subst hx hy; rfl

/-- `sub` denotes `Nat.sub` of what its parts denote. -/
theorem eval_sub (env : Nat → Nat) (x y : Expr) (a b : Nat) (hx : eval x env = a)
    (hy : eval y env = b) : eval (sub x y) env = Nat.sub a b := by
  subst hx hy; rfl

/-- `land` denotes `Nat.land` of what its parts denote. -/
theorem eval_land (env : Nat → Nat) (x y : Expr) (a b : Nat) (hx : eval x env = a)
    (hy : eval y env = b) : eval (land x y) env = Nat.land a b := by
  subst hx hy; rfl

/-- `lor` denotes `Nat.lor` of what its parts denote. -/
theorem eval_lor (env : Nat → Nat) (x y : Expr) (a b : Nat) (hx : eval x env = a)
    (hy : eval y env = b) : eval (lor x y) env = Nat.lor a b := by
  subst hx hy; rfl

/-- `xor` denotes `Nat.xor` of what its parts denote. -/
theorem eval_xor (env : Nat → Nat) (x y : Expr) (a b : Nat) (hx : eval x env = a)
    (hy : eval y env = b) : eval (xor x y) env = Nat.xor a b := by
  subst hx hy; rfl

/-- `shiftLeft` denotes `Nat.shiftLeft` of what its parts denote. -/
theorem eval_shiftLeft (env : Nat → Nat) (x y : Expr) (a b : Nat) (hx : eval x env = a)
    (hy : eval y env = b) : eval (shiftLeft x y) env = Nat.shiftLeft a b := by
  subst hx hy; rfl

/-- `shiftRight` denotes `Nat.shiftRight` of what its parts denote. -/
theorem eval_shiftRight (env : Nat → Nat) (x y : Expr) (a b : Nat) (hx : eval x env = a)
    (hy : eval y env = b) : eval (shiftRight x y) env = Nat.shiftRight a b := by
  subst hx hy; rfl

/-- `mul` denotes the product of what its parts denote. -/
theorem eval_mul (env : Nat → Nat) (bound : Nat) (x y : Expr) (a b : Nat) (hx : eval x env = a)
    (hy : eval y env = b) : eval (mul bound x y) env = Nat.mul a b := by
  subst hx hy; rfl

/-- `mulLeft` denotes the product of what its parts denote. -/
theorem eval_mulLeft (env : Nat → Nat) (bound : Nat) (x y : Expr) (a b : Nat)
    (hx : eval x env = a) (hy : eval y env = b) : eval (mulLeft bound x y) env = Nat.mul a b := by
  subst hx hy; rfl

/-- Adding the constant one denotes the successor. -/
theorem eval_succ (env : Nat → Nat) (x : Expr) (a : Nat) (hx : eval x env = a) :
    eval (add x (const 1)) env = Nat.succ a := by
  subst hx; rfl

/-- `pow2` denotes the power of two. -/
theorem eval_pow2 (env : Nat → Nat) (x : Expr) (a : Nat) (hx : eval x env = a) :
    eval (pow2 x) env = Nat.pow 2 a := by
  subst hx; rfl

/-- `shiftLeftBy` denotes the left shift by its count. -/
theorem eval_shiftLeftBy (env : Nat → Nat) (x : Expr) (a count : Nat) (hx : eval x env = a) :
    eval (shiftLeftBy x count) env = Nat.shiftLeft a count := by
  subst hx; rfl

/-- `shiftRightBy` denotes the right shift by its count. -/
theorem eval_shiftRightBy (env : Nat → Nat) (x : Expr) (a count : Nat) (hx : eval x env = a) :
    eval (shiftRightBy x count) env = Nat.shiftRight a count := by
  subst hx; rfl

/-- `ifEq` denotes the case distinction on `Nat.beq`. -/
theorem eval_ifEq (env : Nat → Nat) (x y equal other : Expr) (a b t f : Nat)
    (hx : eval x env = a) (hy : eval y env = b) (ht : eval equal env = t)
    (hf : eval other env = f) :
    eval (ifEq x y equal other) env = Bool.casesOn (motive := fun _ => Nat) (Nat.beq a b) f t := by
  subst hx hy ht hf; rfl

/-- `ifLe` denotes the case distinction on `Nat.ble`. -/
theorem eval_ifLe (env : Nat → Nat) (x y atMost other : Expr) (a b t f : Nat)
    (hx : eval x env = a) (hy : eval y env = b) (ht : eval atMost env = t)
    (hf : eval other env = f) :
    eval (ifLe x y atMost other) env = Bool.casesOn (motive := fun _ => Nat) (Nat.ble a b) f t := by
  subst hx hy ht hf; rfl

/-- `ifLe` on a successor denotes the case distinction on `Nat.blt`. -/
theorem eval_ifLt (env : Nat → Nat) (x y below other : Expr) (a b t f : Nat)
    (hx : eval x env = a) (hy : eval y env = b) (ht : eval below env = t)
    (hf : eval other env = f) :
    eval (ifLe (add x (const 1)) y below other) env =
      Bool.casesOn (motive := fun _ => Nat) (Nat.blt a b) f t := by
  subst hx hy ht hf; rfl

/-- `bind` denotes the body applied to what the value denotes. -/
theorem eval_bind (env : Nat → Nat) (value body : Expr) (a : Nat) (f : Nat → Nat)
    (hvalue : eval value env = a) (hbody : ∀ u, eval body (push u env) = f u) :
    eval (bind value body) env = f a := by
  subst hvalue; exact hbody _

/-- `call` denotes its function applied to what the argument denotes. -/
theorem eval_call (env : Nat → Nat) (function : Nat → Nat) (limit : Nat) (body argument : Expr)
    (a : Nat) (hargument : eval argument env = a) :
    eval (call function limit body argument) env = function a := by
  subst hargument; rfl

end Expr

/-! ## Rows given as naturals -/

/-- The environment whose variable `i` is the row `rows[i]`, and the empty row beyond. -/
def rowEnv (rows : List Nat) : Nat → Machine.Val :=
  fun index => Machine.input (rows.getD index 0)

/-- The numbers in lane `k` of the rows of an environment. -/
def laneEnv (w : Nat) (rows : List Nat) (k : Nat) : Nat → Nat :=
  fun index => lane w k (rows.getD index 0)

/-- Whether every row is a well-formed input of the frame. -/
def accepted (F : Machine.Frame) (rows : List Nat) : Bool :=
  rows.all F.accepts

/-- The empty row is a well-formed input. -/
theorem accepts_zero (F : Machine.Frame) : F.accepts 0 = true := by
  simp [Machine.Frame.accepts]

/-- Accepted rows stand for their own lanes. -/
theorem rowEnv_holds {F : Machine.Frame} (hF : F.Valid) {rows : List Nat}
    (h : accepted F rows = true) (index : Nat) :
    Machine.Holds F (fun k => laneEnv F.width rows k index) (rowEnv rows index) := by
  refine Machine.input_holds hF ?_
  unfold accepted at h
  rw [List.all_eq_true] at h
  rw [List.getD_eq_getElem?_getD]
  cases hrow : rows[index]? with
  | none => exact accepts_zero F
  | some row => exact h row (List.mem_of_getElem? hrow)

/--
One lane of a program run on accepted rows: when the error of the lane is zero, its value is the
number that the program denotes for the numbers in that lane of the rows.
-/
theorem lane_run {F : Machine.Frame} (hF : F.Valid) (e : Expr) (hsound : e.Sound)
    {rows : List Nat} (haccepted : accepted F rows = true) {k : Nat} (hk : k < F.count)
    (herror : lane F.width k (e.run F (rowEnv rows)).error = 0) :
    lane F.width k (e.run F (rowEnv rows)).value = e.eval (laneEnv F.width rows k) :=
  (Expr.run_holds hF e hsound (rowEnv rows) (fun index k => laneEnv F.width rows k index)
    (rowEnv_holds hF haccepted)).exact k hk herror

/--
Two programs that run to the same value row without any error denote the same number in every
lane of the rows.
-/
theorem eval_eq_of_run {F : Machine.Frame} (hF : F.Valid) (lhs rhs : Expr)
    (hl : lhs.Sound) (hr : rhs.Sound) {rows : List Nat}
    (haccepted : accepted F rows = true)
    (hlhs : (lhs.run F (rowEnv rows)).error = 0) (hrhs : (rhs.run F (rowEnv rows)).error = 0)
    (hvalue : (lhs.run F (rowEnv rows)).value = (rhs.run F (rowEnv rows)).value)
    {k : Nat} (hk : k < F.count) :
    lhs.eval (laneEnv F.width rows k) = rhs.eval (laneEnv F.width rows k) := by
  rw [← lane_run hF lhs hl haccepted hk (by rw [hlhs, lane_zero_row]),
    ← lane_run hF rhs hr haccepted hk (by rw [hrhs, lane_zero_row]), hvalue]

/-! ## Rows of all indices and of all pairs -/

/--
The row whose lane `k` is `f k`, for `k < n`. It is the recursor of the natural numbers on `n`,
which Lean's kernel runs in `n` steps.
-/
def tabulate (w : Nat) (f : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun k row => Nat.add row (Nat.shiftLeft (f k) (Nat.mul w k))) n

/-- The empty tabulated row. -/
theorem tabulate_zero (w : Nat) (f : Nat → Nat) : tabulate w f 0 = 0 :=
  rfl

/-- A tabulated row with one more lane. -/
theorem tabulate_succ (w : Nat) (f : Nat → Nat) (n : Nat) :
    tabulate w f (n + 1) = tabulate w f n + f n <<< (w * n) :=
  rfl

/-- A tabulated row is below `2 ^ (w * n)` when its entries fit their lanes. -/
theorem tabulate_lt {w : Nat} {f : Nat → Nat} :
    ∀ {n : Nat}, (∀ k, k < n → f k < 2 ^ w) → tabulate w f n < 2 ^ (w * n)
  | 0, _ => by simp [tabulate_zero]
  | n + 1, h => by
      have ih := tabulate_lt (n := n) fun k hk => h k (Nat.lt_succ_of_lt hk)
      have hlast := h n (Nat.lt_succ_self n)
      rw [tabulate_succ, Nat.shiftLeft_eq, Nat.mul_succ, Nat.pow_add]
      have : f n * 2 ^ (w * n) + 2 ^ (w * n) ≤ 2 ^ w * 2 ^ (w * n) := by
        rw [← Nat.succ_mul]
        exact Nat.mul_le_mul_right _ hlast
      rw [Nat.mul_comm (2 ^ (w * n))]
      omega

/-- The lanes of a tabulated row. -/
theorem lane_tabulate {w : Nat} {f : Nat → Nat} :
    ∀ {n : Nat}, (∀ k, k < n → f k < 2 ^ w) → ∀ k,
      lane w k (tabulate w f n) = if k < n then f k else 0
  | 0, _, k => by simp [tabulate_zero]
  | n + 1, h, k => by
      have hsmall := tabulate_lt (n := n) fun j hj => h j (Nat.lt_succ_of_lt hj)
      have ih := lane_tabulate (n := n) (fun j hj => h j (Nat.lt_succ_of_lt hj)) k
      have hlast := h n (Nat.lt_succ_self n)
      rw [tabulate_succ, Nat.shiftLeft_eq, lane_eq]
      rcases Nat.lt_trichotomy k n with hlt | heq | hgt
      · -- A lane below the new one: the new entry is a multiple of a higher power.
        obtain ⟨m, rfl⟩ : ∃ m, n = k + 1 + m := ⟨n - k - 1, by omega⟩
        have hexp : w * (k + 1 + m) = w * k + (w + w * m) := by
          rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.add_assoc]
        have hsplit : f (k + 1 + m) * 2 ^ (w * (k + 1 + m)) =
            2 ^ (w * k) * (2 ^ w * (f (k + 1 + m) * 2 ^ (w * m))) := by
          rw [hexp, Nat.pow_add, Nat.pow_add, Nat.mul_left_comm, Nat.mul_left_comm (f _)]
        rw [hsplit, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.add_mul_mod_self_left,
          ← lane_eq, ih, ite_eq_left hlt, ite_eq_left (Nat.lt_succ_of_lt hlt)]
      · subst heq
        rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hsmall, Nat.zero_add,
          Nat.mod_eq_of_lt hlast, ite_eq_left (Nat.lt_succ_self k)]
      · have hnext := tabulate_lt (n := n + 1) h
        have hle : 2 ^ (w * (n + 1)) ≤ 2 ^ (w * k) :=
          Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hgt)
        have hunfold : tabulate w f (n + 1) = tabulate w f n + f n * 2 ^ (w * n) := by
          rw [tabulate_succ, Nat.shiftLeft_eq]
        rw [← hunfold, Nat.div_eq_of_lt (lt_of_lt_of_le hnext hle), Nat.zero_mod,
          ite_eq_right (by omega)]

/-- Lane `a * n + b` of a row is lane `b` of its block `a` of `n` lanes. -/
theorem lane_block {w n a b : Nat} (hb : b < n) (u : Nat) :
    lane w (a * n + b) u = lane w b (lane (w * n) a u) := by
  have hexp : w * (a * n + b) = w * n * a + w * b := by
    rw [Nat.mul_add, Nat.mul_comm a n, Nat.mul_assoc]
  have hsplit : 2 ^ (w * n) = 2 ^ (w * b) * 2 ^ (w * (n - b)) := by
    rw [← Nat.pow_add, ← Nat.mul_add]
    congr 2
    omega
  have hdvd : 2 ^ w ∣ 2 ^ (w * (n - b)) :=
    Nat.pow_dvd_pow 2 (Nat.le_mul_of_pos_right w (by omega))
  rw [lane_eq, lane_eq, lane_eq, hexp, Nat.pow_add, ← Nat.div_div_eq_div_mul, hsplit,
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ hdvd]

/--
The two rows of all pairs of indices below `n`: lane `a * n + b` holds `a` in the first row and
`b` in the second. Each row is `n` blocks of `n` lanes, so it is built in `n` steps.
-/
def pairRows (w n : Nat) : List Nat :=
  (fun block =>
    [tabulate (Nat.mul w n) (fun a => Nat.mul (Packed.ones w n) a) n,
      tabulate (Nat.mul w n) (fun _ => block) n])
    (tabulate w (fun b => b) n)

/-- The lanes of the two rows of all pairs. -/
theorem lane_pairRows {w n : Nat} (hw : 1 ≤ w) (hn : n ≤ 2 ^ w) {a b : Nat} (ha : a < n)
    (hb : b < n) :
    lane w (a * n + b) ((pairRows w n).getD 0 0) = a ∧
      lane w (a * n + b) ((pairRows w n).getD 1 0) = b := by
  constructor
  · change lane w (a * n + b) (tabulate (w * n) (fun a => Packed.ones w n * a) n) = a
    rw [lane_block hb, lane_tabulate (fun k hk => by
      have := (lanes_mul_ones (n := n) hw (lt_of_lt_of_le hk hn)).2
      rwa [Nat.mul_comm] at this), ite_eq_left ha, lane_const hw (lt_of_lt_of_le ha hn),
      ite_eq_left hb]
  · change lane w (a * n + b) (tabulate (w * n) (fun _ => tabulate w (fun b => b) n) n) = b
    have hblock : ∀ k, k < n → k < 2 ^ w := fun k hk => lt_of_lt_of_le hk hn
    rw [lane_block hb, lane_tabulate (fun _ _ => tabulate_lt hblock), ite_eq_left ha,
      lane_tabulate hblock, ite_eq_left hb]

/-- The index of a pair is below the number of pairs. -/
theorem pair_lt {n a b : Nat} (ha : a < n) (hb : b < n) : a * n + b < n * n :=
  calc a * n + b < a * n + n := Nat.add_lt_add_left hb _
    _ = (a + 1) * n := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ n * n := Nat.mul_le_mul_right _ ha

/-- The numbers in the lane of the pair `(a, b)` of the rows of all pairs: `a`, then `b`. -/
theorem laneEnv_pairRows {w n : Nat} (hw : 1 ≤ w) (hn : n ≤ 2 ^ w) {a b : Nat} (ha : a < n)
    (hb : b < n) :
    laneEnv w (pairRows w n) (a * n + b) = push a (push b fun _ => 0) := by
  have hrows := lane_pairRows hw hn ha hb
  funext index
  match index with
  | 0 => exact hrows.1
  | 1 => exact hrows.2
  | _ + 2 => exact lane_zero_row _ _

/-- The frame of all pairs holds the indices below `n` when `n ≤ 2 ^ (w - 1)`. -/
private theorem pairs_fit {w n : Nat} (hw : 2 ≤ w)
    (hsize : Nat.ble n (pow2 (Nat.sub w 1)) = true) : n ≤ 2 ^ w := by
  have hn : n ≤ 2 ^ (w - 1) := by
    have := Nat.le_of_ble_eq_true hsize
    rwa [pow2_eq] at this
  exact le_trans hn (Nat.pow_le_pow_right (by decide) (by omega))

/--
The closed check behind `forall_pairs`: the two rows of all pairs are well-formed inputs, both
programs run without an error in any lane, and their value rows are equal.
-/
def pairsCheck (w n depth : Nat) (lhs rhs : Expr) : Bool :=
  (fun F rows =>
    (fun left right =>
      Nat.ble n (pow2 (Nat.sub w 1)) && (accepted F rows &&
        (Nat.beq left.error 0 && (Nat.beq right.error 0 && Nat.beq left.value right.value))))
      (lhs.run F (rowEnv rows)) (rhs.run F (rowEnv rows)))
    (Machine.Frame.make w (Nat.mul n n) depth) (pairRows w n)

/--
Two functions `f` and `g` that two programs in two variables denote agree on all pairs of
indices below `n` when `pairsCheck` holds: one run of each program on rows of `n * n` lanes, and
one comparison. Variable zero is the first index and variable one the second.
-/
theorem forall_pairs {w n depth : Nat} (hw : 2 ≤ w) (hdepth : w - 1 ≤ 2 ^ depth)
    (lhs rhs : Expr) (f g : Nat → Nat → Nat) (hl : lhs.Sound) (hr : rhs.Sound)
    (hf : ∀ x y, lhs.eval (push x (push y fun _ => 0)) = f x y)
    (hg : ∀ x y, rhs.eval (push x (push y fun _ => 0)) = g x y)
    (hcheck : pairsCheck w n depth lhs rhs = true) :
    ∀ a b : Fin n, f a.val b.val = g a.val b.val := by
  intro a b
  rw [← hf, ← hg]
  have hF : (Machine.Frame.make w (n * n) depth).Valid := Machine.Frame.make_valid hw hdepth
  unfold pairsCheck at hcheck
  simp only [Bool.and_eq_true] at hcheck
  obtain ⟨hsize, haccepted, hle, hre, hvalue⟩ := hcheck
  have hrun := eval_eq_of_run hF lhs rhs hl hr haccepted (Nat.eq_of_beq_eq_true hle)
    (Nat.eq_of_beq_eq_true hre) (Nat.eq_of_beq_eq_true hvalue) (k := a.val * n + b.val)
    (pair_lt a.isLt b.isLt)
  exact laneEnv_pairRows (w := w) (by omega) (pairs_fit hw hsize) a.isLt b.isLt ▸ hrun

/-- The value row of a program run on all pairs of indices below `n`. -/
def pairsRow (w n depth : Nat) (program : Expr) : Nat :=
  (program.run (Machine.Frame.make w (Nat.mul n n) depth) (rowEnv (pairRows w n))).value

/--
The closed check behind `lane_pairsRow`: the two rows of all pairs are well-formed inputs and
the program runs without an error in any lane.
-/
def rowCheck (w n depth : Nat) (program : Expr) : Bool :=
  (fun F rows =>
    Nat.ble n (pow2 (Nat.sub w 1)) && (accepted F rows &&
      Nat.beq (program.run F (rowEnv rows)).error 0))
    (Machine.Frame.make w (Nat.mul n n) depth) (pairRows w n)

/-- `lane_pairsRow` from the three facts of its check. -/
private theorem lane_pairsRow_of {w n depth : Nat} (hw : 2 ≤ w) (hdepth : w - 1 ≤ 2 ^ depth)
    (program : Expr) (f : Nat → Nat → Nat) (hs : program.Sound)
    (hf : ∀ x y, program.eval (push x (push y fun _ => 0)) = f x y)
    (hsize : Nat.ble n (pow2 (Nat.sub w 1)) = true)
    (haccepted : accepted (Machine.Frame.make w (Nat.mul n n) depth) (pairRows w n) = true)
    (herror : Nat.beq
      (program.run (Machine.Frame.make w (Nat.mul n n) depth) (rowEnv (pairRows w n))).error 0 =
        true) :
    ∀ a b : Fin n, lane w (a.val * n + b.val) (pairsRow w n depth program) = f a.val b.val := by
  intro a b
  rw [← hf]
  have hF : (Machine.Frame.make w (n * n) depth).Valid := Machine.Frame.make_valid hw hdepth
  have hrun := lane_run hF program hs haccepted (k := a.val * n + b.val) (pair_lt a.isLt b.isLt)
    ((congrArg (lane _ _) (Nat.eq_of_beq_eq_true herror)).trans (lane_zero_row _ _))
  exact laneEnv_pairRows (w := w) (by omega) (pairs_fit hw hsize) a.isLt b.isLt ▸ hrun

/--
The row of a program on all pairs is the table of the function `f` that it denotes: lane
`a * n + b` holds `f a b`, for all indices below `n`, when `rowCheck` holds.
-/
theorem lane_pairsRow {w n depth : Nat} (hw : 2 ≤ w) (hdepth : w - 1 ≤ 2 ^ depth)
    (program : Expr) (f : Nat → Nat → Nat) (hs : program.Sound)
    (hf : ∀ x y, program.eval (push x (push y fun _ => 0)) = f x y)
    (hcheck : rowCheck w n depth program = true) :
    ∀ a b : Fin n, lane w (a.val * n + b.val) (pairsRow w n depth program) = f a.val b.val := by
  unfold rowCheck at hcheck
  simp only [Bool.and_eq_true] at hcheck
  exact lane_pairsRow_of hw hdepth program f hs hf hcheck.1 hcheck.2.1 hcheck.2.2

/-! ## Two rows with lanes of different widths -/

/-- The lanes below `m` of a row are the lanes of its lowest `m` lanes. -/
theorem lane_mod_lanes {w m k : Nat} (hk : k < m) (u : Nat) :
    lane w k (u % 2 ^ (w * m)) = lane w k u := by
  have h := lane_block (w := w) (n := m) (a := 0) hk u
  rw [Nat.zero_mul, Nat.zero_add, lane_zero] at h
  exact h.symm

/--
The number of lanes `k < leaf * 2 ^ levels` in which the row `u`, with lanes of `w` bits, and
the row `v`, with lanes of `W` bits, differ. Both rows are split in halves `levels` times, and a
piece of `leaf` lanes is compared lane by lane. The numbers that Lean's kernel builds on the way
are `levels` copies of the two rows in pieces, where a loop that shifted each lane out of the
whole row would build a number of half the row for every lane.
-/
def differences (w W leaf levels : Nat) : Nat → Nat → Nat :=
  (fun mask Mask =>
    Nat.rec (motive := fun _ => Nat → Nat → Nat)
      (fun u v =>
        Nat.rec (motive := fun _ => Nat) 0
          (fun k count =>
            Nat.add count
              (Bool.casesOn (motive := fun _ => Nat)
                (Nat.beq (Nat.land (Nat.shiftRight u (Nat.mul w k)) mask)
                  (Nat.land (Nat.shiftRight v (Nat.mul W k)) Mask)) 1 0))
          leaf)
      (fun level lower u v =>
        (fun su sv =>
          (fun uh vh =>
            Nat.add (lower (Nat.sub u (Nat.shiftLeft uh su)) (Nat.sub v (Nat.shiftLeft vh sv)))
              (lower uh vh))
            (Nat.shiftRight u su) (Nat.shiftRight v sv))
          (Nat.shiftLeft (Nat.mul w leaf) level) (Nat.shiftLeft (Nat.mul W leaf) level))
      levels)
    (Nat.sub (pow2 w) 1) (Nat.sub (pow2 W) 1)

/-- The differences of two rows of `leaf * 2 ^ (level + 1)` lanes are those of their halves. -/
theorem differences_succ (w W leaf level u v : Nat) :
    differences w W leaf (level + 1) u v =
      differences w W leaf level (u % 2 ^ (w * (leaf * 2 ^ level)))
          (v % 2 ^ (W * (leaf * 2 ^ level))) +
        differences w W leaf level (u >>> (w * (leaf * 2 ^ level)))
          (v >>> (W * (leaf * 2 ^ level))) := by
  have hlow : ∀ x s : Nat, x - (x >>> s) <<< s = x % 2 ^ s := fun x s => by
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mod_def, Nat.mul_comm]
  change differences w W leaf level (u - (u >>> ((w * leaf) <<< level)) <<< ((w * leaf) <<< level))
      (v - (v >>> ((W * leaf) <<< level)) <<< ((W * leaf) <<< level)) +
        differences w W leaf level (u >>> ((w * leaf) <<< level))
          (v >>> ((W * leaf) <<< level)) = _
  rw [hlow, hlow, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.mul_assoc, Nat.mul_assoc]

/-- Two rows without a difference have the same number in every lane below `leaf * 2 ^ levels`. -/
theorem lane_eq_of_differences {w W leaf : Nat} :
    ∀ {levels u v : Nat}, differences w W leaf levels u v = 0 →
      ∀ k, k < leaf * 2 ^ levels → lane w k u = lane W k v
  | 0, u, v, h, k, hk => by
      have h : Nat.rec (motive := fun _ => Nat) 0
          (fun k count =>
            Nat.add count
              (Bool.casesOn (motive := fun _ => Nat) (Nat.beq (lane w k u) (lane W k v)) 1 0))
          leaf = 0 := h
      have hloop : ∀ m : Nat,
          Nat.rec (motive := fun _ => Nat) 0
              (fun k count =>
                Nat.add count
                  (Bool.casesOn (motive := fun _ => Nat) (Nat.beq (lane w k u) (lane W k v)) 1 0))
              m = 0 →
            ∀ k < m, lane w k u = lane W k v := by
        intro m
        induction m with
        | zero => intro _ k hk; exact absurd hk (Nat.not_lt_zero _)
        | succ m ih =>
            intro hm k hk
            have hsplit := Nat.eq_zero_of_add_eq_zero hm
            rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hlt | rfl
            · exact ih hsplit.1 k hlt
            · have hlast := hsplit.2
              cases hb : Nat.beq (lane w k u) (lane W k v) with
              | true => exact Nat.eq_of_beq_eq_true hb
              | false => rw [hb] at hlast; exact absurd hlast (by decide)
      exact hloop leaf h k (by simpa using hk)
  | levels + 1, u, v, h, k, hk => by
      rw [differences_succ] at h
      obtain ⟨hlow, hhigh⟩ := Nat.eq_zero_of_add_eq_zero h
      by_cases hlt : k < leaf * 2 ^ levels
      · have := lane_eq_of_differences hlow k hlt
        rwa [lane_mod_lanes hlt, lane_mod_lanes hlt] at this
      · have hk' : k - leaf * 2 ^ levels < leaf * 2 ^ levels := by
          rw [Nat.pow_succ, ← Nat.mul_assoc] at hk
          omega
        have := lane_eq_of_differences hhigh (k - leaf * 2 ^ levels) hk'
        rwa [lane_shiftRight, lane_shiftRight,
          Nat.sub_add_cancel (Nat.le_of_not_lt hlt)] at this

/--
The closed check behind `lane_table`: the program runs on all pairs without an error in any
lane, and its row has no difference with the table in the first `leaf * 2 ^ levels ≥ n * n`
lanes.
-/
def tableCheck (w W n leaf levels depth table : Nat) (program : Expr) : Bool :=
  (fun F rows =>
    (fun result =>
      Nat.ble n (pow2 (Nat.sub W 1)) && (accepted F rows && (Nat.beq result.error 0 &&
        (Nat.ble (Nat.mul n n) (Nat.mul leaf (Nat.pow 2 levels)) &&
          Nat.beq (differences w W leaf levels table result.value) 0))))
      (program.run F (rowEnv rows)))
    (Machine.Frame.make W (Nat.mul n n) depth) (pairRows W n)

/--
A packed table with lanes of `w` bits is the table of the function `f` that a program denotes:
lane `a * n + b` holds `f a b`, for all indices below `n`, when `tableCheck` holds. The program
runs once on rows of `n * n` lanes of `W` bits, and the table is compared with its row.
-/
theorem lane_table {w W n leaf levels depth table : Nat} (hW : 2 ≤ W)
    (hdepth : W - 1 ≤ 2 ^ depth)
    (program : Expr) (f : Nat → Nat → Nat) (hs : program.Sound)
    (hf : ∀ x y, program.eval (push x (push y fun _ => 0)) = f x y)
    (hcheck : tableCheck w W n leaf levels depth table program = true) :
    ∀ a b : Fin n, lane w (a.val * n + b.val) table = f a.val b.val := by
  intro a b
  unfold tableCheck at hcheck
  simp only [Bool.and_eq_true] at hcheck
  obtain ⟨hsize, haccepted, herror, hcount, hsame⟩ := hcheck
  have hrow := lane_pairsRow_of hW hdepth program f hs hf hsize haccepted herror a b
  have hlt : a.val * n + b.val < leaf * 2 ^ levels :=
    lt_of_lt_of_le (pair_lt a.isLt b.isLt) (Nat.le_of_ble_eq_true hcount)
  exact (lane_eq_of_differences (Nat.eq_of_beq_eq_true hsame) _ hlt).trans hrow

end FloatLib.Numerics.Packed
