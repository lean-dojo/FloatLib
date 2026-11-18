/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
import Lean

/-!
# Harness for timing exact arithmetic in Lean's kernel

`#kernel_op "tag" (sizes := [64, 256]) (count := 8) (reps := 3) f` times the function `f` in
Lean's kernel (`Lean.Kernel.whnf`, the reduction that `decide +kernel` and `rfl` run). `f` takes
natural numbers and returns a `Nat` or a `Bool`. For each size the command builds `count`
applications of `f` to pseudo-random natural-number literals of exactly that many bits, reduces
them all with one fresh kernel state per repetition, and prints one line

`KOP tag bits=<size> ns=<fastest total / count> warm=<the same in one kernel state> value=<digest>`.

`ns` gives each application a fresh kernel state, so it includes what a first use pays (unfolding
each definition once, constants that depend on a width). `warm` reduces the sum of all `count`
results in one kernel state, as one proof would, so definitions and constants are shared; it is
the cost of one more operation inside a proof that already did one.

The operands are literals, so their construction costs the kernel nothing, and a function that
needs integers or fractions builds them from the naturals inside the kernel (`Int.ofNat a`), as
a certificate would. The operands depend only on the tag-free seed, the size and the index, so
two runs, and two functions with the same seed, see the same numbers.

`#kernel_term "tag" (reps := 3) t` times one closed term the same way and prints
`KTERM tag ns=<fastest> value=<value>`.

`#time_command "tag" in cmd` elaborates the command `cmd` once and prints
`KCMD tag ns=<elapsed> errors=<whether it logged an error>`: the time a user waits for one
`example` or `theorem`, with the tactic, the kernel check and the addition to the environment.
-/

open Lean Elab Command Term Meta

namespace FloatLibBenchmarks.Exact

/-- One step of the 64-bit generator of Marsaglia's xorshift family. -/
def xorshift (s : UInt64) : UInt64 :=
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  s ^^^ (s <<< 17)

/-- A natural number of exactly `bits` bits from the state `seed`, and the next state. -/
def randomNat (seed : UInt64) (bits : Nat) : Nat × UInt64 := Id.run do
  let mut s := seed
  let mut n := 0
  for _ in [0:(bits + 63) / 64] do
    s := xorshift s
    n := n <<< 64 ||| s.toNat
  if bits = 0 then return (0, s)
  return ((n % 2 ^ bits) ||| 2 ^ (bits - 1), s)

/-- The first forty characters of a value, for the digest column. -/
def digest (e : Expr) : String :=
  let s := toString e
  if s.length ≤ 40 then s else (s.take 40).toString ++ "…"

/-- Reduce every term in a fresh kernel state, `reps` times; the fastest total of one
repetition, and the values. -/
def timeAll (env : Environment) (terms : Array Expr) (reps : Nat) : IO (Nat × Array Expr) := do
  let mut best := 0
  let mut values := #[]
  for rep in [0:reps] do
    let start ← IO.monoNanosNow
    let mut out := #[]
    for t in terms do
      match Kernel.whnf env {} t with
      | .ok v => out := out.push v
      | .error _ => throw <| IO.userError "kernel reduction failed"
    let stop ← IO.monoNanosNow
    if rep = 0 || stop - start < best then best := stop - start
    values := out
  return (best, values)

/-- The arity of a function type whose arguments are all `Nat`. -/
partial def natArity (type : Expr) : Nat :=
  match type with
  | .forallE _ d b _ => if d.isConstOf ``Nat then 1 + natArity b else 0
  | _ => 0

syntax (name := kernelOp) "#kernel_op " str (" (" &"sizes" " := " "[" num,* "]" ")")?
  (" (" &"count" " := " num ")")? (" (" &"reps" " := " num ")")? (" (" &"seed" " := " num ")")?
  ppSpace term : command

@[command_elab kernelOp] def elabKernelOp : CommandElab := fun stx => do
  let tag := stx[1].isStrLit?.getD ""
  let sizes : Array Nat :=
    if stx[2].isNone then #[64, 256, 1024, 4096]
    else stx[2][4].getSepArgs.map fun s => s.isNatLit?.getD 0
  let count := if stx[3].isNone then 8 else stx[3][3].isNatLit?.getD 8
  let reps := if stx[4].isNone then 3 else stx[4][3].isNatLit?.getD 3
  let seed := if stx[5].isNone then 2026 else stx[5][3].isNatLit?.getD 2026
  let f ← liftTermElabM do
    let f ← Term.elabTerm stx[6] none
    Term.synthesizeSyntheticMVarsNoPostponing
    let f ← instantiateMVars f
    if f.hasMVar || f.hasSorry then throwError "#kernel_op: the term is not fully elaborated"
    return f
  let arity ← liftTermElabM do return natArity (← whnf (← inferType f))
  let env ← getEnv
  for size in sizes do
    let mut state : UInt64 := UInt64.ofNat (seed * 1000003 + size * 7919 + 88172645463325252)
    let mut terms := #[]
    for _ in [0:count] do
      let mut t := f
      for _ in [0:arity] do
        let (n, next) := randomNat state size
        state := next
        t := mkApp t (mkRawNatLit n)
      terms := terms.push t
    let (best, values) ← timeAll env terms reps
    -- One state for all: the sum of the results, a Boolean counted as zero or one.
    let isBool := match values[0]? with
      | some v => v.isConstOf ``Bool.true || v.isConstOf ``Bool.false
      | none => false
    let asNat (t : Expr) : Expr :=
      if isBool then
        mkApp4 (mkConst ``Bool.rec [Level.one]) (mkLambda `_ .default (mkConst ``Bool) (mkConst ``Nat))
          (mkRawNatLit 0) (mkRawNatLit 1) t
      else t
    let total := terms.foldl (fun acc t => mkApp2 (mkConst ``Nat.add) acc (asNat t)) (mkRawNatLit 0)
    let (warm, _) ← timeAll env #[total] reps
    let shown := values.foldl (fun acc v => acc ++ " " ++ digest v) ""
    logInfo m!"KOP {tag} bits={size} ns={best / count} warm={warm / count} \
      value={(shown.take 50).toString}"

syntax (name := kernelTerm) "#kernel_term " str (" (" &"reps" " := " num ")")? ppSpace term :
  command

@[command_elab kernelTerm] def elabKernelTerm : CommandElab := fun stx => do
  let tag := stx[1].isStrLit?.getD ""
  let reps := if stx[2].isNone then 3 else stx[2][3].isNatLit?.getD 3
  let t ← liftTermElabM do
    let t ← Term.elabTerm stx[3] none
    Term.synthesizeSyntheticMVarsNoPostponing
    let t ← instantiateMVars t
    if t.hasMVar || t.hasSorry then throwError "#kernel_term: the term is not fully elaborated"
    return t
  let (best, values) ← timeAll (← getEnv) #[t] reps
  logInfo m!"KTERM {tag} ns={best} value={digest values[0]!}"

syntax (name := timeCommand) "#time_command " str " in " command : command

@[command_elab timeCommand] def elabTimeCommand : CommandElab := fun stx => do
  let tag := stx[1].isStrLit?.getD ""
  let before := (← get).messages
  let start ← IO.monoNanosNow
  elabCommand stx[3]
  let stop ← IO.monoNanosNow
  let failed := (← get).messages.hasErrors && !before.hasErrors
  logInfo m!"KCMD {tag} ns={stop - start} errors={failed}"

end FloatLibBenchmarks.Exact
