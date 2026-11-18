/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import Lean.Elab.Command
public meta import Lean.Meta.Basic
public import FloatLib.Numerics.Packed.Basic

/-!
# Kernel reduction of closed data

These utilities read closed data through Lean's kernel and measure or normalize the result.
They do not execute compiled replacements.
-/

@[expose] public meta section

namespace FloatLib.Numerics.Packed

open Lean Meta

/-- Kernel reduction of a closed term to weak head normal form. It needs no compiled code and runs
the kernel's fast paths on natural-number literals, so commands and tactics read the data of a
certificate with it: `packed_values` reads decoded values and `interval` reads coefficients. -/
def kernelWhnf (e : Expr) : MetaM Expr := do
  match Kernel.whnf (← getEnv) (← getLCtx) e with
  | .ok e => pure e
  | .error ex => throwKernelException ex

/-- The value of a closed natural-number term, by kernel reduction. -/
def natValue (e : Expr) : MetaM Nat := do
  match ← kernelWhnf e with
  | .lit (.natVal n) => pure n
  | e => throwError "could not evaluate the natural number {e}"

/-- The value of a closed integer term, by kernel reduction. -/
def intValue (e : Expr) : MetaM Int := do
  let e ← kernelWhnf e
  match e.getAppFnArgs with
  | (``Int.ofNat, #[t]) => return (← natValue t)
  | (``Int.negSucc, #[t]) => return -((← natValue t : Int) + 1)
  | _ => throwError "could not evaluate the integer {e}"

/-- The value of a closed rational term, by kernel reduction. -/
def ratValue (e : Expr) : MetaM Rat := do
  let e ← kernelWhnf e
  match e.getAppFnArgs with
  | (``Rat.mk', #[num, den, _, _]) => return mkRat (← intValue num) (← natValue den)
  | _ => throwError "could not evaluate the rational {e}"

/-- The elements of a closed list term, by kernel reduction of its spine. -/
partial def listValues (e : Expr) (acc : Array Expr := #[]) : MetaM (Array Expr) := do
  let e ← kernelWhnf e
  match e.getAppFnArgs with
  | (``List.nil, _) => return acc
  | (``List.cons, #[_, hd, tl]) => listValues tl (acc.push hd)
  | _ => throwError "could not evaluate the list {e}"

end FloatLib.Numerics.Packed

namespace FloatLib.Floats.ExecFloat.KernelPath

open Lean Meta

/--
Normalize `term` with the kernel: weak head normal form, then the same for every constructor
argument that is data (not a type, a proof or a function).
-/
partial def kernelNormalize (term : Expr) : MetaM Expr := do
  let value ← FloatLib.Numerics.Packed.kernelWhnf term
  let .const name _ := value.getAppFn | return value
  let some (.ctorInfo info) := (← getEnv).find? name | return value
  let mut arguments := value.getAppArgs
  for index in [info.numParams:arguments.size] do
    let argument := arguments[index]!
    let type ← whnf (← inferType argument)
    if type.isSort || type.isForall || (← isProp type) then
      continue
    arguments := arguments.set! index (← kernelNormalize argument)
  return mkAppN value.getAppFn arguments

/--
The median time in nanoseconds of the kernel evaluations of a closed term to weak head normal
form, and that normal form: one evaluation to warm up, then as many as fit in about 20 ms, at
least 3 and at most 200.
-/
def kernelTime (term : Expr) : MetaM (Nat × Expr) := do
  let run : MetaM (Nat × Expr) := do
    let start ← IO.monoNanosNow
    let value ← FloatLib.Numerics.Packed.kernelWhnf term
    return ((← IO.monoNanosNow) - start, value)
  let (first, value) ← run
  let repetitions := max 3 (min 200 (20000000 / max first 1))
  let mut times : Array Nat := #[]
  for _ in [0:repetitions] do
    times := times.push (← run).1
  return ((times.qsort (· < ·))[repetitions / 2]!, value)

/-- A time in nanoseconds, printed in microseconds with one decimal. -/
def microseconds (nanos : Nat) : String :=
  s!"{nanos / 1000}.{nanos % 1000 / 100} µs"

end FloatLib.Floats.ExecFloat.KernelPath
