/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
import Lean

/-!
# Harness for timing reduction in Lean's kernel

`#kernel_bench "tag" reps term` reduces `term` to weak head normal form with Lean's kernel (the
proof checker, `Lean.Kernel.whnf`), `reps` times, each time with a fresh kernel state, and prints
one line `KBENCH tag <fastest time in nanoseconds> <value>`. Nothing is compiled: this is the work
`decide +kernel` makes the kernel do.

`operandTable% ew fw bias inf nan cls kind n` elaborates to a literal list of `n` operand triples
(natural-number encodings) for a binary format with `ew` exponent bits, `fw` fraction bits and the
given bias. `inf` and `nan` say whether the encoding has infinities and NaNs. `cls` is `normal`,
`subnormal` or `special`, and `kind` is `additive`, `multiplicative`, `fused` or `root`. In the
subnormal class the second operand is subnormal for sums, normal for products and quotients, and
the third is subnormal for a fused multiply-add. With `root` the first operand of the normal and
subnormal classes is positive, so that a square root is taken of a value in its domain.
-/

open Lean Elab Command Term Meta

namespace FloatLibBenchmarks.KernelReduction

/-- Operand class of one benchmark row. -/
inductive OperandClass where
  | normal | subnormal | special
  deriving Repr, DecidableEq

/-- How an operation combines its operands, which decides the subnormal operand table. -/
inductive OperandKind where
  | additive | multiplicative | fused | root
  deriving Repr, DecidableEq

/-- The parameters of a sign/exponent/fraction layout that the operand tables need. -/
structure Layout where
  expWidth : Nat
  fracWidth : Nat
  bias : Nat
  hasInfinity : Bool
  hasNaN : Bool

/-- Pack a sign, an exponent field and a fraction reduced to the fraction width. -/
def Layout.word (l : Layout) (sign exponent fraction : Nat) : Nat :=
  sign * 2 ^ (l.expWidth + l.fracWidth) + exponent * 2 ^ l.fracWidth +
    fraction % 2 ^ l.fracWidth

/-- Zeros, the smallest subnormal, one, the largest finite value, and the infinities and NaNs the
encoding has. -/
def Layout.specials (l : Layout) : Array Nat :=
  let top := 2 ^ l.expWidth - 1
  let sign := 2 ^ (l.expWidth + l.fracWidth)
  let finite := #[0, sign, 1, l.word 0 l.bias 0,
    if l.hasInfinity then l.word 0 (top - 1) (2 ^ l.fracWidth - 1)
    else if l.hasNaN then l.word 0 top (2 ^ l.fracWidth - 2)
    else l.word 0 top (2 ^ l.fracWidth - 1)]
  let infinities := if l.hasInfinity then #[l.word 0 top 0, l.word 1 top 0] else #[]
  let nans :=
    if l.hasInfinity then #[l.word 0 top (2 ^ (l.fracWidth - 1)), l.word 1 top 1]
    else if l.hasNaN then #[l.word 0 top (2 ^ l.fracWidth - 1)]
    else #[]
  finite ++ infinities ++ nans

/-- `n` deterministic operand triples of one class. -/
def Layout.operands (l : Layout) (cls : OperandClass) (kind : OperandKind) (n : Nat) :
    List (Nat × Nat × Nat) :=
  (List.range n).map fun i =>
    let m1 := i * 2654435761 + 12345
    -- The terms in `i / 8` and `i / 16` keep the triples of a narrow format distinct beyond the
    -- first eight, since the kernel remembers a repeated computation.
    let m2 := (i * 40503 + i / 8 * 2654435769 + 977) * 7919
    let m3 := (i * 69069 + 1) * 31
    let subnormal (m : Nat) := 1 + m % (2 ^ l.fracWidth - 1)
    let sign := if kind = .root then 0 else i % 2
    match cls with
    | .normal =>
        (l.word sign (l.bias + (if kind = .root then i % 5 else i / 16 % 4)) m1,
          l.word 0 (l.bias + 1 - i % 3) m2, l.word (i / 2 % 2) (l.bias - 1 + i % 2) m3)
    | .subnormal =>
        let second :=
          match kind with
          | .additive | .root => l.word (i / 2 % 2) 0 (subnormal m2)
          | .multiplicative | .fused => l.word 0 (l.bias - i % 2) m2
        (l.word sign 0 (subnormal m1), second, l.word 0 0 (subnormal m3))
    | .special =>
        let s := l.specials
        (s[i % s.size]!, s[(3 * i + 1) % s.size]!, s[(5 * i + 2) % s.size]!)

declare_syntax_cat operand_class
syntax "normal" : operand_class
syntax "subnormal" : operand_class
syntax "special" : operand_class
declare_syntax_cat operand_kind
syntax "additive" : operand_kind
syntax "multiplicative" : operand_kind
syntax "fused" : operand_kind
syntax "root" : operand_kind

/-- A literal list of operand triples, computed while elaborating. -/
syntax (name := operandTable) "operandTable% " num num num ident ident operand_class operand_kind
  num : term

@[term_elab operandTable] def elabOperandTable : TermElab := fun stx _ => do
  match stx with
  | `(operandTable% $ew $fw $bias $inf $nan $cls $kind $n) =>
      let flag (i : Ident) : TermElabM Bool :=
        match i.getId with
        | `true => pure true
        | `false => pure false
        | _ => throwErrorAt i "expected `true` or `false`"
      let cls ← match cls with
        | `(operand_class| normal) => pure OperandClass.normal
        | `(operand_class| subnormal) => pure OperandClass.subnormal
        | _ => pure OperandClass.special
      let kind ← match kind with
        | `(operand_kind| additive) => pure OperandKind.additive
        | `(operand_kind| multiplicative) => pure OperandKind.multiplicative
        | `(operand_kind| root) => pure OperandKind.root
        | _ => pure OperandKind.fused
      let layout : Layout :=
        { expWidth := ew.getNat, fracWidth := fw.getNat, bias := bias.getNat
          hasInfinity := ← flag inf, hasNaN := ← flag nan }
      return toExpr (layout.operands cls kind n.getNat)
  | _ => throwUnsupportedSyntax

/--
Fold an operation over a table of operand encodings and add up the result encodings.

`ofBits` and `toBits` are the format's conversions from and to its natural-number encoding. The
operation receives all three operands, and a no-operation run (`fun x _ _ => x`) over the same
table measures the cost of the fold and the conversions.
-/
def run {F : Type} (ofBits : Nat → F) (toBits : F → Nat) (op : F → F → F → F)
    (table : List (Nat × Nat × Nat)) : Nat :=
  table.foldl
    (fun acc t => Nat.add acc (toBits (op (ofBits t.1) (ofBits t.2.1) (ofBits t.2.2)))) 0

/--
`#kernel_bench "tag" reps term` reduces `term` with Lean's kernel `reps` times and prints
`KBENCH tag <fastest nanoseconds> <weak head normal form>`.

`#kernel_bench "tag" reps rewriting [f, g] term` first rewrites `term`, a natural number, as
`float_decide` rewrites a goal: with the rules tagged `@[kernel_optimize]`, after unfolding the
definitions `f` and `g`. The kernel then reduces the rewritten term, which is what it checks in
a proof by `float_decide`.
-/
syntax (name := kernelBench) "#kernel_bench " str num (" rewriting " "[" ident,* "]")? term :
  command

elab_rules : command
  | `(#kernel_bench $tag:str $reps:num $[rewriting [$names,*]]? $t:term) => do
  let e ← liftTermElabM do
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    match names with
    | none => pure e
    | some names =>
        let lemmas ← names.getElems.mapM fun name =>
          `(Lean.Parser.Tactic.simpLemma| $name:ident)
        let goal ← mkFreshExprSyntheticOpaqueMVar (← mkEq e (mkNatLit 0))
        let remaining ← Tactic.run goal.mvarId! do
          Tactic.evalTactic (← `(tactic|
            set_option backward.isDefEq.respectTransparency false in
            simp (failIfUnchanged := false) only [kernel_optimize, $lemmas,*]))
        let [rewritten] := remaining
          | throwError "the rewrite did not leave one goal"
        let some (_, lhs, _) := (← instantiateMVars (← rewritten.getType)).eq?
          | throwError "the rewrite did not leave an equation"
        pure lhs
  let env ← getEnv
  let mut best : Nat := 0
  let mut value : Expr := e
  for i in [0:reps.getNat] do
    let start ← IO.monoNanosNow
    match Kernel.whnf env {} e with
    | .ok v =>
        let stop ← IO.monoNanosNow
        value := v
        if i == 0 || stop - start < best then best := stop - start
    | .error _ => throwError "the kernel failed to reduce the term"
  logInfo m!"KBENCH {tag.getString} {best} {value}"

end FloatLibBenchmarks.KernelReduction
