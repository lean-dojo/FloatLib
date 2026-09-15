/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import FloatLib.Numerics.Automation.Attributes
public import FloatLib.Numerics.Core.ExactSemantics
public import FloatLib.Numerics.Operation
public meta import Lean.Elab.Tactic.Omega

/-!
# Representation-independent numerical automation

`numerics` rewrites executable numerical expressions through proved semantic rules registered by
their concrete families, then discharges routine arithmetic and side conditions. Closed bit-level
evaluation is attempted only after semantic simplification. `numerics!` explicitly requests that
concrete phase even for goals with local variables.

The tactic never chooses a runtime backend and does not unfold optimized kernels on symbolic
goals. Numerical families keep direct monomorphic executable functions; this module only consumes
their proof theorems.
-/

public meta section

open Lean Elab Tactic

namespace FloatLib.Numerics

attribute [numerics_simps]
  NumericalSystem.At.denote
  NumericalSystem.AtFinite.represents
  NumericalSystem.exact_represents_iff
  ExactSemantics.decode_eq

attribute [aesop safe apply (rule_sets := [Numerics])]
  NumericalSystem.At.denote
  NumericalSystem.AtFinite.represents
  ExactSemantics.decode_eq

attribute [aesop unsafe 90% apply (rule_sets := [Numerics])]
  Operation.Total3.denote_eq
  Operation.Finite3.denote_eq
  Operation.Finite3If.denote_eq

attribute [aesop unsafe 95% apply (rule_sets := [Numerics])]
  Operation.Total3.denote

attribute [aesop unsafe 80% apply (rule_sets := [Numerics])]
  Operation.Total2.denote_eq
  Operation.Finite2.denote_eq
  Operation.Finite2If.denote_eq

attribute [aesop unsafe 85% apply (rule_sets := [Numerics])]
  Operation.Total2.denote

attribute [aesop unsafe 70% apply (rule_sets := [Numerics])]
  Operation.Total1.denote_eq
  Operation.Finite1.denote_eq
  Operation.Finite1If.denote_eq

attribute [aesop unsafe 75% apply (rule_sets := [Numerics])]
  Operation.Total1.denote

attribute [aesop unsafe 60% apply (rule_sets := [Numerics])]
  Operation.QuantizerOn.represents_eq

attribute [aesop unsafe 65% apply (rule_sets := [Numerics])]
  Operation.QuantizerOn.represents

open Aesop.BuiltinRules in
attribute [aesop safe -50 (rule_sets := [Numerics])] assumption

/--
Apply checked-operation eliminators through Lean's tactic elaborator.

These are tactic rules rather than indexed apply rules because the semantic operands are inferred
from the family contract, not from the displayed `Option.map` result.
-/
private meta def applyChecked3 : Aesop.RuleTac :=
  Aesop.RuleTac.ofTacticSyntax fun _ =>
    `(tactic| apply Operation.Checked3.map_denote_eq)

private meta def applyChecked3On : Aesop.RuleTac :=
  Aesop.RuleTac.ofTacticSyntax fun _ =>
    `(tactic| apply Operation.Checked3On.map_denote_eq)

private meta def applyChecked2 : Aesop.RuleTac :=
  Aesop.RuleTac.ofTacticSyntax fun _ =>
    `(tactic| apply Operation.Checked2.map_denote_eq)

private meta def applyChecked2On : Aesop.RuleTac :=
  Aesop.RuleTac.ofTacticSyntax fun _ =>
    `(tactic| apply Operation.Checked2On.map_denote_eq)

private meta def applyChecked1 : Aesop.RuleTac :=
  Aesop.RuleTac.ofTacticSyntax fun _ =>
    `(tactic| apply Operation.Checked1.map_denote_eq)

private meta def applyChecked1On : Aesop.RuleTac :=
  Aesop.RuleTac.ofTacticSyntax fun _ =>
    `(tactic| apply Operation.Checked1On.map_denote_eq)

attribute [aesop unsafe 99% tactic (rule_sets := [Numerics])]
  applyChecked3 applyChecked3On

attribute [aesop unsafe 90% tactic (rule_sets := [Numerics])]
  applyChecked2 applyChecked2On

attribute [aesop unsafe 80% tactic (rule_sets := [Numerics])]
  applyChecked1 applyChecked1On

/-- Close arithmetic side conditions created while selecting a numerical operation contract. -/
private meta def closeNumericsByNormNum : Aesop.RuleTac :=
  Aesop.SingleRuleTac.toRuleTac fun input => do
    let tactic := do
      Mathlib.Meta.NormNum.elabNormNum .missing .missing .missing
    let goals ← Lean.Elab.Tactic.run input.goal tactic |>.run'
    if !goals.isEmpty then
      failure
    pure (#[], none, some .hundred)

attribute [aesop unsafe 10% tactic (rule_sets := [Numerics])]
  closeNumericsByNormNum

/-- Normalize a concrete numerical goal and discharge closed arithmetic and bit-vector facts. -/
syntax (name := numericsReduce) "numerics_reduce" : tactic

macro_rules
| `(tactic| numerics_reduce) =>
    `(tactic|
      (simp (config := { decide := true }) [numerics_reduction, numerics_side]
       all_goals try norm_num
       all_goals try field_simp
       all_goals try norm_num
       all_goals try omega))

private def reduceClosedGoals : TacticM Unit := do
  let goals ← getUnsolvedGoals
  let mut remaining := #[]
  for goal in goals do
    if ← goal.isAssigned then
      continue
    setGoals [goal]
    let closed ← withMainContext do
      let target ← instantiateMVars (← getMainTarget)
      pure !target.hasFVar
    if closed then
      try
        evalTactic (← `(tactic| numerics_reduce))
      catch _ =>
        pure ()
    remaining := remaining ++ (← getUnsolvedGoals)
  setGoals remaining.toList

/-- Simplify numerical semantics and search the registered operation contracts. -/
private def simplifyNumerics : TacticM Unit := do
  evalTactic (← `(tactic|
    (simp_all (config := { decide := true }) (failIfUnchanged := false)
      only [numerics_simps, numerics_side]
     all_goals try norm_num
     all_goals try omega)))
  reduceClosedGoals
  evalTactic (← `(tactic|
    all_goals try (
      aesop (rule_sets := [Numerics, -default])
        (erase Aesop.BuiltinRules.ext)
        (config := {
          maxRuleApplications := 32
          warnOnNonterminal := false
          enableSimp := false
          enableUnfold := false
        }))))

/--
Expose registered numerical semantics and solve routine arithmetic, range, and closed encoding
goals without unfolding executable kernels on symbolic expressions.
-/
elab (name := numerics) "numerics" : tactic => do
  simplifyNumerics
  reduceClosedGoals

/-- Force concrete carrier reduction after the ordinary semantic phase. -/
elab (name := numericsBang) "numerics!" : tactic => do
  simplifyNumerics
  evalTactic (← `(tactic| all_goals try numerics_reduce))

/--
Construct a proof-indexed numerical view from a runtime code.

The expected type determines the numerical system and semantic value. The proof component is
erased, so the resulting runtime data is exactly `code`.
-/
syntax (name := numericsRefine) "numerics_refine" term : term

macro_rules
| `(numerics_refine $code) => `(⟨$code, by numerics⟩)

end FloatLib.Numerics
