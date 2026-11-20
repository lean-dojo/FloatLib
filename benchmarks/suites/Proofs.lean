/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

import FloatLib.Tactic.Interval
import FloatLib.Tactic.Roundoff
import FloatLib.Floats.Formats.BinaryInterchange.Configured
import FloatLib.Floats.Formats.BinaryInterchange.Configured.CorrectlyRounded
import FloatLib.Floats.Formats.BinaryInterchange.Complex.Core
public meta import Lean.Util.CollectAxioms
public meta import Lean.Elab.Command
public meta import Lean.Elab.Tactic

/-!
# Sequential proof benchmark runner

`FLOATLIB_SUITE_PLAN` names a JSON array of cases with `id`, `declaration`, and `commands` fields.
Each case elaborates in a fresh copy of the imported environment. Success requires a theorem
without any axiom other than `propext`, `Classical.choice`, and `Quot.sound`. The complete statement,
axioms, and elapsed elaboration time go to `FLOATLIB_SUITE_OUTPUT` as JSON lines. An error is data:
it cannot produce a successful row or contaminate the next case.

The Python driver hashes the input plan and every source dependency before running this file.
This is a benchmark of elaboration, not a persistent library declaration or a trusted data import.

The runner is a `module`, so each case elaborates as it does in a module of the library: with
the exported declarations of its imports. A plain file also loads their private ones, which
takes about twice the memory, and it can unfold Mathlib's private definitions of the arithmetic
and the order of the reals, so a unification of two real numerals recurses until Lean's limit.
-/

open Lean Elab Command
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

/-- Normalize concrete format constants using existing library equalities. -/
elab "suite_format" : tactic => do
  -- Binary64's subnormal scale needs exponents through 1075.
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    set_option exponentiation.threshold 2048 in
    norm_num [Model.toReal_posMaxFinite, Model.unitRoundoffAt_eq, Model.underflowErrorAt_eq,
      Model.pow2, Model.bpow, FloatLib.Floats.Formats.Flocq.bpow,
      FloatLib.Numerics.binaryRadix, FloatLib.Numerics.Radix.toReal,
      FloatFormat.binary32, FloatFormat.binary64,
      FloatFormat.maxFiniteFracField, FloatFormat.fracMaskNat,
      FloatFormat.maxNormalExponent, FloatFormat.maxFiniteExpField,
      FloatFormat.Encoding.maxFiniteExponent,
      FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
      FloatFormat.Encoding.defaultBias, FloatFormat.ieeeBias]))

/-- Discharge a range premise through a checked, conservative format bound. -/
elab "suite_range" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    first
    | assumption
    | (have hmax : (2 : ℝ) ^ 100 ≤
          Model.toReal (Model.posMaxFinite FloatFormat.binary32) := by
         rw [Model.toReal_posMaxFinite]
         suite_format
       apply le_trans (b := (2 : ℝ) ^ 100) ?_ hmax
       norm_num <;> interval)
    | (have hmax : (2 : ℝ) ^ 1000 ≤
          Model.toReal (Model.posMaxFinite FloatFormat.binary64) := by
         rw [Model.toReal_posMaxFinite]
         suite_format
       apply le_trans (b := (2 : ℝ) ^ 1000) ?_ hmax
       suite_format <;> interval)
    | (suite_format <;> interval)))

private meta def field (json : Json) (key : String) : CommandElabM String :=
  match json.getObjValAs? String key with
  | .ok value => pure value
  | .error error => throwError "{error}"

-- A case must finish elaborating before its diagnostics are inspected or its state is restored.
set_option Elab.async false in
run_cmd do
  let some planPath ← IO.getEnv "FLOATLIB_SUITE_PLAN"
    | throwError "FLOATLIB_SUITE_PLAN is required"
  let some outputPath ← IO.getEnv "FLOATLIB_SUITE_OUTPUT"
    | throwError "FLOATLIB_SUITE_OUTPUT is required"
  let .ok plan := Json.parse (← IO.FS.readFile planPath)
    | throwError "Invalid plan JSON"
  let .ok cases := plan.getArr?
    | throwError "The plan must be an array"
  let output ← IO.FS.Handle.mk outputPath .append
  for item in cases do
    let id ← field item "id"
    if let some activePath ← IO.getEnv "FLOATLIB_SUITE_ACTIVE" then
      IO.FS.writeFile activePath id
    let declaration ← field item "declaration"
    let .ok commands := item.getObjValAs? (Array String) "commands"
      | throwError "Missing commands for {id}"
    let saved : Command.State ← get
    let start ← IO.monoNanosNow
    let mut status := "proved"
    let mut reason := ""
    let mut statement := ""
    let mut dependencies : Array String := #[]
    try
      for text in commands do
        let .ok command := Parser.runParserCategory (← getEnv) `command text
          | throwError "Invalid command: {text}"
        elabCommand command
      let messages := (← get).messages.toList.filter (fun msg => msg.severity == .error)
      unless messages.isEmpty do
        let errors ← messages.mapM (fun msg => msg.data.toString)
        throwError "{String.intercalate "\n" errors}"
      -- A declaration of a module is private to it unless its command says otherwise.
      let stated := declaration.toName
      let environment ← getEnv
      let name := if environment.contains stated then stated else mkPrivateName environment stated
      let some (.thmInfo info) := (← getEnv).find? name
        | throwError "Expected theorem {declaration}"
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
          throwError "Unexpected axiom: {dependency}"
      dependencies := axioms.map Name.toString
      statement ← liftTermElabM do
        withOptions (fun options =>
            options.set `pp.maxDepth (100000 : Nat) |>.set `pp.maxSteps (10000000 : Nat)) do
          return (← Meta.ppExpr info.type).pretty 120
    catch error =>
      status := "refused"
      reason ← error.toMessageData.toString
    let elapsed := (← IO.monoNanosNow) - start
    set saved
    let row := Json.mkObj [
      ("id", toJson id), ("status", toJson status), ("reason", toJson reason),
      ("elapsed_ns", toJson elapsed), ("statement", toJson statement),
      ("axioms", toJson dependencies)]
    output.putStrLn row.compress
    output.flush
