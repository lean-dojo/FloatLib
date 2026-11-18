/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Tactic.Roundoff.Backward.Analyze

/-!
# Statements from the backward analysis

`inferBackward` runs the backward analysis of a computation and concludes one of two statements.

* The backward-error statement (`conclude`): there are perturbations `δ`, each within its bound,
  such that the computed value is the exact computation on the inputs `x * (1 + δ)`, up to the
  absolute error of the analysis. An input that is read more than once takes one perturbation;
  when its reads took different ones, the analysis is run again with that input unperturbed.
* The forward bound in closed form (`concludeClosed`): the distance between the computed value
  and the exact computation on the inputs is at most what the perturbations change
  (`Tree.deviation`) plus the absolute error. A perturbed read `x * (1 + δ)` with `|δ| ≤ b`
  changes at most `b * |x|`, and a loop accumulates the changes of its steps through the exact
  loop (`List.abs_foldl_sub_foldl_le`), as a sum when the step adds to its accumulator. The
  analysis is run for a forward bound (`Config.forward`): each read is bounded by itself, so
  exact constants and inputs that every step reads may take roundings, a rounding that an
  operation cannot pass on stays on its result (`Tree.unit`), and the exponential and the
  logarithm of a computed value are followed (`Tree.apply`). A perturbed divisor or argument of
  a logarithm adds the premise that its change is below its magnitude.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.Roundoff

open Lean Meta Elab Tactic Qq
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

namespace Backward

/-- What the perturbations of an exact computation change. -/
structure Deviation where
  /-- The computation on perturbed inputs. -/
  reference : Q(ℝ)
  /-- The computation on the inputs themselves. -/
  exact : Q(ℝ)
  /-- A bound of their distance; the literal zero when nothing is perturbed. -/
  bound : Q(ℝ)
  /-- A proof of `|reference - exact| ≤ bound`. -/
  proof : Lean.Expr

/-- Simplify the bound of `deviation` with the identities of zero and one. -/
def Deviation.tidy (deviation : Deviation) : MetaM Deviation := do
  let (bound, proof) ← tidyBound deviation.bound deviation.proof
  return { deviation with bound, proof }

/-- The bound of the real perturbation `delta`, which took `growth` by `bound`, as the statement
shows it, with its proof. -/
def statedOf (delta growth bound : Lean.Expr) : BackM (Q(ℝ) × Lean.Expr) := do
  let (shape, proof) ← statedLeaf delta growth bound
  let growth : Q(ℝ) := growth
  match shape with
  | .real _ (some stated) => return (stated, proof)
  | _ => return (q($growth - 1), proof)

mutual

/-- What the perturbations change in the exact computation `tree`: a bound of the distance
between the computation on perturbed inputs and the computation on the inputs themselves, in
terms of the exact values and the bounds of the perturbations. The reads and loops are those of
the state. A perturbed divisor adds the premise that its change is below its magnitude, and has
no such bound inside a loop step. -/
partial def Tree.deviation (tree : Tree) : BackM Deviation := do
  let unchanged (value : Q(ℝ)) : BackM Deviation :=
    return ⟨value, value, q(0), ← mkAppM ``FloatLib.Numerics.exact_error #[value]⟩
  match tree with
  | .const value _ _ => unchanged value
  | .acc => unchanged (← tree.render)
  | .slot index =>
    let slot := (← get).slots[index]!
    let key := slot.key
    match slot.delta?, slot.bound? with
    | some delta, some bound =>
      let (stated, proof) ← statedOf delta slot.growth bound
      let delta : Q(ℝ) := delta
      return ⟨q($key * (1 + $delta)), key, q(|$key| * $stated),
        ← mkAppM ``FloatLib.Numerics.Backward.deviation_leaf #[key, proof]⟩
    | _, _ => unchanged key
  | .add left right =>
    let left ← left.deviation
    let right ← right.deviation
    let (x, y, r, s, a, b) :=
      (left.reference, right.reference, left.exact, right.exact, left.bound, right.bound)
    Deviation.tidy ⟨q($x + $y), q($r + $s), q($a + $b),
      ← mkAppM ``FloatLib.Numerics.Backward.add #[left.proof, right.proof]⟩
  | .sub left right =>
    -- `exp s - 1 - s` moves with its argument by its derivative, not term by term.
    if let .sub (.apply function inner) one := left then
      let unperturbedOne ← match one with
        | .const value _ _ => pure (value.nat? == some 1)
        | .slot index =>
          let slot := (← get).slots[index]!
          pure (slot.key.nat? == some 1 && slot.delta?.isNone)
        | _ => pure false
      if function == ``Real.exp && unperturbedOne && (← inner.render) == (← right.render) then
        let operand ← inner.deviation
        let (x, r, a) := (operand.reference, operand.exact, operand.bound)
        return ← Deviation.tidy ⟨q(Real.exp $x - 1 - $x), q(Real.exp $r - 1 - $r),
          q((Real.exp (|$r| + $a) - 1) * $a),
          ← mkAppM ``FloatLib.Numerics.Backward.deviation_exp_sub_one_sub #[operand.proof]⟩
    let left ← left.deviation
    let right ← right.deviation
    let (x, y, r, s, a, b) :=
      (left.reference, right.reference, left.exact, right.exact, left.bound, right.bound)
    Deviation.tidy ⟨q($x - $y), q($r - $s), q($a + $b),
      ← mkAppM ``FloatLib.Numerics.Backward.sub #[left.proof, right.proof]⟩
  | .neg operand =>
    let operand ← operand.deviation
    let (x, r) := (operand.reference, operand.exact)
    return { operand with
      reference := q(-$x), exact := q(-$r)
      proof := ← mkAppM ``FloatLib.Numerics.Backward.neg #[operand.proof] }
  | .mul left right =>
    let left ← left.deviation
    let right ← right.deviation
    let (x, y, r, s, a, b) :=
      (left.reference, right.reference, left.exact, right.exact, left.bound, right.bound)
    Deviation.tidy ⟨q($x * $y), q($r * $s), q($a * (|$s| + $b) + |$r| * $b),
      ← mkAppM ``FloatLib.Numerics.Backward.deviation_mul #[left.proof, right.proof]⟩
  | .div left right =>
    let left ← left.deviation
    let right ← right.deviation
    let (x, y, r, s, a, b) :=
      (left.reference, right.reference, left.exact, right.exact, left.bound, right.bound)
    if b.nat? == some 0 then
      return ← Deviation.tidy ⟨q($x / $y), q($r / $s), q($a / |$y|),
        ← mkAppM ``FloatLib.Numerics.Backward.div #[left.proof, right.proof]⟩
    -- A perturbed divisor must stay away from zero: that is a premise of the statement.
    if (← get).accumulator?.isSome then
      throwError "roundoff: the divisor `{right.exact}` is perturbed inside a loop step, and the \
        closed forward bound does not divide by a perturbed value there. Use `roundoff mixed \
        theorem`."
    let apart ← mkFreshExprMVar q($b < |$s|)
    modifyThe Analysis fun analysis =>
      { analysis with pending := analysis.pending.push apart.mvarId! }
    Deviation.tidy ⟨q($x / $y), q($r / $s), q(($a * |$s| + |$r| * $b) / (|$s| * (|$s| - $b))),
      ← mkAppM ``FloatLib.Numerics.Backward.deviation_div #[left.proof, right.proof, apart]⟩
  | .ite condition decidable positive negative =>
    let positive ← positive.deviation
    let negative ← negative.deviation
    let branch (first second : Q(ℝ)) : Q(ℝ) :=
      mkApp5 (mkConst `ite [Level.one]) q(ℝ) condition decidable first second
    Deviation.tidy ⟨branch positive.reference negative.reference,
      branch positive.exact negative.exact, branch positive.bound negative.bound,
      ← mkAppOptM ``FloatLib.Numerics.Backward.branch #[none, none, none, none,
        some condition, some decidable, none, none, some positive.proof, some negative.proof]⟩
  | .sqrt operand =>
    let operand ← operand.deviation
    let (x, r, a) := (operand.reference, operand.exact, operand.bound)
    Deviation.tidy ⟨q(Real.sqrt $x), q(Real.sqrt $r), q(Real.sqrt $a),
      ← mkAppM ``FloatLib.Numerics.Backward.sqrt #[operand.proof]⟩
  | .lattice upper left right =>
    let left ← left.deviation
    let right ← right.deviation
    let (x, y, r, s, a, b) :=
      (left.reference, right.reference, left.exact, right.exact, left.bound, right.bound)
    let (reference, exact) : Q(ℝ) × Q(ℝ) :=
      if upper then (q(max $x $y), q(max $r $s)) else (q(min $x $y), q(min $r $s))
    let proof ← mkAppM (if upper then ``FloatLib.Numerics.Backward.maximum
      else ``FloatLib.Numerics.Backward.minimum) #[left.proof, right.proof]
    -- The larger of a bound and zero is the bound.
    if b.nat? == some 0 && a.nat? != some 0 then
      return ⟨reference, exact, a, ← mkAppM ``LE.le.trans_eq #[proof, ← mkAppM ``max_eq_left
        #[← mkAppM ``FloatLib.Numerics.Backward.budget_nonneg #[left.proof]]]⟩
    if a.nat? == some 0 && b.nat? != some 0 then
      return ⟨reference, exact, b, ← mkAppM ``LE.le.trans_eq #[proof, ← mkAppM ``max_eq_right
        #[← mkAppM ``FloatLib.Numerics.Backward.budget_nonneg #[right.proof]]]⟩
    Deviation.tidy ⟨reference, exact, q(max $a $b), proof⟩
  | .unit operand index =>
    let operand ← operand.deviation
    let slot := (← get).slots[index]!
    match slot.delta?, slot.bound? with
    | some delta, some bound =>
      let (stated, proof) ← statedOf delta slot.growth bound
      let delta : Q(ℝ) := delta
      let (x, r, a) := (operand.reference, operand.exact, operand.bound)
      Deviation.tidy ⟨q($x * (1 + $delta)), r, q($a + (|$r| + $a) * $stated),
        ← mkAppM ``FloatLib.Numerics.Backward.deviation_node #[operand.proof, proof]⟩
    | _, _ => return operand
  | .apply function operand =>
    let operand ← operand.deviation
    let (x, r, a) := (operand.reference, operand.exact, operand.bound)
    let (reference, exact) : Q(ℝ) × Q(ℝ) := (mkApp (mkConst function) x, mkApp (mkConst function) r)
    if function == ``Real.exp then
      return ← Deviation.tidy ⟨reference, exact, q((Real.exp $r) * (Real.exp $a - 1)),
        ← mkAppM ``FloatLib.Numerics.Backward.deviation_exp #[operand.proof]⟩
    if a.nat? == some 0 then
      return ⟨reference, exact, q(0),
        ← mkAppM ``FloatLib.Numerics.Backward.log_exact #[operand.proof]⟩
    -- The change of the argument of a logarithm must stay below it: a premise of the statement.
    if (← get).accumulator?.isSome then
      throwError "roundoff: the argument `{r}` of a logarithm is perturbed inside a loop step, \
        and the closed forward bound does not follow it there. Use `roundoff mixed theorem`."
    let apart ← mkFreshExprMVar q($a < $r)
    modifyThe Analysis fun analysis =>
      { analysis with pending := analysis.pending.push apart.mvarId! }
    Deviation.tidy ⟨reference, exact, q($a / ($r - $a)),
      ← mkAppM ``FloatLib.Numerics.Backward.deviation_log #[operand.proof, apart]⟩
  | .fold index => (← get).folds[index]!.deviation

/-- What the perturbations change in a loop: the differences of one step, accumulated through
the exact loop. The step is read again from its record, at the perturbations of the loop and
their bounds. What one step changes must not depend on the accumulator, as it does when the
accumulator is multiplied by a perturbed entry. The accumulated differences of a step with slope
one are stated as a sum. -/
partial def Fold.deviation (fold : Fold) : BackM Deviation := do
  let some record := fold.record? |
    throwError "roundoff: the loop over `{fold.input}` has no closed forward bound"
  let entries := fold.entries
  let count := fold.names.size
  -- The start: an input that took a factor is perturbed.
  let startReference := fold.start (fold.startWitness?.map (·.term))
  let startExact := fold.start none
  let (startBound, startProof) ← match fold.start?, fold.startWitness? with
    | some value, some witness =>
      let .real growth _ := witness.shape |
        throwError "roundoff: unexpected perturbation of the start of a loop"
      let (stated, proof) ← statedOf witness.term growth witness.proof
      let value : Q(ℝ) := value
      pure ((q(|$value| * $stated) : Q(ℝ)),
        ← mkAppM ``FloatLib.Numerics.Backward.deviation_leaf #[value, proof])
    | _, _ =>
      pure ((q(0) : Q(ℝ)), ← mkAppM ``FloatLib.Numerics.exact_error #[startReference])
  -- The tables of the step at the accumulator `s`, without perturbations.
  let plain (s : Q(ℝ)) : State := {
    slots := record.slots.map ({ · with delta? := none, bound? := none })
    folds := fold.inner
    accumulator? := some { record.accumulator with value := s, rho? := none, bound? := none } }
  -- One step at the accumulator `s` and the perturbations `part`, with bounds `shape` by `proof`.
  let stepAt (s : Q(ℝ)) (part proof : Lean.Expr) (shape : Shape) : BackM Deviation := do
    let saved ← get
    let parts ← projections part count
    let proofs ← conjuncts proof count
    let mut state := plain s
    for (indices, loop?) in record.parts, piece in parts, pieceProof in proofs,
        position in [0:count] do
      let pieceShape := shape.component position count
      for index in indices do
        let .real growth _ := pieceShape |
          throwError "roundoff: unexpected perturbation of an entry of a loop"
        let slots := state.slots.modify index fun slot =>
          { slot with delta? := some piece, bound? := some pieceProof, growth := growth }
        state := { state with slots }
      if let some (index, witnessPosition) := loop? then
        let folds := state.folds.modify index
          (·.setWitness witnessPosition piece pieceProof (some pieceShape))
        state := { state with folds }
    set state
    try record.tree.deviation finally set saved
  -- The slope of the exact step in its accumulator.
  let slopeAt (s : Q(ℝ)) : BackM (Q(ℝ) × Bool) := do
    let saved ← get
    set (plain s)
    let slope? ← try record.tree.slope {} finally set saved
    match slope? with
    | some slope => return if slope.nat? == some 1 then (q(1), true) else (q(|$slope|), false)
    | none => return (q(|(0 : ℝ)|), false)
  let dependent : MessageData := m!"roundoff: what the perturbations change in a step of the \
    loop over `{fold.input}` depends on its accumulator, so the loop has no closed forward \
    bound. Use `roundoff mixed theorem`."
  let stored := record.binders[1]!
  let value := mkFVar stored.fvarId
  -- The accumulated changes of a step with slope one, as a sum over the indices.
  let total (indexType changes : Lean.Expr) (proof : Lean.Expr) : BackM Lean.Expr := do
    let proof ← mkAppM ``LE.le.trans_eq
      #[proof, ← mkAppM ``List.foldl_finRange_add_eq_sum #[changes, startBound]]
    let sum : Q(ℝ) ← mkAppM ``Finset.sum
      #[← mkAppOptM ``Finset.univ #[some indexType, none], changes]
    mkExpectedTypeHint proof
      (mkApp (← whnfR (← inferType proof)).appFn! q($startBound + $sum))
  let (proof, exact) ← do
    if fold.overFin then
      let .family _ body _ := entries.shape |
        throwError "roundoff: unexpected perturbations of a loop over `Fin n`"
      withExistingLocalDecls [stored] <| withLocalDeclD fold.binders.1 q(ℝ) fun s => do
        let deviation ←
          stepAt s (mkApp entries.term value).headBeta (mkApp entries.proof value) (body value)
        if deviation.bound.containsFVar s.fvarId! then throwError dependent
        let (slope, unit) ← slopeAt s
        let step ← mkLambdaFVars #[s, value] deviation.reference
        let exactStep ← mkLambdaFVars #[s, value] deviation.exact
        let slopes ← mkLambdaFVars #[value] slope
        let changes ← mkLambdaFVars #[value] deviation.bound
        let sign ← if unit then pure q((zero_le_one : (0 : ℝ) ≤ 1))
          else mkAppM ``abs_nonneg #[slope.appArg!]
        let signs ← mkLambdaFVars #[value] sign
        let head ← mkAppM ``List.abs_foldl_finRange_sub_le
          #[step, exactStep, slopes, changes, signs]
        let slopeProof ← slopeLaw (← whnfR (← inferType head)).bindingDomain! unit
        let stepLaw ← mkLambdaFVars #[value, s] deviation.proof
        let proof ← mkAppM' (mkApp2 head slopeProof stepLaw) #[startProof]
        let proof ← if unit then total fold.elementType changes proof else pure proof
        return (proof, ← mkAppM ``List.foldl #[exactStep, startExact, fold.input])
    else
      let .list _ body := entries.shape |
        throwError "roundoff: unexpected perturbations of a loop over a list"
      let lengths ← mkAppM ``And.left #[entries.proof]
      let bounds ← mkAppM ``And.right #[entries.proof]
      let perturbationType := entries.shape.type.appArg!
      let indexType ← mkAppM ``Fin #[← mkAppM ``List.length #[fold.input]]
      withLocalDeclD `k indexType fun k => withLocalDeclD fold.binders.1 q(ℝ) fun s => do
        let position ← mkAppM ``Fin.val #[k]
        let inside ← mkAppM ``Fin.isLt #[k]
        let inPerturbations ← mkAppM ``lt_of_lt_of_eq #[inside, ← mkEqSymm lengths]
        let entry ← listEntry fold.elementType fold.input position inside
        -- The entry of the step is the entry at the position: a local definition, so that
        -- bounds that read the entry at the position fit the step.
        let located : LocalDecl := .ldecl stored.index stored.fvarId stored.userName stored.type
          entry false stored.kind
        withExistingLocalDecls [located] do
        let part ← listEntry perturbationType entries.term position inPerturbations
        let deviation ← stepAt s part (mkApp3 bounds position inside inPerturbations)
          (body position inside)
        if deviation.bound.containsFVar s.fvarId! then throwError dependent
        let (slope, unit) ← slopeAt s
        let atEntry (term : Lean.Expr) : Lean.Expr := term.replaceFVar value entry
        -- The exact step is a function of the accumulator and of any entry.
        let exactStep := Lean.Expr.lam fold.binders.1 q(ℝ) (.lam stored.userName stored.type
          (deviation.exact.abstract #[s, value]) .default) .default
        if exactStep.containsFVar k.fvarId! then throwError dependent
        let slopes ← mkLambdaFVars #[k] (atEntry slope)
        let changes ← mkLambdaFVars #[k] (atEntry deviation.bound)
        let sign ← if unit then pure q((zero_le_one : (0 : ℝ) ≤ 1))
          else mkAppM ``abs_nonneg #[slope.appArg!]
        let signs ← mkLambdaFVars #[k] (atEntry sign)
        let head ← mkAppM ``List.abs_foldl_zip_sub_foldl_le
          #[fold.input, entries.term, fold.exactStep, exactStep, slopes, changes, lengths, signs]
        let slopeProof ← slopeLaw (← whnfR (← inferType head)).bindingDomain! unit
        let stepLaw ← mkLambdaFVars #[k, s] (atEntry deviation.proof)
        let proof ← mkAppM' (mkApp2 head slopeProof stepLaw) #[startProof]
        let proof ← if unit then total indexType changes proof else pure proof
        return (proof, ← mkAppM ``List.foldl #[exactStep, startExact, fold.input])
  let reference ← fold.loop startReference entries.term
  let exact : Q(ℝ) := exact
  let bound : Q(ℝ) := (← whnfR (← instantiateMVars (← inferType proof))).getArg! 3
  Deviation.tidy ⟨reference, exact, bound,
    ← mkExpectedTypeHint proof q(|$reference - $exact| ≤ $bound)⟩

end

/-- The forward statement about `actual` and its proof, from the form of `actual`: the distance
to the exact computation is at most what the perturbations of the backward statement change,
plus its absolute error. -/
def concludeClosed (actual : Q(ℝ)) (form : Form) : BackM (Lean.Expr × Lean.Expr) := do
  let deviation ← form.tree.deviation
  let (budget, exact, change) := (form.budget, deviation.exact, deviation.bound)
  let (bound, proof) ← tidyBound q($change + $budget)
    (← mkAppM ``FloatLib.Numerics.Backward.forward #[form.proof, deviation.proof])
  let statement : Q(Prop) := q(|$actual - $exact| ≤ $bound)
  return (← mkExpectedTypeHint proof statement, statement)

/-- The perturbations of the statement about `tree` and the view that renders `tree` at
variables for them: one for each perturbed input read, a read made twice counting once, and
those of each loop. A loop over `Fin n` has one family for each perturbation of its step. Fails
when one input is read with two different perturbations, after recording it in
`Config.conflicts`. -/
def witnesses (tree : Tree) : BackM (Array Witness × (Array Lean.Expr → BackM View)) := do
  let state ← get
  let (slots, folds) := tree.leaves
  let mut result : Array Witness := #[]
  let mut keys : Array (Lean.Expr × Nat) := #[]
  let mut slotWitness : Array (Nat × Nat) := #[]
  for index in slots do
    let slot := state.slots[index]!
    -- A rounding that stayed on a computation as a whole has no place among the inputs.
    if let some refusal := slot.pending? then throwError refusal
    let known? := keys.find? (·.1 == slot.key)
    match slot.delta?, slot.bound?, known? with
    | some delta, some bound, none =>
      -- Another read of this input must have taken the same perturbation.
      for other in slots do
        let otherSlot := state.slots[other]!
        if otherSlot.key == slot.key && otherSlot.delta? != some delta then
          (← read).conflicts.modify (·.push (← keyName slot.key))
          throwError "roundoff: `{slot.key}` is read more than once, with roundings that differ, \
            so the computation has no backward-error form in it; choose other inputs with \
            `(perturb := [...])` or use `roundoff mixed theorem` for a forward bound"
      keys := keys.push (slot.key, result.size)
      slotWitness := slotWitness.push (index, result.size)
      result := result.push {
        name := ← perturbationName slot.origin?.toArray, shape := .real slot.growth
        term := delta, proof := bound }
    | some _, some _, some (_, position) => slotWitness := slotWitness.push (index, position)
    | _, _, _ => pure ()
  -- Each loop with the position of its first perturbation and their number.
  let mut foldWitness : Array (Nat × Nat × Nat) := #[]
  for index in folds do
    let fold := state.folds[index]!
    let first := result.size
    if let some witness := fold.startWitness? then result := result.push witness
    let entries := fold.entries
    let count := fold.names.size
    match fold.overFin && count > 1, entries.shape with
    | true, .family domain body binder =>
      -- One family for each perturbation of a step.
      for name in fold.names, position in [0:count] do
        let term ← withLocalDeclD `j domain fun j => do
          mkLambdaFVars #[j] (← projections (mkApp entries.term j).headBeta count)[position]!
        let proof ← withLocalDeclD `j domain fun j => do
          mkLambdaFVars #[j] (← conjuncts (mkApp entries.proof j) count)[position]!
        result := result.push {
          name, term, proof
          shape := .family domain (fun j => (body j).component position count) binder }
    | _, _ => result := result.push entries
    foldWitness := foldWitness.push (index, first, result.size - first)
  let view (binders : Array Lean.Expr) : BackM View := do
    let mut foldTerms := #[]
    for (index, first, count) in foldWitness do
      let fold := state.folds[index]!
      let own := binders.extract first (first + count)
      let offset := if fold.startWitness?.isSome then 1 else 0
      let terms ← if fold.overFin && fold.names.size > 1 then do
          let entries ← withLocalDeclD `j fold.elementType fun j => do
            mkLambdaFVars #[j] (← tuple ((own.extract offset own.size).map (mkApp · j)))
          pure ((own.extract 0 offset).push entries)
        else pure own
      foldTerms := foldTerms.push (index, ← fold.at terms)
    return { deltas := slotWitness.map fun (index, position) => (index, binders[position]!)
             folds := foldTerms }
  return (result, view)

/-- The backward-error statement about `actual` and its proof, from the form of `actual`:
`∃ δ …, bounds ∧ actual = reference`, or `|actual - reference| ≤ budget` when the form has an
absolute error. Each bound is shown as `(1 + u) ^ k - 1` for the `k` roundings its perturbation
took, and names that occur twice are numbered. -/
def conclude (actual : Q(ℝ)) (form : Form) : BackM (Lean.Expr × Lean.Expr) := do
  let (found, view) ← witnesses form.tree
  let found ← found.mapM fun witness => do
    let (shape, proof) ← witness.shape.restateM .whole witness.term witness.proof statedLeaf
    pure { witness with shape, proof }
  let mut used : Array Name := #[]
  let mut names : Array Name := #[]
  for witness in found do
    let mut name := witness.name
    let mut index := 2
    while used.contains name do
      name := witness.name.appendIndexAfter index
      index := index + 1
    used := used.push name
    names := names.push name
  let budget := form.budget
  let statement ← withLocalDeclsDND (names.zip (found.map (·.shape.type))) fun binders => do
    let reference ← form.tree.render (← view binders)
    let main : Q(Prop) := if form.isExact then q($actual = $reference)
      else q(|$actual - $reference| ≤ $budget)
    let mut body : Lean.Expr := main
    for witness in found.reverse, binder in binders.reverse do
      body := mkAnd (← witness.shape.statement binder) body
    let mut statement := body
    for binder in binders.reverse do
      statement ← mkAppM ``Exists #[← mkLambdaFVars #[binder] statement]
    pure statement
  -- The proof, at the perturbations the analysis found.
  let main ← if form.isExact then mkAppM ``eq_of_abs_sub_nonpos #[form.proof] else pure form.proof
  let rec close (statement : Lean.Expr) (index : Nat) : MetaM Lean.Expr := do
    if h : index < found.size then
      let witness := found[index]
      let inner := (mkApp (statement.getArg! 1) witness.term).headBeta
      existsIntro statement witness.term (← close inner (index + 1))
    else
      let mut proof := main
      for witness in found.reverse do
        proof ← mkAppM ``And.intro #[witness.proof, proof]
      mkExpectedTypeHint proof statement
  return (← close statement 0, statement)

end Backward

/-- One run of the backward analysis of the real observation `actual`, as `inferBackward`
describes it, without a case distinction: control flow that needs one is recorded in `split`
and the run fails. -/
def Backward.inferDirect (actual : Q(ℝ)) (selected? : Option (Array FVarId)) (preferRight : Bool)
    (forward : Bool) (split : IO.Ref (Option Lean.Expr)) :
    TacticM (Lean.Expr × Lean.Expr × Array MVarId × Option MVarId) := do
  let session ← (← Session.prepare).index (mixed := true)
  let mut excluded : Array String := #[]
  for _ in [0:8] do
    let conflicts ← IO.mkRef #[]
    split.set none
    let config : Backward.Config := {
      selected?, preferRight, forward, excluded, conflicts, split, relatives := ← IO.mkRef #[] }
    let saved ← saveState
    try
      let (((proof, statement), _), analysis) ← (((do
        let form ← Backward.analyze actual 256
        if forward then Backward.concludeClosed actual form
        else Backward.conclude actual form).run config).run {} |>.run session).run {}
      let mut pending ← analysis.pending.filterM fun goal => return !(← goal.isAssigned)
      -- A closed premise that is false is refused before the finiteness of the result, which
      -- would then never hold, closes it.
      checkGeneratedConditions pending
      -- The finiteness that the rules need follows from the finiteness of the result.
      let mut root? : Option MVarId := none
      if let some value := decodedValue? actual then
        let root ← mkFreshExprMVar (← Backward.finiteStatement actual value)
        let facts ← Backward.reflect session root
        trace[roundoff] "finiteness from the result: {facts.map (·.1)}"
        if ← Backward.closeFinite facts pending then
          pending := #[root.mvarId!] ++ (← pending.filterM fun goal => return !(← goal.isAssigned))
          root? := some root.mvarId!
      Backward.closeAmong session pending
      pending ← pending.filterM fun goal => return !(← goal.isAssigned)
      return (proof, statement, pending, root?)
    catch error =>
      let found := (← conflicts.get).filter (!excluded.contains ·)
      if found.isEmpty then throw error
      saved.restore
      excluded := excluded ++ found
  throwError "roundoff: the backward analysis did not settle which inputs to perturb"

/-- The statement of `actual` by cases of `control`, the control flow that stopped its backward
analysis, with its proof, where `infer` generates the statement of one case: its proof, its
statement and the premises it leaves open, which become premises of the case.

* A `match` application whose discriminants are variables of the statement, or proofs: each
  alternative is the computation at its patterns, under the hypotheses of the context restated
  at the patterns (`Cases.withArm`), and the statement is the `match` of the statements of the
  alternatives, proved by the splitter of the matcher (`Cases.proveBySplit`).
* A branch on a condition over the variables of the statement: the statement is the
  conjunction of the statement under the condition and the statement under its negation.

`none` when the control flow reads a variable that the analysis introduced, such as the entry
of a loop step, or the computation is not type correct at a pattern. -/
def Backward.inferCases (control : Lean.Expr) (actual : Q(ℝ))
    (selected? : Option (Array FVarId))
    (infer : Q(ℝ) → Option (Array FVarId) →
      TacticM (Lean.Expr × Lean.Expr × Array MVarId × Option MVarId)) :
    TacticM (Option (Lean.Expr × Lean.Expr)) := do
  let context ← getLCtx
  let rooted (term : Lean.Expr) : Bool := !mentions term fun id => !context.contains id
  -- The statement of one case under its open premises, with its proof for `binders`.
  let stated (binders : Array Lean.Expr) (case : Q(ℝ)) (selected? : Option (Array FVarId)) :
      TacticM (Lean.Expr × Lean.Expr) := do
    let (proof, statement, pending, _) ← infer case selected?
    withConditions pending (← IO.mkRef {}) fun condition evidence => do
      let proof ← instantiateMVars proof
      if condition.isConstOf ``True then return (statement, ← mkLambdaFVars binders proof)
      return (← mkArrow condition statement, ← mkLambdaFVars (binders.push evidence) proof)
  if control.isAppOfArity ``dite 5 then
    let condition := control.getArg! 1
    unless rooted condition do return none
    let name := match control.getArg! 3 with
      | .lam name .. => name
      | _ => `h
    let side (hypothesis : Lean.Expr) : TacticM (Lean.Expr × Lean.Expr) :=
      withLocalDeclD name hypothesis fun given => do
        let (statement, proof) ← stated #[] actual selected?
        return (← mkLambdaFVars #[given] proof, ← mkForallFVars #[given] statement)
    let (yes, yesStatement) ← side condition
    let (no, noStatement) ← side (mkNot condition)
    return some (← mkAppM ``And.intro #[yes, no], mkAnd yesStatement noStatement)
  let some app ← Cases.matcher? control | return none
  if ← app.discrs.anyM fun discriminant => isConstructorApp discriminant then
    throwError "roundoff: the alternatives of{indentExpr control}\noverlap: at the patterns of \
      one alternative the `match` does not reduce, because that alternative holds only where the \
      earlier ones fail. The closed forward and backward modes state each alternative at its \
      patterns alone. Use `roundoff mixed theorem` for a forward bound, or write the \
      alternatives with disjoint patterns."
  unless (app.discrs ++ app.params).all rooted do return none
  unless ← app.discrs.allM fun discriminant => pure discriminant.isFVar <||> isProof discriminant
    do return none
  let patterns ← Cases.patterns app
  let mut statements := #[]
  let mut proofs := #[]
  let mut unused := #[]
  for index in [0:app.alts.size] do
    let arm? ← Cases.withArm app patterns index fun parameters facts matched _ => do
      let pairs := (app.discrs.zip matched).filter (·.1.isFVar)
      let case : Q(ℝ) := actual.replaceFVars (pairs.map (·.1)) (pairs.map (·.2))
      unless ← isTypeCorrect case do return none
      -- A chosen input that the `match` binds again is the pattern variable.
      let selected := selected?.map fun chosen => chosen.map fun id =>
        match pairs.find? (·.1.fvarId! == id) with
        | some (_, .fvar pattern) => pattern
        | _ => id
      let (statement, proof) ← stated #[] case selected
      let used := facts.filter fun fact => statement.containsFVar fact.fvarId!
      let others := facts.filter (!used.contains ·)
      return some (← mkLambdaFVars parameters (← mkForallFVars used statement),
        ← mkLambdaFVars (parameters ++ others ++ used) proof, others.size)
    let some (statement, proof, count) := arm? | return none
    statements := statements.push statement
    proofs := proofs.push proof
    unused := unused.push count
  let statement ← Cases.combine app (.sort .zero) statements
  let proof ← Cases.proveBySplit statement statement proofs false app.altNumParams unused
  return some (proof, statement)

/-- Infer and prove the backward-error statement of the real observation `actual`: its proof, its
statement, the premises it leaves open, and among them the finiteness of the observed value when
the other finiteness premises follow from it. `selected?` are the input variables that may carry
a perturbation, all of them by default, and `preferRight` gives the rounding of a product to its
right factor. An input found with two different perturbations takes none in the next attempt.
With `forward` the statement is the forward bound in closed form; exact constants and inputs
that every step of a loop reads may then take roundings too, each read by itself.

A `match` on inputs of the statement and a branch that binds the proof of a condition on them
have one statement for each case (`Backward.inferCases`): the perturbations of one case, and
their number, are not those of another. The premises of a case are then part of its statement,
and no premise is left open. -/
partial def inferBackward (actual : Q(ℝ)) (selected? : Option (Array FVarId))
    (preferRight : Bool) (forward : Bool := false) :
    TacticM (Lean.Expr × Lean.Expr × Array MVarId × Option MVarId) := do
  let split ← IO.mkRef none
  let saved ← saveState
  try Backward.inferDirect actual selected? preferRight forward split
  catch error =>
    let some control ← split.get | throw error
    saved.restore
    let some (proof, statement) ← Backward.inferCases control actual selected?
        (inferBackward · · preferRight forward) | throw error
    return (proof, statement, #[], none)

end FloatLib.Floats.Formats.BinaryInterchange.Roundoff
