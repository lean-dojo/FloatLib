/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.ErrorBound.Backward
public import FloatLib.Tactic.Roundoff.Tactic

/-!
# The exact computation on perturbed inputs

The backward analysis keeps the exact computation that a computed value is compared with as a
`Tree`: real operations over reads of inputs, each read with the perturbation it has taken so
far, and loops. This module has that tree and what moves a rounding onto it.

* A `Shape` is the type of a perturbation and its bound: a real `δ` with `|δ| ≤ growth - 1`, a
  pair, one perturbation for each index of a type, or a list of them. A `Pattern` says how a
  perturbation takes a factor: each real `δ` becomes `(1 + δ) * c - 1`, or `(1 + δ) * √c - 1`
  where it perturbs a squared input, or stays.
* `Tree.scale` moves a factor `c` onto the perturbations of a tree and proves
  `reference * c = reference'`: a sum, a branch, a maximum and a minimum pass it to both sides,
  a product to one factor, a square as `√c` to both, a quotient to its numerator, a square root
  as `c * c` to its argument, and a loop to its start and to the perturbations of its steps by
  the law of its step. A computation may also be perturbed as a whole (`Tree.unit`): in a
  forward bound the rounding of an exponential or a logarithm stays there, and in a backward
  analysis a rounding that no input of its operation takes waits there for a product to move it
  onto its other factor (`settle`).
* `Tree.coefficient` is the slope of a loop step in its accumulator, and `Tree.magnitude` bounds
  a computation, such as that slope, under the bounds of its perturbations.
* `statedLeaf` restates a bound `∏ (1 + r) ^ e - 1` with one exponent for each relative error
  `r`, as the statement shows it.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.Roundoff

open Lean Meta Elab Tactic Qq
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

namespace Backward

/-- One read of an input in the exact computation, with the perturbation it has taken. -/
structure Slot where
  /-- The decoded input, such as `toReal (x j)`. -/
  key : Q(ℝ)
  /-- The input variable it reads. -/
  origin? : Option FVarId := none
  /-- Whether it may take a perturbation. -/
  perturbable : Bool := true
  /-- Why it may not. -/
  blocked : String := "is not perturbed"
  /-- Its perturbation `d`: the computation reads `key * (1 + d)`. -/
  delta? : Option Q(ℝ) := none
  /-- The growth `g` of its perturbation, as the product of the factors in the order taken. -/
  growth : Q(ℝ) := q(1)
  /-- A proof of `|d| ≤ g - 1`. -/
  bound? : Option Lean.Expr := none
  /-- For the slot of a computation perturbed as a whole (`Tree.unit`) in a backward analysis:
  the refusal to raise unless a product moves the perturbation onto its other factor. -/
  pending? : Option MessageData := none
  /-- For such a slot, a proof of `0 ≤ 1 + d` when each factor it took is known to be
  nonnegative. -/
  nonneg? : Option Lean.Expr := none

instance : Inhabited Slot := ⟨{ key := q(0) }⟩

/-- The accumulator of the loop step under analysis. -/
structure Accumulator where
  /-- The accumulator. -/
  binder : Lean.Expr
  /-- The traversed entry. -/
  element : Lean.Expr
  /-- The decoded accumulator. -/
  value : Q(ℝ)
  /-- Whether it may take a factor: the loop starts from zero or from an input that may. -/
  scalable : Bool
  /-- The input variable the loop traverses. -/
  origin? : Option FVarId := none
  /-- The factor `ρ` it has taken: the step reads `value * ρ`. -/
  rho? : Option Q(ℝ) := none
  /-- The growth `q` of that factor. -/
  growth : Q(ℝ) := q(1)
  /-- A proof of `|ρ - 1| ≤ q - 1`. -/
  bound? : Option Lean.Expr := none
  deriving Inhabited

/-- How a perturbation takes a factor `c`. -/
inductive Pattern where
  /-- It takes none. -/
  | keep
  /-- Each real `δ` becomes `(1 + δ) * c - 1`. -/
  | whole
  /-- Each real `δ` becomes `(1 + δ) * √c - 1`: it perturbs an input that is squared. -/
  | root
  /-- The two components of a pair, each in its way. -/
  | pair (left right : Pattern)
  /-- Each perturbation of a family or a list, in one way. -/
  | each (body : Pattern)
  deriving Inhabited, BEq

/-- The way of each perturbation of a family or a list. -/
def Pattern.body : Pattern → Pattern
  | .each body => body
  | pattern => pattern

/-- The ways of the two components of a pair. -/
def Pattern.sides : Pattern → Pattern × Pattern
  | .pair left right => (left, right)
  | pattern => (pattern, pattern)

/-- The right-nested pair of `patterns`, which are not empty. -/
def Pattern.nest (patterns : Array Pattern) : Pattern :=
  match patterns.toList.reverse with
  | [] => .keep
  | last :: rest => rest.foldl (fun nested pattern => .pair pattern nested) last

/-- The shape of a perturbation and of its bound: a real `δ` with `|δ| ≤ growth - 1`, a pair, one
perturbation for each index of a type, or a list of them. The bounds of a family read the index,
those of a list the position. -/
inductive Shape where
  /-- A real perturbation `δ` with `|δ| ≤ growth - 1`, shown as `|δ| ≤ stated` once the bound is
  restated for the statement. -/
  | real (growth : Lean.Expr) (stated? : Option Lean.Expr := none)
  /-- A pair of perturbations. -/
  | pair (left right : Shape)
  /-- A perturbation for each index of `domain`, which the statement calls `binder`. -/
  | family (domain : Lean.Expr) (body : Lean.Expr → Shape) (binder : Name := `j)
  /-- A list of `count` perturbations, each by its position `k` and the proof of `k < count`. -/
  | list (count : Lean.Expr) (body : Lean.Expr → Lean.Expr → Shape)

instance : Inhabited Shape := ⟨.real default⟩

/-- `shape` with `value` in place of the local variable `binder`. -/
partial def Shape.replaceFVar (shape : Shape) (binder value : Lean.Expr) : Shape :=
  match shape with
  | .real growth stated? =>
      .real (growth.replaceFVar binder value) (stated?.map (·.replaceFVar binder value))
  | .pair left right => .pair (left.replaceFVar binder value) (right.replaceFVar binder value)
  | .family domain body name =>
      .family (domain.replaceFVar binder value)
        (fun index => (body index).replaceFVar binder value) name
  | .list count body =>
      .list (count.replaceFVar binder value) fun index inside =>
        (body index inside).replaceFVar binder value

/-- The type of a perturbation of this shape. The type of an entry does not depend on its index. -/
partial def Shape.type : Shape → Lean.Expr
  | .real .. => q(ℝ)
  | .pair left right => mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) left.type right.type
  | .family domain body _ => .forallE `j domain (body default).type .default
  | .list _ body => mkApp (mkConst ``List [Level.zero]) (body default default).type

/-- The right-nested pair of `shapes`, which are not empty. -/
def Shape.nest (shapes : Array Shape) : Shape :=
  match shapes.toList.reverse with
  | [] => default
  | last :: rest => rest.foldl (fun nested shape => .pair shape nested) last

/-- The component at `position` of a right-nested pair of `count` shapes. -/
def Shape.component (shape : Shape) (position count : Nat) : Shape :=
  match shape, position with
  | .pair left _, 0 => if count == 1 then shape else left
  | .pair _ right, position + 1 => right.component position (count - 1)
  | shape, _ => shape

/-- `shape` with each growth that takes a factor by `pattern` multiplied by `factor`. -/
partial def Shape.scaleGrowth (shape : Shape) (pattern : Pattern) (factor : Lean.Expr) : Shape :=
  match shape, pattern with
  | _, .keep => shape
  | .real growth _, _ =>
      let growth : Q(ℝ) := growth
      let factor : Q(ℝ) := factor
      .real q($growth * $factor)
  | .pair left right, pattern =>
      .pair (left.scaleGrowth pattern.sides.1 factor) (right.scaleGrowth pattern.sides.2 factor)
  | .family domain body name, pattern =>
      .family domain (fun index => (body index).scaleGrowth pattern.body factor) name
  | .list count body, pattern =>
      .list count fun index inside => (body index inside).scaleGrowth pattern.body factor

/-- The first component of a pair, read off when the pair is explicit. -/
def fst (pair : Lean.Expr) : MetaM Lean.Expr :=
  if pair.isAppOfArity ``Prod.mk 4 then pure (pair.getArg! 2) else mkAppM ``Prod.fst #[pair]

/-- The second component of a pair, read off when the pair is explicit. -/
def snd (pair : Lean.Expr) : MetaM Lean.Expr :=
  if pair.isAppOfArity ``Prod.mk 4 then pure (pair.getArg! 3) else mkAppM ``Prod.snd #[pair]

/-- The components of `term`, a right-nested pair of `count` components. -/
def projections (term : Lean.Expr) (count : Nat) : MetaM (Array Lean.Expr) := do
  let mut result := #[]
  let mut rest := term
  for index in [0:count] do
    if index + 1 == count then result := result.push rest
    else
      result := result.push (← fst rest)
      rest ← snd rest
  return result

/-- The right-nested pair of `terms`, which are not empty. -/
def tuple (terms : Array Lean.Expr) : MetaM Lean.Expr := do
  match terms.toList.reverse with
  | [] => throwError "roundoff: a loop step without a perturbation"
  | last :: rest => rest.foldlM (fun nested term => mkAppM ``Prod.mk #[term, nested]) last

/-- The proofs of the `count` conjuncts of a right-nested conjunction. -/
def conjuncts (proof : Lean.Expr) (count : Nat) : MetaM (Array Lean.Expr) := do
  let mut result := #[]
  let mut rest := proof
  for index in [0:count] do
    if index + 1 == count then result := result.push rest
    else
      result := result.push (← mkAppM ``And.left #[rest])
      rest ← mkAppM ``And.right #[rest]
  return result

/-- The proof of the right-nested conjunction of the statements that `proofs` prove. -/
def conjunction (proofs : Array Lean.Expr) : MetaM Lean.Expr := do
  match proofs.toList.reverse with
  | [] => throwError "roundoff: a loop step without a perturbation"
  | last :: rest => rest.foldlM (fun nested proof => mkAppM ``And.intro #[proof, nested]) last

/-- The entry `list[k]` of a list of perturbations, for `hp : k < list.length`. -/
def listEntry (elementType list k hp : Lean.Expr) : MetaM Lean.Expr := do
  let listType := mkApp (mkConst ``List [Level.zero]) elementType
  let valid ← withLocalDeclD `as listType fun as => withLocalDeclD `i q(ℕ) fun i => do
    mkLambdaFVars #[as, i] (← mkAppM ``LT.lt #[i, ← mkAppM ``List.length #[as]])
  mkAppOptM ``GetElem.getElem
    #[some listType, some q(ℕ), some elementType, some valid, none, some list, some k, some hp]

/-- The bound that `shape` states of the perturbation `w`. -/
partial def Shape.statement (shape : Shape) (w : Lean.Expr) : MetaM Lean.Expr := do
  match shape with
  | .real growth stated? =>
    let w : Q(ℝ) := w
    let growth : Q(ℝ) := growth
    match stated? with
    | some stated =>
      let stated : Q(ℝ) := stated
      return q(|$w| ≤ $stated)
    | none => return q(|$w| ≤ $growth - 1)
  | .pair left right => return mkAnd (← left.statement (← fst w)) (← right.statement (← snd w))
  | .family domain body name =>
    withLocalDeclD name domain fun j => do
      mkForallFVars #[j] (← (body j).statement (mkApp w j).headBeta)
  | .list count body =>
    let length ← mkAppM ``List.length #[w]
    let elementType := (body default default).type
    withLocalDeclD `k q(ℕ) fun k => do
      let inCount ← mkAppM ``LT.lt #[k, count]
      let inLength ← mkAppM ``LT.lt #[k, length]
      withLocalDeclD `hk inCount fun hk => withLocalDeclD `hp inLength fun hp => do
        let bounds ← mkForallFVars #[k, hk, hp]
          (← (body k hk).statement (← listEntry elementType w k hp))
        return mkAnd (← mkEq length count) bounds

/-- The perturbation `w` after it took the factor `c` by `pattern`. -/
partial def Shape.scaleTerm (shape : Shape) (pattern : Pattern) (w c : Lean.Expr) :
    MetaM Lean.Expr := do
  match shape, pattern with
  | _, .keep => return w
  | .real .., pattern =>
    let w : Q(ℝ) := w
    let c : Q(ℝ) := c
    return if pattern matches .root then q((1 + $w) * Real.sqrt $c - 1) else q((1 + $w) * $c - 1)
  | .pair left right, pattern =>
    mkAppM ``Prod.mk #[← left.scaleTerm pattern.sides.1 (← fst w) c,
      ← right.scaleTerm pattern.sides.2 (← snd w) c]
  | .family domain body name, pattern =>
    withLocalDeclD name domain fun j => do
      mkLambdaFVars #[j] (← (body j).scaleTerm pattern.body (mkApp w j).headBeta c)
  | .list _ body, pattern =>
    let entryShape := body default default
    withLocalDeclD `δ entryShape.type fun entry => do
      mkAppM ``List.map
        #[← mkLambdaFVars #[entry] (← entryShape.scaleTerm pattern.body entry c), w]

/-- A perturbation that the generated statement quantifies. -/
structure Witness where
  /-- Its name in the statement. -/
  name : Name
  /-- Its type and its bound. -/
  shape : Shape
  /-- How it takes a further factor. -/
  pattern : Pattern := .whole
  /-- The perturbation itself. -/
  term : Lean.Expr
  /-- A proof of `shape.statement term`. -/
  proof : Lean.Expr
  deriving Inhabited

/-- `term` with the projections of explicit pairs read off. -/
partial def reducePairs (term : Lean.Expr) : Lean.Expr :=
  term.replace fun child =>
    if child.isAppOfArity ``Prod.fst 3 || child.isAppOfArity ``Prod.snd 3 then
      let inner := reducePairs child.appArg!
      if inner.isAppOfArity ``Prod.mk 4 then
        some (inner.getArg! (if child.isAppOf ``Prod.fst then 2 else 3))
      else some (mkApp child.appFn! inner)
    else none

/-- `term` after beta reduction and the projections of explicit pairs. -/
def tidyTerm (term : Lean.Expr) : MetaM Lean.Expr := do
  let mut term := term
  for _ in [0:3] do
    term ← Core.betaReduce (reducePairs term)
  return term

/-- A proof of `growth ≤ 2` for the growth `1 + u` of one rounding with a unit roundoff `u`, or
`none` for another growth. It shows the factor of such a rounding nonnegative, which a square
needs to split it into two square roots. -/
def growthLeTwo? (growth : Q(ℝ)) : MetaM (Option Lean.Expr) := do
  unless growth.isAppOfArity ``HAdd.hAdd 6 && (growth.getArg! 4).nat? == some 1 do return none
  let relative := growth.getArg! 5
  unless relative.isAppOfArity ``Model.unitRoundoffAt 1 do return none
  let small ← mkAppM ``LT.lt.le #[← mkAppM ``Model.unitRoundoffAt_lt_one #[relative.appArg!]]
  return some (← mkAppM ``FloatLib.Numerics.Backward.one_add_le_two #[small])

/-- The exact computation that the computed value is compared with. Its input reads and loops are
rendered from the tables of the state, so that a factor moves onto a read by changing its slot. -/
inductive Tree where
  /-- An exact value that takes no perturbation, with the reason, or the real zero, which takes
  any factor. -/
  | const (value : Q(ℝ)) (zero : Bool) (blocked : String := "takes no perturbation")
  /-- A read of an input. -/
  | slot (index : Nat)
  /-- The accumulator of the loop step under analysis. -/
  | acc
  /-- A sum. -/
  | add (left right : Tree)
  /-- A difference. -/
  | sub (left right : Tree)
  /-- A negation. -/
  | neg (operand : Tree)
  /-- A product. -/
  | mul (left right : Tree)
  /-- A quotient. -/
  | div (left right : Tree)
  /-- A branch on `condition`, which the reference keeps as the program states it. -/
  | ite (condition decidable : Lean.Expr) (positive negative : Tree)
  /-- A square root. -/
  | sqrt (operand : Tree)
  /-- A maximum (`upper`) or a minimum. -/
  | lattice (upper : Bool) (left right : Tree)
  /-- An exact computation perturbed as a whole, `operand * (1 + δ)` for the perturbation `δ` of
  the slot `index`. A rounding that the operand cannot take stays here: for good in a forward
  bound, and in a backward analysis until a product moves it onto its other factor. -/
  | unit (operand : Tree) (index : Nat)
  /-- The real function `function`, the exponential or the logarithm, of an exact computation.
  It occurs in a forward bound only. -/
  | apply (function : Name) (operand : Tree)
  /-- A loop. -/
  | fold (index : Nat)
  deriving Inhabited

/-- What the analysis of a loop step keeps for a forward bound of the loop: the exact
computation of the step, its input reads, which reads and which perturbation of a loop inside
the step each perturbation of the step feeds, and the local variables of the step, its
accumulator and its entry. -/
structure Record where
  /-- The exact computation of the step. -/
  tree : Tree
  /-- The input reads of the step. -/
  slots : Array Slot
  /-- For each perturbation of the step: the reads it perturbs, or the loop inside the step and
  the position among that loop's perturbations. -/
  parts : Array (Array Nat × Option (Nat × Nat))
  /-- The local variables for the accumulator and the entry. -/
  binders : Array LocalDecl
  /-- The accumulator of the step. -/
  accumulator : Accumulator
  deriving Inhabited

/-- A loop in the exact computation: the exact loop of `exactStep` on perturbed entries. -/
structure Fold where
  /-- Whether the loop runs over `List.finRange n`, with perturbations a function on `Fin n`;
  otherwise they are a list beside the input. -/
  overFin : Bool
  /-- The exact step, a function of the accumulator, the entry and the perturbations of the
  step: one, or a right-nested pair of them. -/
  exactStep : Lean.Expr
  /-- The type of the entries. -/
  elementType : Lean.Expr
  /-- The traversed input. -/
  input : Lean.Expr
  /-- The decoded initial value, or `none` for an exact zero. -/
  start? : Option Lean.Expr
  /-- For a start from an input that may take a perturbation, its input variable. -/
  startOrigin? : Option (Option FVarId) := none
  /-- The perturbation of the start, once it has taken a factor. -/
  startWitness? : Option Witness := none
  /-- The perturbations of the steps: a family on `Fin n` or a list. -/
  entries : Witness
  /-- The names of the perturbations of one step. Over `Fin n` the statement quantifies each of
  them as a family of its own. -/
  names : Array Name
  /-- How the perturbations of one step take a factor of the accumulator, `fun c p => …`. -/
  scale : Lean.Expr
  /-- A proof that scaling the accumulator scales the step,
  `∀ c s v p, exactStep (s * c) v (scale c p) = exactStep s v p * c`, when it does. When a
  perturbation takes the square root of the factor (`root`), the law is for `0 ≤ c`:
  `∀ c, 0 ≤ c → ∀ s v p, …`. -/
  homogeneous? : Option Lean.Expr := none
  /-- Whether a perturbation of the step takes the square root of a factor. -/
  root : Bool := false
  /-- The names of the accumulator and of the entry in the program's step. -/
  binders : Name × Name := (`s, `j)
  /-- What the analysis of the step keeps for a forward bound. -/
  record? : Option Record := none
  /-- The loops inside the step. -/
  inner : Array Fold := #[]
  deriving Inhabited

/-- The start of the loop at the perturbation `delta?` of its initial value. -/
def Fold.start (fold : Fold) (delta? : Option Lean.Expr) : Q(ℝ) :=
  match fold.start?, delta? with
  | none, _ => q(0)
  | some value, some delta =>
      let value : Q(ℝ) := value
      let delta : Q(ℝ) := delta
      q($value * (1 + $delta))
  | some value, none => value

/-- The exact loop from `startTerm` on entries perturbed by `entries`. -/
def Fold.loop (fold : Fold) (startTerm entries : Lean.Expr) : MetaM Q(ℝ) := do
  if fold.overFin then
    let body ← withLocalDeclD fold.binders.1 q(ℝ) fun s =>
        withLocalDeclD fold.binders.2 fold.elementType fun j => do
      mkLambdaFVars #[s, j]
        (← tidyTerm (mkApp3 fold.exactStep s j (mkApp entries j).headBeta).headBeta)
    mkAppM ``List.foldl #[body, startTerm, fold.input]
  else
    let pairs ← mkAppM ``List.zip #[fold.input, entries]
    let pairType ← mkAppM ``Prod #[fold.elementType, fold.entries.shape.type.appArg!]
    let body ← withLocalDeclD fold.binders.1 q(ℝ) fun s =>
        withLocalDeclD `entry pairType fun pair => do
      mkLambdaFVars #[s, pair] (← tidyTerm (mkApp3 fold.exactStep s (← mkAppM ``Prod.fst #[pair])
        (← mkAppM ``Prod.snd #[pair])).headBeta)
    mkAppM ``List.foldl #[body, startTerm, pairs]

/-- The perturbations of the loop: that of its start, if any, then those of its steps. -/
def Fold.witnesses (fold : Fold) : Array Witness :=
  fold.startWitness?.toArray.push fold.entries

/-- The loop with the perturbation at `position` of `Fold.witnesses` replaced, and its shape
when one is given. -/
def Fold.setWitness (fold : Fold) (position : Nat) (term proof : Lean.Expr)
    (shape? : Option Shape := none) : Fold :=
  match fold.startWitness?, position with
  | some witness, 0 =>
      let witness := { witness with term, proof, shape := shape?.getD witness.shape }
      { fold with startWitness? := some witness }
  | _, _ =>
      let entries := { fold.entries with term, proof, shape := shape?.getD fold.entries.shape }
      { fold with entries }

/-- The reference of the loop at perturbations `terms`, in the order of `Fold.witnesses`. -/
def Fold.at (fold : Fold) (terms : Array Lean.Expr) : MetaM Q(ℝ) :=
  if fold.startWitness?.isSome then fold.loop (fold.start (some terms[0]!)) terms[1]!
  else fold.loop (fold.start none) terms[0]!

/-- Why the loop takes no further factor, or `none` when it does: its step must scale with its
accumulator, and its start must be zero or an input that may take a perturbation. -/
def Fold.obstacle (fold : Fold) : Option MessageData :=
  if fold.homogeneous?.isNone then
    some m!"the result of the loop over `{fold.input}` takes no further factor"
  else if fold.start?.isSome && fold.startWitness?.isNone && fold.startOrigin?.isNone then
    some m!"the loop over `{fold.input}` starts from a value that takes no perturbation"
  else none

/-- What the caller chooses. -/
structure Config where
  /-- The input variables that may carry a perturbation; all of them without a choice. -/
  selected? : Option (Array FVarId) := none
  /-- Whether the right factor of a product takes its rounding when both factors could. -/
  preferRight : Bool := false
  /-- Whether a forward bound is wanted. The reads of one input may then take different
  perturbations: each read is bounded by itself. -/
  forward : Bool := false
  /-- Whether a product gives a factor to the factor that reads the loop's accumulator: the
  factor of the accumulator stays with it when a step is scaled as a whole. -/
  followAccumulator : Bool := false
  /-- Input reads, as printed, that take no perturbation: they were read twice with different
  perturbations in an earlier attempt. -/
  excluded : Array String := #[]
  /-- The reads that this attempt found with different perturbations. -/
  conflicts : IO.Ref (Array String)
  /-- The relative errors met so far, each in the spelling of its first occurrence
  (`canonical`). -/
  relatives : IO.Ref (Array Lean.Expr)
  /-- The control flow that stopped this attempt: a `match` application whose discriminants stay
  open, or a branch that binds the proof of its condition. Its cases have one statement each,
  which the caller of the analysis generates. -/
  split : IO.Ref (Option Lean.Expr)

/-- The reads and loops of the exact computation. -/
structure State where
  /-- The input reads. -/
  slots : Array Slot := #[]
  /-- The accumulator of the loop step under analysis. -/
  accumulator? : Option Accumulator := none
  /-- The loops. -/
  folds : Array Fold := #[]

/-- The backward analysis: the caller's choices, its tables, and the forward analysis below. -/
abbrev BackM := ReaderT Config (StateRefT State AnalyzeM)

/-- The result for one analyzed value `actual`: a proof of `|actual - reference| ≤ budget`, where
`reference` is `tree` as the tables render it now. -/
structure Form where
  /-- The exact computation. -/
  tree : Tree
  /-- The absolute error; the literal zero when the computed value equals the reference. -/
  budget : Q(ℝ)
  /-- A proof of `|actual - reference| ≤ budget`. -/
  proof : Lean.Expr

/-- Whether the computed value equals the reference. -/
def Form.isExact (form : Form) : Bool := form.budget.nat? == some 0

/-- The relative error `relative` in the spelling of its first occurrence. Two rules may state the
unit roundoff of one format with different proofs in its descriptor, and the bounds count the
factors of each relative error. -/
def canonical (relative : Lean.Expr) : BackM Lean.Expr := do
  let known ← (← read).relatives.get
  for other in known do
    if other == relative then return other
    if ← withNewMCtxDepth (withReducible (isDefEq other relative)) then return other
  (← read).relatives.modify (·.push relative)
  return relative

/-- Terms that replace parts of a rendered tree: the scaled accumulator, perturbations of slots
and references of loops. -/
structure View where
  /-- The term for the scaled accumulator. -/
  accumulator? : Option Q(ℝ) := none
  /-- The perturbation of each listed slot. -/
  deltas : Array (Nat × Q(ℝ)) := #[]
  /-- The reference of each listed loop. -/
  folds : Array (Nat × Q(ℝ)) := #[]

/-- A name for the perturbation of the input variables `origins`: `δ`, then their names. -/
def perturbationName (origins : Array FVarId) : MetaM Name := do
  let mut name := "δ"
  for origin in origins do
    name := name ++ toString (← origin.getUserName).eraseMacroScopes
  return Name.mkSimple name

/-- The exact computation `tree` as a real term, read from the tables and `view`. -/
partial def Tree.render (tree : Tree) (view : View := {}) : BackM Q(ℝ) := do
  match tree with
  | .const value _ _ => return value
  | .slot index =>
    let slot := (← get).slots[index]!
    let key := slot.key
    match (view.deltas.find? (·.1 == index)).map (·.2) <|> slot.delta? with
    | some delta => return q($key * (1 + $delta))
    | none => return key
  | .acc =>
    if let some term := view.accumulator? then return term
    let some accumulator := (← get).accumulator? |
      throwError "roundoff: no loop accumulator in scope"
    let value := accumulator.value
    match accumulator.rho? with
    | some rho => return q($value * $rho)
    | none => return value
  | .add left right =>
    let left ← left.render view
    let right ← right.render view
    return q($left + $right)
  | .sub left right =>
    let left ← left.render view
    let right ← right.render view
    return q($left - $right)
  | .neg operand =>
    let operand ← operand.render view
    return q(-$operand)
  | .mul left right =>
    let left ← left.render view
    let right ← right.render view
    return q($left * $right)
  | .div left right =>
    let left ← left.render view
    let right ← right.render view
    return q($left / $right)
  | .ite condition decidable positive negative =>
    return mkApp5 (mkConst `ite [Level.one]) q(ℝ) condition decidable (← positive.render view)
      (← negative.render view)
  | .sqrt operand =>
    let operand ← operand.render view
    return q(Real.sqrt $operand)
  | .lattice upper left right =>
    let left ← left.render view
    let right ← right.render view
    return if upper then q(max $left $right) else q(min $left $right)
  | .unit operand index =>
    let inner ← operand.render view
    match (view.deltas.find? (·.1 == index)).map (·.2) <|> (← get).slots[index]!.delta? with
    | some delta => return q($inner * (1 + $delta))
    | none => return inner
  | .apply function operand => return mkApp (mkConst function) (← operand.render view)
  | .fold index =>
    if let some term := (view.folds.find? (·.1 == index)).map (·.2) then return term
    let fold := (← get).folds[index]!
    fold.at (fold.witnesses.map (·.term))

/-- Why `tree` takes no factor, or `none` when it does. A sum takes a factor in both terms, a
product in one factor, a quotient in its numerator. -/
partial def Tree.obstacle (tree : Tree) : BackM (Option MessageData) := do
  match tree with
  | .const value zero blocked =>
    return if zero then none else some m!"`{value}` {blocked}"
  | .slot index =>
    let slot := (← get).slots[index]!
    return if slot.perturbable then none else some m!"`{slot.key}` {slot.blocked}"
  | .acc =>
    return if ((← get).accumulator?.map (·.scalable)).getD false then none
      else some m!"the loop starts from a value that takes no perturbation"
  | .add left right | .sub left right | .lattice _ left right =>
    if let some reason ← left.obstacle then return some reason
    right.obstacle
  | .neg operand | .sqrt operand => operand.obstacle
  | .mul left right =>
    let some first ← left.obstacle | return none
    let some second ← right.obstacle | return none
    -- A square names its factor once.
    if (← left.render) == (← right.render) then return some first
    return some m!"{first} and {second}"
  | .div left _ => left.obstacle
  | .ite _ _ positive negative =>
    if let some reason ← positive.obstacle then return some reason
    negative.obstacle
  | .unit .. => return none
  | .apply function _ => return some m!"`{.ofConstName function}` takes no factor"
  | .fold index => return (← get).folds[index]!.obstacle

/-- Whether `tree` takes a factor. -/
def Tree.scalable (tree : Tree) : BackM Bool :=
  return (← tree.obstacle).isNone

/-- Whether `tree` reads the accumulator of the loop step. -/
partial def Tree.readsAccumulator : Tree → Bool
  | .acc => true
  | .add left right | .sub left right | .mul left right | .div left right
  | .ite _ _ left right | .lattice _ left right =>
      left.readsAccumulator || right.readsAccumulator
  | .neg operand | .sqrt operand | .unit operand _ | .apply _ operand => operand.readsAccumulator
  | _ => false

/-- The coefficient of the accumulator in `tree`, as a computation, or `none` when `tree` does
not read it. Fails when `tree` is not affine in the accumulator. -/
partial def Tree.coefficient (tree : Tree) : BackM (Option Tree) := do
  let isOne (tree : Tree) : Bool := match tree with
    | .const value _ _ => value.nat? == some 1
    | _ => false
  match tree with
  | .acc => return some (.const q((1 : ℝ)) false "")
  | .const .. | .slot _ | .fold _ => return none
  | .add left right =>
    match ← left.coefficient, ← right.coefficient with
    | some a, some b => return some (.add a b)
    | some a, none => return some a
    | none, coefficient? => return coefficient?
  | .sub left right =>
    match ← left.coefficient, ← right.coefficient with
    | some a, some b => return some (.sub a b)
    | some a, none => return some a
    | none, some b => return some (.neg b)
    | none, none => return none
  | .neg operand => return (← operand.coefficient).map .neg
  | .mul left right =>
    match ← left.coefficient, ← right.coefficient with
    | some a, none => return some (if isOne a then right else .mul a right)
    | none, some b => return some (if isOne b then left else .mul left b)
    | none, none => return none
    | some _, some _ =>
      throwError "roundoff: the loop step multiplies its accumulator by itself, so it has no \
        backward-error form; use `roundoff mixed theorem` for a forward bound"
  | .sqrt operand | .unit operand _ | .apply _ operand =>
    if (← operand.coefficient).isSome then
      throwError "roundoff: the loop step reads its accumulator under a square root, a function \
        or a rounding of its own, which the backward-error mode does not follow; use `roundoff \
        mixed theorem` for a forward bound"
    return none
  | .ite _ _ positive negative | .lattice _ positive negative =>
    match ← positive.coefficient, ← negative.coefficient with
    | none, none => return none
    | _, _ =>
      throwError "roundoff: a branch, maximum or minimum of the loop step reads its \
        accumulator, which the backward-error mode does not follow; use `roundoff mixed \
        theorem` for a forward bound"
  | .div left right =>
    if (← right.coefficient).isSome then
      throwError "roundoff: the loop step divides by its accumulator, so it has no \
        backward-error form; use `roundoff mixed theorem` for a forward bound"
    let some a ← left.coefficient | return none
    return some (.div a right)

/-- The coefficient of the accumulator in `tree` at `view`, or `none` when `tree` does not read
it. -/
def Tree.slope (tree : Tree) (view : View) : BackM (Option Q(ℝ)) := do
  let some coefficient ← tree.coefficient | return none
  return some (← coefficient.render view)

/-- A bound of the exact computation `tree` at `view` that does not read the perturbations `p`,
with the proof of `|tree| ≤ bound`. For each slot that `view` perturbs, `facts` has the growth
`g` of its perturbation `δ` and a proof of `|δ| ≤ g - 1`. Fails with `refusal` where the
perturbed part of `tree` has a loop or a perturbed divisor. -/
partial def Tree.magnitude (tree : Tree) (view : View) (p : FVarId)
    (facts : Array (Nat × Q(ℝ) × Lean.Expr)) (refusal : MessageData) :
    BackM (Q(ℝ) × Lean.Expr) := do
  let rendered ← tree.render view
  unless rendered.containsFVar p do
    return (q(|$rendered|), ← mkAppM ``le_refl #[q(|$rendered|)])
  let both (left right : Tree) (law : Name) (combine : Q(ℝ) → Q(ℝ) → Q(ℝ)) :
      BackM (Q(ℝ) × Lean.Expr) := do
    let (a, ha) ← left.magnitude view p facts refusal
    let (b, hb) ← right.magnitude view p facts refusal
    return (combine a b, ← mkAppM law #[ha, hb])
  match tree with
  | .slot index =>
    let some (_, growth, fact) := facts.find? (·.1 == index) | throwError refusal
    let key : Q(ℝ) := (← get).slots[index]!.key
    return (q(|$key| * $growth),
      ← mkAppM ``FloatLib.Numerics.Backward.abs_perturbed_le #[key, fact])
  | .add left right =>
    both left right ``FloatLib.Numerics.Backward.abs_add_le_add fun a b => q($a + $b)
  | .sub left right =>
    both left right ``FloatLib.Numerics.Backward.abs_sub_le_add fun a b => q($a + $b)
  | .mul left right =>
    both left right ``FloatLib.Numerics.Backward.abs_mul_le_mul fun a b => q($a * $b)
  | .neg operand =>
    let (a, ha) ← operand.magnitude view p facts refusal
    return (a, ← mkAppM ``FloatLib.Numerics.Backward.abs_neg_le #[ha])
  | .div left right =>
    let divisor ← right.render view
    if divisor.containsFVar p then throwError refusal
    let (a, ha) ← left.magnitude view p facts refusal
    return (q($a / |$divisor|),
      ← mkAppM ``FloatLib.Numerics.Backward.abs_div_le #[divisor, ha])
  | .lattice upper left right =>
    both left right (if upper then ``FloatLib.Numerics.Backward.abs_max_le
      else ``FloatLib.Numerics.Backward.abs_min_le) fun a b => q(max $a $b)
  | .ite condition decidable positive negative =>
    let (a, ha) ← positive.magnitude view p facts refusal
    let (b, hb) ← negative.magnitude view p facts refusal
    let bound : Q(ℝ) := mkApp5 (mkConst `ite [Level.one]) q(ℝ) condition decidable a b
    return (bound, ← mkAppOptM ``FloatLib.Numerics.Backward.abs_ite_le
      #[some condition, some decidable, none, none, none, none, some ha, some hb])
  | .sqrt operand =>
    let (a, ha) ← operand.magnitude view p facts refusal
    return (q(Real.sqrt $a), ← mkAppM ``FloatLib.Numerics.Backward.abs_sqrt_le #[ha])
  | _ => throwError refusal

/-- Carry the bound of the perturbation `w` of `shape`, proved by `h`, through the factor `c`
that `w` takes by `pattern`. At each real `δ` that takes it, `leaf root δ growth bound` gives the
new growth and its proof for `(1 + δ) * c - 1`, or for `(1 + δ) * √c - 1` when `root`. Returns
the shape and the proof of its statement at `shape.scaleTerm pattern w c`. -/
partial def Shape.scaleM (shape : Shape) (pattern : Pattern) (w h c : Lean.Expr)
    (leaf : Bool → Lean.Expr → Lean.Expr → Lean.Expr → BackM (Lean.Expr × Lean.Expr)) :
    BackM (Shape × Lean.Expr) := do
  match shape, pattern with
  | _, .keep => return (shape, h)
  | .real growth _, pattern =>
    let (grown, proof) ← leaf (pattern matches .root) w growth h
    return (.real grown, proof)
  | .pair left right, pattern =>
    let (left, hleft) ← left.scaleM pattern.sides.1 (← fst w) (← mkAppM ``And.left #[h]) c leaf
    let (right, hright) ←
      right.scaleM pattern.sides.2 (← snd w) (← mkAppM ``And.right #[h]) c leaf
    return (.pair left right, ← mkAppM ``And.intro #[hleft, hright])
  | .family domain body name, pattern =>
    withLocalDeclD name domain fun j => do
      let (scaled, proof) ←
        (body j).scaleM pattern.body (mkApp w j).headBeta (mkApp h j) c leaf
      return (.family domain (fun index => scaled.replaceFVar j index) name,
        ← mkLambdaFVars #[j] proof)
  | .list count body, pattern =>
    let elementType := (body default default).type
    withLocalDeclD `k q(ℕ) fun k => do
      let inCount ← mkAppM ``LT.lt #[k, count]
      withLocalDeclD `hk inCount fun hk => withLocalDeclD `δ elementType fun entry => do
        let before := body k hk
        let stated ← before.statement entry
        withLocalDeclD `hδ stated fun hentry => do
          let (after, proof) ← before.scaleM pattern.body entry hentry c leaf
          let scaled ← before.scaleTerm pattern.body entry c
          let map ← mkLambdaFVars #[entry] scaled
          let law ← mkLambdaFVars #[k, hk, entry, hentry] proof
          let bound ← mkLambdaFVars #[k, hk, entry] stated
          let bound' ← mkLambdaFVars #[k, hk, entry] (← after.statement entry)
          let bounds ← mkAppM ``FloatLib.Numerics.Backward.forall_getElem_map
            #[map, count, bound, bound', w, law, ← mkAppM ``And.right #[h]]
          let lengths ← mkAppM ``FloatLib.Numerics.Backward.length_map
            #[map, w, ← mkAppM ``And.left #[h]]
          return (.list count fun index inside =>
              (after.replaceFVar k index).replaceFVar hk inside,
            ← mkAppM ``And.intro #[lengths, bounds])

/-- Restate the bound of the perturbation `w` of `shape`, proved by `h`, at each real that takes
a factor by `pattern`: `leaf δ growth bound` gives its new shape and proof. The perturbation is
unchanged. -/
partial def Shape.restateM (shape : Shape) (pattern : Pattern) (w h : Lean.Expr)
    (leaf : Lean.Expr → Lean.Expr → Lean.Expr → BackM (Shape × Lean.Expr)) :
    BackM (Shape × Lean.Expr) := do
  match shape, pattern with
  | _, .keep => return (shape, h)
  | .real growth _, _ => leaf w growth h
  | .pair left right, pattern =>
    let (left, hleft) ← left.restateM pattern.sides.1 (← fst w) (← mkAppM ``And.left #[h]) leaf
    let (right, hright) ←
      right.restateM pattern.sides.2 (← snd w) (← mkAppM ``And.right #[h]) leaf
    return (.pair left right, ← mkAppM ``And.intro #[hleft, hright])
  | .family domain body name, pattern =>
    withLocalDeclD name domain fun j => do
      let (restated, proof) ←
        (body j).restateM pattern.body (mkApp w j).headBeta (mkApp h j) leaf
      return (.family domain (fun index => restated.replaceFVar j index) name,
        ← mkLambdaFVars #[j] proof)
  | .list count body, pattern =>
    let length ← mkAppM ``List.length #[w]
    let elementType := (body default default).type
    withLocalDeclD `k q(ℕ) fun k => do
      let inCount ← mkAppM ``LT.lt #[k, count]
      let inLength ← mkAppM ``LT.lt #[k, length]
      withLocalDeclD `hk inCount fun hk => withLocalDeclD `hp inLength fun hp => do
        let (restated, proof) ← (body k hk).restateM pattern.body
          (← listEntry elementType w k hp) (mkApp3 (← mkAppM ``And.right #[h]) k hk hp) leaf
        return (.list count fun index inside =>
            (restated.replaceFVar k index).replaceFVar hk inside,
          ← mkAppM ``And.intro #[← mkAppM ``And.left #[h], ← mkLambdaFVars #[k, hk, hp] proof])

/-- The input reads and the loops of `tree`, in order, a loop once. -/
def Tree.leaves (tree : Tree) : Array Nat × Array Nat :=
  let rec visit (tree : Tree) (found : Array Nat × Array Nat) : Array Nat × Array Nat :=
    match tree with
    | .slot index => (found.1.push index, found.2)
    | .fold index => (found.1, if found.2.contains index then found.2 else found.2.push index)
    | .add left right | .sub left right | .mul left right | .div left right
    | .ite _ _ left right | .lattice _ left right => visit right (visit left found)
    | .neg operand | .sqrt operand | .apply _ operand => visit operand found
    | .unit operand index => visit operand (found.1.push index, found.2)
    | _ => found
  visit tree (#[], #[])

/-- Move the factor `c` onto the perturbations of `tree`, where `hc : |c - 1| ≤ growth - 1`.
Returns a proof of `reference * c = reference'` for the references of `tree` before and after.
`nonneg?` is a proof of `0 ≤ c` when there is one: a square takes the square root of the factor
in both factors, and other products give the factor to one of them. -/
partial def Tree.scale (tree : Tree) (c growth : Q(ℝ)) (hc : Lean.Expr)
    (nonneg? : Option Lean.Expr) : BackM Lean.Expr := do
  -- The slot `index` takes the factor: `value * (1 + δ) * c = value * (1 + δ')`.
  let perturb (index : Nat) (value : Q(ℝ)) : BackM Lean.Expr := do
    let slot := (← get).slots[index]!
    match slot.delta?, slot.bound? with
    | some delta, some bound =>
      let previous := slot.growth
      let proof ← mkAppM ``FloatLib.Numerics.Backward.abs_delta_scale #[bound, hc]
      let sign? ← match slot.nonneg?, nonneg? with
        | some first, some second =>
          some <$> mkAppM ``FloatLib.Numerics.Backward.one_add_scale_nonneg #[first, second]
        | _, _ => pure none
      modify fun state => { state with slots := state.slots.set! index { slot with
        delta? := some q((1 + $delta) * $c - 1), growth := q($previous * $growth),
        bound? := some proof, nonneg? := sign? } }
      mkAppM ``FloatLib.Numerics.Backward.scale_leaf #[value, delta, c]
    | _, _ =>
      -- Only a rounding that a product may still move needs the sign of its factor.
      let sign? ← match slot.pending?, nonneg? with
        | some _, some nonneg =>
          some <$> mkAppM ``FloatLib.Numerics.Backward.one_add_nonneg #[nonneg]
        | _, _ => pure none
      modify fun state => { state with slots := state.slots.set! index { slot with
        delta? := some q($c - 1), growth := growth, bound? := some hc, nonneg? := sign? } }
      mkAppM ``FloatLib.Numerics.Backward.scale_fresh #[value, c]
  match tree with
  | .const value zero blocked =>
    unless zero do throwError "roundoff: `{value}` {blocked}"
    mkExpectedTypeHint (← mkAppM ``FloatLib.Numerics.Backward.scale_zero #[c])
      q($value * $c = $value)
  | .slot index =>
    let slot := (← get).slots[index]!
    unless slot.perturbable do throwError "roundoff: `{slot.key}` {slot.blocked}"
    perturb index slot.key
  | .unit operand index => perturb index (← operand.render)
  | .apply function _ => throwError "roundoff: `{.ofConstName function}` takes no factor"
  | .acc =>
    let some accumulator := (← get).accumulator? |
      throwError "roundoff: no loop accumulator in scope"
    unless accumulator.scalable do
      throwError "roundoff: the loop starts from a value that takes no perturbation"
    let value := accumulator.value
    match accumulator.rho?, accumulator.bound? with
    | some rho, some bound =>
      let previous := accumulator.growth
      let proof ← mkAppM ``FloatLib.Numerics.Backward.abs_mul_sub_one_le #[bound, hc]
      modify fun state => { state with accumulator? := some { accumulator with
        rho? := some q($rho * $c), growth := q($previous * $growth), bound? := some proof } }
      mkAppM ``mul_assoc #[value, rho, c]
    | _, _ =>
      modify fun state => { state with accumulator? := some { accumulator with
        rho? := some c, growth := growth, bound? := some hc } }
      mkEqRefl q($value * $c)
  | .add left right =>
    let left ← left.scale c growth hc nonneg?
    let right ← right.scale c growth hc nonneg?
    mkAppM ``FloatLib.Numerics.Backward.scale_add #[left, right]
  | .sub left right =>
    let left ← left.scale c growth hc nonneg?
    let right ← right.scale c growth hc nonneg?
    mkAppM ``FloatLib.Numerics.Backward.scale_sub #[left, right]
  | .neg operand =>
    mkAppM ``FloatLib.Numerics.Backward.scale_neg #[← operand.scale c growth hc nonneg?]
  | .mul left right =>
    let leftTakes ← left.scalable
    let rightTakes ← right.scalable
    -- A square takes the square root of the factor in both factors.
    if leftTakes && rightTakes && (← left.render) == (← right.render) then
      if let some nonneg := nonneg? then
        let root : Q(ℝ) := q(Real.sqrt $c)
        let hroot ← mkAppM ``FloatLib.Numerics.Backward.abs_sqrt_sub_one_le #[nonneg, hc]
        let rootNonneg ← mkAppM ``Real.sqrt_nonneg #[c]
        let leftProof ← left.scale root growth hroot (some rootNonneg)
        let rightProof ← right.scale root growth hroot (some rootNonneg)
        return ← mkAppM ``FloatLib.Numerics.Backward.scale_sq #[nonneg, leftProof, rightProof]
    -- The factor of a loop's accumulator stays with the factor that reads the accumulator.
    let config ← read
    let follow := config.followAccumulator && left.readsAccumulator != right.readsAccumulator
    if follow && !(if left.readsAccumulator then leftTakes else rightTakes) then
      throwError "roundoff: the factor that reads the accumulator takes no factor"
    let preferRight := if follow then right.readsAccumulator else config.preferRight
    if leftTakes && !(preferRight && rightTakes) then
      let other ← right.render
      mkAppM ``FloatLib.Numerics.Backward.scale_mul_left
        #[other, ← left.scale c growth hc nonneg?]
    else
      let other ← left.render
      mkAppM ``FloatLib.Numerics.Backward.scale_mul_right
        #[other, ← right.scale c growth hc nonneg?]
  | .div left right =>
    let other ← right.render
    mkAppM ``FloatLib.Numerics.Backward.scale_div #[other, ← left.scale c growth hc nonneg?]
  | .lattice upper left right =>
    let some nonneg := nonneg? |
      throwError "roundoff: a maximum or minimum takes a factor that is known to be nonnegative \
        only"
    let left ← left.scale c growth hc nonneg?
    let right ← right.scale c growth hc nonneg?
    mkAppM (if upper then ``FloatLib.Numerics.Backward.scale_max
      else ``FloatLib.Numerics.Backward.scale_min) #[nonneg, left, right]
  | .sqrt operand =>
    -- The argument of a square root takes the square of the factor.
    let some nonneg := nonneg? |
      throwError "roundoff: a square root takes a factor that is known to be nonnegative only"
    let proof ← operand.scale q($c * $c) q($growth * $growth)
      (← mkAppM ``FloatLib.Numerics.Backward.abs_mul_sub_one_le #[hc, hc])
      (some (← mkAppM ``mul_nonneg #[nonneg, nonneg]))
    mkAppM ``FloatLib.Numerics.Backward.scale_sqrt #[nonneg, proof]
  | .ite condition decidable positive negative =>
    let positive ← positive.scale c growth hc nonneg?
    let negative ← negative.scale c growth hc nonneg?
    mkAppOptM ``FloatLib.Numerics.Backward.scale_ite
      #[none, none, none, none, none, some condition, some decidable, some positive, some negative]
  | .fold index =>
    let fold := (← get).folds[index]!
    if let some reason := fold.obstacle then throwError "roundoff: {reason}"
    let some homogeneous := fold.homogeneous? | throwError "roundoff: the loop takes no factor"
    let unsigned : MessageData := m!"roundoff: the loop over `{fold.input}` squares an entry, \
      which takes the square root of a factor, and this factor is not known to be nonnegative"
    let law ← if fold.root then do
        let some nonneg := nonneg? | throwError unsigned
        pure (mkApp2 homogeneous c nonneg)
      else pure (mkApp homogeneous c)
    -- Each real perturbation takes the factor, or its square root, and its growth that of `c`.
    let leaf (root : Bool) (_ grown bound : Lean.Expr) : BackM (Lean.Expr × Lean.Expr) := do
      let grown : Q(ℝ) := grown
      let hfactor ← if root then do
          let some nonneg := nonneg? | throwError unsigned
          mkAppM ``FloatLib.Numerics.Backward.abs_sqrt_sub_one_le #[nonneg, hc]
        else pure hc
      return (q($grown * $growth),
        ← mkAppM ``FloatLib.Numerics.Backward.abs_delta_scale #[bound, hfactor])
    let entries := fold.entries
    let previousStart := fold.start (fold.startWitness?.map (·.term))
    let previous ← fold.loop previousStart entries.term
    -- The start takes the factor: zero keeps it, an input adds it to its perturbation.
    let (startWitness?, startProof) ← match fold.start?, fold.startWitness? with
      | none, _ =>
          pure (none, ← mkExpectedTypeHint
            (← mkAppM ``FloatLib.Numerics.Backward.scale_zero #[c]) q($previousStart * $c = 0))
      | some value, some witness =>
          let (shape, proof) ← witness.shape.scaleM .whole witness.term witness.proof c leaf
          pure (some { witness with
              shape, proof, term := ← witness.shape.scaleTerm .whole witness.term c },
            ← mkAppM ``FloatLib.Numerics.Backward.scale_leaf #[value, witness.term, c])
      | some value, none =>
          pure (some {
              name := (← perturbationName (fold.startOrigin?.getD none).toArray).appendAfter "₀"
              shape := .real growth, term := q($c - 1), proof := hc },
            ← mkAppM ``FloatLib.Numerics.Backward.scale_fresh #[value, c])
    -- The perturbations of the steps take the factor as the step's law says.
    let (shape, proof) ← entries.shape.scaleM entries.pattern entries.term entries.proof c leaf
    let term ← entries.shape.scaleTerm entries.pattern entries.term c
    let scaled ← if fold.overFin then
        mkAppM ``List.foldl_scale
          #[fold.exactStep, fold.scale, c, law, entries.term, fold.input, previousStart]
      else
        mkAppM ``List.foldl_zip_scale
          #[fold.exactStep, fold.scale, c, law, fold.input, entries.term, previousStart]
    let next : Fold := { fold with startWitness?, entries := { entries with shape, term, proof } }
    let nextStart := next.start (startWitness?.map (·.term))
    let reference ← next.loop nextStart term
    modify fun state => { state with folds := state.folds.set! index next }
    -- `scaled` moves the factor from the loop onto its start, and `startProof` into the start.
    let motive ← withLocalDeclD `start q(ℝ) fun startValue => do
      mkLambdaFVars #[startValue] (← next.loop startValue term)
    mkExpectedTypeHint
      (← mkEqTrans (← mkEqSymm scaled) (← mkAppM ``congrArg #[motive, startProof]))
      q($previous * $c = $reference)

/-- The computation and the slot of `tree` when it is perturbed as a whole by a rounding that a
backward statement must still move, with the refusal to raise if it stays. -/
def pendingUnit? (tree : Tree) : BackM (Option (Tree × Nat × MessageData)) := do
  let .unit operand index := tree | return none
  return ((← get).slots[index]!.pending?).map fun refusal => (operand, index, refusal)

/-- Refuse `form` when its computation is perturbed as a whole by a rounding that no product
moved onto an input. -/
def settled (form : Form) : BackM Form := do
  if let some (_, _, refusal) ← pendingUnit? form.tree then throwError refusal
  return form

/-- Move a rounding that stayed on a factor of the product, quotient or negation `form`: onto
the other factor of a product when that takes it, and otherwise onto the result as a whole. -/
partial def settle (form : Form) : BackM Form := do
  let restated (tree : Tree) (equality : Lean.Expr) : BackM Form :=
    return { form with
      tree, proof := ← mkAppM ``FloatLib.Numerics.Backward.restate #[form.proof, equality] }
  -- The factor `1 + δ` of the slot `index`, with its growth, bound and sign.
  let factorOf (index : Nat) : BackM (Q(ℝ) × Q(ℝ) × Lean.Expr × Option Lean.Expr) := do
    let slot := (← get).slots[index]!
    let (some delta, some bound) := (slot.delta?, slot.bound?) |
      throwError "roundoff: a rounding without a perturbation"
    let delta : Q(ℝ) := delta
    let close ← mkAppM ``FloatLib.Numerics.Backward.abs_one_add_sub_one_le #[bound]
    return (q(1 + $delta), slot.growth, close, slot.nonneg?)
  match form.tree with
  | .mul left right =>
    if let some (operand, index, _) ← pendingUnit? left then
      let (factor, growth, close, nonneg?) ← factorOf index
      let inner ← operand.render
      if ← right.scalable then
        let other ← right.render
        let moved ← right.scale factor growth close nonneg?
        -- The right factor may itself carry a rounding to move.
        return ← settle (← restated (.mul operand right) (← mkExpectedTypeHint
          (← mkAppM ``FloatLib.Numerics.Backward.move_right #[inner, moved])
          (← mkEq q($inner * $factor * $other) (← (Tree.mul operand right).render))))
      let other ← right.render
      return ← restated (.unit (.mul operand right) index)
        (← mkAppM ``mul_right_comm #[inner, factor, other])
    if let some (operand, index, _) ← pendingUnit? right then
      let (factor, growth, close, nonneg?) ← factorOf index
      let inner ← operand.render
      let other ← left.render
      if ← left.scalable then
        let moved ← left.scale factor growth close nonneg?
        return ← restated (.mul left operand) (← mkExpectedTypeHint
          (← mkAppM ``FloatLib.Numerics.Backward.move_left #[inner, moved])
          (← mkEq q($other * ($inner * $factor)) (← (Tree.mul left operand).render)))
      return ← restated (.unit (.mul left operand) index)
        (← mkEqSymm (← mkAppM ``mul_assoc #[other, inner, factor]))
    return form
  | .div left right =>
    let some (operand, index, _) ← pendingUnit? left | return form
    let (factor, _, _, _) ← factorOf index
    restated (.unit (.div operand right) index)
      (← mkAppM ``mul_div_right_comm #[← operand.render, factor, ← right.render])
  | .neg operand =>
    let some (inner, index, _) ← pendingUnit? operand | return form
    let (factor, _, _, _) ← factorOf index
    restated (.unit (.neg inner) index)
      (← mkEqSymm (← mkAppM ``neg_mul #[← inner.render, factor]))
  | _ => return form

/-- Simplify the bound `bound` of `proof : _ ≤ bound` with the identities of zero and one. -/
def tidyBound (bound : Q(ℝ)) (proof : Lean.Expr) : MetaM (Q(ℝ) × Lean.Expr) := do
  let mut theorems : SimpTheorems := {}
  for name in #[``zero_add, ``add_zero, ``zero_mul, ``mul_zero, ``mul_one, ``one_mul, ``zero_div,
      ``abs_zero, ``ite_self, ``max_self, ``Real.sqrt_zero, ``Real.exp_zero, ``sub_self,
      ``List.length_finRange] do
    theorems ← theorems.addConst name
  let context ← Simp.mkContext { implicitDefEqProofs := false } #[theorems]
  let (result, _) ← simp bound context
  if result.expr == bound then return (bound, proof)
  return (result.expr, ← mkAppM ``LE.le.trans_eq #[proof, ← result.getProof])

/-- Simplify the budget of `form` with the identities of zero and one. -/
def tidy (form : Form) : MetaM Form := do
  let (budget, proof) ← tidyBound form.budget form.proof
  return { form with budget, proof }

/-- Restate `form`, a bound for `next`, for `actual` along `equality : actual = next`. -/
def transport (form : Form) (reference : Q(ℝ)) (equality : Lean.Expr) : MetaM Form := do
  let budget := form.budget
  let motive := q(fun value : ℝ => |value - $reference| ≤ $budget)
  return { form with
    proof := (← mkAppM ``Eq.mpr #[← mkAppM ``congrArg #[motive, equality], form.proof]) }

/-- One relative error `r` in a growth `∏ (1 + r) ^ e`: the exponent is the sum of the terms
`moving` plus `fixed`. -/
structure Power where
  /-- The relative error. -/
  base : Lean.Expr
  /-- The numeral in the exponent. -/
  fixed : Nat := 0
  /-- The other terms of the exponent. -/
  moving : Array Lean.Expr := #[]

/-- The power with its exponent multiplied by `exponent`. -/
def Power.times (power : Power) (exponent : Q(ℕ)) : Power :=
  match exponent.nat? with
  | some count =>
    { power with
      fixed := power.fixed * count
      moving := power.moving.map fun term =>
        let term : Q(ℕ) := term
        let numeral : Q(ℕ) := toExpr count
        if count == 1 then term else q($numeral * $term) }
  | none =>
    let head : Array Lean.Expr := match power.fixed with
      | 0 => #[]
      | 1 => #[exponent]
      | fixed =>
        let numeral : Q(ℕ) := toExpr fixed
        #[q($numeral * $exponent)]
    { power with
      fixed := 0
      moving := head ++ power.moving.map fun term =>
        let term : Q(ℕ) := term
        q($term * $exponent) }

/-- The relative errors of `growth`, a product of powers of terms `1 + r`, each with its
exponent, or `none` for another term. -/
partial def powers? (growth : Lean.Expr) : BackM (Option (Array Power)) := do
  if growth.nat? == some 1 then return some #[]
  if growth.isAppOfArity ``HAdd.hAdd 6 && (growth.getArg! 4).nat? == some 1 then
    return some #[{ base := ← canonical (growth.getArg! 5), fixed := 1 }]
  if growth.isAppOfArity ``HMul.hMul 6 then
    let some left ← powers? (growth.getArg! 4) | return none
    let some right ← powers? (growth.getArg! 5) | return none
    return some <| right.foldl (init := left) fun all power =>
      match all.findIdx? (·.base == power.base) with
      | some index => all.modify index fun known =>
          { known with fixed := known.fixed + power.fixed, moving := known.moving ++ power.moving }
      | none => all.push power
  if growth.isAppOfArity ``HPow.hPow 6 then
    let some inner ← powers? (growth.getArg! 4) | return none
    return some (inner.map (·.times (growth.getArg! 5)))
  return none

/-- The bound `growth - 1` as the statement shows it, with the relative errors it reads: `r`
for one relative error, and otherwise `∏ (1 + r) ^ e - 1` with one exponent for each `r`. -/
def statedBound? (growth : Lean.Expr) : BackM (Option (Q(ℝ) × Array Lean.Expr)) := do
  let some powers ← powers? growth | return none
  let powers := powers.filter fun power => power.fixed != 0 || !power.moving.isEmpty
  if let #[power] := powers then
    if power.fixed == 1 && power.moving.isEmpty then return some (power.base, #[power.base])
  let mut product? : Option Q(ℝ) := none
  for power in powers do
    let base : Q(ℝ) := power.base
    let fixed : Q(ℕ) := toExpr power.fixed
    let moving? : Option Q(ℕ) := power.moving.foldl (init := none) fun sum? term =>
      match sum? with
      | some sum =>
        let sum : Q(ℕ) := sum
        let term : Q(ℕ) := term
        some q($sum + $term)
      | none => some term
    let factor : Q(ℝ) := match moving? with
      | none => if power.fixed == 1 then q(1 + $base) else q((1 + $base) ^ $fixed)
      | some moving =>
        if power.fixed == 0 then q((1 + $base) ^ $moving) else q((1 + $base) ^ ($moving + $fixed))
    product? := some (match product? with
      | some product => q($product * $factor)
      | none => factor)
  let some product := product? | return none
  return some (q($product - 1), powers.map (·.base))

/-- The bound of one real perturbation as the statement shows it: `(1 + u) ^ k - 1` for the `k`
factors `u` it took, or `u` for one. `ring` proves the two bounds equal after reading each
`1 + r` as one variable, so that it compares powers of it; the bound is unchanged when it does
not. -/
def statedLeaf (_ growth bound : Lean.Expr) : BackM (Shape × Lean.Expr) := do
  let unchanged : Shape × Lean.Expr := (.real growth, bound)
  let some (stated, relatives) ← statedBound? growth | return unchanged
  let growth : Q(ℝ) := growth
  if stated == q($growth - 1) then return unchanged
  let equal (abstract : Bool) : TacticM (Option Lean.Expr) := attempt? 2000 do
    let mut statement : Lean.Expr := q($growth - 1 = $stated)
    let mut bases : Array Lean.Expr := #[]
    if abstract then
      for relative in relatives do
        let relative : Q(ℝ) := relative
        let base : Q(ℝ) := q(1 + $relative)
        let abstracted ← kabstract statement base
        if abstracted.hasLooseBVars then
          statement := .forallE `b q(ℝ) abstracted .default
          bases := bases.push base
    let equality ← mkFreshExprMVar statement
    let remaining ← Lean.Elab.Tactic.run equality.mvarId!
      (evalTactic (← `(tactic| (intros; ring))))
    unless remaining.isEmpty do return none
    return some (mkAppN (← instantiateMVars equality) bases.reverse)
  let some equality ← (do if let some found ← equal true then pure (some found) else equal false) |
    return unchanged
  trace[roundoff] "bound {growth} - 1 restated as {stated}"
  return (.real growth (some stated), ← mkAppM ``LE.le.trans_eq
    #[bound, ← mkExpectedTypeHint equality q($growth - 1 = $stated)])

end Backward

end FloatLib.Floats.Formats.BinaryInterchange.Roundoff
