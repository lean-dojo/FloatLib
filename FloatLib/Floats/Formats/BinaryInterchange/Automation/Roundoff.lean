/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Automation.Roundoff.Tactic
public import FloatLib.Numerics.ErrorBound.SumLoop

/-!
# Numerical proofs from the implementation

`roundoff` builds an absolute-error proof from configured floating-point arithmetic itself, so
there is no model-specific expression language and no second copy of the implementation to supply.
It keeps each operation and the capability selected for it, reuses FloatLib's primitive theorems,
and shares the analysis of repeated subexpressions. The same analysis also proves mixed bounds
`MixedError actual reference r a`, finiteness `isFinite value = true`, decoded exact values
`toRat? value = some q`, signs of decoded values, and conjunctions of these.

It tries FloatLib's exact operations first, such as a finite `x - x`, products with zero or one and
sums with zero, whose results are finite with no range condition. Then it composes each
operation's local rounding with propagation through the exact real operation. A sum of same-sign
values keeps a relative error weighted by its terms' magnitudes, while cancellation keeps an
absolute one.

Here is a dot product from our `roundoff` tests, where `Value` is the configured type
`ExecFloat (Configured.Family format code plan)`:

```lean
def dot {n : Nat} (x y : Fin n → Value) : Value :=
  Fin.foldl n (fun s j => s + x j * y j) 0

roundoff mixed theorem dot_mixedError :=
  fun {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (dot x y)
```

The loop is analyzed once for a symbolic accumulator, so the theorem holds at every length `n`. Its
reference is `List.foldl referenceStep 0 (List.finRange n)`, the exact dot product of the decoded
entries. Its premise is a `List.AllSteps` condition on the states the loop visits, and it concludes
`ExecFloat.Binary.isFinite output = true` together with the mixed bound.
`List.abs_sub_le_of_sumFold` restates the generated bound of a summation loop like this one in
closed form, and `List.abs_sub_le_of_sumFold_of_exact` that of a sum of exact terms. The
descriptor, storage plan and scalar representation stay parameters. IEEE-format and finiteness
conditions are proved from the context when possible and otherwise stay goals.

## Tactic, term and theorem forms

On an ordinary target, `roundoff` leaves any missing premises as proof goals. To inspect a
generated reference and budget without writing them first, use the term form in a local proof:
`have bound := by roundoff (ExecFloat.Binary.toReal (program input))`. Its range and domain
premises must already be provable. To generate a reusable conditional theorem, use
`roundoff theorem name := fun input => ExecFloat.Binary.toReal (program input)`. The generated
statement records the required conditions, and you prove them when you apply it.

`roundoff mixed theorem` states a mixed bound instead, against the exact computation on the decoded
inputs, except at a contracted call whose model the analysis cannot read (see the contracts below)
and at the choices listed under the trust assumptions, which stay as the program makes them.
With `using` an equation whose left side is the inferred reference, written before `:=`, a mixed
theorem states the bound against the right side. When the observation is a configured
`ExecFloat.Binary.toReal value`, the bound is preceded by `isFinite value = true`, derived from
range conditions or, where the analysis cannot derive it, assumed in the premise. A model
observation `Model.toReal`, or an observation under another function, states the mixed bound alone.

The mixed reference reads a stored function only at index data and casts only index data to the
reals, with index data as defined below. A cast of an integer computed from numerical values is
rejected. A stored container, such as a tensor, is read at any index through its own getter or a
registered read. An index chosen by comparing stored values, as a pivot is, selects a stored value,
but one computed from rounded values would keep that choice in the reference. A getter of another
dictionary is analyzed as the function it is.

A mixed statement names the recurrences and folds of loops, the output, reference and budgets, and
other large repeated real terms by `let`. An absolute statement names its reference and budget.
Both spell binary16, bfloat16, binary32 and binary64 by name in the format's constants, while values
keep the program's spelling.

## Loops

A loop of a registered kind (`Extension.loops`) over lists, arrays, vectors, `Fin n` and matrices,
and over the containers another library registers, reuses one scalar invariant theorem without
unrolling its elements. Loops carry a relational invariant: the finiteness of the accumulator and a
sign of its reference when these are established, and otherwise their absolute analysis. The step's
condition concerns the states the loop actually visits (`List.AllSteps`), while other conditions can
be contracts on all inputs. A registered sum (`Extension.sums`) is analyzed as the loop its laws
write it as. A selection `if m < x then x else m` of finite values, the step of C's maximum loop, is
read as `max`. It is finite when its operands are, and a loop whose step keeps zero budgets zero is
exact.

Producers and operations on these containers are supported as far as registered laws expose them.
A loop over a computed container is first fused into its step (`Loop.fusions`), so that the
reference reads the inputs the producer reads. Otherwise the reference may read the loop's entries
only when they are stored inputs or indices, from an index computation such as `List.range` or
`List.finRange` whose length, start and step are themselves index data. A loop whose reference reads
an entry of any other computed container, whatever its type, is rejected. So is a loop over a
computed container that is not index data whose reference ignores its entries but still folds over
the container, since it takes a step for each entry.

A loop whose state is a pair or a nondependent record carries one relation of all its components
instead (`List.fold_relation`). That relation consists of a bound for each value of the observed
format, exact where the step keeps it exact, and equality with a shadow copy for data whose type
mentions no numerical carrier. A record is split into its fields, so the fields of a record of
binary32 values, or of a wrapper of one, are values of that format. A shadow copy is part of the
reference, so it starts at index data and each step updates it to index data.

The shadow copy reads a test of exact finite values as the test of their references when the
conditions, indices and other data in those references are index data too. It reads another test of
rounded values as the test of its operands' references, under the premise in the step's condition
that the two agree. It does so when that test is FloatLib's own test under the observation's codec
and the references of its operands, and of the components they read, are plain real expressions over
decoded stored values.

A library can also register a relation that one step preserves, such as Kahan's bound on the sum
minus its compensation, with lemmas that start it and read a bound off it
(`Extension.stepRelations`). A loop whose step unfolds to the relation's step is then read through
it before the rules for the operations of its step are tried, and the loop's budgets are the
relation's budgets.

## Index data

Index data is built from literals, parameters, the fields and lengths of inputs, arithmetic on them
and comparisons of stored values. It computes no numerical value, and these rules keep it that way:

* It reads a stored value of a floating-point, rational or real type only to compare, select or
  store it. Such types include Lean's own float models, and a type counts even through an alias of
  any reducibility, a local definition or a field of a record. It does this through FloatLib's own
  order dictionaries, which take FloatLib's own comparison, through a registered read and the
  storage classes whose methods its laws pin (`Read.trusts`, `Read.laws`), or through a function
  generic in the value's type, which can only compare, select or store it, or hand it to the
  functions and dictionaries it takes.
* A numerical function is any term whose type, at default transparency and with its local
  definitions expanded, is a function type over such values. It is applied only fully and only to
  index data whose types hold no number, however the function is produced: a variable, a projection
  or a field of a record applied to arguments, or the value of any other constant at the arguments
  its type names, such as an entry that a getter reads from a container, applied to the arguments
  after those.
* A value can hold a numerical function when it is one, a list, an array, an option, a pair or a
  record of them at any depth, also of an indexed family at its indices, or a function that takes a
  type and so can be applied at a numerical one. A definition that takes such a value is read
  through its value and checked use by use, and rejected when that does not finish. A function
  written as `fun` is checked through its body, and is such a value when its result can hold one.
* Index data never looks into such a value. A value computed from numerical values, such as the
  bound `x * x` against which comparisons could rebuild a rounded square, is not index data.
* Index data calls only definitions whose values are index data in turn. Every constant of a value
  counts, also one that only its proofs use, so an opaque constant or an axiom that is not a proof,
  whose value cannot be inspected, is rejected.
* Lean's core library is the one exception, and only for such constants, since the module system
  exports many core definitions without their values. An opaque constant or an axiom of a module
  that Lean's own library holds is index data when its type mentions no carrier, except
  `Classical.choice`. A core definition whose value is exported is read through it like any other.

An entry of a stored function read at index data, and an entry of a stored container, is exact
data.

## Literals, casts and primitive operations

Inputs are decoded as stored. Floating-point literals and casts inside the computation carry
conversion error relative to their exact real values, except a literal that the format represents,
such as `127` in binary32, which converts without error. A closed condition on a literal, such as
its range, is checked by arithmetic with the largest finite value of the format in closed form. One
the check proves is discharged, and one it refutes, such as the range of `1e40` in binary32 or the
nonzero divisor of a division by the literal `0`, stops the analysis with an error. A condition the
bounded check settles neither way stays a premise, as in a format with more than 20 exponent bits
or `2 ^ 20` fraction bits. The conversion of an integer or a natural number has relative error `u` and
keeps its sign. It is exact at magnitudes up to `2 ^ p`, `p = fracWidth + 1`, as a hypothesis can
show. Rounding to an integral value moves a value by at most one half to nearest and one otherwise,
and a C integer cast reads that rounding. An `int8_t` cast keeps its integer when the integer's
bound stays below `2 ^ 7`, a condition on the reals.

The primitive float rules require finite results, and division a finite divisor. Square root also
requires a finite operand in its domain, which the sign of the operand establishes, and above zero
it divides the error of its operand by about `2 √x₀`. A weak sign of a rounded value needs no
finiteness, because a NaN or an infinity has real value zero. Finiteness of a result follows from a
range condition on the enclosure of its exact value, an inequality on the inputs and budgets.
Where the analysis cannot derive the finiteness of an output, such as the value a `match` on an
option returns, the finiteness stays a premise, and a mixed theorem then assumes the finiteness it
concludes. A supplied error tolerance still has to bound the generated budget.

## Elementary functions

A call of FloatLib's correctly rounded exponential, logarithm, `expMinus1`, `logPlus1` or `expMul`
on an IEEE descriptor contributes half an ulp of local error at its real result in the absolute
analysis, and the unit roundoff with the underflow allowance in the mixed analysis, unless an exact
case applies. A dictionary method gets this bound only when its selected implementation is
identified with one of those functions, either by a registered implementation equality
(`Extension.bridges`) or because the selected instance unfolds to such a call. Another instance of
the same class, whose implementation is neither, gets none. The domain and range conditions of
FloatLib's rounding theorem become premises, and a premise that such a call is finite becomes the
same conditions.

Sine, cosine and the hyperbolic functions reuse FloatLib's rational enclosures instead. The distance
from the actual candidate to the enclosure endpoints bounds its local error, and input perturbations
are propagated by the same registered real-error theorems.

## Registered rules and hypotheses

`[roundoff_rule]` registers an existing numerical bound or observation equality. It also accepts
imported, polymorphic theorems and local registrations of the rule shapes it recognizes. An equality
adds no local rounding error of its own, and the computation on its right side is analyzed as usual.
A registered theorem concluding that a Boolean test is `false`, such as the NaN or infinity test of
a finite value, decides a branch guard on that test when the context discharges the theorem's
premises and its instantiated proof keeps no unresolved obligation. Only the other branch is then
analyzed.

Quantified input-error assumptions can be reused at each coordinate. A hypothesis stated like a
generated theorem, such as the contract of a function the program takes, is used as a registered
one is: its mixed bound by mixed analysis and its finiteness for finiteness goals. When the analysis
reads the contract's model, the error of the call's argument is propagated through it, so that the
reference is the model at the exact argument. A model it has no rule for, such as a real function
the program takes, keeps the model at the decoded computed argument. The statement then shows that
argument, and its rounding is not part of the bound.

## Trust assumptions

The kernel checks the displayed proposition from its hypotheses and dependencies, and the axiom
audit lists the axioms it rests on. Neither shows that the displayed reference agrees with an
exact-arithmetic specification written independently, and that agreement rests on what follows.
The analysis checks three conditions. A registered read counts as a stored read only when it uses
the dictionaries of Lean's own getters or has a checked selection equality to such a read
(`Read.isCertified`). Registration checks that the laws a read registers (`Read.laws`) give each
method of a class it trusts (`Read.trusts`) a defining equality, directly or through an observer
with an injectivity law (`Read.checkLaws`). Such a class is storage only for a certified read whose
laws use no constant that holds a number. Its dictionary is index data only as an input, a local
definition of an accepted dictionary, or a constant whose optional decisions of equality reduce to
`none` or `some` for generic arguments, applied to types, proofs, local variables without a visible
value or their data fields, and checked index data. A value of a type parameter of the statement
counts as possibly numerical, unless a dictionary of such a storage class supplies its type.

The rest is assumed:

* The opaque constants and axioms of the running Lean's own library, other than
  `Classical.choice`, hold no number when their types hold none.
* FloatLib's IEEE comparisons on a configured type compare its decoded models, while its decidable
  equality compares the stored values, so the two zeros differ and a NaN equals itself.
* A configured type's codec and storage plan define what its stored words mean.
* Lean's list, array and vector getters, with their forwarding instance for `Fin` indices, select
  stored entries.
* The observers a read registers mean what they say about its storage.
* Types that a storage class supplies, applications of its type families included, stay abstract to
  index computations: their identity is not tested to produce data, and their values are not
  transported to expose another representation. Registration screens the direct occurrences of the
  class's own type projections in its proof fields and in the laws a read registers, and rejects
  their use as terms, in equalities of types and as types of heterogeneous equalities. The screen
  skips the arguments a constant takes as proofs, does not unfold the definitions it calls, and does
  not follow one of its types through a constructed type, such as `ULift` of it.
* Index data is not checked inside the types it mentions. Such a type, with the definitions and
  dictionaries it uses, is assumed not to be chosen by a rounded value, as
  `if x * x == x then Unit else Empty` is.
* A local value without a visible definition or a supplied error bound, such as one a `have` in a
  tactic proof introduces, is an input whatever computed it.
* An entry that the genuine getter of an input option returns is a stored input.

Some choices stay as the program makes them. A stored read keeps the program's index, also one
chosen from rounded values. A branch whose condition the analysis cannot decide keeps the program's
condition. An exact test of a loop component can inherit such a choice through the component's
reference, while an agreement test whose references depend on it is rejected.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.Roundoff

open Lean Meta Elab Tactic Qq
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

/-- Prove an absolute-error bound, a mixed bound, finiteness, a decoded value or a sign of a
configured computation from its code, leaving the conditions it cannot prove as goals. -/
elab "roundoff" : tactic => roundoffTactic

/-- Expose selected implementation definitions before the numerical pass. -/
syntax "roundoff" " [" ident,+ "]" : tactic

macro_rules
  | `(tactic| roundoff [$[$names:ident],*]) =>
      `(tactic| (simp (config := {
        failIfUnchanged := false, implicitDefEqProofs := false }) only
        [$[$names:ident],*] at *; roundoff))

/-- Fail when `proof` depends on an unassigned goal that is not among the obligations `pending`,
through its assignments or the types of the goals they reach. -/
def checkObligations (proof : Lean.Expr) (pending : Array MVarId) : MetaM Unit := do
  let mut reached : Std.HashSet MVarId := {}
  let mut goals ← getMVarsNoDelayed proof
  while let some goal := goals.back? do
    goals := goals.pop
    if reached.contains goal then continue
    reached := reached.insert goal
    unless pending.contains goal do
      throwError "roundoff: the generated proof depends on a goal that is not an obligation: \
        {← instantiateMVars (← goal.getType)}"
    goals := goals ++ (← getMVarsNoDelayed (← goal.getType))

/-- Infer a reference and budget with the ordinary numerical pass, retaining its obligations.
In `mixed` mode, infer a mixed bound instead, preceded by the finiteness of the configured value
that `actual` decodes when `actual` is `ExecFloat.Binary.toReal value`. -/
def inferBound (actual : Q(ℝ)) (mixed : Bool := false) :
    TacticM (Lean.Expr × Array MVarId) := do
  let reference : Q(ℝ) ← mkFreshExprMVar q(ℝ)
  let target ← if mixed then do
      let relative : Q(ℝ) ← mkFreshExprMVar q(ℝ)
      let absolute : Q(ℝ) ← mkFreshExprMVar q(ℝ)
      let bound : Q(Prop) := q(MixedError $actual $reference $relative $absolute)
      if let (true, some value) := (actual.isAppOf ``ExecFloat.Binary.toReal, decodedValue? actual)
      then
        mkAppM ``And #[← mkEq (← mkAppM ``ExecFloat.Binary.isFinite #[value])
          (mkConst ``Bool.true), bound]
      else pure bound
    else do
      let budget : Q(ℝ) ← mkFreshExprMVar q(ℝ)
      pure q(|$actual - $reference| ≤ $budget)
  let numerical ← mkFreshExprMVar target
  let pending ← Tactic.run numerical.mvarId! do evalTactic (← `(tactic| roundoff))
  let pending ← pending.filterM fun goal => return !(← goal.isAssigned)
  -- State the bound for the computation as written, not for its analyzed normal form.
  let proof ← mkExpectedTypeHint (← instantiateMVars numerical) (← instantiateMVars target)
  checkObligations proof pending.toArray
  return (proof, pending.toArray)

/-- Infer a numerical statement for a local `have` with the ordinary proof-producing pass. The
term is a real observation of the computation, and both its reference and budget are inferred. -/
elab "roundoff" "(" value:term ")" : tactic => withMainContext do
  let actual : Q(ℝ) ← Term.elabTermEnsuringType value q(ℝ)
  Term.synthesizeSyntheticMVarsNoPostponing
  let (proof, pending) ← inferBound actual
  let mut goals := pending
  for goal in (proof.collectMVars {}).result do
    unless goals.contains goal do goals := goals.push goal
  let mut types := #[]
  let mut premises := #[]
  for goal in goals do
    if ← goal.isAssigned then continue
    let type ← instantiateMVars (← goal.getType)
    unless types.contains type do
      types := types.push type
      premises := premises.push m!"{type}"
  unless premises.isEmpty do
    throwError "roundoff: prove these premises before inferring a local bound:\n\
      {MessageData.joinSep premises.toList (m!"\n")}"
  let goal ← (← getMainGoal).change (← inferType proof)
  goal.assign proof
  replaceMainGoal []

/-- Refuse a generated conditional theorem when a closed obligation is false: when it computes to
false, or when arithmetic refutes it (`refutesClosed`), such as the range of the literal `1e40` in
binary32 or the condition `0 < 0` of a division by the literal `0`. The check is bounded, and it
cannot decide whether arbitrary premises are consistent. -/
def checkGeneratedConditions (pending : Array MVarId) : TacticM Unit := do
  for goal in pending do
    if ← goal.isAssigned then continue
    let condition ← instantiateMVars (← goal.getType)
    if condition.hasFVar || condition.hasExprMVar then continue
    let refuted? ← attempt? 500 do
      let decision ← withDefault (whnf (← mkDecide condition))
      return if decision.isConstOf ``Bool.false then some () else none
    if refuted?.isSome || (← refutesClosed condition) then
      throwError "roundoff: a required numerical condition is false: {condition}"

/-- The number of nodes of `expression`, counting shared subterms once per occurrence, up to
`limit`. -/
partial def termSize (expression : Lean.Expr) (limit : Nat := 100000) : Nat :=
  let rec go (expression : Lean.Expr) (count : Nat) : Nat :=
    if count ≥ limit then count else
    match expression with
    | .app function argument => go argument (go function (count + 1))
    | .lam _ type body _ | .forallE _ type body _ => go body (go type (count + 1))
    | .letE _ type value body _ => go body (go value (go type (count + 1)))
    | .mdata _ inner | .proj _ _ inner => go inner (count + 1)
    | _ => count + 1
  go expression 0

/-- Spell the formats of a generated statement by name. A descriptor rebuilt from the fields of a
format is that format, and a literal descriptor of binary16, bfloat16, binary32 or binary64 is its
name. A format is renamed only where the arguments that depend on it are renamed with it, such as
in the unit roundoff or the largest finite value of the format. Configured values, storage plans
and proofs, and the formats they depend on, keep the program's spelling, so the statement's terms
have the types the program's do. The result is definitionally equal to `statement`. -/
partial def nameFormats (statement : Lean.Expr) : MetaM Lean.Expr := do
  let catalogue := #[``FloatFormat.binary16, ``FloatFormat.bfloat16, ``FloatFormat.binary32,
    ``FloatFormat.binary64]
  let named? (term : Lean.Expr) : MetaM (Option Lean.Expr) := do
    unless term.isAppOf ``ExecFloat.Binary.descriptor || term.isAppOf ``FloatFormat.mk do
      return none
    if term.hasLooseBVars then return none
    if let some width := term.getAppArgs[0]? then
      if width.isAppOfArity ``FloatFormat.expWidth 1 then
        let format := width.appArg!
        if ← withNewMCtxDepth (isDefEq term format) then return some format
    for name in catalogue do
      if ← withNewMCtxDepth (isDefEq term (mkConst name)) then return some (mkConst name)
    return none
  -- Whether `term` is renamed with the formats it mentions: it has no variables, configured
  -- values or proofs, whose types keep the original spelling.
  let environment ← getEnv
  let renamable (term : Lean.Expr) : Bool :=
    !term.hasLooseBVars && !term.hasFVar && !term.hasMVar &&
      term.getUsedConstants.all fun name =>
        !(`FloatLib.Floats.ExecFloat).isPrefixOf name &&
          !(`FloatLib.Floats.Formats.BinaryInterchange.Configured).isPrefixOf name &&
          !((environment.find? name).any (·.isThm)) && !name.isInternal
  let visited ← IO.mkRef ({} : Std.HashMap Lean.Expr Lean.Expr)
  let rec visit (term : Lean.Expr) : MetaM Lean.Expr := do
    if let some done := (← visited.get).get? term then return done
    let result ← match term with
      | .app .. => do
          if let some name ← named? term then return name
          let function := term.getAppFn
          let arguments := term.getAppArgs
          let parameters ← if function.isConst then
              pure (← getFunInfoNArgs function arguments.size).paramInfo
            else pure #[]
          let mut next := #[]
          for h : index in [:arguments.size] do
            let argument := arguments[index]
            -- An argument that the types of others mention is renamed only with them.
            let dependents := (List.range arguments.size).filter fun later =>
              (parameters[later]?.map (·.backDeps.contains index)).getD false
            if dependents.all fun later => renamable arguments[later]! then
              next := next.push (← visit argument)
            else next := next.push argument
          pure (mkAppN (← visit function) next)
      | .lam name type body info => return .lam name (← visit type) (← visit body) info
      | .forallE name type body info => return .forallE name (← visit type) (← visit body) info
      | .letE name type value body nondep =>
          return .letE name (← visit type) (← visit value) (← visit body) nondep
      | .mdata data inner => return .mdata data (← visit inner)
      | .proj typeName index inner => return .proj typeName index (← visit inner)
      | _ => pure term
    visited.modify (·.insert term result)
    return result
  visit statement

/-- Replace each proof or instance argument in `statement` by the first one of the same type, so
that terms differing only in these arguments, such as two spellings of one coordinate cast, are
shared. A proof is replaced by proof irrelevance and an instance only by one it unifies with at
instance transparency. Proofs and instances are not entered, and those mentioning a variable bound
inside the statement are kept. The result is definitionally equal to `statement`. -/
partial def canonicalArguments (statement : Lean.Expr) : MetaM Lean.Expr := do
  let first ← IO.mkRef ({} : Std.HashMap Lean.Expr Lean.Expr)
  let visited ← IO.mkRef ({} : Std.HashMap Lean.Expr Lean.Expr)
  let canonical (argument : Lean.Expr) (byUnification : Bool) : MetaM Lean.Expr := do
    let type ← instantiateMVars (← inferType argument)
    let some earlier := (← first.get).get? type | do
      first.modify (·.insert type argument)
      return argument
    if earlier == argument then return argument
    if byUnification && !(← withReducibleAndInstances (isDefEq earlier argument)) then
      return argument
    return earlier
  let rec visit (term : Lean.Expr) : MetaM Lean.Expr := do
    if let some done := (← visited.get).get? term then return done
    let result ← match term with
      | .app .. => do
          let function := term.getAppFn
          let arguments := term.getAppArgs
          let parameters ← if function.isConst then
              pure (← getFunInfoNArgs function arguments.size).paramInfo
            else pure #[]
          let mut next := #[]
          for h : index in [:arguments.size] do
            let argument := arguments[index]
            let parameter? := parameters[index]?
            let special := parameter?.any fun parameter =>
              parameter.isProp || parameter.isInstImplicit
            if special && !argument.hasLooseBVars && !argument.hasExprMVar then
              next := next.push (← canonical argument (parameter?.any (·.isInstImplicit)))
            else next := next.push (← visit argument)
          pure (mkAppN (← visit function) next)
      | .lam name type body info => return .lam name (← visit type) (← visit body) info
      | .forallE name type body info => return .forallE name (← visit type) (← visit body) info
      | .letE name type value body nondep =>
          return .letE name (← visit type) (← visit value) (← visit body) nondep
      | .mdata data inner => return .mdata data (← visit inner)
      | .proj typeName index inner => return .proj typeName index (← visit inner)
      | _ => pure term
    visited.modify (·.insert term result)
    return result
  visit statement

/-- The names of the step, reference, relative-error and absolute-error functions that a mixed
fold's recurrences take as their first four arguments. -/
def recurrenceArguments : Array Name :=
  #[`step, `referenceStep, `relativeStep, `absoluteStep]

/-- The names of the step, reference and error functions that an absolute fold's recurrences take
as their first three arguments. -/
def errorRecurrenceArguments : Array Name :=
  #[`step, `referenceStep, `errorStep]

/-- The names of the step, reference and budget functions that the recurrences of a loop whose
state is a tuple take as their first three arguments. -/
def relationRecurrenceArguments : Array Name :=
  #[`step, `referenceStep, `budgetStep]

/-- The name of a shared real term in a generated statement, after its outermost operation. -/
def realName (head : Name) : Name :=
  match head with
  | ``HAdd.hAdd => `sum
  | ``HSub.hSub => `difference
  | ``HMul.hMul => `product
  | ``HDiv.hDiv => `quotient
  | ``Real.sqrt => `root
  | ``abs => `magnitude
  | ``Min.min => `minimum
  | ``Max.max => `maximum
  | ``Inv.inv => `inverse
  | ``Neg.neg => `negation
  | ``HPow.hPow => `power
  | ``Real.exp => `exponential
  | ``Real.log => `logarithm
  | _ => `term

/-- Name the parts of a generated statement that are hard to read when repeated in full. These are
the recurrence functions of folds, the folds and their accumulated errors, with `decoded` large
repeated decoded values and coordinates, large repeated real terms, and the value, reference and
budgets of the concluding bound, bound in this order. Each becomes a `let`, so the result is
definitionally equal to `statement`. Without `full`, only the reference and budget of the
concluding bound are named. An absolute statement repeats the decoded value of every intermediate
result, and naming its parts one at a time is costly there. -/
partial def shareSubterms (statement : Lean.Expr) (threshold : Nat := 60) (full := true) :
    MetaM Lean.Expr := do
  let loops := (← extension).loops
  let sums := ((← extension).sums.filter fun sum => !sum.entries && !sum.exact).map (·.head)
  let recurrences := loops.map (·.foldRelative) ++ loops.map (·.foldAbsolute) ++
    loops.map (·.mixedFoldStep)
  let errorRecurrences := loops.map (·.foldError) ++ loops.map (·.foldStep)
  let relationRecurrences := loops.foldl (init := #[]) fun names loop =>
    match loop.relation with
    | some (step, budget, _) => names.push step |>.push budget
    | none => names
  -- The heads of the terms that are candidates without `others`.
  let heads := (recurrences ++ errorRecurrences ++ relationRecurrences ++
    (loops.filter (·.named)).map (·.fold) ++ sums).foldl (·.insert ·) ({} : Std.HashSet Name)
  -- The candidates: recurrence functions and folds, or with `others` repeated decoded values
  -- and coordinates, smallest first. The latter are collected once the conclusion's parts are
  -- named, from their values too, and bound around them. Each comes with the term it was read
  -- from: a function with its recurrence, any other candidate with itself.
  let candidates (body : Lean.Expr) (others : Bool) (real : Bool := false) :
      MetaM (Array (Lean.Expr × Name × Lean.Expr)) := do
    let (terms, seen) := occurrences body
    let table := if others then sizes body else {}
    let repeated (term : Lean.Expr) : Bool := seen.get? term == some true
    let mut functions := #[]
    let mut folds := #[]
    let mut remaining := #[]
    -- A fold is named only when fully applied; its partial applications are shared prefixes.
    let applied (term : Lean.Expr) : MetaM Bool := do
      return !(← whnfR (← inferType term)).isForall
    for term in terms do
      let head := term.getAppFn.constName?.getD .anonymous
      unless others || heads.contains head do continue
      if recurrences.contains head || errorRecurrences.contains head ||
          relationRecurrences.contains head then
        let info ← getFunInfoNArgs term.getAppFn term.getAppNumArgs
        let explicit := (term.getAppArgs.zip info.paramInfo).filterMap fun (argument, param) =>
          if param.binderInfo.isExplicit then some argument else none
        let names := if recurrences.contains head then recurrenceArguments
          else if errorRecurrences.contains head then errorRecurrenceArguments
          else relationRecurrenceArguments
        for (argument, name) in explicit.zip names do
          if argument.isLambda && repeated argument then
            functions := functions.push (argument, name, term)
      if loops.any (·.foldRelative == head) then
        if ← applied term then folds := folds.push (term, `relativeError, term)
      else if loops.any (·.foldAbsolute == head) then
        if ← applied term then folds := folds.push (term, `absoluteError, term)
      else if loops.any (·.foldError == head) then
        if ← applied term then folds := folds.push (term, `loopError, term)
      else if loops.any (·.relation.any (·.2.1 == head)) then
        if repeated term && (← applied term) then folds := folds.push (term, `loopBudgets, term)
      else if loops.any (fun loop => loop.named && loop.fold == head) && repeated term then
        let type ← whnfR (← inferType term)
        unless type.isForall do
          folds := folds.push
            (term, if type.isConstOf ``Real then `exactFold else `computedFold, term)
      else if sums.contains head && repeated term && (← applied term) then
        folds := folds.push (term, `computedSum, term)
      else if others && repeated term then
        -- Decoded values and coordinates, and large repeated real terms of the reference and
        -- budgets named after their operation; representation data stays where it is.
        let size := table.getD term 0
        if size ≥ threshold then
          let name? ← if real then
              if head.isAnonymous || head == ``ExecFloat.Binary.toReal || head == ``Fin.cast then
                pure none
              else if (← whnfR (← inferType term)).isConstOf ``Real then
                pure (some (realName head))
              else pure none
            else if head == ``ExecFloat.Binary.toReal && (← applied term) then
              pure (some `decoded)
            else if head == ``Fin.cast then pure (some `index)
            else pure none
          if let some name := name? then remaining := remaining.push (term, name, size)
    if others then
      -- Smallest first, then in order of first occurrence.
      let sorted := (remaining.zipIdx.qsort fun ((_, _, a), i) ((_, _, b), j) =>
        a < b || (a == b && i < j)).map (·.1)
      return sorted.map fun (term, name, _) => (term, name, term)
    return functions ++ folds
  -- Bind `term` as `name`, or a numbered variant of it, around the rest of the statement. With
  -- `defeq`, occurrences that differ from `term` only up to reducible unfolding and instances,
  -- such as in a literal's representation or an `id` around a coordinate, are bound as well.
  let letIn (name : Name) (used : NameSet) (term body : Lean.Expr)
      (rest : Lean.Expr → NameSet → MetaM Lean.Expr) (defeq : Bool := false) :
      MetaM Lean.Expr := do
    let mut fresh := name
    let mut index := 2
    while used.contains fresh do
      fresh := name.appendIndexAfter index
      index := index + 1
    withLetDecl fresh (← inferType term) term fun shared => do
      let replaced := body.replace fun child => if child == term then some shared else none
      let replaced ← if defeq then withReducibleAndInstances (replaceDefEq replaced term shared)
        else pure replaced
      mkLetFVars #[shared] (← rest replaced (used.insert fresh)) (generalizeNondepLet := false)
  -- Repeated real terms are collected once, smallest first, and bound in that order; a later
  -- term reads the earlier ones through their names.
  let rec bindAll (terms : List (Lean.Expr × Name)) (body : Lean.Expr) (used : NameSet) :
      MetaM Lean.Expr := do
    let (term, name) :: more := terms | return body
    unless (body.find? (· == term)).isSome do return ← bindAll more body used
    let mut fresh := name
    let mut index := 2
    while used.contains fresh do
      fresh := name.appendIndexAfter index
      index := index + 1
    withLetDecl fresh (← inferType term) term fun shared => do
      let replace (expression : Lean.Expr) :=
        expression.replace fun child => if child == term then some shared else none
      let more := more.map fun (other, otherName) => (replace other, otherName)
      mkLetFVars #[shared] (← bindAll more (replace body) (used.insert fresh))
        (generalizeNondepLet := false)
  let rec rest (body : Lean.Expr) (used : NameSet) : MetaM Lean.Expr := do
    let some (term, name, _) := (← candidates body true)[0]? | do
      let found ← candidates body true (real := true)
      bindAll (found.map fun (term, name, _) => (term, name)).toList body used
    letIn name used term body rest (defeq := true)
  -- The value, reference and budgets of the concluding bound are named even when they occur
  -- once. The generated conditions, an implication's premise, may use them.
  let rec conclude (index : Nat) (body : Lean.Expr) (used : NameSet) : MetaM Lean.Expr := do
    let conclusion := body.getForallBody
    let (finite?, bound) := match finiteMixed? conclusion with
      | some (finite, bound) => (some finite, bound)
      | none => (none, conclusion)
    let output := match finite?.bind (·.getArg! 1 |>.getAppArgs.back?) with
      | some value => #[(value, `output)]
      | none => #[]
    let parts ← if bound.isAppOfArity ``MixedError 4 then
        pure (output ++ #[(bound.getArg! 1, `reference), (bound.getArg! 2, `relative),
          (bound.getArg! 3, `absolute)])
      else do
        -- An absolute bound `|actual - reference| ≤ error`, read as written.
        let left := bound.getArg! 2
        unless bound.isAppOfArity ``LE.le 4 && left.isAppOfArity ``abs 4 &&
            left.appArg!.isAppOfArity ``HSub.hSub 6 do return body
        pure #[(left.appArg!.appArg!, `reference), (bound.getArg! 3, `error)]
    let some (term, name) := parts[index]? | return body
    -- A constant of the format, such as the unit roundoff, reads better than a name for it.
    if term.nat?.isSome || term.isFVar || term.hasLooseBVars || termSize term < 10 then
      return ← conclude (index + 1) body used
    letIn name used term body (conclude (index + 1))
  -- Bind the first candidate as `letIn` does, then go on with the others. Replacing a closed term
  -- by a variable changes the occurrences of no other term, so only subterms of the bound term can
  -- stop being repeated or move, and only terms it heads change their head. Unless a remaining
  -- candidate or the term it was read from lies inside it or is it applied, or definitional
  -- equality bound more than its occurrences (the result differs from the syntactic replacement,
  -- binder names included), the candidates of the new body are the remaining ones with the terms
  -- bound so far (`bound`) replaced. Otherwise the new body is scanned again.
  let rec share (body : Lean.Expr) (used : NameSet)
      (known? : Option (Array (Lean.Expr × Name × Lean.Expr)))
      (bound : Std.HashMap Lean.Expr Lean.Expr) : MetaM Lean.Expr := do
    let found ← match known? with
      | some known => pure known
      | none => candidates body false
    let some (original, name, _) := found[0]? | do
      let concluded := [`output, `reference, `relative, `absolute, `error].foldl NameSet.insert
        used
      rest (← conclude 0 body used) concluded
    let term := if bound.isEmpty then original else original.replace bound.get?
    let mut fresh := name
    let mut index := 2
    while used.contains fresh do
      fresh := name.appendIndexAfter index
      index := index + 1
    withLetDecl fresh (← inferType term) term fun shared => do
      let syntactic := body.replace fun child => if child == term then some shared else none
      let replaced ← if term.isLambda then
          withReducibleAndInstances (replaceDefEq syntactic term shared)
        else pure syntactic
      let remaining := (found.extract 1 found.size).filter (·.1 != original)
      let unchanged := replaced.equal syntactic && (remaining.isEmpty ||
        let inside := subterms original
        remaining.all fun (candidate, _, source) =>
          !inside.contains candidate && !inside.contains source &&
            !appliedTo original candidate && !appliedTo original source)
      let next := if unchanged then (some remaining, bound.insert original shared) else (none, {})
      mkLetFVars #[shared] (← share replaced (used.insert fresh) next.1 next.2)
        (generalizeNondepLet := false)
  unless full do return ← conclude 0 statement {}
  share (← canonicalArguments statement) {} none {}
where
  /-- `(kabstract expression pattern).instantiate1 replacement` for a closed `pattern` and a free
  variable `replacement`: the occurrences of `pattern` up to definitional equality are replaced.
  Unlike `kabstract`, which walks the term as a tree, each distinct subterm is visited once.
  Subterms are identified with their binder names, so the result is the same. -/
  replaceDefEq (expression pattern replacement : Lean.Expr) : MetaM Lean.Expr := do
    let head := pattern.toHeadIndex
    let arity := pattern.headNumArgs
    let visited ← IO.mkRef ({} : Std.HashMap ExprStructEq Lean.Expr)
    let rec visit (term : Lean.Expr) : MetaM Lean.Expr := do
      if let some done := (← visited.get).get? term then return done
      let matched ← if term.hasLooseBVars || term.toHeadIndex != head ||
          term.headNumArgs != arity then pure false
        else isDefEq term pattern
      let result ← if matched then pure replacement else match term with
        | .app function argument => do
            pure (term.updateApp! (← visit function) (← visit argument))
        | .mdata _ inner => do pure (term.updateMData! (← visit inner))
        | .proj _ _ inner => do pure (term.updateProj! (← visit inner))
        | .letE _ type value body _ => do
            pure (term.updateLetE! (← visit type) (← visit value) (← visit body))
        | .lam _ type body _ => do
            pure (term.updateLambdaE! (← visit type) (← visit body))
        | .forallE _ type body _ => do
            pure (term.updateForallE! (← visit type) (← visit body))
        | _ => pure term
      visited.modify (·.insert term result)
      return result
    visit (← instantiateMVars expression)
  /-- The size `termSize` of every distinct subterm of `expression`, each computed once. -/
  sizes (expression : Lean.Expr) : Std.HashMap Lean.Expr Nat :=
    -- The table so far and the size of `term`, which `visit` returns along with it.
    let rec visit (term : Lean.Expr) (table : Std.HashMap Lean.Expr Nat) :
        Std.HashMap Lean.Expr Nat × Nat :=
      match table.get? term with
      | some size => (table, size)
      | none =>
        let (table, size) := match term with
          | .app function argument =>
              let (table, first) := visit function table
              let (table, second) := visit argument table
              (table, 1 + first + second)
          | .lam _ type body _ | .forallE _ type body _ =>
              let (table, first) := visit type table
              let (table, second) := visit body table
              (table, 1 + first + second)
          | .letE _ type value body _ =>
              let (table, first) := visit type table
              let (table, second) := visit value table
              let (table, third) := visit body table
              (table, 1 + first + second + third)
          | .mdata _ inner | .proj _ _ inner =>
              let (table, first) := visit inner table
              (table, 1 + first)
          | _ => (table, 1)
        (table.insert term size, size)
    (visit expression {}).1
  /-- Whether `term` is `function` applied to one or more arguments. -/
  appliedTo (function : Lean.Expr) : Lean.Expr → Bool
    | .app inner _ => inner == function || appliedTo function inner
    | _ => false
  /-- The distinct subterms of `expression`, itself included. -/
  subterms (expression : Lean.Expr) : Std.HashSet Lean.Expr :=
    let rec visit (term : Lean.Expr) (seen : Std.HashSet Lean.Expr) : Std.HashSet Lean.Expr :=
      if seen.contains term then seen else
      let seen := seen.insert term
      match term with
      | .app function argument => visit argument (visit function seen)
      | .lam _ type body _ | .forallE _ type body _ => visit body (visit type seen)
      | .letE _ type value body _ => visit body (visit value (visit type seen))
      | .mdata _ inner | .proj _ _ inner => visit inner seen
      | _ => seen
    visit expression {}
  /-- The distinct closed subterms of `expression` in the order of their first occurrence, and
  every distinct subterm with whether it occurs more than once in it. -/
  occurrences (expression : Lean.Expr) : Array Lean.Expr × Std.HashMap Lean.Expr Bool :=
    -- A subterm occurs more than once when it is reached along two edges, or inside a subterm
    -- that does: a subterm reached again is marked with the subterms below it, each once.
    let rec mark (term : Lean.Expr) (seen : Std.HashMap Lean.Expr Bool) :
        Std.HashMap Lean.Expr Bool :=
      match seen.get? term with
      | some true => seen
      | _ =>
        let seen := seen.insert term true
        match term with
        | .app function argument => mark argument (mark function seen)
        | .lam _ type body _ | .forallE _ type body _ => mark body (mark type seen)
        | .letE _ type value body _ => mark body (mark value (mark type seen))
        | .mdata _ inner | .proj _ _ inner => mark inner seen
        | _ => seen
    let rec visit (term : Lean.Expr) (closed : Array Lean.Expr)
        (seen : Std.HashMap Lean.Expr Bool) : Array Lean.Expr × Std.HashMap Lean.Expr Bool :=
      match seen.get? term with
      | some true => (closed, seen)
      | some false => (closed, mark term seen)
      | none =>
        let closed := if term.hasLooseBVars || term.isFVar || term.isConst || term.isSort ||
          term.isLit then closed else closed.push term
        let seen := seen.insert term false
        match term with
        | .app function argument =>
            let (closed, seen) := visit function closed seen
            visit argument closed seen
        | .lam _ type body _ | .forallE _ type body _ =>
            let (closed, seen) := visit type closed seen
            visit body closed seen
        | .letE _ type value body _ =>
            let (closed, seen) := visit type closed seen
            let (closed, seen) := visit value closed seen
            visit body closed seen
        | .mdata _ inner | .proj _ _ inner => visit inner closed seen
        | _ => (closed, seen)
    visit expression #[] {}

/-- Restate the reference of the concluding mixed bound of `statement`, which `value` proves, by
the equation `equation`: its left side must unify with the inferred reference, and its right side
becomes the stated reference. Return the restated proof and statement. -/
def restateReference (equation : Name) (value statement : Lean.Expr) :
    MetaM (Lean.Expr × Lean.Expr) :=
  forallTelescope statement fun conditions body => do
    let (finite?, bound) := match finiteMixed? body with
      | some (finite, bound) => (some finite, bound)
      | none => (none, body)
    unless bound.isAppOfArity ``MixedError 4 do
      throwError "roundoff: the generated statement has no mixed bound to restate"
    let law ← mkConstWithFreshMVarLevels equation
    let (arguments, _, type) ← forallMetaTelescopeReducing (← ruleType law)
    let some (_, left, right) := (← zetaReduce (← instantiateMVars type)).eq? |
      throwError "roundoff: {equation} is not an equation"
    unless ← isDefEq left (bound.getArg! 1) do
      throwError "roundoff: the left side of {equation} is not the inferred reference"
    let proof ← instantiateMVars (mkAppN law arguments)
    if proof.hasExprMVar then
      throwError "roundoff: the inferred reference does not determine the arguments of {equation}"
    let restate (reference : Lean.Expr) : Lean.Expr :=
      let bound := mkAppN bound.getAppFn (bound.getAppArgs.set! 1 reference)
      match finite? with
      | some finite => mkAnd finite bound
      | none => bound
    let motive ← withLocalDeclD `reference q(ℝ) fun reference => do
      mkLambdaFVars #[reference] (restate reference)
    let restated ← mkEqMP (← mkCongrArg motive proof) (mkAppN value conditions)
    return (← mkLambdaFVars conditions restated,
      ← mkForallFVars conditions (restate (← instantiateMVars right)))

/-- The equation whose right side `roundoff mixed theorem` states its bound against. -/
syntax roundoffEquation := " using " ident

/-- Construct the proof term inside Lean's ordinary declaration elaboration, which handles section
variables, universes and declaration checking. The function's arguments retain their binders.
With `mixed`, the inferred statement is a mixed bound, and in both modes its repeated subterms are
named. `using` an equation restates its reference first. -/
elab "roundoff_proof% " mixed:(&"mixed")? computation:term equation:(roundoffEquation)? : term =>
    Term.withoutErrToSorry do
  let equation ← equation.mapM fun clause => realizeGlobalConstNoOverloadWithInfo clause.raw[1]
  if equation.isSome && mixed.isNone then
    throwError "roundoff: `using` restates the reference of a mixed bound"
  let computation ← Term.elabTerm computation none
  Term.synthesizeSyntheticMVarsNoPostponing
  let computation ← instantiateMVars computation
  let value ← forallTelescope (← inferType computation) fun arguments result => do
    unless ← isDefEq result q(ℝ) do throwError "roundoff: expected a real observation"
    let actual : Q(ℝ) := (mkAppN computation arguments).headBeta
    let expected ← mkFreshExprMVar q(Prop)
    let proof ← mkFreshExprMVar expected
    let remaining ← Tactic.run proof.mvarId! do
      let (numerical, pending) ← inferBound actual mixed.isSome
      checkGeneratedConditions pending
      let value ← if pending.isEmpty then pure numerical else
        withConditions pending (← IO.mkRef {}) fun _ evidence => do
          mkLambdaFVars #[evidence] (← instantiateMVars numerical)
      let statement ← instantiateMVars (← inferType value)
      let (value, statement) ← match equation with
        | some equation => restateReference equation value statement
        | none => pure (value, statement)
      let statement ← shareSubterms (← nameFormats statement) (full := mixed.isSome)
      let goal ← (← getMainGoal).change statement
      goal.assign (← mkExpectedTypeHint value statement)
      replaceMainGoal []
    unless remaining.isEmpty do throwError "roundoff: unfinished generated proof"
    mkLambdaFVars arguments (← instantiateMVars proof)
  if value.hasExprMVar || value.hasLooseBVars || value.hasSorry then
    throwError "roundoff: generated proof contains unresolved obligations"
  -- The kernel checks the proof when it is declared.
  return value

-- Infer the proof once; the public theorem reuses its checked type and value. `roundoff mixed
-- theorem` infers a mixed bound and the finiteness of the decoded value; `using` an equation
-- before `:=` states the bound against its right side instead of the inferred reference.
elab doc:(docComment)? "roundoff" mixed:(&"mixed")? "theorem" name:ident
    equation:(roundoffEquation)? " := " computation:term : command => do
  let proofName ← Command.liftCoreM <| Core.mkFreshUserName (name.getId ++ `proof)
  let proof := mkIdentFrom name proofName
  let errorsBefore := (← get).messages.toList.countP (·.severity == .error)
  let generated ← match mixed.isSome, equation with
    | true, some equation => `(roundoff_proof% mixed $computation:term $equation:roundoffEquation)
    | true, none => `(roundoff_proof% mixed $computation)
    | false, some equation => `(roundoff_proof% $computation:term $equation:roundoffEquation)
    | false, none => `(roundoff_proof% $computation)
  Command.elabCommand (← `(command|
    private abbrev $proof := @($generated)))
  if (← get).messages.toList.countP (·.severity == .error) > errorsBefore then return
  Command.elabCommand (← `(command|
    $[$doc:docComment]? theorem $name : type_of% (private_decl% @$proof) := @$proof))

/-! ## Primitive evidence, for coverage reports -/

/-- The rounding theorems of the correctly rounded primitives the analysis uses. -/
def primitiveRoundings : Array Name := primitives.map (·.rounding)

/-- The enclosure theorems the analysis uses for primitives without a rounding theorem. -/
def primitiveEnclosures : Array Name := elementaryEnclosures.map (·.1)

end FloatLib.Floats.Formats.BinaryInterchange.Roundoff
