/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Numerics.Kernel.Bits.Proof.Arithmetic
public meta import FloatLib.Numerics.Kernel.Bits.Proof.PopCount
public meta import FloatLib.Util.Packed
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.Closure
public meta import Lean.Meta.KAbstract
public meta import Lean.Meta.Tactic.Delta
public import FloatLib.Numerics.Packed.Program
public import FloatLib.Tactic.LaneCall

/-!
# Reading a lane program off a definition, and `lane_decide`

`lane_decide` proves a goal `∀ a b : Fin n, lhs = rhs` between natural numbers, in which `a` and
`b` occur as `a.val` and `b.val`, with one evaluation of each side on rows of `n * n` lanes
(`Packed.forall_pairs`), instead of `n * n` evaluations.

It reads a lane program off each side (`read`). The sides may use the kernel's natural-number
operations (`Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.land`, `Nat.lor`, `Nat.xor`, both shifts,
`Nat.succ`, `Nat.pow 2`, `Nat.mod` by a power of two, which is a mask, and `Bool.casesOn` or
`Bool.rec` on `Nat.beq`, `Nat.ble` or `Nat.blt`), numerals, terms without `a` and `b` (which
become constants), applied functions (whose arguments become shared bindings), and any
definition that unfolds to these. So the kernel shape of a definition (`kernel_shape`) is read
as it is. `Nat.div`, `Nat.mod` by another number and loops whose length depends on a lane have no
lane step, and a term that uses them is refused.

A function that does not unfold to these operations can be given a replacement with
`@[lane_call]`: a theorem `∀ v, v < limit → replacement v = function v` (after its parameters),
proved with no axiom beyond the standard three (`Provenance.requireProved`).
The lanes whose argument is below the limit run the replacement, and the others are marked as
errors.

The tactic tries lanes of 16, 32 and 64 bits (`frames`) and keeps the first run in which no
lane has an error: a narrow lane halves the work, and a value that does not fit it is an error,
never a wrong result. The check fails, and the tactic reports it, when some lane has an error
with lanes of 64 bits (a value that does not fit the 63 value bits of a lane, a shift count of
64 or more) or when the two sides differ.

The proof term is one application of `Packed.forall_pairs` to the two programs, the proofs that
they denote the two sides (built from the denotation equations `Expr.eval_add` and its siblings,
one per node, so that Lean's kernel never unfolds an operation on an open term), and `rfl` for
the closed check.
-/

public meta section

namespace FloatLib.Numerics.Packed.Reify

open Lean Meta Elab Tactic

/-- What reading a term gives. -/
structure Result where
  /-- The program, a term of type `Packed.Expr`. -/
  program : Lean.Expr
  /-- A proof of `Expr.Sound program`. -/
  sound : Lean.Expr
  /--
  A proof of `Expr.eval program env = term` for the term that was read, up to a reduction at
  the head of `term`.
  -/
  denotes : Lean.Expr
  /-- An upper bound on the bit length of the value, used to order and bound products. -/
  bits : Nat

/-- The variables in scope, innermost first, with the bound on their bits. -/
abbrev Scope := List (FVarId × Nat)

/--
The frames that `lane_decide` and `lane_table` try, narrowest first: the lane width and the
number of bits of a shift count. A lane holds one bit less than its width, and the cost of a run
grows with the width.
-/
def frames : List (Nat × Nat) := [(16, 4), (32, 5), (64, 6)]

/-- The bit length of a natural number. -/
def bitLength (n : Nat) : Nat :=
  FloatLib.Numerics.Kernel.Compiled.size n

/-- The value of a closed natural-number term, when the kernel can compute it. -/
def closedValue? (e : Lean.Expr) : MetaM (Option Nat) := do
  try
    let value ← FloatLib.Numerics.Packed.natValue e
    return some value
  catch _ => return none

private def packedExpr (name : Name) : Lean.Expr :=
  mkConst (`FloatLib.Numerics.Packed.Expr ++ name)

private def natType : Lean.Expr := mkConst ``Nat

/-- The denotation equation of each node that is read with its node's name. The equations are
named here, so that a renamed one fails where this table is compiled. -/
private def denotations : List (Name × Name) :=
  [(`add, ``FloatLib.Numerics.Packed.Expr.eval_add),
    (`sub, ``FloatLib.Numerics.Packed.Expr.eval_sub),
    (`land, ``FloatLib.Numerics.Packed.Expr.eval_land),
    (`lor, ``FloatLib.Numerics.Packed.Expr.eval_lor),
    (`xor, ``FloatLib.Numerics.Packed.Expr.eval_xor),
    (`shiftLeft, ``FloatLib.Numerics.Packed.Expr.eval_shiftLeft),
    (`shiftRight, ``FloatLib.Numerics.Packed.Expr.eval_shiftRight),
    (`shiftLeftBy, ``FloatLib.Numerics.Packed.Expr.eval_shiftLeftBy),
    (`shiftRightBy, ``FloatLib.Numerics.Packed.Expr.eval_shiftRightBy),
    (`mul, ``FloatLib.Numerics.Packed.Expr.eval_mul),
    (`mulLeft, ``FloatLib.Numerics.Packed.Expr.eval_mulLeft)]

/-- The denotation equation of a node. -/
private def denotation (node : Name) : Lean.Expr :=
  mkConst ((denotations.lookup node).getD .anonymous)

private def soundOf (program : Lean.Expr) : Lean.Expr :=
  mkApp (mkConst ``FloatLib.Numerics.Packed.Expr.Sound) program

private def evalOf (program env : Lean.Expr) : Lean.Expr :=
  mkApp2 (mkConst ``FloatLib.Numerics.Packed.Expr.eval) program env

private def andIntro (left right leftProof rightProof : Lean.Expr) : Lean.Expr :=
  mkApp4 (mkConst ``And.intro) left right leftProof rightProof

/-- `Eq.trans` between natural numbers, with its three terms given. -/
private def eqTrans (a b c first second : Lean.Expr) : Lean.Expr :=
  mkApp6 (mkConst ``Eq.trans [Level.one]) natType a b c first second

/-- A node with two subprograms that denote `a` and `b`. -/
private def binary (env : Lean.Expr) (name : Name) (x y : Result) (a b : Lean.Expr) (bits : Nat) :
    Result :=
  { program := mkApp2 (packedExpr name) x.program y.program
    sound := andIntro (soundOf x.program) (soundOf y.program) x.sound y.sound
    denotes := mkAppN (denotation name)
      #[env, x.program, y.program, a, b, x.denotes, y.denotes]
    bits := min bits 64 }

/-- A choice node: two compared subprograms and two branches, with the terms they denote. -/
private def choice (env : Lean.Expr) (name lemmaName : Name) (first : Lean.Expr)
    (a b whenTrue whenFalse : Result) (terms : Array Lean.Expr) : Result :=
  { program := mkApp4 (packedExpr name) first b.program whenTrue.program whenFalse.program
    sound :=
      andIntro (soundOf first)
        (mkAnd (soundOf b.program) (mkAnd (soundOf whenTrue.program) (soundOf whenFalse.program)))
        a.sound
        (andIntro (soundOf b.program)
          (mkAnd (soundOf whenTrue.program) (soundOf whenFalse.program)) b.sound
          (andIntro (soundOf whenTrue.program) (soundOf whenFalse.program) whenTrue.sound
            whenFalse.sound))
    denotes := mkAppN (mkConst (`FloatLib.Numerics.Packed.Expr ++ lemmaName))
      (#[env, a.program, b.program, whenTrue.program, whenFalse.program] ++ terms ++
        #[a.denotes, b.denotes, whenTrue.denotes, whenFalse.denotes])
    bits := max whenTrue.bits whenFalse.bits }

/-- The constant program of a closed term. -/
private def constant (env e : Lean.Expr) : MetaM Result := do
  let bits := match ← closedValue? e with
    | some value => bitLength value
    | none => 64
  return { program := mkApp (packedExpr `const) e, sound := mkConst ``True.intro
           denotes := mkApp2 (mkConst ``FloatLib.Numerics.Packed.Expr.eval_const) env e, bits }

/-- The arguments of a natural-number operation given by its function or by its notation. -/
private def operands? (e : Lean.Expr) (function operator : Name) :
    Option (Lean.Expr × Lean.Expr) :=
  if e.isAppOfArity function 2 then some (e.appFn!.appArg!, e.appArg!)
  else if e.isAppOfArity operator 6 then some (e.appFn!.appArg!, e.appArg!)
  else none

/-- The operations with one node each: the function, its notation and the node. -/
private def operations : List (Name × Name × Name) :=
  [(``Nat.add, ``HAdd.hAdd, `add), (``Nat.sub, ``HSub.hSub, `sub), (``Nat.land, ``HAnd.hAnd, `land),
    (``Nat.lor, ``HOr.hOr, `lor), (``Nat.xor, ``HXor.hXor, `xor)]

/--
Read the lane program of the natural-number term `e`, whose lane variables are those of `scope`
and whose environment is the term `env`.
-/
partial def read (scope : Scope) (env e : Lean.Expr) : MetaM Result := do
  let e ← instantiateMVars e
  let isLane (id : FVarId) : Bool := scope.any fun entry => entry.1 == id
  -- A term without lane variables is a constant, whatever it is made of.
  unless e.hasAnyFVar isLane do
    return ← constant env e
  if let .fvar id := e then
    let some index := scope.findIdx? fun entry => entry.1 == id
      | throwError "lane program: unknown variable {e}"
    return { program := mkApp (packedExpr `var) (mkRawNatLit index)
             sound := mkConst ``True.intro
             denotes := mkApp2 (mkConst ``Eq.refl [Level.one]) natType e
             bits := (scope[index]!).2 }
  -- An applied function binds its first argument, once.
  if e.getAppFn.isLambda then
    let function := e.getAppFn
    let arguments := e.getAppArgs
    let argument := arguments[0]!
    let rest := arguments.extract 1 arguments.size
    let isNumber := (← whnfR function.bindingDomain!).isConstOf ``Nat
    if !argument.hasAnyFVar isLane || argument.isFVar || !isNumber then
      return ← read scope env (mkAppN (function.bindingBody!.instantiate1 argument) rest)
    let value ← read scope env argument
    return ← withLocalDeclD function.bindingName! natType fun u => do
      let term := mkAppN (function.bindingBody!.instantiate1 u) rest
      let body ← read ((u.fvarId!, value.bits) :: scope)
        (mkApp3 (mkConst ``FloatLib.Numerics.Packed.push) natType u env) term
      return { program := mkApp2 (packedExpr `bind) value.program body.program
               sound := andIntro (soundOf value.program) (soundOf body.program) value.sound
                 body.sound
               denotes := mkAppN (mkConst ``FloatLib.Numerics.Packed.Expr.eval_bind)
                 #[env, value.program, body.program, argument, ← mkLambdaFVars #[u] term,
                   value.denotes, ← mkLambdaFVars #[u] body.denotes]
               bits := body.bits }
  for (function, operator, node) in operations do
    if let some (a, b) := operands? e function operator then
      let x ← read scope env a
      let y ← read scope env b
      let bits := match node with
        | `add => max x.bits y.bits + 1
        | `sub => x.bits
        | `land => min x.bits y.bits
        | _ => max x.bits y.bits
      return binary env node x y a b bits
  if e.isAppOfArity ``Nat.succ 1 then
    let x ← read scope env e.appArg!
    let one := mkApp (packedExpr `const) (mkNatLit 1)
    return { program := mkApp2 (packedExpr `add) x.program one
             sound := andIntro (soundOf x.program) (soundOf one) x.sound (mkConst ``True.intro)
             denotes := mkAppN (mkConst ``FloatLib.Numerics.Packed.Expr.eval_succ)
               #[env, x.program, e.appArg!, x.denotes]
             bits := min (x.bits + 1) 64 }
  if let some (a, b) := operands? e ``Nat.mul ``HMul.hMul then
    let x ← read scope env a
    let y ← read scope env b
    -- One factor is taken bit by bit: the shorter one.
    let (node, bound) := if y.bits ≤ x.bits then (`mul, y.bits) else (`mulLeft, x.bits)
    return { program := mkApp3 (packedExpr node) (mkRawNatLit bound) x.program y.program
             sound := andIntro (soundOf x.program) (soundOf y.program) x.sound y.sound
             denotes := mkAppN (denotation node)
               #[env, mkRawNatLit bound, x.program, y.program, a, b, x.denotes, y.denotes]
             bits := min (x.bits + y.bits) 64 }
  -- A remainder by a power of two keeps the low bits: the mask `2 ^ width - 1`.
  if let some (a, divisor) := operands? e ``Nat.mod ``HMod.hMod then
    unless divisor.hasAnyFVar isLane do
      if let some modulus ← closedValue? divisor then
        if modulus != 0 && modulus &&& (modulus - 1) == 0 then
          let x ← read scope env a
          let width := modulus.log2
          -- `a &&& 2 ^ width - 1 = a % 2 ^ width`, whose right side is `e` by evaluation.
          let masks := mkApp2 (mkConst ``Nat.and_two_pow_sub_one_eq_mod) a (mkRawNatLit width)
          let some (_, masked, _) := (← inferType masks).eq?
            | throwError "lane program: no mask for the remainder{indentExpr e}"
          let mask := masked.appArg!
          let maskProgram := mkApp (packedExpr `const) mask
          let program := mkApp2 (packedExpr `land) x.program maskProgram
          let land := mkApp2 (mkConst ``Nat.land) a mask
          return { program
                   sound := andIntro (soundOf x.program) (soundOf maskProgram) x.sound
                     (mkConst ``True.intro)
                   denotes := eqTrans (evalOf program env) land e
                     (mkAppN (denotation `land) #[env, x.program, maskProgram, a, mask, x.denotes,
                       mkApp2 (mkConst ``FloatLib.Numerics.Packed.Expr.eval_const) env mask])
                     masks
                   bits := min x.bits width }
  for (function, operator, node, fixed) in
      [(``Nat.shiftLeft, ``HShiftLeft.hShiftLeft, `shiftLeft, `shiftLeftBy),
        (``Nat.shiftRight, ``HShiftRight.hShiftRight, `shiftRight, `shiftRightBy)] do
    if let some (shifted, countTerm) := operands? e function operator then
      let x ← read scope env shifted
      let left := node == `shiftLeft
      if !Lean.Expr.hasAnyFVar countTerm isLane then
        let amount ← closedValue? countTerm
        return { program := mkApp2 (packedExpr fixed) x.program countTerm, sound := x.sound
                 denotes := mkAppN (denotation fixed)
                   #[env, x.program, shifted, countTerm, x.denotes]
                 bits := if left then min (x.bits + amount.getD 64) 64
                   else x.bits - amount.getD 0 }
      let count ← read scope env countTerm
      return binary env node x count shifted countTerm
        (if !left then x.bits else if count.bits ≤ 6 then x.bits + 2 ^ count.bits - 1 else 64)
  if e.isAppOfArity ``Nat.pow 2 || e.isAppOfArity ``HPow.hPow 6 then
    let base := e.appFn!.appArg!
    if (← closedValue? base) == some 2 then
      let count ← read scope env e.appArg!
      return { program := mkApp (packedExpr `pow2) count.program, sound := count.sound
               denotes := mkAppN (mkConst ``FloatLib.Numerics.Packed.Expr.eval_pow2)
                 #[env, count.program, e.appArg!, count.denotes]
               bits := if count.bits ≤ 6 then 2 ^ count.bits else 64 }
  -- A case distinction on a comparison of two numbers, or on a condition without lane variables,
  -- written with `Bool.casesOn` or with the recursor it abbreviates.
  let distinction? : Option (Lean.Expr × Lean.Expr × Lean.Expr) :=
    if e.isAppOfArity ``Bool.casesOn 4 then some (e.getArg! 1, e.getArg! 2, e.getArg! 3)
    else if e.isAppOfArity ``Bool.rec 4 then some (e.getArg! 3, e.getArg! 1, e.getArg! 2)
    else none
  if let some (condition, whenFalse, whenTrue) := distinction? then
    unless condition.hasAnyFVar isLane do
      let value ← whnf condition
      if value.isConstOf ``Bool.true then return ← read scope env whenTrue
      if value.isConstOf ``Bool.false then return ← read scope env whenFalse
      throwError "lane program: cannot decide the condition{indentExpr condition}"
    let condition ← if condition.getAppFn.isConst then pure condition else whnfR condition
    for (comparison, node, lemmaName) in
        [(``Nat.beq, `ifEq, `eval_ifEq), (``Nat.ble, `ifLe, `eval_ifLe),
          (``Nat.blt, `ifLe, `eval_ifLt)] do
      if condition.isAppOfArity comparison 2 then
        let left := condition.appFn!.appArg!
        let right := condition.appArg!
        let a ← read scope env left
        let b ← read scope env right
        let t ← read scope env whenTrue
        let f ← read scope env whenFalse
        let first := if comparison == ``Nat.blt then
          mkApp2 (packedExpr `add) a.program (mkApp (packedExpr `const) (mkNatLit 1))
          else a.program
        return choice env node lemmaName first a b t f #[left, right, whenTrue, whenFalse]
    throwError "lane program: the condition{indentExpr condition}\nis not `Nat.beq`, `Nat.ble` \
      or `Nat.blt` of two numbers"
  if let .const name levels := e.getAppFn then
    let arguments := e.getAppArgs
    -- A registered replacement of a function of one lane argument.
    if let some replacement := (laneCallExt.getState (← getEnv)).find? name then
      let parameters := arguments.pop
      unless parameters.any (·.hasAnyFVar isLane) do
        let argument ← read scope env arguments.back!
        -- Instantiate `∀ parameters v, v < limit → replacement v = function parameters v`.
        let statement ← inferType (mkConst replacement)
        let (holes, _, conclusion) ← forallMetaTelescope statement
        let some (_, lhs, rhs) := conclusion.eq?
          | throwError "lane program: `{replacement}` does not end in an equation"
        let valueHole := holes[holes.size - 2]!
        unless ← isDefEq rhs (mkAppN e.getAppFn (parameters.push valueHole)) do
          throwError "lane program: `{replacement}` does not apply to{indentExpr e}"
        let boundType ← instantiateMVars (← inferType holes[holes.size - 1]!)
        let some (_, _, _, limit) := boundType.app4? ``LT.lt
          | throwError "lane program: `{replacement}` has no bound `v < limit`"
        let limit ← instantiateMVars limit
        let function := mkAppN e.getAppFn parameters
        return ← withLocalDeclD `v natType fun v => do
          valueHole.mvarId!.assign v
          let below := mkApp4 (mkConst ``LT.lt [Level.zero]) natType (mkConst ``instLTNat) v limit
          let lhs ← instantiateMVars lhs
          let argumentEnv := mkApp3 (mkConst ``FloatLib.Numerics.Packed.push) natType v
            (mkLambda `index .default natType (mkNatLit 0))
          let body ← read [(v.fvarId!, 64)] argumentEnv lhs
          let proof ← withLocalDeclD `h below fun h => do
            holes[holes.size - 1]!.mvarId!.assign h
            let replaced ← instantiateMVars (mkAppN (mkConst replacement) holes)
            mkLambdaFVars #[v, h]
              (eqTrans (evalOf body.program argumentEnv) lhs (mkApp function v) body.denotes
                replaced)
          let property ← mkForallFVars #[v] (← mkArrow below
            (← mkEq (evalOf body.program argumentEnv) (mkApp function v)))
          return { program := mkApp4 (packedExpr `call) function limit body.program
                     argument.program
                   sound := andIntro property
                     (mkAnd (soundOf body.program) (soundOf argument.program)) proof
                     (andIntro (soundOf body.program) (soundOf argument.program) body.sound
                       argument.sound)
                   denotes := mkAppN (mkConst ``FloatLib.Numerics.Packed.Expr.eval_call)
                     #[env, function, limit, body.program, argument.program, arguments.back!,
                       argument.denotes]
                   bits := 64 }
    -- A number that an argument computes from the lane variables is computed once.
    for index in [0:arguments.size] do
      let argument := arguments[index]!
      if argument.hasAnyFVar isLane && !argument.isFVar then
        if (← whnfR (← inferType argument)).isConstOf ``Nat then
          let shared ← withLocalDeclD `u natType fun u =>
            mkLambdaFVars #[u] (mkAppN e.getAppFn (arguments.set! index u))
          return ← read scope env (mkApp shared argument)
    -- A definition that is not recursive is replaced by its value.
    if let some info@(.defnInfo _) := (← getEnv).find? name then
      unless (← getEnv).contains (mkSmartUnfoldingNameFor name) || (← isMatcher name) do
        let value := info.instantiateValueLevelParams! levels
        let function := e.getAppFn
        let mut unfolded ← mkExpectedTypeHint (← mkEqRefl function) (← mkEq function value)
        for argument in arguments do
          unfolded ← mkCongrFun unfolded argument
        let applied := mkAppN value arguments
        let result ← read scope env applied
        return { result with
                 denotes := eqTrans (evalOf result.program env) applied e result.denotes
                   (← mkEqSymm unfolded) }
  -- Anything else: reduce a recursor on a constructor or a projection, or unfold a definition.
  let reduced ← whnfCore e
  if reduced != e then
    return ← read scope env reduced
  if let some unfolded ← unfoldDefinition? e then
    return ← read scope env unfolded
  throwError "lane program: cannot read{indentExpr e}\nas a program in the kernel's \
    natural-number operations"

/--
`lane_decide` proves `∀ a b : Fin n, lhs = rhs` for natural numbers `lhs` and `rhs` in which the
indices occur as `a.val` and `b.val`, by one evaluation of each side on rows of `n * n` lanes
in Lean's kernel. It tries lanes of 16, 32 and 64 bits and keeps the first run without an error.
See the module documentation for the terms it can read.
-/
syntax (name := laneDecide) "lane_decide" : tactic

elab_rules : tactic
  | `(tactic| lane_decide) => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let .forallE nameA typeA bodyA _ := target
    | throwError "lane_decide: the goal is not of the form `∀ a b : Fin n, lhs = rhs`"
  unless typeA.isAppOfArity ``Fin 1 do
    throwError "lane_decide: the goal is not of the form `∀ a b : Fin n, lhs = rhs`"
  let size := typeA.appArg!
  let some bound := size.nat?
    | throwError "lane_decide: the size `{size}` of the index type is not a numeral"
  let .forallE nameB typeB _ _ := bodyA
    | throwError "lane_decide: the goal is not of the form `∀ a b : Fin n, lhs = rhs`"
  unless typeB == typeA do
    throwError "lane_decide: the two index types differ"
  let inputBits := bitLength (bound - 1)
  let (lhs, rhs, f, g, hf, hg) ← withLocalDeclD nameA typeA fun a =>
      withLocalDeclD nameB typeA fun b => do
    let statement := ((bodyA.instantiate1 a).bindingBody!).instantiate1 b
    let some (type, left, right) := statement.eq?
      | throwError "lane_decide: the statement is not an equation{indentExpr statement}"
    unless ← isDefEq type natType do
      throwError "lane_decide: the two sides are not natural numbers{indentExpr statement}"
    withLocalDeclD `x natType fun x => withLocalDeclD `y natType fun y => do
      let scope : Scope := [(x.fvarId!, inputBits), (y.fvarId!, inputBits)]
      let push (head tail : Lean.Expr) : Lean.Expr :=
        mkApp3 (mkConst ``FloatLib.Numerics.Packed.push) natType head tail
      let env := push x (push y (mkLambda `index .default natType (mkNatLit 0)))
      let abstract (side : Lean.Expr) : MetaM Lean.Expr := do
        let side := (← kabstract side (mkApp2 (mkConst ``Fin.val) size a)).instantiate1 x
        let side := (← kabstract side (mkApp2 (mkConst ``Fin.val) size b)).instantiate1 y
        if side.containsFVar a.fvarId! || side.containsFVar b.fvarId! then
          throwError "lane_decide: an index occurs other than as its value in{indentExpr side}"
        return side
      let leftTerm ← abstract left
      let rightTerm ← abstract right
      let left ← read scope env leftTerm
      let right ← read scope env rightTerm
      if left.program.hasFVar || right.program.hasFVar then
        throwError "lane_decide: the programs are not closed"
      return (left, right, ← mkLambdaFVars #[x, y] leftTerm, ← mkLambdaFVars #[x, y] rightTerm,
        ← mkLambdaFVars #[x, y] left.denotes, ← mkLambdaFVars #[x, y] right.denotes)
  -- `forall_pairs` on the narrowest frame whose check holds.
  let checkProof := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)
  let mut failure : Option Exception := none
  for (laneWidth, shiftBits) in frames do
    let width := mkRawNatLit laneWidth
    let depth := mkRawNatLit shiftBits
    let widthProof ← mkDecideProof (← mkAppM ``LE.le #[mkRawNatLit 2, width])
    let depthProof ← mkDecideProof
      (← mkAppM ``LE.le #[← mkAppM ``HSub.hSub #[width, mkRawNatLit 1],
        ← mkAppM ``HPow.hPow #[mkRawNatLit 2, depth]])
    let proof := mkAppN (mkConst ``FloatLib.Numerics.Packed.forall_pairs)
      #[width, size, depth, widthProof, depthProof, lhs.program, rhs.program, f, g, lhs.sound,
        rhs.sound, hf, hg, checkProof]
    -- The kernel checks that the programs denote the two sides and that the check is `true`.
    let (sharedTarget, sharedProof) := ShareCommon.shareCommon' (target, proof)
    try
      let lemmaName ← withOptions (Elab.async.set · false) do
        mkAuxLemma [] sharedTarget sharedProof
      goal.assign (mkConst lemmaName)
      replaceMainGoal []
      return
    catch error => failure := some error
  let check := mkApp5 (mkConst ``FloatLib.Numerics.Packed.pairsCheck) (mkRawNatLit 64) size
    (mkRawNatLit 6) lhs.program rhs.program
  match Kernel.whnf (← getEnv) {} check with
  | .ok value =>
      if value.isConstOf ``Bool.true then
        throwError "lane_decide: the check holds, but the kernel did not accept the programs as \
          the two sides of the goal\n{(failure.map (·.toMessageData)).getD m!""}"
      else
        throwError "lane_decide: the check is false: a lane has an error (a value that does \
          not fit 63 bits, a shift count of 64 or more, a function without a replacement) or \
          the two sides differ"
  | .error _ => throwError "lane_decide: the kernel could not evaluate the check"

end FloatLib.Numerics.Packed.Reify
