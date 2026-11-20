/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Tactic.LaneDecide

/-!
# Packed tables of functions of two small indices

`lane_table name (width := w) (size := n) := f` declares, for a function `f : Nat → Nat → Nat`
that `Packed.Reify.read` can read as a lane program,

* `name : Nat`, one literal whose lane `a * n + b` of `w` bits is `f a b` (a packed row, as
  `packed_row` declares: irreducible and without compiled code), and
* `name.lookup : ∀ a b : Fin n, lane w (a.val * n + b.val) name = f a.val b.val`.

A lookup is one shift and one mask of the literal, whatever `f` costs.

The theorem is `Packed.lane_table` with one closed check that Lean's kernel evaluates: the
program of `f` runs once on rows of `n * n` lanes, which gives the table of `f` with the lanes
of the run, and the literal is compared with that row by halving both (`Packed.differences`).
No value of `f` is computed one pair at a time. The run uses lanes of 16, 32 or 64 bits, the
narrowest of `Reify.frames` on which no lane has an error. A frame whose check the kernel
rejects leaves no declaration in the environment.

The command fails when a lane has an error with lanes of 64 bits (a value that does not fit 63
bits, a shift count of 64 or more, a function without a `@[lane_call]` replacement) or when a
value does not fit `w` bits.
-/

public meta section

namespace FloatLib.Numerics.Packed

open Lean Meta Elab Command

/-- The `count` lanes of `width` bits of `row`, lowest first, splitting the row in halves. -/
partial def unpack (width row count : Nat) : Array Nat :=
  if count = 0 then #[]
  else if count = 1 then #[row % 2 ^ width]
  else
    let half := count / 2
    unpack width (row % 2 ^ (width * half)) half ++
      unpack width (row >>> (width * half)) (count - half)

/--
`lane_table name (width := w) (size := n) := f` declares the packed table `name` of
`f : Nat → Nat → Nat` on the indices below `n`, with lanes of `w` bits, and the theorem
`name.lookup : ∀ a b : Fin n, lane w (a.val * n + b.val) name = f a.val b.val`. See the module
documentation for how the theorem is checked.
-/
syntax (name := laneTable) (docComment)? "lane_table " ident " (" &"width" " := " num ")" " ("
  &"size" " := " num ")" " := " term : command

/--
The elaborator of `lane_table`: it reads the program of the function, evaluates it on all lanes
to build the literal, and declares the table and its lookup theorem, whose proof is one kernel
check of the literal against the program.
-/
@[command_elab laneTable]
def elabLaneTable : CommandElab := fun stx => do
  let doc? : Option (TSyntax ``Parser.Command.docComment) := stx[0].getOptional?.map (⟨·⟩)
  let name : Ident := ⟨stx[2]⟩
  let width := stx[6].isNatLit?.getD 0
  let size := stx[11].isNatLit?.getD 0
  let function : Term := ⟨stx[14]⟩
  let declName := (← getCurrNamespace) ++ name.getId
  let lookupName := declName ++ `lookup
  let nat := mkConst ``Nat
  let (entries, lemmaName, statement) ← liftTermElabM do
    let f ← Term.elabTermEnsuringType function (← mkArrow nat (← mkArrow nat nat))
    Term.synthesizeSyntheticMVarsNoPostponing
    let f ← instantiateMVars f
    let inputBits := Reify.bitLength (size - 1)
    let (program, sound, denotes) ← withLocalDeclD `x nat fun x => withLocalDeclD `y nat fun y => do
      let push (head tail : Lean.Expr) : Lean.Expr :=
        mkApp3 (mkConst ``FloatLib.Numerics.Packed.push) nat head tail
      let env := push x (push y (mkLambda `index .default nat (mkNatLit 0)))
      let result ← Reify.read [(x.fvarId!, inputBits), (y.fvarId!, inputBits)] env (mkApp2 f x y)
      if result.program.hasFVar then
        throwError "lane_table: the program is not closed"
      return (result.program, result.sound, ← mkLambdaFVars #[x, y] result.denotes)
    let sizeTerm := mkNatLit size
    let widthTerm := mkNatLit width
    let fin := mkApp (mkConst ``Fin) sizeTerm
    let leaf := 8
    let levels := (List.range 64).find? (fun level => size * size ≤ leaf * 2 ^ level) |>.getD 64
    -- The statement about a table: lane `a * n + b` is `f a b`.
    let statementOf (table : Lean.Expr) : MetaM Lean.Expr :=
      withLocalDeclD `a fin fun a => withLocalDeclD `b fin fun b => do
        let aValue := mkApp2 (mkConst ``Fin.val) sizeTerm a
        let bValue := mkApp2 (mkConst ``Fin.val) sizeTerm b
        let index ← mkAdd (← mkMul aValue sizeTerm) bValue
        mkForallFVars #[a, b]
          (mkApp3 (mkConst ``Eq [Level.one]) nat
            (mkApp3 (mkConst ``FloatLib.Numerics.Packed.lane) widthTerm index table)
            (mkApp2 f aValue bValue).headBeta)
    -- The narrowest frame on which the program runs without an error gives the table.
    let mut found : Option (Array Nat × Name) := none
    let mut failure : MessageData := m!""
    for (laneBits, shiftBits) in Reify.frames do
      let laneWidth := mkRawNatLit laneBits
      let depth := mkRawNatLit shiftBits
      -- The table of `f` with the lanes of the frame, computed once in Lean's kernel.
      let row ← natValue (mkApp4 (mkConst ``pairsRow) laneWidth sizeTerm depth program)
      let entries := unpack laneBits row (size * size)
      if let some index := entries.findIdx? (· ≥ 2 ^ width) then
        failure := m!"the value {entries[index]!} at the pair ({index / size}, {index % size}) \
          does not fit {width} bits"
        continue
      let tableValue := mkRawNatLit (packSlice width entries 0 entries.size)
      let widthProof ← mkDecideProof (← mkAppM ``LE.le #[mkRawNatLit 2, laneWidth])
      let depthProof ← mkDecideProof
        (← mkAppM ``LE.le #[← mkAppM ``HSub.hSub #[laneWidth, mkRawNatLit 1],
          ← mkAppM ``HPow.hPow #[mkRawNatLit 2, depth]])
      let proof := mkAppN (mkConst ``FloatLib.Numerics.Packed.lane_table)
        #[widthTerm, laneWidth, sizeTerm, mkRawNatLit leaf, mkRawNatLit levels, depth, tableValue,
          widthProof, depthProof, program, f, sound, denotes,
          mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)]
      let (statement, proof) := ShareCommon.shareCommon' (← statementOf tableValue, proof)
      let environment ← getEnv
      try
        let lemmaName ← withOptions (Elab.async.set · false) do mkAuxLemma [] statement proof
        found := some (entries, lemmaName)
        break
      catch error =>
        -- Lean keeps a declaration that its kernel rejects as an axiom, so that later uses of
        -- its name still elaborate. The table of a frame that is too narrow is no axiom.
        setEnv environment
        failure := m!"a lane has an error (a value that does not fit {laneBits - 1} bits, a \
          shift count of {laneBits} or more, a function without a replacement)\n\
          {error.toMessageData}"
    let some (entries, lemmaName) := found
      | throwError "lane_table: the check failed: {failure}"
    return (entries, lemmaName, ← statementOf (mkConst declName))
  -- The table is a packed row: one raw literal, irreducible and without compiled code.
  addRow declName width entries
    (match doc? with
      | some doc => doc.getDocString
      | none => s!"The packed table of a function on the indices below {size}, in lanes of \
          {width} bits.") stx name
  liftCoreM do
    addDecl <| .thmDecl
      { name := lookupName, levelParams := [], type := statement, value := mkConst lemmaName }
    addDocStringCore lookupName
      s!"Lane `a * {size} + b` of `{declName}` is the value of the tabulated function at \
        `(a, b)`, for all indices below {size}."

end FloatLib.Numerics.Packed
