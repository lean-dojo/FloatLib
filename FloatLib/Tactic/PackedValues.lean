/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Util.Packed
public import FloatLib.Numerics.Executable.Packed

/-!
# Packed rows of exact stored values

`packed_values` reads exact values with the kernel, checks a common denominator, and
constructs the packed row and its link theorem.
-/

@[expose] public meta section

/-! ### The command -/

namespace FloatLib.Floats.ExecFloat.Packed

/-- `packed_values r (width := w) := xs` decodes the values `xs` exactly, picks their least common
denominator `d`, and defines the row `r` and the kernel-checked theorem
`r.link : link w d (values xs) r = true`. -/
syntax (name := packedValues) (docComment)? "packed_values " ident " (" &"width" " := " num ")"
    " := " term : command

end FloatLib.Floats.ExecFloat.Packed

namespace FloatLib.Floats.ExecFloat.Packed

open Lean Elab Command Term Meta
open FloatLib.Numerics.Packed

/-- The row and the scale of a list of exact values: the integers `v * d` for the least common
denominator `d`, or the index of the first value that has no finite meaning. -/
def rowOfValues (vs : List (Option ℚ)) : Except Nat (Array Int × Nat) := do
  let mut qs := #[]
  for h : i in [0:vs.length] do
    match vs[i] with
    | some v => qs := qs.push v
    | none => throw i
  let d := commonDen #[qs]
  return (numerators d qs, d)

/-- Elaborate `packed_values`: read the lanes by kernel reduction, compute the row and its
denominator, add the row, and prove the link with `decide +kernel`. -/
@[command_elab packedValues]
def elabPackedValues : CommandElab := fun stx => do
  let `($[$doc?:docComment]? packed_values $id:ident (width := $w:num) := $xs) := stx
    | throwUnsupportedSyntax
  let w := w.getNat
  if w = 0 then
    throwErrorAt id "the lane width must be positive"
  let vs ← liftTermElabM do
    let e ← elabTerm (← `(values $xs)) (some (mkApp (mkConst ``List [0])
      (mkApp (mkConst ``Option [0]) (mkConst ``Rat))))
    synthesizeSyntheticMVarsNoPostponing
    (← listValues (← instantiateMVars e)).mapM fun v => do
      let v ← kernelWhnf v
      match v.getAppFnArgs with
      | (``Option.none, _) => pure none
      | (``Option.some, #[_, q]) => pure (some (← ratValue q))
      | _ => throwError "could not evaluate the value {v}"
  let (xs', d) ← match rowOfValues vs.toList with
    | .ok r => pure r
    | .error i => throwErrorAt id "value {i} has no finite exact value"
  let lanes ← match rowLanes w true xs' with
    | .ok lanes => pure lanes
    | .error e => throwErrorAt id "{e}"
  let declName := (← getCurrNamespace) ++ id.getId
  addRow declName w lanes (match doc? with
    | some doc => doc.getDocString
    | none => s!"A packed row of {xs'.size} decoded values at the denominator {d}, in lanes of \
      width {w}.")
    stx id
  let link := mkIdentFrom id (id.getId ++ `link)
  let wLit := Syntax.mkNumLit (toString w)
  let dLit := Syntax.mkNumLit (toString d)
  elabCommand (← `(
    /-- The kernel-checked link between the row and the decoded values. -/
    theorem $link : link $wLit $dLit (values $xs) $id = true := by decide +kernel))

end FloatLib.Floats.ExecFloat.Packed
