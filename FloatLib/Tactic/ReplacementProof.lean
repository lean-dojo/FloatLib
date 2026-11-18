/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Util.Provenance

/-!
# Proofs for compiler replacements

The attribute registers a checked equality for an `implemented_by` replacement.

See Note [FloatLib registry trust] for the shared proof checks.
-/

public meta section

/--
`@[replacement_proof]` registers a theorem `replacement x₁ … xₙ = definition x₁ … xₙ` as the proof
that the `@[implemented_by replacement]` code of `definition` computes it. `requireCompiled`
accepts a replacement only with such a proof.
-/
syntax (name := Parser.Attr.replacement_proof) "replacement_proof" : attr

namespace FloatLib.Numerics.Provenance

open Lean Meta

/-- Register `proof` as the replacement proof of the definition on the right of its equation. -/
def addReplacementProof (proof : Name) (kind : AttributeKind) : MetaM Unit := do
  let info ← getConstInfo proof
  let definition ← forallTelescope info.type fun _ conclusion => do
    let some (_, _, rhs) := conclusion.eq?
      | throwError "`@[replacement_proof]`: the statement of `{.ofConstName proof}` must end in \
          an equation `replacement x = definition x`"
    let some name := rhs.getAppFn.constName?
      | throwError "`@[replacement_proof]`: the right side of `{.ofConstName proof}` is not an \
          applied definition"
    return name
  let some replacement := Compiler.getImplementedBy? (← getEnv) definition
    | throwError "`@[replacement_proof]`: `{.ofConstName definition}` has no \
        `@[implemented_by]` replacement"
  checkReplacementEquality definition replacement proof
  requireProved `replacement_proof proof
    "A replacement is registered only with a complete proof that it equals the definition"
  replacementProofExt.add (definition, proof) kind

initialize
  registerBuiltinAttribute {
    name := `replacement_proof
    descr := "proof that an `@[implemented_by]` replacement computes its definition"
    applicationTime := .afterCompilation
    add := fun declName _ kind => discard <| (addReplacementProof declName kind).run {} {} }

end FloatLib.Numerics.Provenance
