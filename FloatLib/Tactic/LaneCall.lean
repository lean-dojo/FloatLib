/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import Lean.Elab.Command
public meta import Lean.Meta.Basic
public import FloatLib.Util.Provenance

/-!
# Replacements inside lane programs

`@[lane_call]` registers an equation for a function that the packed evaluator cannot unfold.
The equation is checked when the attribute is applied; `lane_decide` uses it when reading a
program. See Note [FloatLib registry trust] for the shared axiom check.
-/

public meta section

/--
`@[lane_call]` registers a replacement for a function that lane programs cannot unfold. The
theorem has the shape `∀ parameters v, v < limit → replacement v = function parameters v`, with
the lane argument last.
-/
syntax (name := Parser.Attr.lane_call) "lane_call" : attr

namespace FloatLib.Numerics.Packed.Reify

open Lean Meta Elab

/-- The registered replacements: the replaced function and the theorem. -/
initialize laneCallExt : SimpleScopedEnvExtension (Name × Name) (NameMap Name) ←
  registerSimpleScopedEnvExtension {
    initial := {}
    addEntry := fun table (function, proof) => table.insert function proof }

initialize
  registerBuiltinAttribute {
    name := `lane_call
    descr := "replacement of a function inside lane programs"
    applicationTime := .afterCompilation
    add := fun declName _ kind => do
      let info ← getConstInfo declName
      let function ← (forallTelescope info.type fun _ conclusion => do
        let some (_, _, rhs) := conclusion.eq?
          | throwError "`@[lane_call]`: the statement of `{.ofConstName declName}` must end \
              in an equation `replacement v = function parameters v`"
        let some name := rhs.getAppFn.constName?
          | throwError "`@[lane_call]`: the right side of `{.ofConstName declName}` is not an \
              applied function"
        return name : MetaM Name).run' {} {}
      FloatLib.Numerics.Provenance.requireProved `lane_call declName
        "A replacement inside lane programs is registered only with a complete proof"
      laneCallExt.add (function, declName) kind }

end FloatLib.Numerics.Packed.Reify
