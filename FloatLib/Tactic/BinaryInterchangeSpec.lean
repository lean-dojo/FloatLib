/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Proof.Exact

/-!
# Binary interchange specification rewriting

The tactic rewrites descriptor arithmetic with the family's proved specification equations.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

/--
Rewrite binary-interchange descriptor arithmetic in the goal and local hypotheses to its exact
specifications. When a public-to-specification equality is itself the goal, use `grind` instead.
-/
syntax (name := binaryInterchangeSpec) "binary_interchange_spec" : tactic

macro_rules
| `(tactic| binary_interchange_spec) =>
    `(tactic|
      simp_all (failIfUnchanged := false) only [
        FloatLib.Floats.Formats.BinaryInterchange.Model.Proof.add_eq_spec,
        FloatLib.Floats.Formats.BinaryInterchange.Model.Proof.sub_eq_spec,
        FloatLib.Floats.Formats.BinaryInterchange.Model.Proof.mul_eq_spec,
        FloatLib.Floats.Formats.BinaryInterchange.Model.Proof.div_eq_spec,
        FloatLib.Floats.Formats.BinaryInterchange.Model.Proof.sqrt_eq_spec,
        FloatLib.Floats.Formats.BinaryInterchange.Model.Proof.fma_eq_spec
      ])

end FloatLib.Floats.Formats.BinaryInterchange.Model
